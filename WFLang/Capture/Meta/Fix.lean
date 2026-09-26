import RequestProject.WFLang.Capture.Meta.Signature

/-!
# Capture metaprogramming: the well-founded definition of a Lean function

The `WellFounded.fix` Lean used to define a function (`findFixIn`), and the recognition of
structural, well-founded and mutual recursion.
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-! ## The well-founded definition of a Lean function -/

/-- The well-founded definition of a Lean function `fn`, seen at its parameters `xs`:
the `WellFounded.fix` (or `WellFounded.Nat.fix`) application Lean used to define it, with its
domain `dom`, relation `r`, well-foundedness proof `hwf` and functional `F`.  The first
`nFixed` parameters are *fixed*: Lean keeps them outside the fixpoint, so `dom`, `r`, `hwf`
and `F` may mention `xs[0], …, xs[nFixed-1]`. -/
structure FixInfo where
  nFixed : Nat
  /-- The positions (in `xs`) of the parameters packed into the argument of the fixpoint, in
  packing order, when they could be read off; `none` if unknown (then the fixed parameters are
  assumed to be the first `nFixed`). -/
  varying : Option (List Nat) := none
  /-- The argument of the fixpoint (the parameters, packed), if the definition applies it. -/
  arg? : Option Lean.Expr := none
  dom : Lean.Expr
  r : Lean.Expr
  hwf : Lean.Expr
  F : Lean.Expr

/-- Find the well-founded definition of `fn`, instantiated at the parameters `xs`. -/
def findFixIn (fn : Name) (xs : Array Lean.Expr) (lvls : List Level := []) : MetaM FixInfo := do
  -- the number of parameters packed into the domain (nested non-dependent `PSigma`s)
  let rec packed (α : Lean.Expr) (fuel : Nat) : MetaM Nat := do
    let α ← whnfR α
    match fuel with
    | 0 => return 1
    | fuel + 1 =>
      if α.isAppOfArity ``PSigma 2 then
        let B := α.getArg! 1
        if B.isLambda && !B.bindingBody!.hasLooseBVars then
          return 1 + (← packed B.bindingBody! fuel)
      return 1
  -- the parameters packed into the argument `x` of the fixpoint (nested `PSigma.mk`)
  let rec leaves (x : Lean.Expr) (fuel : Nat) : List Lean.Expr :=
    match fuel with
    | 0 => [x]
    | fuel + 1 =>
      let x := x.consumeMData
      if x.isAppOfArity ``PSigma.mk 4 then x.getArg! 2 :: leaves (x.getArg! 3) fuel else [x]
  let varyingOf (x? : Option Lean.Expr) (n : Nat) : Option (List Nat) := do
    let x ← x?
    let ps ← (leaves x xs.size).mapM fun l => xs.findIdx? (· == l)
    guard (ps.length == n && ps.eraseDups.length == n)
    return ps
  let mkInfo (dom r hwf F : Lean.Expr) (x? : Option Lean.Expr) : MetaM FixInfo := do
    let n ← packed dom xs.size
    return { nFixed := xs.size - n, varying := varyingOf x? n, arg? := x?, dom, r, hwf, F }
  let rec go (e : Lean.Expr) (i : Nat) (unfoldDepth : Nat) : MetaM FixInfo := do
    let e := e.consumeMData.headBeta
    if e.isLambda then
      if h : i < xs.size then
        return ← go (e.bindingBody!.instantiate1 xs[i]) (i + 1) unfoldDepth
      throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
    let h := e.getAppFn
    if h.isConstOf ``WellFounded.fix && e.getAppNumArgs ≥ 5 then
      return ← mkInfo (e.getArg! 0) (e.getArg! 2) (e.getArg! 3) (e.getArg! 4) (if e.getAppNumArgs > 5 then some (e.getArg! 5) else none)
    if h.isConstOf ``WellFounded.Nat.fix && e.getAppNumArgs ≥ 4 then
      let nat := Lean.mkConst ``Nat
      let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
        mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
      let r ← mkAppM ``InvImage #[lt, e.getArg! 2]
      let hwf ← mkAppM ``InvImage.wf #[e.getArg! 2,
        ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
      let hwf ← mkExpectedTypeHint hwf (← mkAppM ``WellFounded #[r])
      return ← mkInfo (e.getArg! 0) r hwf (e.getArg! 3) (if e.getAppNumArgs > 4 then some (e.getArg! 4) else none)
    match unfoldDepth, h with
    | d + 1, .const c lvls =>
      -- only the auxiliary definitions of `fn` itself (`fn._unary`, …), not other functions
      -- (in particular not the `where`/`let rec` helpers `fn.go` of a non-recursive `fn`)
      unless c.getPrefix == fn && c.isInternal do
        throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
      let info ← getConstInfo c
      let some _ := info.value? (allowOpaque := true) |
        throwError "#lean_wf_func_to_term: {c} has no definition"
      let v ← instantiateValueLevelParams info lvls
      go (mkAppN v e.getAppArgs) i d
    | _, _ => throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
  let info ← getConstInfo fn
  let some v := info.value? (allowOpaque := true) |
    throwError "#lean_wf_func_to_term: {fn} has no definition"
  let v ← if lvls.isEmpty then pure v else instantiateValueLevelParams info lvls
  go v 0 3

/-- `findFixIn`, or `none` if `fn` is not defined by well-founded recursion. -/
def findFixIn? (fn : Name) (xs : Array Lean.Expr) (lvls : List Level := []) :
    MetaM (Option FixInfo) :=
  try some <$> findFixIn fn xs lvls catch _ => pure none

/-- If `fn` is defined by *structural* recursion on one of its (`Nat`) parameters: the position
of that parameter. -/
def structRecArg? (fn : Name) : MetaM (Option Nat) := do
  let some info := Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) fn | return none
  return some info.recArgPos

/-- `set_option wfLang.pfixMeasure k` chooses the measure of the functions defined by
`partial_fixpoint`: the `k`-th candidate of `pfixCandidates` (the value of a `Nat` parameter,
the length of a `List` parameter, or the difference `a - b` of two `Nat` parameters), which must
decrease at each recursive call.  `#lean_wf_func_to_term f` for such an `f` tries each candidate
in turn (unless this option is set). -/
register_option wfLang.pfixMeasure : Nat := {
  defValue := 0
  descr := "#lean_wf_func_to_term: the measure of a partial_fixpoint function (index among the candidate measures)"
}

/-- Is `fn` defined by `partial_fixpoint` (a single function, not a mutual group)? -/
def isPFix (fn : Name) : MetaM Bool := do
  let some info := Lean.Elab.PartialFixpoint.eqnInfoExt.find? (← getEnv) fn | return false
  return info.declNames.size == 1

/-- A candidate measure of a function defined by `partial_fixpoint`, in terms of the positions
of its parameters. -/
inductive PFixMeasure where
  /-- the value of the `Nat` parameter `i` -/
  | val (i : Nat)
  /-- the length of the `List` parameter `i` -/
  | len (i : Nat)
  /-- `a - b` for the `Nat` parameters `a`, `b` (e.g. `n - i` for a counter `i` going up to `n`) -/
  | diff (a b : Nat)
  deriving Inhabited, BEq

/-- The candidate measures of a `partial_fixpoint` definition `fn`, in the order they are tried:
the values of its `Nat` parameters and the lengths of its `List` parameters, then the
differences of two `Nat` parameters. -/
def pfixCandidates (fn : Name) : MetaM (Array PFixMeasure) := do
  forallTelescope (← inferType (← mkConstWithLevelParams fn)) fun xs _ => do
    let mut out := #[]
    let mut nats := #[]
    for i in [0:xs.size] do
      let t ← whnfR (← inferType xs[i]!)
      if t.isConstOf ``Nat then
        out := out.push (.val i)
        nats := nats.push i
      else if t.isAppOfArity ``List 1 then out := out.push (.len i)
    for a in nats do
      for b in nats do
        if a != b then out := out.push (.diff a b)
    return out

/-- For a function defined by `partial_fixpoint`: the measure chosen for it
(`wfLang.pfixMeasure`).  Lean gives no termination argument for such a function; the capture
uses this one, and each recursive call must be proved to decrease it (as for the other
functions, from the path condition).  The agreement theorem then states that the function is
total and equal to the program. -/
def pfixMeasure? (fn : Name) : MetaM (Option PFixMeasure) := do
  unless ← isPFix fn do return none
  let k := wfLang.pfixMeasure.get (← getOptions)
  return (← pfixCandidates fn)[k]?

/-- The parameter whose value (or length) decreases at each recursive call of `fn`: the
argument of its structural recursion, or the parameter measuring a `partial_fixpoint`
definition. -/
def recArgOrMeasure? (fn : Name) : MetaM (Option Nat) := do
  if let some i ← structRecArg? fn then return some i
  match ← pfixMeasure? fn with
  | some (.val i) | some (.len i) => return some i
  | _ => return none

/-- Is `fn` recursive, i.e. defined by well-founded or by structural recursion (or by
`partial_fixpoint`, with a measure: `pfixMeasure?`)? -/
def isWFRec (fn : Name) : MetaM Bool := do
  if (← structRecArg? fn).isSome then return true
  if (← pfixMeasure? fn).isSome then return true
  -- (a member of a group of mutually recursive functions defined by well-founded recursion)
  if (Lean.Elab.WF.eqnInfoExt.find? (← getEnv) fn).isSome then return true
  forallTelescope (← inferType (← mkConstWithLevelParams fn)) fun xs _ => do
    return (← findFixIn? fn xs).isSome

/-- The group of mutually recursive functions `fn` belongs to (with at least two members). -/
def mutualGroup? (fn : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  if let some i := Lean.Elab.Structural.eqnInfoExt.find? env fn then
    if i.declNames.size > 1 then return some i.declNames
  if let some i := Lean.Elab.WF.eqnInfoExt.find? env fn then
    if i.declNames.size > 1 then return some i.declNames
  return none

end WFLang.Meta
