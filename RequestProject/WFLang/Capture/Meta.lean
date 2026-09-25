import Lean
import Mathlib.Tactic.CasesM
import RequestProject.WFLang.Core.PExpr
import RequestProject.WFLang.Core.Loops
import RequestProject.WFLang.Core.While

/-!
# Reading a well-founded Lean function (metaprogramming for the capture)

* reading a Lean function: its signature (`signatureOf`), the right-hand side of its unfolding
  equation (`withEqnRhs`), the `WellFounded.fix` Lean used to define it (`findFixIn`), the
  decreasing proofs at its recursive call sites (`callSiteProofs`), and the pull-back of its
  well-founded relation to environments (`pullBackRel`, `closedRel`, `closedFixOf`);
* calls to other user functions: the attribute `@[inlinable]`; non-recursive `@[inlinable]`
  functions are inlined (`inlineCalls`), recursive `@[inlinable]` ones are reported
  (`recCallees`) so that the capture turns them into loops at the call site (if they are
  tail-recursive) or global functions, and the other ones are collected as global functions of
  the program (`collectGlobals`);
  calls whose arguments are all known are evaluated first (`foldCall?`, `wfFoldCalls`);
* the skeleton of the agreement tactic (`agreeTarget`, `agreeRec`, `rewriteCalleesWith`) and the
  tactics `wf_dec` (one decrease obligation) and `wf_close` (the goals left after unfolding).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-! ## Types and signatures -/

/-- The object type of a Lean type (`Nat`, `Bool`, `Int`, pairs, lists).  A subtype
`{x : α // P x}` is represented by its carrier `α` (its property becomes a postcondition). -/
partial def tyOf (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfR e
  if e.isConstOf ``Nat then return mkConst ``WFLang.Ty.nat
  if e.isConstOf ``Bool then return mkConst ``WFLang.Ty.bool
  if e.isConstOf ``Int then return mkConst ``WFLang.Ty.int
  if e.isAppOfArity ``Prod 2 then
    return mkApp2 (mkConst ``WFLang.Ty.prod) (← tyOf (e.getArg! 0)) (← tyOf (e.getArg! 1))
  if e.isAppOfArity ``List 1 then return mkApp (mkConst ``WFLang.Ty.list) (← tyOf (e.getArg! 0))
  if e.isAppOfArity ``Subtype 2 then return ← tyOf (e.getArg! 0)
  throwError "#lean_wf_func_to_term: unsupported type {e} (only Nat, Bool, Int, pairs, lists and subtypes of them)"

/-- Build a list literal of object types. -/
def mkTyList (ts : List Lean.Expr) : Lean.Expr :=
  ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``WFLang.Ty) t acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``WFLang.Ty))

/-- The parameters of a Lean function, split into *object* parameters (of an object type) and
*proof* parameters (of a `Prop` type: a precondition), and its result. -/
structure FnSig where
  /-- positions of the object parameters -/
  objPos : List Nat
  /-- positions of the proof parameters -/
  prfPos : List Nat
  /-- object types of the object parameters -/
  argTys : List Lean.Expr
  /-- object type of the result (the carrier of a subtype) -/
  retTy : Lean.Expr
  /-- total number of parameters -/
  arity : Nat
  /-- is the result a subtype (i.e. is there a postcondition)? -/
  subtypeRet : Bool
  /-- number of *lifted* variables (free variables of the function arguments of a
  specialised function), which come first in the parameters of the global function -/
  nExtra : Nat := 0
  /-- positions of the specialised parameters (function, type and instance parameters) -/
  specPos : List Nat := []
  /-- for a member of a group of mutually recursive functions: its index in the group (the tag
  passed as the first argument of the global function capturing the group) -/
  tag : Option Nat := none
  /-- for a function that calls itself inside a function argument (captured together with the
  specialised function, see `Translate.HOInfo`): the number of padded parameters after its own -/
  pad : Nat := 0
  deriving Inhabited

/-! ## Specialisation of function parameters -/

/-- Is a parameter with binder type `d` and binder info `bi` *specialised* when a function is
captured at a call site: a type, an instance, or a function (a non-`Prop` `∀`)? -/
def isSpecBinder (d : Lean.Expr) (bi : BinderInfo) : MetaM Bool := do
  if bi.isInstImplicit then return true
  let d' ← whnfR d
  if d'.isSort then return true
  if d'.isForall then return !(← isProp d)
  return false

/-- A function to capture, possibly *specialised*: its specialised parameters
(`isSpecBinder`: function, type and instance parameters) are replaced by the values `spec` (in
order), which are abstracted over the *lifted* variables (of types `extraTys`): the free
variables of the function arguments at the call site.  The lifted variables become the first
(fixed) parameters of the loop or global function capturing the specialised copy.  E.g.
`Tco.iter Tco.mc91`, or `WFLang.rangeLoop (fun i s => s + i * n)` with `n` lifted. -/
structure FnRef where
  name : Name
  /-- universe levels of the constant (`[]`: its level parameters) -/
  levels : List Level := []
  /-- Lean types of the lifted variables -/
  extraTys : Array Lean.Expr := #[]
  /-- values of the specialised parameters, as `fun ys => v` over the lifted variables -/
  spec : Array Lean.Expr := #[]
  /-- if non-empty: the group of mutually recursive functions `name` belongs to, captured as one
  global function whose first parameter (a tag `i`) selects the function `group[i]` -/
  group : Array Name := #[]
  deriving Inhabited

instance : Coe Name FnRef := ⟨fun n => { name := n }⟩

/-- Is this a specialised copy? -/
def FnRef.isSpec (f : FnRef) : Bool := !f.spec.isEmpty

/-- The constant of `f`, at its universe levels. -/
def FnRef.const (f : FnRef) : MetaM Lean.Expr := do
  if f.levels.isEmpty then mkConstWithLevelParams f.name else return mkConst f.name f.levels

/-- Structural equality of two references (up to binder names). -/
def FnRef.beq (f g : FnRef) : Bool :=
  f.name == g.name && f.levels == g.levels && f.extraTys == g.extraTys && f.spec == g.spec &&
    f.group == g.group

/-- Adapt the value `v` of a specialised parameter to the binder type `d`: a `λ` gets the binder
types of `d` (they may mention other parameters, e.g. `i < n` in `Nat.fold`). -/
def respec (d v : Lean.Expr) : MetaM Lean.Expr := do
  let n := v.getNumHeadLambdas
  if n == 0 then return v
  forallBoundedTelescope d (some n) fun zs _ => do
    mkLambdaFVars zs (v.beta zs).headBeta

/-- The positions of the specialised parameters of the constant `fn` applied to `args`. -/
def specPosAt (fn : Lean.Expr) (args : Array Lean.Expr) : MetaM (List Nat) := do
  let mut ty ← inferType fn
  let mut out := #[]
  for i in [0:args.size] do
    ty ← whnfR ty
    let .forallE _ d b bi := ty | break
    if ← isSpecBinder d bi then out := out.push i
    ty := b.instantiate1 args[i]!
  return out.toList

def FnRef.telescopeAux {n : Type → Type} [MonadControlT MetaM n] [Monad n]
    [MonadLiftT MetaM n] {α : Type} (f : FnRef) (ys : Array Lean.Expr) (ty : Lean.Expr)
    (xs : Array Lean.Expr) (j : Nat)
    (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → n α) : (fuel : Nat) → n α
  | 0 => k ys xs ty
  | fuel + 1 => do
  let ty ← if ty.isForall then pure ty else liftM (m := MetaM) (whnfR ty)
  match ty with
  | .forallE nm d b bi =>
    if f.isSpec && (← liftM (m := MetaM) (isSpecBinder d bi)) then
      let some v := f.spec[j]? |
        liftM (m := MetaM) (throwError "#lean_wf_func_to_term: missing function argument of {f.name}")
      let v ← liftM (m := MetaM) (respec d (v.beta ys))
      f.telescopeAux ys (b.instantiate1 v) (xs.push v) (j + 1) k fuel
    else
      withLocalDecl nm bi d fun x => f.telescopeAux ys (b.instantiate1 x) (xs.push x) j k fuel
  | _ => k ys xs ty

/-- Run `k ys xs r` where `ys` are (fresh) lifted variables, `xs` the arguments of `f.name`:
the specialised values at the specialised positions and fresh variables elsewhere, and `r` the
result type. -/
def FnRef.telescope {n : Type → Type} [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
    {α : Type} (f : FnRef) (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → n α) : n α := do
  let ty ← liftM (m := MetaM) (do inferType (← f.const))
  let rec withYs (tys : List Lean.Expr) (ys : Array Lean.Expr) : n α :=
    match tys with
    | [] => f.telescopeAux ys ty #[] 0 k 1000
    | t :: ts => withLocalDeclD (Name.mkSimple s!"y{ys.size}") t fun y => withYs ts (ys.push y)
  withYs f.extraTys.toList #[]

/-- The signature of `fn` (of its specialised copy, for a specialised reference; of the local
recursive function capturing the group, for a group of mutually recursive functions: a tag
parameter in front of the common parameters). -/
partial def fnSig (f : FnRef) : MetaM FnSig := do
  if !f.group.isEmpty then
    let sigs ← f.group.mapM fun n => fnSig { name := n }
    let s0 := sigs[0]!
    for (n, s) in f.group.zip sigs do
      unless s.argTys == s0.argTys && s.retTy == s0.retTy && s.prfPos.isEmpty &&
          !s.subtypeRet && s.objPos == s0.objPos do
        throwError "#lean_wf_func_to_term: the mutually recursive functions {f.group} must have the same parameter and result types, without proof parameters or subtype results ({n} differs)"
    return { s0 with argTys := mkConst ``WFLang.Ty.nat :: s0.argTys }
  if f.isSpec then
    return ← f.telescope fun ys xs r => do
      let mut objPos := #[]
      let mut prfPos := #[]
      let mut specPos := #[]
      let mut argTys := #[]
      for y in ys do argTys := argTys.push (← tyOf (← inferType y))
      let ty0 ← inferType (← f.const)
      let mut ty := ty0
      for i in [0:xs.size] do
        ty ← whnfR ty
        let .forallE _ d b bi := ty | break
        if ← isSpecBinder d bi then specPos := specPos.push i
        else if ← isProp d then prfPos := prfPos.push i
        else
          objPos := objPos.push i
          argTys := argTys.push (← tyOf d)
        ty := b.instantiate1 xs[i]!
      let r' ← whnfR r
      return { objPos := objPos.toList, prfPos := prfPos.toList, argTys := argTys.toList,
               retTy := ← tyOf r, arity := xs.size, subtypeRet := r'.isAppOfArity ``Subtype 2,
               nExtra := ys.size, specPos := specPos.toList }
  let fn := f.name
  let fnTy ← inferType (← mkConstWithLevelParams fn)
  forallTelescope fnTy fun xs r => do
    let mut objPos := #[]
    let mut prfPos := #[]
    let mut argTys := #[]
    for i in [0:xs.size] do
      let ty ← inferType xs[i]!
      let d ← xs[i]!.fvarId!.getDecl
      if ← isSpecBinder d.type d.binderInfo then
        throwError "#lean_wf_func_to_term: {fn} has a function (or type) parameter; capture a copy specialised to a closed function instead: `#lean_wf_func_to_term ({fn} f)`"
      if ← isProp ty then prfPos := prfPos.push i
      else
        objPos := objPos.push i
        argTys := argTys.push (← tyOf ty)
    let r' ← whnfR r
    return { objPos := objPos.toList, prfPos := prfPos.toList, argTys := argTys.toList,
             retTy := ← tyOf r, arity := xs.size, subtypeRet := r'.isAppOfArity ``Subtype 2 }

/-- The object types of the (object) arguments and of the result of `fn`. -/
def signatureOf (fn : FnRef) : MetaM (List Lean.Expr × Lean.Expr) := do
  let s ← fnSig fn
  return (s.argTys, s.retTy)

/-- The `i`-th component of an environment `e`. -/
def envProj (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
  let mut v := e
  for _ in [0:i] do v ← mkAppM ``Prod.snd #[v]
  mkAppM ``Prod.fst #[v]

/-- The `i`-th of `n` components of a proof of a right-nested conjunction. -/
def conjProj (h : Lean.Expr) (i n : Nat) : MetaM Lean.Expr := do
  let mut v := h
  for _ in [0:i] do v ← mkAppM ``And.right #[v]
  if i + 1 < n then mkAppM ``And.left #[v] else return v

/-- The right-nested conjunction of `ps` (`True` if empty). -/
def mkConj : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``And) p (mkConj ps)

/-- For `fn` with parameters `xs` (a telescope of its type): its precondition, as a predicate
on environments of its object parameters (`none` if it has no proof parameter), and its
postcondition, as a relation between environments and results (`none` if the result is not a
subtype).  Proof parameters may depend on object parameters only. -/
def prePostOf (fn : FnRef) (xs : Array Lean.Expr) (resTy : Lean.Expr)
    (ys : Array Lean.Expr := #[]) : MetaM (Option Lean.Expr × Option Lean.Expr) := do
  let sig ← fnSig fn
  let gam := mkTyList sig.argTys
  let objXs := ys ++ (sig.objPos.map (xs[·]!)).toArray
  let prfXs := (sig.prfPos.map (xs[·]!)).toArray
  withLocalDeclD `e (mkApp (mkConst ``WFLang.Env) gam) fun e => do
    let vals ← (List.range sig.argTys.length).toArray.mapM (envProj e)
    let pre ← if sig.prfPos.isEmpty then pure none else do
      let props ← prfXs.toList.mapM fun h => do
        let ty := (← inferType h).replaceFVars objXs vals
        if ty.hasAnyFVar (prfXs.contains <| mkFVar ·) then
          throwError "#lean_wf_func_to_term: a proof parameter of {fn.name} depends on another one"
        pure ty
      pure (some (← mkLambdaFVars #[e] (mkConj props)))
    let r ← whnfR resTy
    let post ← if !r.isAppOfArity ``Subtype 2 then pure none else do
      let P := (r.getArg! 1).replaceFVars objXs vals
      if P.hasAnyFVar (prfXs.contains <| mkFVar ·) then
        throwError "#lean_wf_func_to_term: the result type of {fn.name} depends on a proof parameter"
      let vTy := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
      pure (some (← withLocalDeclD `v vTy fun v => do
        mkLambdaFVars #[e, v] (P.beta #[v]).headBeta))
    return (pre, post)

/-- Binary `Nat` operators, as `(BinOp constructor, lhs, rhs)`. -/
def natBin? (e : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) :=
  let ops : List (Name × Name) := [(``HAdd.hAdd, ``WFLang.BinOp.add),
    (``HSub.hSub, ``WFLang.BinOp.sub), (``HMul.hMul, ``WFLang.BinOp.mul),
    (``HDiv.hDiv, ``WFLang.BinOp.div), (``HMod.hMod, ``WFLang.BinOp.mod),
    (``HPow.hPow, ``WFLang.BinOp.pow), (``HShiftLeft.hShiftLeft, ``WFLang.BinOp.shiftLeft),
    (``HShiftRight.hShiftRight, ``WFLang.BinOp.shiftRight), (``HAnd.hAnd, ``WFLang.BinOp.land),
    (``HOr.hOr, ``WFLang.BinOp.lor), (``HXor.hXor, ``WFLang.BinOp.xor)]
  ops.findSome? fun (n, op) =>
    if e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Nat && (e.getArg! 1).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5) else none

/-- Binary `Int` operators, as `(BinOp constructor, lhs, rhs)`. -/
def intBin? (e : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) :=
  let ops : List (Name × Name) := [(``HAdd.hAdd, ``WFLang.BinOp.iadd),
    (``HSub.hSub, ``WFLang.BinOp.isub), (``HMul.hMul, ``WFLang.BinOp.imul),
    (``HDiv.hDiv, ``WFLang.BinOp.idiv), (``HMod.hMod, ``WFLang.BinOp.imod)]
  ops.findSome? fun (n, op) =>
    if e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Int && (e.getArg! 1).isConstOf ``Int then
      some (op, e.getArg! 4, e.getArg! 5) else none

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

/-- Is `fn` recursive, i.e. defined by well-founded or by structural recursion? -/
def isWFRec (fn : Name) : MetaM Bool := do
  if (← structRecArg? fn).isSome then return true
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

/-! ## Calls to other functions -/

/-- `@[inlinable]` marks a function whose calls `#lean_wf_func_to_term` inlines: a
non-recursive function is replaced by its body, a tail-recursive one becomes a loop (a
recursive join point) at the call site, and a recursive one with non-tail self calls becomes a
global function after all.  The calls of the functions *not* marked `@[inlinable]` are
calls of **global functions**: each such function is captured once, as an entry of the global
context of the program, and called from there (`Expr.gCall`). -/
initialize inlinableAttr : TagAttribute ←
  registerTagAttribute `inlinable
    "#lean_wf_func_to_term inlines the calls of this function (otherwise it is a global function of the captured program)"

/-- Is `c` marked `@[inlinable]`? -/
def isInlinable (c : Name) : CoreM Bool :=
  return inlinableAttr.hasTag (← getEnv) c


/-- Is `c` a constant of a library (`Init`, `Std`, `Lean`, `Mathlib`, `Batteries`)?  Library
functions are primitives of the translation or unsupported, never inlined. -/
def isLibraryConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? c | return false
  let mod := env.header.moduleNames[idx.toNat]!
  return [`Init, `Std, `Lean, `Mathlib, `Batteries].contains mod.getRoot

/-- Is `c` an internal name (an auxiliary definition)?  Private names count as user names. -/
def isInternalName (c : Name) : Bool :=
  ((privateToUserName? c).getD c).isInternal

/-- Is `c` a user-defined first-order function (`Nat`/`Bool` parameters and result), other
than `fn`? -/
def isUserFn (fn c : Name) : MetaM Bool := do
  if c == fn || isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  unless (← getConstInfo c).isDefinition do return false
  try discard <| signatureOf c; return true catch _ => return false

/-- The user-defined first-order functions (other than `fn`) that occur in `e`. -/
def userCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) :=
  e.getUsedConstants.filterM (isUserFn fn)

/-! ## Calls with known arguments -/

/-- `set_option wfLang.foldCalls false` turns off the evaluation, at capture time, of the calls
of user-defined functions whose arguments are all known (see `foldCall?`). -/
register_option wfLang.foldCalls : Bool := {
  defValue := true
  descr := "#lean_wf_func_to_term evaluates the calls of user functions whose arguments are all known (closed terms)"
}

/-- The value of the closed term `e` of an object type (`Nat`, `Bool`, `Int`, pairs, lists), as a
literal, computed by the kernel (the same evaluation that checks `decide +kernel`), if the
kernel reduces it to constructors. -/
partial def kernelValue? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty ← whnfR (← inferType e)
  let env ← getEnv
  let whnfK (x : Lean.Expr) : Option Lean.Expr :=
    match Kernel.whnf env {} x with
    | .ok v => some v
    | .error _ => none
  let rec natVal? (x : Lean.Expr) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match whnfK x with
      | some (.lit (.natVal n)) => some n
      | some v =>
        if v.isConstOf ``Nat.zero then some 0
        else if v.isAppOfArity ``Nat.succ 1 then (natVal? (v.getArg! 0) fuel).map (· + 1)
        else none
      | none => none
  if ty.isConstOf ``Nat then
    return (natVal? e 64).map mkNatLit
  if ty.isConstOf ``Bool then
    let some v := whnfK e | return none
    return if v.isConstOf ``Bool.true || v.isConstOf ``Bool.false then some v else none
  if ty.isConstOf ``Int then
    let some v := whnfK e | return none
    if v.isAppOfArity ``Int.ofNat 1 then
      return (natVal? (v.getArg! 0) 64).map fun n => toExpr (n : Int)
    if v.isAppOfArity ``Int.negSucc 1 then
      return (natVal? (v.getArg! 0) 64).map fun n => toExpr (-((n : Int) + 1))
    return none
  if ty.isAppOfArity ``Prod 2 then
    let some v := whnfK e | return none
    unless v.isAppOfArity ``Prod.mk 4 do return none
    let some a ← kernelValue? (v.getArg! 2) | return none
    let some b ← kernelValue? (v.getArg! 3) | return none
    return some (mkApp4 v.getAppFn (ty.getArg! 0) (ty.getArg! 1) a b)
  if ty.isAppOfArity ``List 1 then
    let some v := whnfK e | return none
    if v.isAppOfArity ``List.nil 1 then return some (mkApp v.getAppFn (ty.getArg! 0))
    unless v.isAppOfArity ``List.cons 3 do return none
    let some h ← kernelValue? (v.getArg! 1) | return none
    let some t ← kernelValue? (v.getArg! 2) | return none
    return some (mkApp3 v.getAppFn (ty.getArg! 0) h t)
  return none

/-- Is `c` a user-defined first-order function whose calls with known arguments can be
evaluated: a function of the user (not of a library, nor of this project's own definitions),
not a matcher, with object parameters and an object result that is not a subtype. -/
def isFoldableFn (c : Name) : MetaM Bool := do
  if isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  if (`WFLang).isPrefixOf c then return false
  unless (← getConstInfo c).isDefinition do return false
  try
    let sig ← fnSig c
    return !sig.subtypeRet && sig.specPos.isEmpty && sig.prfPos.isEmpty
  catch _ => return false

/-- **Evaluation of calls with known arguments.**  If `e` is a fully applied call `g a₁ … aₙ` of
a user-defined function `g` (other than `fn`, whether `g` is `@[inlinable]`, a global function
or a loop) whose arguments are all known (`e` is a closed term), the value
of `e` as a literal.  The capture replaces such a call by its value (so `g` is neither inlined
nor put in the global context for that call), and the agreement tactic proves the equation
`g a₁ … aₙ = v` by kernel evaluation (`wfFoldCalls`).  Turned off by
`set_option wfLang.foldCalls false`. -/
def foldCall? (fn : Name) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless wfLang.foldCalls.get (← getOptions) do return none
  let .const c _ := e.getAppFn | return none
  if c == fn then return none
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  unless ← isFoldableFn c do return none
  unless e.getAppNumArgs == (← fnSig c).arity do return none
  kernelValue? e

/-- The simplification procedure of the agreement proofs matching the evaluation of calls with
known arguments by the capture (`foldCall?`): it rewrites `g a₁ … aₙ` (closed) to its value
`v`, with the proof `of_decide_eq_true rfl`, checked by the kernel. -/
simproc_decl wfFoldCalls (_) := fun e => do
  let some v ← foldCall? .anonymous e | return .continue
  let p ← mkEq e v
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  return .done { expr := v, proof? := some pf }

/-- Replace the calls with known arguments in `e` by their values (`foldCall?`), outside
proofs. -/
def foldCalls (fn : Name) (e : Lean.Expr) : MetaM Lean.Expr := do
  unless wfLang.foldCalls.get (← getOptions) do return e
  Meta.transform e
    (pre := fun e => do
      if e.isApp && !e.hasLooseBVars then
        if (← try isProof e catch _ => pure false) then return .done e
      return .continue)
    (post := fun e => do
      if let some v ← foldCall? fn e then return .done v
      return .continue)

/-- Inline the fully applied calls of the *non-recursive* user-defined functions marked
`@[inlinable]` in `e` (using their unfolding equations `g.eq_def`, transitively), and replace
the calls with known arguments by their values (`foldCall?`, outside proofs).  Returns the new
term and the unfolding equations used.  The calls of the other non-recursive functions stay:
they become calls of global functions. -/
def inlineCalls (fn : Name) (e : Lean.Expr) : MetaM (Lean.Expr × Array Name) := do
  let used ← IO.mkRef (#[] : Array Name)
  let e ← foldCalls fn e
  let e ← Meta.transform e (post := fun e => do
    let .const c _ := e.getAppFn | return .continue
    unless ← isUserFn fn c do return .continue
    unless ← isInlinable c do return .continue
    if ← isWFRec c then return .continue
    let (argTys, _) ← signatureOf c
    unless e.getAppNumArgs == argTys.length do return .continue
    let some eqn ← getUnfoldEqnFor? c (nonRec := true) | return .continue
    let ty ← instantiateForall (← inferType (← mkConstWithLevelParams eqn)) e.getAppArgs
    let some (_, _, rhs) := ty.eq? | return .continue
    if (rhs.find? (·.isConstOf c)).isSome then return .continue
    used.modify fun u => if u.contains eqn then u else u.push eqn
    return .visit rhs)
  return (← foldCalls fn e, ← used.get)

/-! ## Bounded loops -/

/-- The value `t` of a loop body that always continues with `ForInStep.yield t` (through
`let`s and `if`s), if it does. -/
partial def yieldVal? (m : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let m := m.consumeMData
  if m.isLet then return ← yieldVal? (m.letBody!.instantiate1 m.letValue!)
  if m.isAppOfArity ``ForInStep.yield 2 then return some (m.getArg! 1)
  if m.isAppOfArity ``ite 5 then
    let some a ← yieldVal? (m.getArg! 3) | return none
    let some b ← yieldVal? (m.getArg! 4) | return none
    return some (mkAppN m.getAppFn #[← inferType a, m.getArg! 1, m.getArg! 2, a, b])
  return none

/-- `for i in [a:b] do …` (in `Id`, step `1`, a body that always continues) as
`WFLang.rangeLoop (fun i s => …) b a init`. -/
def rangeLoopOfForIn? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless (e.getArg! 1).isConstOf ``Std.Legacy.Range do return none
  let r ← whnfD (e.getArg! 5)
  unless r.isAppOfArity ``Std.Legacy.Range.mk 4 do return none
  unless (← evalNat (r.getArg! 2)) == some 1 do return none
  let body := e.getArg! 7
  lambdaBoundedTelescope body 2 fun zs m => do
    unless zs.size == 2 do return none
    let some t ← yieldVal? m | return none
    return some (← mkAppM ``WFLang.rangeLoop
      #[← mkLambdaFVars zs t, r.getArg! 1, r.getArg! 0, e.getArg! 6])

/-- `Nat.fold n (fun i _ acc => …) init` (the body does not use the proof `i < n`) as
`WFLang.rangeLoop (fun i acc => …) n 0 init`. -/
def rangeLoopOfFold? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  lambdaBoundedTelescope (e.getArg! 2) 3 fun zs b => do
    unless zs.size == 3 do return none
    if b.containsFVar zs[1]!.fvarId! then return none
    return some (← mkAppM ``WFLang.rangeLoop
      #[← mkLambdaFVars #[zs[0]!, zs[2]!] b, e.getArg! 1, mkNatLit 0, e.getArg! 3])

/-- Remove the `Id` monad (`Id.run`, `bind`, `pure`) and rewrite bounded loops (`for` over a
range, `Nat.fold`) into `WFLang.rangeLoop`, whose function argument is then specialised, and
`while` loops with a measure (`WFLang.whileMeasure`, the notation `wf_while`) into the general
well-founded loop `WFLang.whileWF`, which becomes a `PCL` `while` statement. -/
def normLoops (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let isId (m : Lean.Expr) := m.isConstOf ``Id
    if e.isAppOfArity ``Id.run 2 then return .visit (e.getArg! 1)
    if e.isAppOfArity ``Bind.bind 6 && isId (e.getArg! 0) then
      return .visit (mkApp (e.getArg! 5) (e.getArg! 4)).headBeta
    if e.isAppOfArity ``Pure.pure 4 && isId (e.getArg! 0) then return .visit (e.getArg! 3)
    if e.isAppOfArity ``ForIn.forIn 8 && isId (e.getArg! 0) then
      if let some r ← rangeLoopOfForIn? e then return .visit r
    if e.isAppOfArity ``Nat.fold 4 then
      if let some r ← rangeLoopOfFold? e then return .visit r
    -- a `while` loop with a measure: the general well-founded loop `whileWF`
    if e.isAppOfArity ``WFLang.whileMeasure 6 then
      if let some r ← unfoldDefinition? e then return .visit r.headBeta
    return .continue)

/-- Is `c` a recursive function (other than `fn`) with specialised parameters (function, type
or instance parameters), to be captured by specialisation at each call site? -/
def isSpecFn (fn c : Name) : MetaM Bool := do
  if c == fn || isInternalName c || (← isMatcher c) then return false
  -- the library, and the definitions of this project (except the loop combinator)
  if (← isLibraryConst c) then return false
  if (`WFLang).isPrefixOf c && c != ``WFLang.rangeLoop then return false
  unless (← getConstInfo c).isDefinition do return false
  unless ← isWFRec c do return false
  forallTelescope (← inferType (← mkConstWithLevelParams c)) fun xs _ =>
    xs.anyM fun x => do
      let d ← x.fvarId!.getDecl
      isSpecBinder d.type d.binderInfo

/-- A quick syntactic test: does `rhs` apply a recursive function with function parameters to
a function argument that mentions `fn`? -/
def hoCandidate (fn : Name) (rhs : Lean.Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  Meta.forEachExpr rhs fun e => do
    let .const g _ := e.getAppFn | return
    if g == fn then return
    if e.getAppArgs.any (fun a => (a.find? (·.isConstOf fn)).isSome) then
      if ← isSpecFn fn g then found.set true
  found.get

/-- Does the recursive function `g` call itself inside a function argument (e.g. in the body
of a `for` loop)?  Such a function is captured together with the specialised loop (`HOInfo`),
always at its call site. -/
def callsSelfInFnArg (g : Name) : MetaM Bool := do
  let some eqn ← getUnfoldEqnFor? g (nonRec := true) | return false
  forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
    let some (_, _, rhs) := eq.eq? | return false
    hoCandidate g (← normLoops (← Core.betaReduce rhs))

/-- Is the call of `c` (from the capture of `fn`) a call of a **global function**?  That is the
case of every first-order user-defined function not marked `@[inlinable]`, except the members
of a group of mutually recursive functions and the functions calling themselves inside a
function argument, which are always captured at their call sites (as are the functions with
function parameters, which are specialised to the arguments of each call). -/
def isGlobalFn (fn c : Name) : MetaM Bool := do
  unless ← isUserFn fn c do return false
  if ← isInlinable c then return false
  if (← mutualGroup? c).isSome then return false
  if (← isWFRec c) && (← callsSelfInFnArg c) then return false
  return true

/-- The recursive user-defined functions called in `e` (other than `fn`) that are not global by
attribute: those marked `@[inlinable]` (loops at the call site if tail-recursive), and those
that are handled specially (see `isGlobalFn`). -/
def localRecCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) := do
  (← userCallees fn e).filterM fun c => return (← isWFRec c) && !(← isGlobalFn fn c)

/-- The user-defined functions called in `e` (other than `fn`) that are not inlined into a plain
expression: the loops and the global functions.  Their values appear in the agreement proofs as
`fixFn …` / `joinFn …` terms, identified by uniqueness (`rewriteCalleesWith`). -/
def recCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) := do
  (← userCallees fn e).filterM fun c => return (← isWFRec c) || !(← isInlinable c)

/-- Can the definition of `c` contain calls to take into account when collecting the global
functions (a user definition of this project, not an auxiliary one)? -/
def isTraversable (c : Name) : MetaM Bool := do
  if isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  if (`WFLang).isPrefixOf c then return false
  return (← getConstInfo c).isDefinition

/-- The global functions of the capture of `root`, callees first: every function `g` with
`isGlobalFn root g` reachable from `root` through the definitions that are captured (`root`,
its group, the inlined, local and specialised functions, and the global functions
themselves).  Each global function only calls global functions that come before it. -/
partial def collectGlobals (root : Name) (extra : Array Name := #[]) : MetaM (Array Name) := do
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array Name)
  let rec visit (f : Name) : MetaM Unit := do
    if (← visited.get).contains f then return
    visited.modify (·.insert f)
    let some eqn ← (try getUnfoldEqnFor? f (nonRec := true) catch _ => pure none) | return
    let consts ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
      let some (_, _, rhs) := eq.eq? | return #[]
      let (rhs, _) ← inlineCalls f (← normLoops (← Core.betaReduce rhs))
      return rhs.getUsedConstants
    for c in consts do
      if c == root || c == f then continue
      unless ← isTraversable c do continue
      visit c
      if (← isGlobalFn root c) && !(← out.get).contains c then out.modify (·.push c)
  let group := (← mutualGroup? root).getD #[root]
  visited.modify fun v => group.foldl (·.insert ·) v
  for g in group do
    visited.modify (·.erase g)
    visit g
  -- the constants of the function arguments of a specialised root
  for c in extra do
    if c == root || !(← isTraversable c) then continue
    visit c
    if (← isGlobalFn root c) && !(← out.get).contains c then out.modify (·.push c)
  out.get

/-- The reference to the specialised copy of `g` called with the arguments `args` (the
specialised positions `sp`), and the lifted variables (the free variables of the specialised
arguments, in context order). -/
def mkSpecRef (g : Name) (lvls : List Level) (args : Array Lean.Expr) (sp : List Nat) :
    MetaM (FnRef × Array Lean.Expr) := do
  let specArgs := sp.toArray.map (args[·]!)
  let set := specArgs.foldl (fun s a => collectFVars s a) {}
  let lctx ← getLCtx
  let ys := lctx.foldl (init := #[]) fun arr d =>
    if set.fvarSet.contains d.fvarId then arr.push (mkFVar d.fvarId) else arr
  let tys ← ys.mapM inferType
  let spec ← specArgs.mapM (mkLambdaFVars ys ·)
  return ({ name := g, levels := lvls, extraTys := tys, spec }, ys)

/-- The number of parameters of the constant `c`. -/
def constArity (c : Lean.Expr) : MetaM Nat := do
  forallTelescopeReducing (← inferType c) fun xs _ => pure xs.size

/-- The references to specialised copies of recursive functions called (fully applied, outside
binders) in `e`. -/
def specRefsIn (fn : Name) (e : Lean.Expr) : MetaM (Array FnRef) := do
  let out ← IO.mkRef (#[] : Array FnRef)
  Meta.forEachExpr e fun x => do
    if x.hasLooseBVars then return
    let .const g lvls := x.getAppFn | return
    unless ← isSpecFn fn g do return
    let args := x.getAppArgs
    unless args.size == (← constArity (mkConst g lvls)) do return
    let (ref, _) ← mkSpecRef g lvls args (← specPosAt (mkConst g lvls) args)
    unless (← out.get).any (·.beq ref) do out.modify (·.push ref)
  out.get

/-- Run `k ys xs rhs` on the lifted variables `ys`, the arguments `xs` and the right-hand side
of the unfolding equation `fn.eq_def : ∀ xs, fn xs = rhs` (at the specialised values, for a
specialised reference), in which bounded loops are rewritten (`normLoops`) and the calls of
non-recursive `@[inlinable]` functions are inlined (`inlineCalls`). -/
def withEqnRhs' {α : Type} (fn : FnRef)
    (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → TermElabM α) : TermElabM α := do
  let some eqn ← getUnfoldEqnFor? fn.name (nonRec := true) |
    throwError "#lean_wf_func_to_term: no unfolding equation for {fn.name}"
  -- a function-valued right-hand side (`f : α → (β → γ)`) is eta-expanded, so that the
  -- parameters are those of the type of `f`
  let finish (ys xs : Array Lean.Expr) (rhs : Lean.Expr) : TermElabM α := do
    forallTelescope (← inferType rhs) fun zs _ => do
      let rhs ← Core.betaReduce (mkAppN rhs zs)
      k ys (xs ++ zs) (← inlineCalls fn.name (← normLoops rhs)).1
  if !fn.isSpec then
    return ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun xs eq => do
      let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
      finish #[] xs rhs
  fn.telescope fun ys xs _ => do
    let eqC ← if fn.levels.isEmpty then mkConstWithLevelParams eqn
      else pure (Lean.mkConst eqn fn.levels)
    let eq ← instantiateForall (← inferType eqC) xs
    let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
    finish ys xs (← Core.betaReduce rhs)

/-- Run `k xs rhs` on the parameters and the right-hand side of the unfolding equation
`fn.eq_def : ∀ xs, fn xs = rhs` (see `withEqnRhs'`). -/
def withEqnRhs {α : Type} (fn : FnRef) (k : Array Lean.Expr → Lean.Expr → TermElabM α) :
    TermElabM α :=
  withEqnRhs' fn fun _ xs rhs => k xs rhs

/-- The unfolding equations inlined into the right-hand side of `fn.eq_def`, and the recursive
functions it calls (other than `fn`), transitively through the latter. -/
partial def calleeInfo (fn : Name) : MetaM (Array Name × Array Name) := do
  let rec go (todo : List Name) (eqns recs : Array Name) : MetaM (Array Name × Array Name) := do
    match todo with
    | [] => return (eqns, recs)
    | f :: rest =>
      let some eqn ← getUnfoldEqnFor? f (nonRec := true) | go rest eqns recs
      let (es, rs) ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
        let some (_, _, rhs) := eq.eq? | return (#[], #[])
        let (rhs, es) ← inlineCalls f rhs
        return (es, ← recCallees f rhs)
      let eqns := es.foldl (fun acc e => if acc.contains e then acc else acc.push e) eqns
      let new := rs.filter fun r => r != fn && !recs.contains r
      go (rest ++ new.toList) eqns (recs ++ new)
  go [fn] #[] #[]

/-- Collect the decreasing proofs at the recursive call sites in the functional
`F`, closed over the local variables they depend on. -/
partial def callSiteProofs (F : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let rec visit (e : Lean.Expr) : MetaM Unit := do
    match e.consumeMData with
    | .lam .. => lambdaTelescope e fun _ b => visit b
    | .letE .. => lambdaLetTelescope e fun _ b => visit b
    | e@(.app ..) =>
      let f := e.getAppFn
      for a in e.getAppArgs do
        if f.isFVar && (← isProof a) then
          -- close the proof over the free variables it (transitively) depends on
          let lctx ← getLCtx
          let mut fvs : Std.HashSet FVarId := {}
          let mut todo := (collectFVars {} a).fvarIds.toList
          while !todo.isEmpty do
            let fv :: rest := todo | break
            todo := rest
            if fvs.contains fv then continue
            fvs := fvs.insert fv
            let ty ← fv.getType
            todo := todo ++ (collectFVars {} ty).fvarIds.toList
          let ordered := lctx.foldl (init := #[]) fun arr d =>
            if fvs.contains d.fvarId then arr.push (mkFVar d.fvarId) else arr
          acc.modify (·.push (← mkLambdaFVars ordered a))
        visit a
      visit f
    | _ => pure ()
  visit F
  acc.get

/-- Pack an environment tuple into the (nested `PSigma`) domain used by Lean's
well-founded definition. -/
partial def packE (α : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  let α ← whnfR α
  if α.isAppOfArity ``PSigma 2 then
    let A := α.getArg! 0
    let B := α.getArg! 1
    if B.isLambda && !B.bindingBody!.hasLooseBVars then
      let fst ← mkAppM ``Prod.fst #[e]
      let snd ← packE B.bindingBody! (← mkAppM ``Prod.snd #[e])
      return mkApp4 (Lean.mkConst ``PSigma.mk α.getAppFn.constLevels!) A B fst snd
  mkAppM ``Prod.fst #[e]

/-- Lean's well-founded relation `r` (on the packed domain `dom`, with proof `hwf`) pulled back
to environments `Env gam`: the relation and its well-foundedness proof. -/
def pullBackRel (gam dom r hwf : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let envTy := mkApp (mkConst ``WFLang.Env) gam
  let pack ← withLocalDeclD `e envTy fun e => do mkLambdaFVars #[e] (← packE dom e)
  return (← mkAppM ``InvImage #[r, pack], ← mkAppM ``InvImage.wf #[pack, hwf])

/-- Like `closedRel`, when the parameters packed into the fixpoint are those at the positions
`vs` (in packing order) and the fixed parameters (all the others) are not a prefix: the
relation `WFLang.fixedAtRel f g r`, where `f` reads the fixed components of an environment,
`g` packs the others into Lean's domain `dom`, and `r k` is Lean's relation at the fixed
values `k`. -/
def closedRelAt (argTys : List Lean.Expr) (xs : Array Lean.Expr) (dom r hwf : Lean.Expr)
    (vs : List Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  let fixedPos := (List.range xs.size).filter (!vs.contains ·)
  let fixedXs := fixedPos.toArray.map (xs[·]!)
  if dom.hasAnyFVar (fixedXs.contains <| mkFVar ·) then
    throwError "#lean_wf_func_to_term: the domain of the fixpoint depends on a fixed parameter"
  let gam := mkTyList argTys
  let envTy := mkApp (mkConst ``WFLang.Env) gam
  let kTys := mkTyList (fixedPos.map (argTys[·]!))
  let kTy := mkApp (mkConst ``WFLang.Env) kTys
  let proj (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
    let mut v := e
    for _ in [0:i] do v ← mkAppM ``Prod.snd #[v]
    mkAppM ``Prod.fst #[v]
  let tuple (e : Lean.Expr) (ps : List Nat) : MetaM Lean.Expr := do
    let mut t := Lean.mkConst ``Unit.unit
    for i in ps.reverse do t ← mkAppM ``Prod.mk #[← proj e i, t]
    return t
  let f ← withLocalDeclD `e envTy fun e => do mkLambdaFVars #[e] (← tuple e fixedPos)
  let g ← withLocalDeclD `e envTy fun e => do mkLambdaFVars #[e] (← packE dom (← tuple e vs))
  let (rK, hK) ← withLocalDeclD `k kTy fun k => do
    let vals ← (List.range fixedPos.length).toArray.mapM (proj k)
    let r' := r.replaceFVars fixedXs vals
    let hwf' := hwf.replaceFVars fixedXs vals
    return (← mkLambdaFVars #[k] r', ← mkLambdaFVars #[k] hwf')
  let R := mkAppN (mkConst ``WFLang.fixedAtRel [← getLevel dom]) #[gam, kTy, dom, f, g, rK]
  let wf := mkAppN (mkConst ``WFLang.fixedAtRel_wf [← getLevel dom])
    #[gam, kTy, dom, f, g, rK, hK]
  return (R, wf)

/-- Like `closedRelAt`, for a function with proof parameters (a precondition `pre`, a
predicate on environments): Lean's domain then packs the proofs too, so the packing `g` of an
environment needs a proof of `pre`.  The relation is `WFLang.preRel pre f g r`: related
environments satisfy `pre`, agree on the fixed components (read by `f`), and their packings
are related by Lean's relation.  `arg` is the argument of Lean's fixpoint in terms of `xs`. -/
def closedRelPre (fn : Name) (xs : Array Lean.Expr) (dom r hwf arg pre : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let sig ← fnSig fn
  let argTys := sig.argTys
  let objXs := (sig.objPos.map (xs[·]!)).toArray
  let prfXs := (sig.prfPos.map (xs[·]!)).toArray
  -- the fixed parameters: those that are not packed into the argument of the fixpoint
  let fixedIdx := (List.range objXs.size).filter fun i => !arg.containsFVar objXs[i]!.fvarId!
  if prfXs.any (!arg.containsFVar ·.fvarId!) then
    throwError "#lean_wf_func_to_term: a proof parameter of {fn} is fixed (not supported)"
  let fixedXs := (fixedIdx.map (objXs[·]!)).toArray
  let gam := mkTyList argTys
  let envTy := mkApp (mkConst ``WFLang.Env) gam
  let kTys := mkTyList (fixedIdx.map (argTys[·]!))
  let kTy := mkApp (mkConst ``WFLang.Env) kTys
  let tuple (e : Lean.Expr) (ps : List Nat) : MetaM Lean.Expr := do
    let mut t := Lean.mkConst ``Unit.unit
    for i in ps.reverse do t ← mkAppM ``Prod.mk #[← envProj e i, t]
    return t
  let f ← withLocalDeclD `e envTy fun e => do mkLambdaFVars #[e] (← tuple e fixedIdx)
  let g ← withLocalDeclD `e envTy fun e => do
    withLocalDeclD `h (mkApp pre e).headBeta fun h => do
      let vals ← (List.range objXs.size).toArray.mapM (envProj e)
      let prfs ← (List.range prfXs.size).toArray.mapM (conjProj h · prfXs.size)
      mkLambdaFVars #[e, h] ((arg.replaceFVars objXs vals).replaceFVars prfXs prfs)
  let (rK, hK) ← withLocalDeclD `k kTy fun k => do
    let vals ← (List.range fixedIdx.length).toArray.mapM (envProj k)
    return (← mkLambdaFVars #[k] (r.replaceFVars fixedXs vals),
      ← mkLambdaFVars #[k] (hwf.replaceFVars fixedXs vals))
  let lvl ← getLevel dom
  let R := mkAppN (mkConst ``WFLang.preRel [lvl]) #[gam, kTy, dom, pre, f, g, rK]
  let wf := mkAppN (mkConst ``WFLang.preRel_wf [lvl]) #[gam, kTy, dom, pre, f, g, rK, hK]
  return (R, wf)

/-- The well-founded relation of `fn` (found by `findFixIn fn xs`) as a *closed* relation on
environments `Env argTys`, with its well-foundedness proof.  The fixed parameters become
components that every related pair of environments shares (`WFLang.fixedRel`). -/
def closedRel (argTys : List Lean.Expr) (xs : Array Lean.Expr) (info : FixInfo) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let j := info.nFixed
  if let some vs := info.varying then
    if vs != (List.range (xs.size - j)).map (· + j) then
      return ← closedRelAt argTys xs info.dom info.r info.hwf vs
  let (R0, wf0) ← pullBackRel (mkTyList (argTys.drop j)) info.dom info.r info.hwf
  let mut R := R0
  let mut wf := wf0
  for i in (List.range j).reverse do
    let t := argTys[i]!
    let ts := mkTyList (argTys.drop (i + 1))
    let lamR ← mkLambdaFVars #[xs[i]!] R
    let lamWf ← mkLambdaFVars #[xs[i]!] wf
    R := mkApp3 (mkConst ``WFLang.fixedRel) t ts lamR
    wf := mkApp4 (mkConst ``WFLang.fixedRel_wf) t ts lamR lamWf
  return (R, wf)

/-- The relation "the `j`-th component decreases" (its value for `Nat`, its length for a list)
on `Env gam`, with its well-foundedness proof: the relation of a structurally recursive
function. -/
def structRel (gam : Lean.Expr) (j : Nat) (isList : Bool) : MetaM (Lean.Expr × Lean.Expr) := do
  let proj ← withLocalDeclD `e (mkApp (Lean.mkConst ``WFLang.Env) gam) fun e => do
    let v ← envProj e j
    mkLambdaFVars #[e] (← if isList then mkAppM ``List.length #[v] else pure v)
  let nat := Lean.mkConst ``Nat
  let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
    mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
  let R ← mkAppM ``InvImage #[lt, proj]
  let wf ← mkAppM ``InvImage.wf #[proj,
    ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
  return (R, wf)

/-- `closedFixOf` for a specialised copy: the lifted variables become fixed parameters in front
of the object parameters; the specialised parameters must be fixed in Lean's definition too. -/
def closedFixOfSpec (f : FnRef) : MetaM (Option (Lean.Expr × Lean.Expr × Array Lean.Expr)) := do
  let sig ← fnSig f
  unless sig.prfPos.isEmpty do
    throwError "#lean_wf_func_to_term: specialising {f.name}, which has proof parameters, is not supported"
  let changes : MetaM Unit := throwError
    "#lean_wf_func_to_term: a function argument of {f.name} changes in its recursive calls (not supported)"
  f.telescope fun ys xs _ => do
    let objXs := ys ++ (sig.objPos.map (xs[·]!)).toArray
    if let some info ← findFixIn? f.name xs f.levels then
      let remap (p : Nat) : MetaM Nat := do
        match sig.objPos.findIdx? (· == p) with
        | some j => pure (j + ys.size)
        | none => changes; pure 0
      let varying ← info.varying.mapM (·.mapM remap)
      if info.varying.isNone && sig.specPos.any (· ≥ info.nFixed) then changes
      let nFixed := ys.size + (sig.objPos.filter (· < info.nFixed)).length
      let (R, wf) ← closedRel sig.argTys objXs { info with nFixed, varying }
      return some (R, wf, ← callSiteProofs info.F)
    let some i ← structRecArg? f.name | return none
    let some j := sig.objPos.findIdx? (· == i) | return none
    let isList := (← whnfR (← inferType xs[i]!)).isAppOfArity ``List 1
    let (R, wf) ← structRel (mkTyList sig.argTys) (j + ys.size) isList
    return some (R, wf, #[])

/-- For a function `fn` defined by well-founded (or structural) recursion: its relation and well-foundedness
proof as closed terms over `Env argTys` (`closedRel`), and the decreasing proofs at its
recursive call sites (`callSiteProofs`), closed over what they depend on.  `none` if `fn` is not
defined by well-founded recursion. -/
def closedFixOf (f : FnRef) : MetaM (Option (Lean.Expr × Lean.Expr × Array Lean.Expr)) := do
  if f.isSpec then return ← closedFixOfSpec f
  let fn := f.name
  let sig ← fnSig fn
  let argTys := sig.argTys
  forallTelescope (← inferType (← mkConstWithLevelParams fn)) fun xs resTy => do
    if let some info ← findFixIn? fn xs then
      if sig.prfPos.isEmpty then
        let (R, wf) ← closedRel argTys xs info
        return some (R, wf, ← callSiteProofs info.F)
      let some arg := info.arg? |
        throwError "#lean_wf_func_to_term: cannot read the packing of the parameters of {fn}"
      let (some pre, _) ← prePostOf fn xs resTy | unreachable!
      let (R, wf) ← closedRelPre fn xs info.dom info.r info.hwf arg pre
      return some (R, wf, ← callSiteProofs info.F)
    -- structural recursion on parameter `i`: the relation "parameter `i` decreases" (its
    -- value for `Nat`, its length for a list)
    let some i ← structRecArg? fn | return none
    let some j := sig.objPos.findIdx? (· == i) | return none
    let gam := mkTyList argTys
    let isList := (← whnfR (← inferType xs[i]!)).isAppOfArity ``List 1
    let proj ← withLocalDeclD `e (mkApp (Lean.mkConst ``WFLang.Env) gam) fun e => do
      let v ← envProj e j
      mkLambdaFVars #[e] (← if isList then mkAppM ``List.length #[v] else pure v)
    let nat := Lean.mkConst ``Nat
    let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
      mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
    let R ← mkAppM ``InvImage #[lt, proj]
    let wf ← mkAppM ``InvImage.wf #[proj,
      ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
    return some (R, wf, #[])

/-! ## Mutual recursion -/

/-- The reference to `fn`, as a member of its group of mutually recursive functions if it has
one. -/
def FnRef.ofName (fn : Name) : MetaM FnRef := do
  match ← mutualGroup? fn with
  | some g => return { name := fn, group := g }
  | none => return { name := fn }

/-- The `i`-th of the `k` summands of a nested `PSum` type. -/
partial def psumSummand (dom : Lean.Expr) (i k : Nat) : MetaM Lean.Expr := do
  if k ≤ 1 then return dom
  let dom ← whnfR dom
  unless dom.isAppOfArity ``PSum 2 do throwError "#lean_wf_func_to_term: unexpected domain {dom}"
  if i == 0 then return dom.getArg! 0
  psumSummand (dom.getArg! 1) (i - 1) (k - 1)

/-- The injection of `payload` into the `i`-th of the `k` summands of a nested `PSum` type. -/
partial def psumInj (dom : Lean.Expr) (i k : Nat) (payload : Lean.Expr) : MetaM Lean.Expr := do
  if k ≤ 1 then return payload
  let dom ← whnfR dom
  unless dom.isAppOfArity ``PSum 2 do throwError "#lean_wf_func_to_term: unexpected domain {dom}"
  let (α, β) := (dom.getArg! 0, dom.getArg! 1)
  if i == 0 then return ← mkAppOptM ``PSum.inl #[α, β, payload]
  mkAppOptM ``PSum.inr #[α, β, ← psumInj β (i - 1) (k - 1) payload]

/-- `if t = 0 then vs[0] else if t = 1 then vs[1] else … vs[k-1]`. -/
def tagSelect (t : Lean.Expr) (vs : Array Lean.Expr) : MetaM Lean.Expr := do
  let mut v := vs.back!
  for i in (List.range (vs.size - 1)).reverse do
    v ← mkAppM ``ite #[← mkEq t (mkNatLit i), vs[i]!, v]
  return v

/-- The relation of the global function capturing a group of mutually recursive
functions, over environments `(tag, xs)`, with its well-foundedness proof and the decreasing
proofs of the calls.  Structural recursion on the same parameter: that parameter decreases.
Well-founded recursion: Lean's relation on the domain `PSum D₀ (PSum D₁ …)` of the combined
definition `f._mutual`, pulled back along `(i, xs) ↦ inj_i (pack xs)`. -/
def groupFixOf (group : Array Name) : MetaM (Lean.Expr × Lean.Expr × Array Lean.Expr) := do
  let sig ← fnSig { name := group[0]!, group }
  let gam := mkTyList sig.argTys
  let env ← getEnv
  if let some i := Lean.Elab.Structural.eqnInfoExt.find? env group[0]! then
    for g in group do
      let some i' := Lean.Elab.Structural.eqnInfoExt.find? env g | throwError "unexpected"
      unless i'.recArgPos == i.recArgPos do
        throwError "#lean_wf_func_to_term: the mutually recursive functions {group} must recurse on the same parameter"
    let some j := sig.objPos.findIdx? (· == i.recArgPos) |
      throwError "#lean_wf_func_to_term: unexpected recursive parameter"
    let isList := (sig.argTys[j + 1]!).isAppOf ``WFLang.Ty.list
    let (R, wf) ← structRel gam (j + 1) isList
    return (R, wf, #[])
  let some info := Lean.Elab.WF.eqnInfoExt.find? env group[0]! |
    throwError "#lean_wf_func_to_term: {group[0]!} is not defined by well-founded recursion"
  let mutualFn := info.declNameNonRec
  forallTelescope (← inferType (← mkConstWithLevelParams mutualFn)) fun ps _ => do
    let fi ← findFixIn mutualFn ps
    unless fi.nFixed == 0 do
      throwError "#lean_wf_func_to_term: mutually recursive functions with fixed parameters are not supported"
    let k := group.size
    let pack ← withLocalDeclD `e (mkApp (mkConst ``WFLang.Env) gam) fun e => do
      let t ← envProj e 0
      let rest ← mkAppM ``Prod.snd #[e]
      let vs ← (List.range k).toArray.mapM fun i => do
        psumInj fi.dom i k (← packE (← psumSummand fi.dom i k) rest)
      mkLambdaFVars #[e] (← tagSelect t vs)
    return (← mkAppM ``InvImage #[fi.r, pack], ← mkAppM ``InvImage.wf #[pack, fi.hwf],
      ← callSiteProofs fi.F)

/-- `fnSolution` for a group: `F (t, xs) _ = ⟨if t = 0 then f₀ xs else if t = 1 then f₁ xs …, _⟩`. -/
def fnSolutionGroup (f : FnRef) : MetaM Lean.Expr := do
  let sig ← fnSig f
  let envTy := mkApp (mkConst ``WFLang.Env) (mkTyList sig.argTys)
  let retD := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
  withLocalDeclD `x envTy fun x => do
    withLocalDeclD `hx (mkConst ``True) fun hx => do
      let t ← envProj x 0
      let rest ← mkAppM ``Prod.snd #[x]
      let args ← (List.range sig.objPos.length).toArray.mapM (envProj rest)
      let vs ← f.group.mapM fun g => do return mkAppN (← mkConstWithLevelParams g) args
      let v ← tagSelect t vs
      let postX := mkLambda `v .default retD (mkConst ``True)
      mkLambdaFVars #[x, hx]
        (mkApp4 (mkConst ``Subtype.mk [levelOne]) retD postX v (Lean.mkConst ``True.intro))

/-! ## Recursion through a function argument -/

/-- The application of the specialised copy `f` (signature `sig`) to the values `ysV` of its
lifted variables and `objV` of its object parameters. -/
def specApp (f : FnRef) (sig : FnSig) (ysV objV : Array Lean.Expr) : MetaM Lean.Expr := do
  let c ← f.const
  let mut ty ← inferType c
  let mut args := #[]
  let mut j := 0
  let mut k := 0
  for i in [0:sig.arity] do
    ty ← whnfR ty
    let .forallE _ d b _ := ty | throwError "#lean_wf_func_to_term: unexpected type of {f.name}"
    let mut v := d
    if sig.specPos.contains i then
      v ← respec d (f.spec[j]!.beta ysV)
      j := j + 1
    else
      v ← pure objV[k]!
      k := k + 1
    args := args.push v
    ty := b.instantiate1 v
  return mkAppN c args

/-- The tuple `(e.ps[0], (e.ps[1], … ()))` of components of an environment `e`. -/
def envTuple (e : Lean.Expr) (ps : List Nat) : MetaM Lean.Expr := do
  let mut t := Lean.mkConst ``Unit.unit
  for i in ps.reverse do t ← mkAppM ``Prod.mk #[← envProj e i, t]
  return t

/-- The disjunction of `ps` (`False` if empty). -/
def mkDisj : List Lean.Expr → Lean.Expr
  | [] => mkConst ``False
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``Or) p (mkDisj ps)

/-- The relation (and its well-foundedness proof) of the global function capturing
`f` (signature `fSig`, relation `Rf`) together with the copy `gRef` of `g` (signature `gSig`,
relation `Rg`) specialised to function arguments that call `f`: `WFLang.hoRel` pulled back along
`(tag, xs, ys, zs) ↦ if tag = 0 then inl xs else inr (ys, zs)`.  The predicate `Call x k`
(\"the function arguments, at the lifted variables `k`, may call `f x`\") is read off the
function arguments: `∃ zs, x = args₁ ∨ …`, over the parameters `zs` of each function argument
and the arguments of the calls of `f` in its body. -/
def hoRelOf (fName : Name) (fSig : FnSig) (gRef : FnRef) (gSig : FnSig)
    (Rf wff Rg wfg : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let fTys := fSig.argTys
  let gTys := gSig.argTys
  let nF := fTys.length
  let nE := gSig.nExtra
  let envOf (ts : List Lean.Expr) := mkApp (mkConst ``WFLang.Env) (mkTyList ts)
  let X := envOf fTys
  let Y := envOf gTys
  let K := envOf (gTys.take nE)
  let lam ← withLocalDeclD `y Y fun y => do mkLambdaFVars #[y] (← envTuple y (List.range nE))
  let call ← withLocalDeclD `x X fun x => withLocalDeclD `k K fun k => do
    let ysV ← (List.range nE).toArray.mapM (envProj k)
    let props ← gRef.spec.toList.mapM fun v => do
      let a := (v.beta ysV).headBeta
      forallTelescope (← inferType a) fun zs _ => do
        let body ← Core.betaReduce (mkAppN a zs)
        let found ← IO.mkRef (#[] : Array Lean.Expr)
        Meta.forEachExpr body fun o => do
          if o.isAppOf fName && o.getAppNumArgs == fSig.arity then
            if o.hasLooseBVars then
              throwError "#lean_wf_func_to_term: a call of {fName} under a binder inside the function argument of {gRef.name} is not supported"
            unless (← found.get).contains o do found.modify (·.push o)
        let mut eqs := #[]
        for o in ← found.get do
          let args := fSig.objPos.map (o.getAppArgs[·]!)
          let mut t := Lean.mkConst ``Unit.unit
          for a in args.reverse do t ← mkAppM ``Prod.mk #[a, t]
          eqs := eqs.push (← mkEq x t)
        let mut p := mkDisj eqs.toList
        for z in zs.reverse do p ← mkAppM ``Exists #[← mkLambdaFVars #[z] p]
        return p
    mkLambdaFVars #[x, k] (mkDisj props)
  let E := envOf (Lean.mkConst ``WFLang.Ty.nat :: fTys ++ gTys)
  let toSum ← withLocalDeclD `e E fun e => do
    let t ← envProj e 0
    let rest ← mkAppM ``Prod.snd #[e]
    let a ← envTuple rest (List.range nF)
    let b ← envTuple rest ((List.range gTys.length).map (· + nF))
    let inl ← mkAppOptM ``Sum.inl #[X, Y, a]
    let inr ← mkAppOptM ``Sum.inr #[X, Y, b]
    mkLambdaFVars #[e] (← mkAppM ``ite #[← mkEq t (mkNatLit 0), inl, inr])
  let hr ← mkAppOptM ``WFLang.hoRel #[X, Y, K, Rf, Rg, lam, call]
  let hwf ← mkAppOptM ``WFLang.hoRel_wf #[X, Y, K, Rf, Rg, lam, call, wff, wfg]
  return (← mkAppM ``InvImage #[hr, toSum], ← mkAppM ``InvImage.wf #[toSum, hwf])

/-- `fnSolution` for the global function capturing `f` with the specialised `gRef`:
`F (t, xs, ys, zs) _ = ⟨if t = 0 then f xs else g (spec ys) zs, _⟩`. -/
def fnSolutionHO (fName : Name) (fSig : FnSig) (gRef : FnRef) (gSig : FnSig) :
    MetaM Lean.Expr := do
  let nF := fSig.argTys.length
  let nE := gSig.nExtra
  let envTy := mkApp (mkConst ``WFLang.Env)
    (mkTyList (Lean.mkConst ``WFLang.Ty.nat :: fSig.argTys ++ gSig.argTys))
  let retD := mkApp (mkConst ``WFLang.Ty.denote) fSig.retTy
  withLocalDeclD `x envTy fun x => do
    withLocalDeclD `hx (mkConst ``True) fun hx => do
      let t ← envProj x 0
      let rest ← mkAppM ``Prod.snd #[x]
      let fargs ← (List.range nF).toArray.mapM (envProj rest)
      let fapp := mkAppN (← mkConstWithLevelParams fName) fargs
      let ysV ← (List.range nE).toArray.mapM fun i => envProj rest (nF + i)
      let objV ← (List.range (gSig.argTys.length - nE)).toArray.mapM fun i =>
        envProj rest (nF + nE + i)
      let gapp ← specApp gRef gSig ysV objV
      let v ← mkAppM ``ite #[← mkEq t (mkNatLit 0), fapp, gapp]
      let postX := mkLambda `v .default retD (mkConst ``True)
      mkLambdaFVars #[x, hx]
        (mkApp4 (mkConst ``Subtype.mk [levelOne]) retD postX v (Lean.mkConst ``True.intro))

/-! ## Tactics -/

/-- `wf_dec [extra simp lemmas]` proves one obligation `∀ e, G e → P e` of a program from its
path condition `G`: the decrease `R (args e) (cur e)` of a recursive call, the precondition of
the arguments of a call, or the postcondition at a `ret`.  It uses the decreasing proofs of
the Lean definition (offered as hypotheses), `omega`, or `decreasing_tactic`. -/
syntax (name := wfDec) "wf_dec" (" [" ident,* "]")? : tactic

/-- The closing step of `wf_dec`. -/
syntax (name := wfSolve) "wf_solve" : tactic

macro_rules
  | `(tactic| wf_solve) => `(tactic| first
        | done
        | assumption
        | omega
        | ((simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, Nat.lt_wfRel,
              sizeOf_nat] at *) <;> omega)
        | solve_by_elim
        | (simp_all; done)
        | (simp_all <;> omega)
        | ((simp only [← List.length_pos_iff, ← ne_eq] at *) <;> omega)
        | (simp_all <;> (try simp only [WFLang.Ty.denote] at *) <;> omega)
        | (simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel, sizeOf_nat] at *
           solve_by_elim)
        | (simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel, sizeOf_nat, bne_iff_ne,
              beq_iff_eq, ne_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true'] at *
           solve_by_elim)
        | decreasing_tactic)

macro_rules
  | `(tactic| wf_dec [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec))
  | `(tactic| wf_dec) => `(tactic| (
      intro e g
      try simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default, WFLang.fixedRel, WFLang.fixedAtRel,
        WFLang.preRel, InvImage] at g ⊢
      try casesm* _ ∧ _
      first
        | wf_solve
        | (and_intros <;> wf_solve)))

/-- `wf_dec_tag [extra simp lemmas]`: `wf_dec` for the global function capturing a group
of mutually recursive functions, whose first parameter is a tag: the tag is made a variable and
substituted by its value from the path condition, which selects the member (and its packing into
Lean's domain). -/
syntax (name := wfDecTag) "wf_dec_tag" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| wf_dec_tag [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec_tag))
  | `(tactic| wf_dec_tag) => `(tactic| (
      intro e g
      obtain ⟨t, e⟩ := e
      try simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default, InvImage] at g ⊢
      try casesm* _ ∧ _
      try subst_vars
      try simp only [ite_true, ite_false, reduceIte, WFLang.Ty.denote] at *
      try ((repeat' split) <;> (try contradiction))
      try simp only [WFLang.Ty.denote] at *
      first
        | wf_solve
        | (and_intros <;> wf_solve)))

/-- `wf_dec_ho [extra simp lemmas]`: `wf_dec` for the global function capturing a
function together with a specialised function whose function argument calls it (relation
`WFLang.hoRel`): the tag is substituted by its value, which selects the case of `hoRel`. -/
syntax (name := wfDecHO) "wf_dec_ho" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| wf_dec_ho [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec_ho))
  | `(tactic| wf_dec_ho) => `(tactic| (
      intro e g
      obtain ⟨t, e⟩ := e
      try simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default, InvImage] at g ⊢
      try casesm* _ ∧ _
      try subst_vars
      try simp only [ite_true, ite_false, reduceIte, WFLang.Ty.denote] at *
      try ((repeat' split) <;> (try contradiction))
      all_goals (
        try simp [WFLang.hoRel, WFLang.fixedRel, WFLang.fixedAtRel, InvImage] at *
        try intros
        try casesm* _ ∧ _
        try subst_vars
        try simp only [WFLang.Ty.denote] at *
        first
          | wf_solve
          | (and_intros <;> wf_solve))))

/-- Case analysis, two levels deep (`[]`, `[a]`, `a :: b :: t`), on the list variable `fv`. -/
def casesList2 (g : MVarId) (fv : FVarId) : MetaM (List MVarId) := do
  let mut out := []
  for s in ← g.cases fv do
    if s.ctorName == ``List.cons then
      let some tl := s.fields[1]? | out := out ++ [s.mvarId]; continue
      out := out ++ ((← s.mvarId.cases tl.fvarId!).toList.map (·.mvarId))
    else out := out ++ [s.mvarId]
  return out

/-- `wf_list_cases` closes a goal by a two-level case analysis on one of its list variables
(the patterns of a Lean `match` on lists, e.g. `x :: y :: rest`, split the cases differently
from the tests `l = []`, `l.tail = []` of the program), followed by `simp_all`. -/
syntax (name := wfListCases) "wf_list_cases" : tactic

@[tactic wfListCases] def evalWfListCases : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    unless (← whnfR d.type).isAppOf ``List do continue
    let saved ← saveState
    try
      let gs ← casesList2 g d.fvarId
      for g' in gs do
        let rest ← Tactic.run g' (Tactic.evalTactic (← `(tactic| simp_all)))
        unless rest.isEmpty do throwError "not closed"
      Tactic.replaceMainGoal []
      return
    catch _ => restoreState saved
  throwError "wf_list_cases: failed"

/-- `wf_close` closes the goals left by an agreement proof after unfolding: split every `if`
and `match`, then simplify or use `omega`. -/
syntax (name := wfClose) "wf_close" : tactic

macro_rules
  | `(tactic| wf_close) => `(tactic| (
      all_goals (repeat' split)
      all_goals first
        | (simp_all [Nat.sub_one_add_one]; done)
        | omega
        | (simp_all [Nat.sub_one_add_one] <;> omega)
        | (simp_all [Nat.sub_one_add_one] <;> congr <;> omega)
        | (simp_all [Nat.sub_one_add_one, Bool.beq_eq_decide_eq]; done)
        | (simp_all [Nat.sub_one_add_one, Bool.beq_eq_decide_eq] <;> omega)
        | wf_list_cases))

/-- The shape of an agreement goal. -/
inductive AgreeKind where
  /-- `∀ xs, Term.eval t xs = f xs` -/
  | eval
  /-- `∀ xs, Term.eval t xs = (f xs).val` (a function with a subtype result) -/
  | evalVal
  /-- `∀ xs hs, PTerm.run t ⟨xs⟩ ⟨hs⟩ = f xs hs` or `… = (f xs hs).val` (a function with a
  precondition) -/
  | run

/-- For an agreement goal: the program constant `t`, the function `f`, its unfolding equation
`f.eq_def` (as identifiers), and the shape of the goal. -/
def agreeTarget (who : String) : Tactic.TacticM (Ident × FnRef × Ident × AgreeKind) :=
  Tactic.withMainContext do
    let goal ← Tactic.getMainTarget
    forallTelescope goal fun _ eq => do
      let some (_, lhs, rhs) := eq.eq? | throwError "{who}: goal must be an equation"
      let kind := if lhs.isAppOf `WFLang.PCL.PTerm.run then AgreeKind.run
        else if rhs.isAppOfArity ``Subtype.val 3 then AgreeKind.evalVal else AgreeKind.eval
      let some tArg := (lhs.withApp fun _ args => args.toList.find? (fun a =>
          a.getAppFn.isConst && !a.getAppFn.isConstOf ``WFLang.Sig.mk)) |
        throwError "{who}: no program found"
      let .const tName _ := tArg.getAppFn | throwError "{who}: no program found"
      let rhs := if rhs.isAppOfArity ``Subtype.val 3 then rhs.getArg! 2 else rhs
      let .const fName lvls := rhs.getAppFn |
        throwError "{who}: right-hand side must be a function"
      -- a function with function arguments: the specialised copy at the given arguments
      let args := rhs.getAppArgs
      let sp ← specPosAt (mkConst fName lvls) args
      let ref ← if sp.isEmpty then pure ({ name := fName } : FnRef) else do
        let (ref, ys) ← mkSpecRef fName lvls args sp
        unless ys.isEmpty do throwError "{who}: the function arguments of {fName} must be closed"
        pure ref
      return (mkIdent tName, ref, mkIdent (fName ++ `eq_def), kind)

/-- The unfolding equations of the non-recursive functions inlined by the capture of `fn`
(for a specialised copy, also those inlined after substituting the specialised values). -/
def inlinedEqns (fn : FnRef) : MetaM (Array Name) := do
  if !fn.group.isEmpty then
    let mut out := #[]
    for g in fn.group do
      for e in (← calleeInfo g).1 do
        unless out.contains e do out := out.push e
    return out
  let base := (← calleeInfo fn.name).1
  if !fn.isSpec then return base
  let some eqn ← getUnfoldEqnFor? fn.name (nonRec := true) | return base
  fn.telescope fun _ xs _ => do
    let eqC ← if fn.levels.isEmpty then mkConstWithLevelParams eqn
      else pure (Lean.mkConst eqn fn.levels)
    let eq ← instantiateForall (← inferType eqC) xs
    let some (_, _, rhs) := eq.eq? | return base
    let (_, es) ← inlineCalls fn.name (← normLoops (← Core.betaReduce rhs))
    return es.foldl (fun acc e => if acc.contains e then acc else acc.push e) base

/-- Unfold, in every goal, the non-recursive functions that the capture of `fn` inlined. -/
def unfoldInlined (fn : FnRef) : Tactic.TacticM Unit := do
  for eqn in ← inlinedEqns fn do
    Tactic.evalTactic (← `(tactic| all_goals try simp only [$(mkIdent eqn):ident]))

/-- `fnSolution` for a specialised copy `f` (without proof parameters): `F x _ = ⟨g v₁ … vₙ, _⟩`
where the `vᵢ` are the specialised values (at the lifted variables, the first components of
`x`) and the other components of `x`. -/
def fnSolutionSpec (f : FnRef) : MetaM Lean.Expr := do
  let sig ← fnSig f
  let (_, post?) ← f.telescope fun ys xs resTy => prePostOf f xs resTy ys
  let envTy := mkApp (mkConst ``WFLang.Env) (mkTyList sig.argTys)
  let retD := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
  let c ← f.const
  withLocalDeclD `x envTy fun x => do
    withLocalDeclD `hx (mkConst ``True) fun hx => do
      let ysV ← (List.range sig.nExtra).toArray.mapM (envProj x)
      let mut ty ← inferType c
      let mut args := #[]
      let mut j := 0
      let mut k := 0
      for i in [0:sig.arity] do
        ty ← whnfR ty
        let .forallE _ d b _ := ty | throwError "wf_agree: unexpected type of {f.name}"
        let mut v := d
        if sig.specPos.contains i then
          v ← respec d (f.spec[j]!.beta ysV)
          j := j + 1
        else
          v ← envProj x (k + sig.nExtra)
          k := k + 1
        args := args.push v
        ty := b.instantiate1 v
      let app := mkAppN c args
      let postX := match post? with
        | some p => (mkApp p x).headBeta
        | none => mkLambda `v .default retD (mkConst ``True)
      let (v, pv) ← if sig.subtypeRet then
          pure (← mkAppM ``Subtype.val #[app], ← mkAppM ``Subtype.property #[app])
        else pure (app, Lean.mkConst ``True.intro)
      mkLambdaFVars #[x, hx] (mkApp4 (mkConst ``Subtype.mk [levelOne]) retD postX v pv)

/-- The function `F : (x : Env params) → pre x → {v // post x v}` that a `fix` node capturing
the Lean function `fn` computes: `F x hx = ⟨fn x₁ … xₙ h₁ … hₘ, _⟩`, where the `xᵢ` are the
components of `x` and the `hⱼ` those of the proof `hx` of the precondition (the value is
`(fn …).val` if `fn` has a subtype result). -/
def fnSolution (f : FnRef) : MetaM Lean.Expr := do
  if !f.group.isEmpty then return ← fnSolutionGroup f
  if f.isSpec then return ← fnSolutionSpec f
  let fn := f.name
  let sig ← fnSig fn
  let fnC ← mkConstWithLevelParams fn
  forallTelescope (← inferType fnC) fun xs resTy => do
    let (pre?, post?) ← prePostOf fn xs resTy
    let gam := mkTyList sig.argTys
    let envTy := mkApp (mkConst ``WFLang.Env) gam
    let retD := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
    withLocalDeclD `x envTy fun x => do
      let preX := match pre? with
        | some p => (mkApp p x).headBeta
        | none => mkConst ``True
      withLocalDeclD `hx preX fun hx => do
        let mut args := #[]
        for i in [0:sig.arity] do
          if let some j := sig.objPos.findIdx? (· == i) then
            args := args.push (← envProj x j)
          else if let some j := sig.prfPos.findIdx? (· == i) then
            args := args.push (← conjProj hx j sig.prfPos.length)
        let app := mkAppN fnC args
        let postX := match post? with
          | some p => (mkApp p x).headBeta
          | none => mkLambda `v .default retD (mkConst ``True)
        let (v, pv) ← if sig.subtypeRet then
            pure (← mkAppM ``Subtype.val #[app], ← mkAppM ``Subtype.property #[app])
          else pure (app, Lean.mkConst ``True.intro)
        let F := mkApp4 (mkConst ``Subtype.mk [levelOne]) retD postX v pv
        mkLambdaFVars #[x, hx] F

/-- Agreement proofs of programs with global functions and loops (captured callees).
In the main goal, find a value `(fixFn wf body x hx).1` of a global function and replace it by
`(F x hx).1`, where `F = fnSolution g` for one of the `callees` `g` with that signature
(uniqueness lemma `fixFn_unique`); or a value `(joinFn wf body e g h je x hx).1` of a loop and
replace it by `(je.1 (g x) _).1` (the rest of the computation `K` on the value of the callee `g`,
uniqueness lemma `joinFn_unique`, stated for all `g h je`).  Each equation is proved by
unfolding `g` once and running `step g`.  Repeats until no such value is left. -/
partial def rewriteCalleesWith (step : FnRef → Tactic.TacticM Unit) (callees : Array Name)
    (afterLoop : Tactic.TacticM Unit := pure ()) (done : Array Lean.Expr := #[]) :
    Tactic.TacticM Unit := do
  if (← Tactic.getGoals).isEmpty then return
  let tgt ← Tactic.withMainContext do instantiateMVars (← Tactic.getMainTarget)
  -- (`done`: the values already rewritten; they may remain inside proofs)
  let some fx := tgt.find? (fun x => !done.contains x && (x.isAppOfArity `WFLang.PCL.fixFn 11 ||
      (x.isAppOfArity `WFLang.PCL.joinFn 19 &&
        (x.getAppArgs.extract 0 14).all (!·.hasLooseBVars)))) | return
  let isLoop := fx.isAppOf `WFLang.PCL.joinFn
  let fnStx ← Tactic.withMainContext do
    if isLoop then `(_) else exprToSyntax fx.appFn!.appFn!
  -- for a loop: the arguments of `joinFn` before the proof of the path condition, the handler
  -- and the join points (these may depend on bound variables: the equation is stated for all)
  let fargs ← Tactic.withMainContext do
    if isLoop then (fx.getAppArgs.extract 0 14).mapM fun a => exprToSyntax a else pure #[]
  -- the candidates: the recursive callees, and the specialised copies called in the goal
  let specs ← Tactic.withMainContext do specRefsIn .anonymous tgt
  let mut cands : Array FnRef := #[]
  for n in callees do
    let r ← FnRef.ofName n
    unless cands.any (·.beq r) do cands := cands.push r
  cands := cands ++ specs
  for g in cands do
    let some (argTys, retTy) ← Tactic.withMainContext do
        try some <$> signatureOf g catch _ => pure none
      | continue
    -- only callees with the signature of the node are candidates
    let fits ← Tactic.withMainContext do
      if isLoop then
        -- a loop: its parameter is the tuple of the parameters of the callee
        return (← isDefEq (fx.getArg! 8) (mkApp (mkConst `WFLang.PCL.tupleTy) (mkTyList argTys)))
      return (← isDefEq (fx.getArg! 2) (mkTyList argTys)) && (← isDefEq (fx.getArg! 3) retTy)
    unless fits do continue
    let saved ← saveState
    try
      let members := if g.group.isEmpty then #[g.name] else g.group
      let eqns ← members.mapM fun m => do
        let some eqn ← getUnfoldEqnFor? m (nonRec := true) | throwError "no equation"
        pure (mkIdent eqn)
      let sol ← Tactic.withMainContext do exprToSyntax (← fnSolution g)
      -- for a loop: the value of the join point on `x` is the rest of the computation (the join
      -- point `K`, the first value of the join points in scope at the loop) on the callee's
      -- value
      let ps ← Tactic.withMainContext do exprToSyntax (mkTyList argTys)
      let je := mkIdent `wfLpJ
      let F ← if isLoop then
          `(fun x _ => ($je).1 (($sol) ($(mkIdent `WFLang.PCL.toEnv) $ps x) trivial).1 trivial)
        else pure sol
      let jf := mkIdent `WFLang.PCL.joinFn
      let stmtStx ← if isLoop then
          `(∀ g h $je:ident x hx, (@$jf $fargs* g h $je x hx).1 = ($F x hx).1)
        else `(∀ x hx, ($fnStx x hx).1 = ($F x hx).1)
      Tactic.withMainContext do
        let hTy ← Term.withoutErrToSorry do
          let t ← Term.elabTerm stmtStx (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars t
        let pf ← mkFreshExprSyntheticOpaqueMVar hTy
        let rest ← Term.withoutErrToSorry <| Tactic.run pf.mvarId! <| Tactic.withoutRecover do
          if isLoop then
            -- (all the arguments of `joinFn` explicitly: the postcondition of the loop cannot
            -- be inferred from `F`)
            -- (the join points in scope, i.e. the rest of the computation, are arbitrary: loops
            -- in the rest of the computation are not unfolded here)
            let lem := mkIdent `WFLang.PCL.joinFn_unique
            Tactic.evalTactic (← `(tactic| (
              intro g h $je:ident
              refine @$lem $fargs* g h $je $F ?_
              intro $(mkIdent `wfLpx):ident hx
              dsimp only)))
            -- the components of the tuple become variables
            for i in [0:argTys.length - 1] do
              let c := mkIdent (Name.mkSimple s!"wfLp{i}")
              let xl := mkIdent `wfLpx
              Tactic.evalTactic (← `(tactic| obtain ⟨$c:ident, $xl:ident⟩ := $xl:ident))
            Tactic.evalTactic (← `(tactic| try simp only [$(mkIdent `WFLang.PCL.toEnv_cons):ident, $(mkIdent `WFLang.PCL.toEnv_one):ident]))
          else
            Tactic.evalTactic (← `(tactic| (
              refine $(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?_
              intro x hx
              dsimp only)))
          if g.group.isEmpty && isLoop then
            -- unfold the callee at the loop variables (the rest of the computation may contain
            -- other calls of the callee)
            let vs := ((List.range (argTys.length - 1)).map
              (fun i => mkIdent (Name.mkSimple s!"wfLp{i}"))).toArray.push (mkIdent `wfLpx)
            let e := eqns[0]!
            Tactic.evalTactic (← `(tactic| first | rw [$e:ident $vs*] | rw [$e:ident]))
          else if g.group.isEmpty then
            Tactic.evalTactic (← `(tactic| rw [$(eqns[0]!):ident]))
          else
            -- rewrite each member at the arguments `x.2` of the solution (the unfolded
            -- right-hand sides contain calls of the other members at other arguments)
            let sig ← fnSig g
            let pfs ← Tactic.withMainContext do
              let fvs := (← getLCtx).getFVars
              let rest ← mkAppM ``Prod.snd #[fvs[fvs.size - 2]!]
              let args ← (List.range sig.objPos.length).toArray.mapM (fun i => envProj rest i)
              eqns.mapM fun e => do
                try some <$> (exprToSyntax (← mkAppM e.getId args)) catch _ => pure none
            for (e, pf?) in eqns.zip pfs do
              match pf? with
              | some pf => Tactic.evalTactic (← `(tactic| try rw [$pf:term]))
              | none => Tactic.evalTactic (← `(tactic| try rw [$e:ident]))
          step g
        unless rest.isEmpty do throwError "could not prove the equation of {g.name}"
        let (_, mvarId) ← (← (← Tactic.getMainGoal).assert `hcallee hTy
          (← instantiateMVars pf)).intro1P
        Tactic.replaceMainGoal [mvarId]
      let h := mkIdent `hcallee
      Tactic.evalTactic (← `(tactic| (simp only [$h:ident] at *); try clear $h))
      -- after a loop: evaluate the rest of the computation (which may contain further nodes)
      if isLoop then afterLoop
      return ← rewriteCalleesWith step callees afterLoop (done.push fx)
    catch _ =>
      restoreState saved
  throwError "wf_agree: could not identify the function computed by{indentExpr fx.appFn!}"

/-- The common skeleton of the agreement proofs for recursive functions.  The goal is first
put in the form `PTerm.run (PTerm.ofFix R wf body) x hx = v` (unfolding `Term.eval`); by
uniqueness of the solution of the recursive equation (`PTerm.ofFix_run`) it suffices that
`F = fnSolution fn` satisfies the equation of the body; this is closed by unfolding `fn` once
(`fn.eq_def`), simplifying with `simpStep`, and `wf_close`. -/
def agreeRec (fn : FnRef) (t eqDef : Ident) (simpStep : TSyntax `tactic)
    (after : Tactic.TacticM Unit := pure ()) : Tactic.TacticM Unit := do
  let F ← Tactic.withMainContext do exprToSyntax (← fnSolution fn)
  Tactic.evalTactic (← `(tactic| (
      intros
      try simp only [$(mkIdent `WFLang.PCL.Term.eval):ident, $(mkIdent `WFLang.PCL.Term.run):ident, WFLang.curryEnv]
      rw [$t:ident]
      refine Eq.trans ($(mkIdent `WFLang.PCL.PTerm.ofFix_run) _ _ _ _ $F ?hF _ _) ?heq
      case heq => rfl
      intro x hx
      dsimp only)))
  -- the parameters become variables (so that case splits on them substitute)
  for _ in [0:(← fnSig fn).argTys.length] do
    Tactic.evalTactic (← `(tactic| obtain ⟨_, x⟩ := x))
  Tactic.evalTactic (← `(tactic| rw [$eqDef:ident]))
  unfoldInlined fn
  Tactic.evalTactic simpStep
  after
  Tactic.evalTactic (← `(tactic| wf_close))

end WFLang.Meta
