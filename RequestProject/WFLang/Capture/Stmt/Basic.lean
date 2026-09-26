import RequestProject.WFLang.PCL.Size
import RequestProject.WFLang.Capture.Translate

/-!
# Helpers of the translation into `PCL` statements

Tests on Lean terms (`isControl`, `tailRecOnly`, `loopableSig`), the classification of the
callees of a function (`calleeKinds`, `calleeKey`), join-point indices (`jvarStx`, `jvarAt`),
tuples of loop states (`mkTuple`, `tupleProjs`) and small syntax builders used by
`Capture/Stmt.lean`.
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- Is `e` a control-flow node whose branches must not be evaluated eagerly? -/
def isControl (e : Lean.Expr) : MetaM Bool := do
  if e.isAppOf ``ite || e.isAppOf ``dite || e.isAppOf ``cond || e.isAppOf ``Nat.casesOn ||
    e.isAppOf ``Bool.casesOn || e.isAppOf ``List.casesOn || e.isAppOf ``and ||
    e.isAppOf ``or then return true
  if let .const n _ := e.getAppFn then return (← isMatcher n) || isSparseCasesOn n
  return false

/-- Are two references to specialised copies of the same function equal (up to definitional
equality of their function arguments)? -/
def specRefEq (a b : FnRef) : MetaM Bool := do
  if a.beq b then return true
  unless a.name == b.name && a.group == b.group && a.spec.size == b.spec.size &&
      a.extraTys.size == b.extraTys.size do
    return false
  for (x, y) in a.extraTys.zip b.extraTys do
    unless ← isDefEq x y do return false
  for (x, y) in a.spec.zip b.spec do
    unless ← isDefEq x y do return false
  return true

/-- Inside the global function capturing `f` together with the specialised `g` (see
`HOInfo`): if `e` is a call of `f` or of the specialised `g`, the arguments of the corresponding
recursive call (`tag :: f's arguments ++ g's lifted variables ++ g's arguments`, `none` for
padding). -/
def hoSelfArgs? (c : Ctx) (h : HOInfo) (e : Lean.Expr) : MetaM (Option (List (Option Lean.Expr))) := do
  let nF := h.fSig.argTys.length
  let nE := h.gSig.nExtra
  let nG := h.gSig.argTys.length - nE
  if e.isAppOf h.fName && e.getAppNumArgs == h.fSig.arity then
    return some (some (mkNatLit 0) :: (objArgs h.fSig e.getAppArgs).map some ++
      List.replicate (nE + nG) none)
  let .const g lvls := e.getAppFn | return none
  unless g == h.gRef.name do return none
  let args := e.getAppArgs
  unless args.size == h.gSig.arity do
    throwError "#lean_wf_func_to_term: partial application of {g} (function values are not supported){indentExpr e}"
  let (ref, ys) ← mkSpecRef g lvls args (← specPosAt (mkConst g lvls) args)
  unless ← specRefEq ref h.gRef do
    throwError "#lean_wf_func_to_term: {g} is called with several different function arguments that call {h.fName} (not supported){indentExpr e}"
  for y in ys do
    unless c.vars.contains y.fvarId! do
      throwError "#lean_wf_func_to_term: the function argument of {g} uses {y}, which is not a variable of the program"
  return some (some (mkNatLit 1) :: List.replicate nF none ++ ys.toList.map some ++
    (objArgs h.gSig args).map some)

/-- The de Bruijn index (`PCL.JVar`) of a join point defined when `v0` variables were in scope,
from a point with `vc` variables in scope, where `later` (innermost first) are the numbers of
variables in scope at the definitions of the join points defined after it: each join point
defined after it is crossed by `there`, each variable bound after it by `wk`. -/
partial def jvarStx (later : List Nat) (vc v0 : Nat) : MetaM Stx :=
  match later with
  | l :: ls =>
    if l == vc then do `(WFLang.PCL.JVar.there $(← jvarStx ls vc v0))
    else do `(WFLang.PCL.JVar.wk $(← jvarStx later (vc - 1) v0))
  | [] =>
    if vc ≤ v0 then `(WFLang.PCL.JVar.here)
    else do `(WFLang.PCL.JVar.wk $(← jvarStx [] (vc - 1) v0))

/-- The index of the join point that was the `d`-th one in scope (counting from the outermost)
and was defined when `v0` variables were in scope, from the context `c`. -/
def jvarAt (c : Ctx) (d v0 : Nat) : MetaM Stx :=
  jvarStx (c.joins.take (c.joins.length - d - 1)) c.vars.length v0

/-- Must the continuation of a non-tail `if`/`match` be duplicated into its branches rather
than become a join point?  Only when a call may have a postcondition (a function with a subtype
result), which the rest of the computation may need: the parameter of a join point does not
record which call produced it. -/
def needsDup (c : Ctx) : Bool :=
  c.hasPost || c.fnSig?.any (·.subtypeRet) || c.callees.any (·.2.1.subtypeRet) ||
    c.globals.any (·.2.subtypeRet)

/-- Put the values `vs` in the `some` positions of `xs`. -/
def fillOpt : List (Option Lean.Expr) → List Lean.Expr → List (Option Lean.Expr)
  | [], _ => []
  | none :: xs, vs => none :: fillOpt xs vs
  | some _ :: xs, v :: vs => some v :: fillOpt xs vs
  | some x :: xs, [] => some x :: fillOpt xs []

/-- The tuple `(v₁, (v₂, … vₙ))` of the values `vs` (the value itself for one value). -/
def mkTuple : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Bool.false
  | [v] => return v
  | v :: vs => do mkAppM ``Prod.mk #[v, ← mkTuple vs]

/-- The type of `mkTuple` of values of types `ts`. -/
def mkTupleTy : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Bool
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← mkTupleTy ts]

/-- The projections of a tuple `st` of `n` values. -/
def tupleProjs (st : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  let mut out := #[]
  let mut cur := st
  for i in [0:n] do
    if i + 1 == n then out := out.push cur
    else
      out := out.push (← mkAppM ``Prod.fst #[cur])
      cur ← mkAppM ``Prod.snd #[cur]
  return out

/-- Is every call of `fn` in `e` in tail position (in the sense of `stmt`: through `let`s,
`match`es and branches), with arguments that do not call `fn`?  Such a function can be
captured as a recursive join point (a loop). -/
partial def tailRecOnly (fn : Name) (e : Lean.Expr) : MetaM Bool := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let mentions (x : Lean.Expr) : Bool := (x.find? (·.isConstOf fn)).isSome
  if !mentions e then return true
  if e.getAppFn.isConstOf fn then return e.getAppArgs.all (!mentions ·)
  if e.isLet then
    if mentions e.letValue! then return false
    return ← tailRecOnly fn (e.letBody!.instantiate1 e.letValue!)
  if let some e' ← unfoldStep? e then return ← tailRecOnly fn e'
  if let some (t, a, b) ← branch? e then
    return !mentions t.expr && (← tailRecOnly fn a) && (← tailRecOnly fn b)
  return false

/-- The recursive functions with function parameters called in `rhs` (to be specialised at each
call site). -/
def specFnsIn (fn : Name) (rhs : Lean.Expr) : MetaM (Array Name) :=
  rhs.getUsedConstants.filterM (isSpecFn fn)

/-- The recursive user functions called by `rhs` (other than `fn`) that are not global
functions by their attribute (`localRecCallees`), with their signatures and how their calls are
captured: a tail-recursive `@[inlinable]` function (without proof parameters or subtype
result) is inlined as a loop; the other ones (`@[inlinable]` functions with non-tail recursive
calls, members of a group of mutually recursive functions, functions calling themselves inside
a function argument) are global functions. -/
def calleeKinds (fn : Name) (rhs : Lean.Expr) (exclude : Array Name := #[]) :
    MetaM (Array (Name × FnSig × CalleeKind)) := do
  let gs ← (← localRecCallees fn rhs).filterM fun g => return !exclude.contains g
  gs.mapM fun (g : Name) => do
    let sig ← fnSig { name := g }
    if let some grp ← mutualGroup? g then
      return (g, { sig with tag := grp.findIdx? (· == g) }, .global)
    if ← callsSelfInFnArg g then return (g, sig, .global)
    if (← isInlinable g) && sig.prfPos.isEmpty && !sig.subtypeRet then return (g, sig, .loop)
    return (g, sig, .global)

/-- The key of the global function capturing a callee `g`: its group, if it is a member of a
group of mutually recursive functions, and `g` otherwise. -/
def calleeKey (g : Name) : MetaM FnRef := do
  match ← mutualGroup? g with
  | some grp => return { name := grp[0]!, group := grp }
  | none => return { name := g }

/-- Can a call of the (possibly specialised) recursive function `f` be inlined as a loop, as
far as its signature is concerned (no proof parameters, no subtype result, not calling itself
inside a function argument)?  Whether its recursive calls are all tail calls is checked when
its body is translated. -/
def loopableSig (f : FnRef) (sig : FnSig) : MetaM Bool := do
  unless sig.prfPos.isEmpty && !sig.subtypeRet && f.group.isEmpty do return false
  if (← mutualGroup? f.name).isSome then return false
  return !(← callsSelfInFnArg f.name)

/-- The proof that a `jump` to a join point without precondition has its precondition. -/
def trivPre : TermElabM Stx := `(fun _ _ => trivial)

/-- Reduce, in `e`, the matches on a pair `⟨x, hx⟩` whose proof component is the local
hypothesis `hx`, and the projections `⟨x, hx⟩.1`: the body of `l.attach.map f` applied to
`⟨x, hx⟩`, with `hx` left only in proofs. -/
def eraseSubtypeArg (hx : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr :=
  Lean.Meta.transform e (pre := fun x => do
    let mentions := (x.find? (· == hx)).isSome
    if mentions then
      if x.isAppOfArity ``Subtype.val 3 && (x.getArg! 2).isAppOfArity ``Subtype.mk 4 then
        return .visit ((x.getArg! 2).getArg! 2)
      if let .proj ``Subtype 0 s := x then
        if s.isAppOfArity ``Subtype.mk 4 then return .visit (s.getArg! 2)
      if let .reduced x' ← Lean.Meta.reduceMatcher? x then return .visit x'.headBeta
    return .continue)

end WFLang.Capture
