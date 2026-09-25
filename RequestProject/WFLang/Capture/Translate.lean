import RequestProject.WFLang.Capture.Meta
import RequestProject.WFLang.Core.PExpr

/-!
# Translating Lean terms into `PCL` surface syntax

The capture elaborator produces *surface syntax* of `PCL`, which Lean then elaborates against
the expected type.  This file translates the call-free part of a Lean term into `PExpr` syntax
(`pexpr`, `pprop`), and recognises the control-flow forms of a Lean term (`branch?`: `if`,
`match` on `Nat`, `Nat.casesOn`, `cond`, short-circuit `&&`/`||`), which `Capture/Elab.lean`
turns into `PCL.Expr.ite` nodes.
-/

namespace WFLang.Translate

open Lean Meta Elab Term
open WFLang.Meta (tyOf natBin? isLibraryConst)

/-- Surface syntax of a term. -/
abbrev Stx := TSyntax `term

/-- Object type as syntax. -/
def tyStx (t : Lean.Expr) : MetaM Stx := do
  let t ← tyOf t
  if t.isConstOf ``WFLang.Ty.nat then `(WFLang.Ty.nat) else `(WFLang.Ty.bool)

/-- de Bruijn variable for position `i`. -/
def varStx : Nat → MetaM Stx
  | 0 => `(WFLang.Var.here)
  | i + 1 => do `(WFLang.Var.there $(← varStx i))

structure Ctx where
  fn : Name
  /-- The local variables, innermost first (the de Bruijn order of the object context). -/
  vars : List FVarId
  /-- Decreasing lemmas to offer to the decrease tactic. -/
  lemmas : Array Stx := #[]
  /-- The tactic proving one decrease obligation (default `wf_dec`). -/
  decTac : Option (TSyntax `tactic) := none
  /-- Other recursive functions that may be called, each with its arity and the head of its
  local recursive function node (`PCL.Expr.fix ps r R wf body`, still to be applied to the
  arguments and the continuation): each call becomes such a nested node. -/
  callees : Array (Name × Nat × Stx) := #[]

/-- A `Ctx` over the parameters `xs` of the captured function. -/
def Ctx.ofParams (fn : Name) (xs : Array Lean.Expr) : Ctx :=
  { fn, vars := xs.toList.map (·.fvarId!) }

def natLit (n : Nat) : MetaM Stx :=
  `(WFLang.PExpr.lit WFLang.Ty.nat $(quote n))

def binStx (op : Stx) (a b : Stx) : MetaM Stx :=
  `(WFLang.PExpr.bin $op $a $b)

/-- `t == 0` -/
def isZeroStx (t : Stx) : MetaM Stx := do
  binStx (← `(WFLang.BinOp.beq WFLang.Ty.nat)) t (← natLit 0)

/-- Does `e` call the function being captured, or one of the recursive callees? -/
def hasCall (c : Ctx) (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOf c.fn || c.callees.any (x.isAppOf ·.1)).isSome

/-- If `e` is a (full) call of one of the recursive callees: the head of its local recursive
function node. -/
def calleeCall? (c : Ctx) (e : Lean.Expr) : Option Stx :=
  match e.getAppFn with
  | .const g _ => (c.callees.find? fun (g', n, _) => g' == g && e.getAppNumArgs == n).map (·.2.2)
  | _ => none

/-- Unfold one layer of `match`/`let`, if possible. -/
def unfoldStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isLet then return some (e.letBody!.instantiate1 e.letValue!)
  if let .const n lvls := e.getAppFn then
    if (← isMatcher n) then
      let v ← instantiateValueLevelParams (← getConstInfo n) lvls
      return some (v.beta e.getAppArgs).headBeta
  return none

/-- The test of a two-way branch. -/
inductive Test where
  /-- A decidable proposition (`if p then … else …`). -/
  | prop (p : Lean.Expr)
  /-- A boolean (`cond b …`, `b && …`, `b || …`). -/
  | bool (b : Lean.Expr)
  /-- `t = 0` (`Nat.casesOn t …`, i.e. `match t with | 0 => … | n + 1 => …`). -/
  | isZero (t : Lean.Expr)

/-- The Lean term inspected by a test. -/
def Test.expr : Test → Lean.Expr
  | .prop e | .bool e | .isZero e => e

/-- The same test on another term. -/
def Test.withExpr : Test → Lean.Expr → Test
  | .prop _, e => .prop e
  | .bool _, e => .bool e
  | .isZero _, e => .isZero e

/-- A two-way branch `(test, then-branch, else-branch)`.  With `shortCircuit`, `a && b` and
`a || b` are branches too. -/
def branch? (e : Lean.Expr) (shortCircuit := true) :
    MetaM (Option (Test × Lean.Expr × Lean.Expr)) := do
  if e.isAppOf ``Nat.casesOn && e.getAppNumArgs ≥ 4 then
    let args := e.getAppArgs
    let t := args[1]!
    let extra := args.extract 4 args.size
    let tPred ← mkAppM ``HSub.hSub #[t, mkNatLit 1]
    return some (.isZero t, (mkAppN args[2]! extra).headBeta,
      (mkAppN (mkApp args[3]! tPred) extra).headBeta)
  if e.isAppOfArity ``ite 5 then
    return some (.prop (e.getArg! 1), e.getArg! 3, e.getArg! 4)
  if e.isAppOfArity ``dite 5 then
    let a := e.getArg! 3
    let b := e.getArg! 4
    if a.isLambda && b.isLambda && !a.bindingBody!.hasLooseBVars &&
        !b.bindingBody!.hasLooseBVars then
      return some (.prop (e.getArg! 1), a.bindingBody!, b.bindingBody!)
  if e.isAppOfArity ``cond 4 then
    return some (.bool (e.getArg! 1), e.getArg! 2, e.getArg! 3)
  if shortCircuit && e.isAppOfArity ``and 2 then
    return some (.bool (e.getArg! 0), e.getArg! 1, mkConst ``Bool.false)
  if shortCircuit && e.isAppOfArity ``or 2 then
    return some (.bool (e.getArg! 0), mkConst ``Bool.true, e.getArg! 1)
  return none

mutual
/-- A call-free Lean expression as a `PExpr`. -/
partial def pexpr (c : Ctx) (e : Lean.Expr) : MetaM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isFVar then
    if let some i := c.vars.findIdx? (· == e.fvarId!) then
      return ← `(WFLang.PExpr.var $(← varStx i))
  if let some n := e.nat? then return ← natLit n
  if let some n := e.rawNatLit? then return ← natLit n
  if e.isConstOf ``Nat.zero then return ← natLit 0
  if e.isConstOf ``Bool.true then return ← `(WFLang.PExpr.lit WFLang.Ty.bool true)
  if e.isConstOf ``Bool.false then return ← `(WFLang.PExpr.lit WFLang.Ty.bool false)
  if e.isAppOfArity ``Nat.succ 1 then
    return ← binStx (← `(WFLang.BinOp.add)) (← pexpr c (e.getArg! 0)) (← natLit 1)
  if let some e' ← unfoldStep? e then return ← pexpr c e'
  if let some (t, a, b) ← branch? e (shortCircuit := false) then
    return ← `(WFLang.PExpr.ite $(← test c t) $(← pexpr c a) $(← pexpr c b))
  if let some (op, a, b) := natBin? e then
    return ← binStx (mkIdent op) (← pexpr c a) (← pexpr c b)
  if e.isAppOfArity ``BEq.beq 4 then
    return ← binStx (← `(WFLang.BinOp.beq $(← tyStx (e.getArg! 0))))
      (← pexpr c (e.getArg! 2)) (← pexpr c (e.getArg! 3))
  if e.isAppOfArity ``Decidable.decide 2 then return ← pprop c (e.getArg! 0)
  if e.isAppOfArity ``and 2 then
    return ← binStx (← `(WFLang.BinOp.and)) (← pexpr c (e.getArg! 0)) (← pexpr c (e.getArg! 1))
  if e.isAppOfArity ``or 2 then
    return ← binStx (← `(WFLang.BinOp.or)) (← pexpr c (e.getArg! 0)) (← pexpr c (e.getArg! 1))
  if e.isAppOfArity ``not 1 then return ← `(WFLang.PExpr.not $(← pexpr c (e.getArg! 0)))
  if let .const g _ := e.getAppFn then
    unless (← isLibraryConst g) || g == c.fn do
      throwError "#lean_wf_func_to_term: unsupported call of {g} (only first-order functions on Nat and Bool, fully applied, can be called){indentExpr e}"
  throwError "#lean_wf_func_to_term: unsupported expression{indentExpr e}"

/-- A decidable proposition as a boolean expression. -/
partial def pprop (c : Ctx) (p : Lean.Expr) : MetaM Stx := do
  let p := (← instantiateMVars p).consumeMData
  let beq (t a b : Lean.Expr) : MetaM Stx := do
    binStx (← `(WFLang.BinOp.beq $(← tyStx t))) (← pexpr c a) (← pexpr c b)
  let not (s : Stx) : MetaM Stx := `(WFLang.PExpr.not $s)
  if p.isAppOfArity ``Eq 3 then
    if (p.getArg! 2).isConstOf ``Bool.true then return ← pexpr c (p.getArg! 1)
    return ← beq (p.getArg! 0) (p.getArg! 1) (p.getArg! 2)
  if p.isAppOfArity ``Ne 3 then
    return ← not (← beq (p.getArg! 0) (p.getArg! 1) (p.getArg! 2))
  if p.isAppOfArity ``Not 1 then return ← not (← pprop c (p.getArg! 0))
  if p.isAppOfArity ``And 2 then
    return ← binStx (← `(WFLang.BinOp.and)) (← pprop c (p.getArg! 0)) (← pprop c (p.getArg! 1))
  if p.isAppOfArity ``Or 2 then
    return ← binStx (← `(WFLang.BinOp.or)) (← pprop c (p.getArg! 0)) (← pprop c (p.getArg! 1))
  for (n, lt, swap) in [(``LT.lt, true, false), (``LE.le, false, false),
      (``GT.gt, true, true), (``GE.ge, false, true)] do
    if p.isAppOfArity n 4 && (p.getArg! 0).isConstOf ``Nat then
      let (a, b) := if swap then (p.getArg! 3, p.getArg! 2) else (p.getArg! 2, p.getArg! 3)
      let op ← if lt then `(WFLang.BinOp.lt) else `(WFLang.BinOp.le)
      return ← binStx op (← pexpr c a) (← pexpr c b)
  throwError "#lean_wf_func_to_term: unsupported condition{indentExpr p}"

/-- A branch test as a boolean expression. -/
partial def test (c : Ctx) : Test → MetaM Stx
  | .prop p => pprop c p
  | .bool b => pexpr c b
  | .isZero t => do isZeroStx (← pexpr c t)
end

/-- Argument tuple syntax (`PExprs`). -/
def pargs (c : Ctx) : List Lean.Expr → MetaM Stx
  | [] => `(WFLang.PExprs.nil)
  | a :: as => do `(WFLang.PExprs.cons $(← pexpr c a) $(← pargs c as))

/-- The proof of one decrease obligation: `c.decTac` (default `wf_dec`), with the decreasing
lemmas of the Lean definition as hypotheses. -/
def decStx (c : Ctx) : MetaM Stx := do
  let mut tac ← c.decTac.getDM `(tactic| wf_dec)
  for l in c.lemmas.reverse do
    tac ← `(tactic| (have := $l; $tac))
  `(by $tac:tactic)

end WFLang.Translate
