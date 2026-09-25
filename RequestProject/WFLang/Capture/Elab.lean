import RequestProject.WFLang.PCL.Lang
import RequestProject.WFLang.Capture.Translate

/-!
# `#lean_wf_func_to_term f` — capture a well-founded Lean function as a `PCL.Term`

```
def gcd_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, PCL.Term.eval gcd_term m n = gcd m n := by wf_agree
```

The elaborator reads `f.eq_def`, and writes the program

```
fix self xs. ⟦rhs⟧   applied to xs
```

as *surface syntax* of `PCL.Expr`, which Lean then elaborates against the expected type:

* control flow (`if`, `match` on `Nat`, `Nat.casesOn`, `&&`/`||` with a call on the right)
  becomes `Expr.ite`, so each branch records its test in the path condition;
* every recursive call is lifted out (A-normal form) into `Expr.fixSelfCall args (by wf_dec …) k`;
* the relation and its well-foundedness proof are the ones Lean built for `f`
  (from `WellFounded.fix`), pulled back along the packing of the arguments;
* each `by wf_dec …` proves that one call goes down, from the path condition, using the
  decreasing proofs Lean extracted for `f` (in particular the user's `decreasing_by`),
  `omega`, or `decreasing_tactic`.
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- Is `e` a control-flow node whose branches must not be evaluated eagerly? -/
def isControl (e : Lean.Expr) : MetaM Bool := do
  if e.isAppOf ``ite || e.isAppOf ``dite || e.isAppOf ``cond || e.isAppOf ``Nat.casesOn ||
    e.isAppOf ``and || e.isAppOf ``or then return true
  if let .const n _ := e.getAppFn then return (← isMatcher n)
  return false

mutual
/-- Evaluate the calls inside `e` first (A-normal form), then continue with the call-free
remainder. -/
partial def lift (c : Ctx) (e : Lean.Expr) (k : Ctx → Lean.Expr → TermElabM Stx) :
    TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← k c e
  if let some e' ← unfoldStep? e then return ← lift c e' k
  if e.isApp && e.getAppFn.isConstOf c.fn then
    return ← liftMany c e.getAppArgs.toList [] fun c args => do
      let retTy ← inferType e
      withLocalDeclD `r retTy fun v => do
        let rest ← k { c with vars := v.fvarId! :: c.vars } v
        `(WFLang.PCL.Expr.fixSelfCall $(← pargs c args) $(← decStx c) $rest)
  -- a call of another recursive function: a nested `fix` node
  if let some head := calleeCall? c e then
    return ← liftMany c e.getAppArgs.toList [] fun c args => do
      let retTy ← inferType e
      withLocalDeclD `r retTy fun v => do
        let rest ← k { c with vars := v.fvarId! :: c.vars } v
        `($head $(← pargs c args) $rest)
  if e.isApp && !(← isControl e) && !hasCall c e.getAppFn then
    return ← liftMany c e.getAppArgs.toList [] fun c args => k c (mkAppN e.getAppFn args.toArray)
  -- a call of another recursive function inside a control-flow node: evaluate it first (all
  -- functions are total, so this does not change the result)
  let hoistable (x : Lean.Expr) : Bool :=
    (calleeCall? c x).isSome && !x.hasLooseBVars && (x.find? (·.isAppOf c.fn)).isNone
  if let some s := e.find? hoistable then
    return ← lift c s fun c v =>
      lift c (e.replace fun x => if x == s then some v else none) k
  throwError "#lean_wf_func_to_term: recursive call in an unsupported position{indentExpr e}"

partial def liftMany (c : Ctx) (es : List Lean.Expr) (acc : List Lean.Expr)
    (k : Ctx → List Lean.Expr → TermElabM Stx) : TermElabM Stx :=
  match es with
  | [] => k c acc.reverse
  | e :: es => lift c e fun c e' => liftMany c es (e' :: acc) k
end

/-- A Lean expression in tail position, as a statement. -/
partial def stmt (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← `(WFLang.PCL.Expr.ret $(← pexpr c e))
  if let some e' ← unfoldStep? e then return ← stmt c e'
  if let some (t, a, b) ← branch? e then
    return ← lift c t.expr fun c cnd => do
      `(WFLang.PCL.Expr.ite $(← test c (t.withExpr cnd)) $(← stmt c a) $(← stmt c b))
  lift c e fun c e => do `(WFLang.PCL.Expr.ret $(← pexpr c e))

mutual
/-- The head `PCL.Expr.fix ps r R wf body` of the local recursive function capturing the
recursive Lean function `fn` (still to be applied to the arguments and the continuation).
`visiting` are the functions whose capture is in progress. -/
partial def fixHead (fn : Name) (visiting : List Name := []) : TermElabM Stx := do
  if visiting.contains fn then
    throwError "#lean_wf_func_to_term: mutual recursion through {fn} is not supported"
  let (argTys, retTy) ← signatureOf fn
  let gam := mkTyList argTys
  let some (R, wf, lemmas) ← closedFixOf fn |
    throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
  let lemmas ← lemmas.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
  let body ← withEqnRhs fn fun xs rhs => do
    let callees ← calleeHeads fn rhs (fn :: visiting)
    stmt { Ctx.ofParams fn xs with lemmas, decTac, callees } rhs
  `(WFLang.PCL.Expr.fix $(← exprToSyntax gam) $(← exprToSyntax retTy) $(← exprToSyntax R)
      $(← exprToSyntax wf) $body)

/-- The recursive functions called by `rhs` (other than `fn`), with their `fix` heads. -/
partial def calleeHeads (fn : Name) (rhs : Lean.Expr) (visiting : List Name) :
    TermElabM (Array (Name × Nat × Stx)) := do
  (← recCallees fn rhs).mapM fun g => do
    return (g, (← signatureOf g).1.length, ← fixHead g visiting)
end

/-- Build the surface syntax of `fix self xs. ⟦rhs of f.eq_def⟧` applied to `xs`. -/
def captureStx (fn : Name) : TermElabM Stx := do
  let isRec ← withEqnRhs fn fun _ rhs => return hasCall { fn, vars := [] } rhs
  if isRec && (← isWFRec fn) then
    `($(← fixHead fn) (WFLang.PExprs.ids _) (WFLang.PCL.Expr.ret (WFLang.PExpr.var WFLang.Var.here)))
  else
    -- not recursive: the program is just the body
    withEqnRhs fn fun xs rhs => do
      stmt { Ctx.ofParams fn xs with callees := ← calleeHeads fn rhs [fn] } rhs

/-- `#lean_wf_func_to_term f`: capture the well-founded Lean function `f` (with `Nat`/`Bool`
parameters and result) as a `PCL.Term`. -/
syntax (name := wfToTerm) "#lean_wf_func_to_term " ident : term

@[term_elab wfToTerm] def elabWfToTerm : TermElab := fun stx expectedType? => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  elabTerm (← captureStx fn) expectedType?

/-- `wf_agree` proves `∀ x₁ … xₙ, PCL.Term.eval f_term x₁ … xₙ = f x₁ … xₙ` for a term
produced by `#lean_wf_func_to_term f`: by uniqueness of the solution of the `fix` equation
(`Term.eval_fix_eq`) it suffices that `f` satisfies the equation of the body, which follows
from `f.eq_def`. -/
syntax (name := wfAgree) "wf_agree" : tactic

/-- The simplification step of the PCL agreement proofs. -/
def pclSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.Ty.beq, WFLang.PCL.Self.top, WFLang.PCL.Self.push, WFLang.PCL.eval_fix,
        WFLang.PCL.Handler.push, WFLang.uncurryEnv])

mutual
/-- Replace every `fixFn wf body x` (a nested `fix` node capturing a recursive callee) in the
main goal by `uncurryEnv g x` (`rewriteCalleesWith`, uniqueness lemma `fixFn_unique`). -/
partial def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit :=
  rewriteCalleesWith ``WFLang.PCL.fixFn 6
    (fun gFn => `(tactic| refine WFLang.PCL.fixFn_unique _ _ $gFn ?_)) calleeStep callees

/-- The rest of the proof that the callee `g` satisfies the equation of the body of its `fix`
node, after unfolding `g` once. -/
partial def calleeStep (g : Name) : Tactic.TacticM Unit := do
  unfoldInlined g
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  rewriteCallees (← calleeInfo g).2
  Tactic.evalTactic (← `(tactic| wf_close))
end

@[tactic wfAgree] def evalWfAgree : Tactic.Tactic := fun _ => do
  let (t, f, eqDef) ← agreeTarget "wf_agree"
  let callees := (← calleeInfo f.getId).2
  if !(← isWFRec f.getId) then
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.PCL.Term.eval, WFLang.PCL.Term.run, WFLang.curryEnv,
        WFLang.PExpr.eval, WFLang.PExprs.eval, WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq,
        WFLang.PCL.eval_fix, WFLang.PCL.Handler.push, $f:ident])))
    unfoldInlined f.getId
    rewriteCallees callees
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  agreeRec f.getId eqDef (← `(tactic| rw [$t:ident, WFLang.PCL.Term.eval_fix_eq _ _ _ $f]))
    (← pclSimp) (rewriteCallees callees)

end WFLang.Capture
