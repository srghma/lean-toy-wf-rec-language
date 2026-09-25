import RequestProject.WFLang.Tail.Lang
import RequestProject.WFLang.Common.Translate

/-!
# `#lean_wf_func_to_tail f` — capture a tail-recursive well-founded Lean function as a loop

```
def gcd_term : Tail.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_tail gcd
theorem gcd_agree : ∀ m n, Tail.Term.eval gcd_term m n = gcd m n := by tail_agree
```

The right-hand side of `f.eq_def` becomes a loop body: tests become `Body.ite`, a
recursive call in tail position becomes `Body.next args (by wf_dec)`, anything else becomes
`Body.done`.  A recursive call anywhere else is rejected: the function is not a loop.
-/

namespace WFLang.Tail.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- A Lean expression in tail position, as a loop body. -/
partial def body (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← `(WFLang.Tail.Body.done $(← pexpr c e))
  if let some e' ← unfoldStep? e then return ← body c e'
  if let some (t, a, b) ← branch? e then
    if hasCall c t.expr then
      throwError "#lean_wf_func_to_tail: recursive call in a test{indentExpr t.expr}"
    return ← `(WFLang.Tail.Body.ite $(← test c t) $(← body c a) $(← body c b))
  if e.getAppFn.isConstOf c.fn && !e.getAppArgs.any (hasCall c) then
    return ← `(WFLang.Tail.Body.next $(← pargs c e.getAppArgs.toList) $(← decStx c))
  throwError "#lean_wf_func_to_tail: {c.fn} is not tail recursive: a recursive call is not in tail position{indentExpr e}"

/-- The head `Tail.Expr.loop ps r R wf body` of the loop capturing the tail-recursive Lean
function `fn` (still to be applied to the initial state and the continuation). -/
def loopHead (fn : Name) : TermElabM Stx := do
  let (argTys, retTy) ← signatureOf fn
  let gam := mkTyList argTys
  let some (R, wf, lemmas) ← closedFixOf fn
    | throwError "#lean_wf_func_to_tail: {fn} is not defined by well-founded recursion"
  let lemmas ← lemmas.mapM exprToSyntax
  let b ← withEqnRhs fn fun xs rhs => body { Ctx.ofParams fn xs with lemmas } rhs
  `(WFLang.Tail.Expr.loop $(← exprToSyntax gam) $(← exprToSyntax retTy) $(← exprToSyntax R)
      $(← exprToSyntax wf) $b)

/-- A Lean expression (outside of any loop) as a `Tail.Expr`: tests become `Expr.ite`, and each
call of a recursive (tail-recursive) function becomes a `loop` node whose result is bound to a
new variable. -/
partial def texpr (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← `(WFLang.Tail.Expr.ret $(← pexpr c e))
  if let some e' ← unfoldStep? e then return ← texpr c e'
  if let some (t, a, b) ← branch? e then
    if !hasCall c t.expr then
      return ← `(WFLang.Tail.Expr.ite $(← test c t) $(← texpr c a) $(← texpr c b))
  -- an innermost call of a recursive function, not under a binder: run its loop first
  let innermost (x : Lean.Expr) : Bool :=
    (calleeCall? c x).isSome && !x.hasLooseBVars && !x.getAppArgs.any (hasCall c)
  let some s := e.find? innermost
    | throwError "#lean_wf_func_to_tail: unsupported call{indentExpr e}"
  let some head := calleeCall? c s | unreachable!
  withLocalDeclD `r (← inferType s) fun v => do
    let rest ← texpr { c with vars := v.fvarId! :: c.vars }
      (e.replace fun x => if x == s then some v else none)
    `($head $(← pargs c s.getAppArgs.toList) $rest)

/-- Build the surface syntax of `loop state := xs; ⟦rhs of f.eq_def⟧`. -/
def captureStx (fn : Name) : TermElabM Stx := do
  if ← isWFRec fn then
    return ← `($(← loopHead fn) (WFLang.PExprs.ids _)
      (WFLang.Tail.Expr.ret (WFLang.PExpr.var WFLang.Var.here)))
  -- not recursive: the program is a `Tail.Expr`, with a loop for each call of a recursive
  -- function
  withEqnRhs fn fun xs rhs => do
    let callees ← (← recCallees fn rhs).mapM fun g => do
      return (g, (← signatureOf g).1.length, ← loopHead g)
    texpr { Ctx.ofParams fn xs with callees } rhs

/-- `#lean_wf_func_to_tail f` -/
syntax (name := toTail) "#lean_wf_func_to_tail " ident : term

@[term_elab toTail] def elabToTail : TermElab := fun stx expectedType? => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  elabTerm (← captureStx fn) expectedType?

/-- `tail_agree` proves `∀ x₁ … xₙ, Tail.Term.eval f_term x₁ … xₙ = f x₁ … xₙ` for a term
produced by `#lean_wf_func_to_tail f` (uniqueness of the loop equation, `Term.eval_loop_eq`,
and `f.eq_def`). -/
syntax (name := tailAgree) "tail_agree" : tactic

/-- The simplification step of the Tail agreement proofs. -/
def tailSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [WFLang.Tail.Body.evalWith, WFLang.PExprs.eval, WFLang.PExpr.eval,
        WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq, WFLang.uncurryEnv])

/-- Replace every `Loop.run wf body x` (a `loop` node capturing a recursive callee) in the main
goal by `uncurryEnv g x` (`rewriteCalleesWith`, uniqueness lemma `Loop.run_unique`). -/
def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit :=
  rewriteCalleesWith ``WFLang.Tail.Loop.run 6
    (fun gFn => `(tactic| refine WFLang.Tail.Loop.run_unique _ _ $gFn ?_))
    (fun g => do
      unfoldInlined g
      Tactic.evalTactic (← `(tactic| all_goals $(← tailSimp):tactic))
      Tactic.evalTactic (← `(tactic| wf_close)))
    callees

@[tactic tailAgree] def evalTailAgree : Tactic.Tactic := fun _ => do
  let (t, f, eqDef) ← agreeTarget "tail_agree"
  if !(← isWFRec f.getId) then
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.Tail.Term.eval, WFLang.Tail.Expr.eval, WFLang.curryEnv,
        WFLang.PExpr.eval, WFLang.PExprs.eval, WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq,
        $f:ident])))
    unfoldInlined f.getId
    rewriteCallees (← calleeInfo f.getId).2
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  agreeRec f.getId eqDef (← `(tactic| rw [$t:ident, WFLang.Tail.Term.eval_loop_eq _ _ _ $f]))
    (← tailSimp)

end WFLang.Tail.Capture
