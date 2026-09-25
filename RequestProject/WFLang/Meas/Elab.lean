import RequestProject.WFLang.Meas.Lang
import RequestProject.WFLang.Common.Translate

/-!
# `#lean_wf_func_to_meas f` — capture a well-founded Lean function as a `Meas.Term`

```
def gcd_term : Meas.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_meas gcd
theorem gcd_agree : ∀ m n, Meas.Term.eval gcd_term m n = gcd m n := by meas_agree
```

* The body is the right-hand side of `f.eq_def`, in direct style (calls stay where they are).
* The measure is read off the `termination_by` measure that Lean used for `f` (a natural
  number, or a pair of natural numbers compared lexicographically) and written as two
  object-language expressions.
* `meas_agree` proves agreement: `f` satisfies the *guarded* equation of the body because
  every guard (measure decrease) holds, which is shown from the path condition with the
  decreasing proofs Lean extracted for `f`, `omega`, or `decreasing_tactic`.
-/

namespace WFLang.Meas.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- Pack the parameters into the (nested `PSigma`) domain of Lean's well-founded definition. -/
partial def packXs (α : Lean.Expr) (xs : List Lean.Expr) : MetaM Lean.Expr := do
  let α ← whnfR α
  match xs with
  | x :: rest@(_ :: _) =>
    if α.isAppOfArity ``PSigma 2 then
      let A := α.getArg! 0
      let B := α.getArg! 1
      if B.isLambda && !B.bindingBody!.hasLooseBVars then
        return mkApp4 (mkConst ``PSigma.mk α.getAppFn.constLevels!) A B x
          (← packXs B.bindingBody! rest)
    throwError "#lean_wf_func_to_meas: unexpected argument packing {α}"
  | [x] => return x
  | [] => throwError "#lean_wf_func_to_meas: no parameters"

/-- The measure of Lean's well-founded relation, as one or two natural-number expressions
over the parameters `xs`. -/
def measureOf (dom r : Lean.Expr) (xs : List Lean.Expr) : MetaM (List Lean.Expr) := do
  let packed ← packXs dom xs
  let r := r.consumeMData
  -- `InvImage (· < ·) g` (from `WellFounded.Nat.fix`)
  if r.isAppOfArity ``InvImage 4 then
    return [← withReducible <| Meta.reduce (mkApp (r.getArg! 3) packed)]
  -- `(invImage f inst).rel`
  let inv? : Option Lean.Expr := match r with
    | .proj _ 0 s => some s
    | _ => if r.isAppOfArity ``WellFoundedRelation.rel 2 then some (r.getArg! 1) else none
  if let some inv := inv? then
    if inv.isAppOfArity ``invImage 4 then
      let v ← withReducible <| Meta.reduce (mkApp (inv.getArg! 2) packed)
      if v.isAppOfArity ``Prod.mk 4 then return [v.getArg! 2, v.getArg! 3]
      return [v]
  throwError "#lean_wf_func_to_meas: unsupported well-founded relation{indentExpr r}"

/-- A `Ctx` producing direct-style `Meas.Expr`s; the recursive callees are called through
their nested `fix` nodes. -/
def directCtx (fn : Name) (xs : Array Lean.Expr) (callees : Array (Name × Nat × Stx) := #[]) : Ctx :=
  { Ctx.ofParams fn xs with
    ns := `WFLang.Meas.Expr, onCall := some (directCall `WFLang.Meas.Expr `WFLang.Meas.Exprs),
    callees,
    onCallee := some fun head args => do
      let argList ← args.foldrM (init := ← `(WFLang.Meas.Exprs.nil))
        fun a acc => `(WFLang.Meas.Exprs.cons $a $acc)
      `($head $argList) }

mutual
/-- The head `Meas.Expr.fix ps r μ₁ μ₂ body` of the local recursive function capturing the
recursive Lean function `fn`, decreasing on the measure of `fn` (still to be applied to the
arguments).  `visiting` are the functions whose capture is in progress. -/
partial def fixHead (fn : Name) (visiting : List Name := []) : TermElabM Stx := do
  if visiting.contains fn then
    throwError "#lean_wf_func_to_meas: mutual recursion through {fn} is not supported"
  let (argTys, retTy) ← signatureOf fn
  let gam := mkTyList argTys
  let (body, μs) ← withEqnRhs fn fun xs rhs => do
    let callees ← calleeHeads fn rhs (fn :: visiting)
    let body ← pexpr (directCtx fn xs callees) rhs
    let μs ← match ← findFixIn? fn xs with
      | some info => measureOf info.dom info.r (xs.toList.drop info.nFixed)
      | none =>
        -- structural recursion: the measure is the recursion argument
        let some i ← structRecArg? fn | throwError "#lean_wf_func_to_meas: {fn} is not recursive"
        pure [xs[i]!]
    let μs ← μs.mapM fun m => (pexpr (Ctx.ofParams fn xs) m : MetaM Stx)
    return (body, μs)
  let (μ₁, μ₂) ← match μs with
    | [a] => pure (a, ← natLit 0)
    | [a, b] => pure (a, b)
    | _ => throwError "#lean_wf_func_to_meas: unsupported measure"
  `(WFLang.Meas.Expr.fix $(← exprToSyntax gam) $(← exprToSyntax retTy) $μ₁ $μ₂ $body)

/-- The recursive functions called by `rhs` (other than `fn`), with their `fix` heads. -/
partial def calleeHeads (fn : Name) (rhs : Lean.Expr) (visiting : List Name) :
    TermElabM (Array (Name × Nat × Stx)) := do
  (← recCallees fn rhs).mapM fun g => do
    return (g, (← signatureOf g).1.length, ← fixHead g visiting)
end

/-- Build `(fix self xs. ⟦rhs⟧) xs`, decreasing on the measure of `f`. -/
def captureStx (fn : Name) : TermElabM Stx := do
  let (argTys, _) ← signatureOf fn
  if !(← isWFRec fn) then
    -- not recursive: the program is just the body
    return ← withEqnRhs fn fun xs rhs => do
      pexpr (directCtx fn xs (← calleeHeads fn rhs [fn])) rhs
  let ids ← (List.range argTys.length).toArray.mapM fun i => do
    `(WFLang.Meas.Expr.var $(← varStx i))
  let argsS ← ids.foldrM (init := ← `(WFLang.Meas.Exprs.nil))
    fun a acc => `(WFLang.Meas.Exprs.cons $a $acc)
  `($(← fixHead fn) $argsS)

/-- `#lean_wf_func_to_meas f` -/
syntax (name := toMeas) "#lean_wf_func_to_meas " ident : term

@[term_elab toMeas] def elabToMeas : TermElab := fun stx expectedType? => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  elabTerm (← captureStx fn) expectedType?

/-- `meas_agree` proves `∀ x₁ … xₙ, Meas.Term.eval f_term x₁ … xₙ = f x₁ … xₙ` for a term
produced by `#lean_wf_func_to_meas f`. -/
syntax (name := measAgree) "meas_agree" : tactic

/-- The simplification step of the Meas agreement proofs. -/
def measSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [WFLang.Meas.Expr.eval, WFLang.Meas.Exprs.eval, WFLang.Meas.measure,
        WFLang.Meas.lexLt, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq,
        WFLang.uncurryEnv])

/-- Offer the decreasing proofs of the recursive function `fn` as hypotheses. -/
def haveDecProofs (fn : Name) : Tactic.TacticM Unit := do
  let some (_, _, proofs) ← closedFixOf fn | return
  for p in proofs do
    Tactic.evalTactic (← `(tactic| all_goals have := $(← Term.exprToSyntax p)))

mutual
/-- Replace every `measFix μ₁ μ₂ F x` (a nested `fix` node capturing a recursive callee) in the
main goal by `uncurryEnv g x` (`rewriteCalleesWith`, uniqueness lemma `measFix_unique`). -/
partial def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit :=
  rewriteCalleesWith ``WFLang.Meas.measFix 6
    (fun gFn => `(tactic| refine WFLang.Meas.measFix_unique _ _ _ $gFn ?_)) calleeStep callees

/-- The rest of the proof that the callee `g` satisfies the guarded equation of the body of its
`fix` node, after unfolding `g` once. -/
partial def calleeStep (g : Name) : Tactic.TacticM Unit := do
  haveDecProofs g
  unfoldInlined g
  Tactic.evalTactic (← `(tactic| all_goals $(← measSimp):tactic))
  rewriteCallees (← calleeInfo g).2
  Tactic.evalTactic (← `(tactic| wf_close))
end

@[tactic measAgree] def evalMeasAgree : Tactic.Tactic := fun _ => do
  let (t, f, eqDef) ← agreeTarget "meas_agree"
  let callees := (← calleeInfo f.getId).2
  if !(← isWFRec f.getId) then
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.Meas.Term.eval, WFLang.Meas.Expr.eval, WFLang.Meas.Exprs.eval,
        WFLang.curryEnv, WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq, $f:ident])))
    unfoldInlined f.getId
    rewriteCallees callees
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  -- the decreasing proofs of `f`, offered as hypotheses
  let some (_, _, proofs) ← closedFixOf f.getId | throwError "meas_agree: {f} is not recursive"
  let mut rwStep ← `(tactic| rw [$t:ident, WFLang.Meas.Term.eval_fix_eq _ _ _ _ (fun _ => rfl) $f])
  for p in proofs.reverse do
    rwStep ← `(tactic| (have := $(← Term.exprToSyntax p); $rwStep))
  agreeRec f.getId eqDef rwStep (← measSimp) (rewriteCallees callees)

end WFLang.Meas.Capture
