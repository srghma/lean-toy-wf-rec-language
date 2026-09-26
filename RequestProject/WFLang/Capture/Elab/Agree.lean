import RequestProject.WFLang.Capture.Elab.Term

/-!
# `wf_agree` — the agreement proof of a captured program

`wf_agree` proves `∀ xs, PCL.Term.eval f_term xs = f xs` for `f_term := #lean_wf_func_to_term f`
(`Capture/Elab/Term.lean`), from the uniqueness of the solutions of the recursive equations of
global functions and recursive join points and the equation lemmas of the Lean functions.
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- `wf_agree` proves the agreement theorem of a program produced by
`#lean_wf_func_to_term f`: `∀ xs, PCL.Term.eval f_term xs = f xs` (or `= (f xs).val` for a
subtype result, or `∀ xs hs, PCL.PTerm.run f_term ⟨xs⟩ ⟨hs⟩ = f xs hs` with a precondition).
By uniqueness of the solution of the recursive equation of each global function
(`fixFn_unique`, `PTerm.ofFix_run`) and of each recursive join point (`joinFn_unique`), it
suffices that the Lean functions satisfy these equations, which follows from their `eq_def`. -/
syntax (name := wfAgree) "wf_agree" : tactic

/-- The simp lemmas shared by the agreement proofs, after the evaluator has been unfolded:
arithmetic normalisation, Lean's `for` and `while` loops as `rangeLoop`/`loopVal`, and the
evaluation of closed calls (`wfFoldCalls`). -/
def agreeSimpLemmas : Array Ident :=
  #[mkIdent ``Nat.pred_eq_sub_one, mkIdent ``bne, mkIdent ``Nat.min_def, mkIdent ``Nat.max_def,
    mkIdent ``Nat.dvd_iff_mod_eq_zero, mkIdent ``WFLang.foldl_range'_eq_rangeLoop,
    mkIdent ``WFLang.rangeLoop_add_sub, mkIdent ``WFLang.fold_eq_rangeLoop,
    mkIdent ``WFLang.ite_pure_yield, mkIdent ``WFLang.PCL.eval_whileLoop,
    mkIdent ``WFLang.whileWF_eq_loopVal, mkIdent ``WFLang.whileMeasure_eq_loopVal,
    mkIdent ``WFLang.Meta.wfFoldCalls]

/-- The definitions unfolding a program run (`Term.eval`, `Term.run`, `PTerm.run`) into the
evaluation of its main statement. -/
def runSimpLemmas : Array Ident :=
  #[mkIdent ``WFLang.PCL.Term.eval, mkIdent ``WFLang.PCL.Term.run,
    mkIdent ``WFLang.PCL.PTerm.run, mkIdent ``WFLang.curryEnv]

/-- `a` followed by the names of `b` that are not in `a`. -/
def mergeNames (a b : Array Name) : Array Name :=
  b.foldl (fun acc n => if acc.contains n then acc else acc.push n) a

/-- The simplification step of the PCL agreement proofs. -/
def pclSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [wflang_eval, WFLang.PCL.Self.top,
        WFLang.PCL.Self.push, WFLang.PCL.Handler.push, WFLang.PCL.toEnv_cons, WFLang.PCL.toEnv_one,
        WFLang.uncurryEnv, $[$agreeSimpLemmas:ident],*])

/-- If `f` calls itself inside a function argument of another recursive function `g`: the
reference to the copy of `g` specialised to that argument (see `hoRefIn?`). -/
def hoRefOf? (f : FnRef) : TermElabM (Option FnRef) := do
  if f.isSpec || !f.group.isEmpty || !(← isWFRec f.name) then return none
  let sig ← fnSig f
  withEqnRhs' f fun ys xs rhs => do
    unless ← hoCandidate f.name rhs do return none
    let reg ← GReg.new f
    let c : Ctx := { (Ctx.ofParams f.name xs sig ys) with
      callees := ← calleeKinds f.name rhs, specFns := ← specFnsIn f.name rhs,
      gref := registerGlobal reg, gcheckpoint := reg.checkpoint, globals := reg.names }
    hoRefIn? f c rhs

mutual
/-- Replace every value of a global function (`fixFn …`) or of a loop (`joinFn …`) capturing a
callee in the main goal by the callee's value (`rewriteCalleesWith`, uniqueness lemmas
`fixFn_unique`, `joinFn_unique`). -/
partial def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit := do
  rewriteHOCallees callees
  rewriteCalleesWith (calleeStep callees) callees
    (Tactic.evalTactic (← `(tactic| all_goals try $(← pclSimp):tactic)))

/-- The rest of the proof that the callee `g` satisfies the equation of the body of its node,
after unfolding `g` once.  (The functions identified in this proof: those of the enclosing
proof `outer`, e.g. the global functions called in the body of a loop, and `g`'s callees.) -/
partial def calleeStep (outer : Array Name) (g : FnRef) : Tactic.TacticM Unit := do
  unfoldInlined g
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  let inner := (← calleeInfo g.name).2
  rewriteCallees (mergeNames inner outer)
  Tactic.evalTactic (← `(tactic| wf_close))

/-- `rewriteCallees` for the callees that call themselves inside a function argument: their
`fix` nodes (with parameters `tag :: …`, see `HOInfo`) compute `fnSolutionHO`. -/
partial def rewriteHOCallees (callees : Array Name) : Tactic.TacticM Unit := do
  for g in callees do
    let some gRef ← hoRefOf? { name := g } | continue
    let sig ← fnSig g
    let gSig ← fnSig gRef
    let tys := mkTyList (Lean.mkConst ``WFLang.Ty.nat :: sig.argTys ++ gSig.argTys)
    repeat
      if (← Tactic.getGoals).isEmpty then return
      let fx? ← Tactic.withMainContext do
        let tgt ← instantiateMVars (← Tactic.getMainTarget)
        let found ← IO.mkRef (#[] : Array Lean.Expr)
        Meta.forEachExpr tgt fun x => do
          if x.isAppOfArity `WFLang.PCL.fixFn 11 && !x.hasLooseBVars then found.modify (·.push x)
        (← found.get).findM? fun x => isDefEq (x.getArg! 2) tys
      let some fx := fx? | break
      let fnStx ← Tactic.withMainContext do exprToSyntax fx.appFn!.appFn!
      let F ← Tactic.withMainContext do exprToSyntax (← fnSolutionHO g sig gRef gSig)
      Tactic.withMainContext do
        let hTy ← Term.withoutErrToSorry do
          let t ← Term.elabTerm (← `(∀ x hx, ($fnStx x hx).1 = ($F x hx).1))
            (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars t
        let pf ← mkFreshExprSyntheticOpaqueMVar hTy
        let rest ← Term.withoutErrToSorry <| Tactic.run pf.mvarId! <| Tactic.withoutRecover do
          Tactic.evalTactic (← `(tactic| refine $(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?_))
          hoEqProof { name := g } gRef
        unless rest.isEmpty do throwError "wf_agree: could not prove the equation of {g}"
        let (_, mvarId) ← (← (← Tactic.getMainGoal).assert `hcallee hTy
          (← instantiateMVars pf)).intro1P
        Tactic.replaceMainGoal [mvarId]
      let h := mkIdent `hcallee
      Tactic.evalTactic (← `(tactic| (simp only [$h:ident] at *); try clear $h))

/-- The proof that `F = fnSolutionHO f gRef` satisfies the equation of the body of the local
recursive function capturing `f` with the specialised `gRef` (goal
`∀ x hx, (F x hx).1 = (body.eval x hx (fun y _ hy => F y hy)).1`): by unfolding `f` (tag `0`)
or `g` (tag `t + 1`) once. -/
partial def hoEqProof (f gRef : FnRef) : Tactic.TacticM Unit := do
  let sig ← fnSig f
  let gSig ← fnSig gRef
  let fEq := mkIdent (f.name ++ `eq_def)
  let gEq := mkIdent (gRef.name ++ `eq_def)
  Tactic.evalTactic (← `(tactic| (
      intro x hx
      dsimp only
      obtain ⟨t, x⟩ := x)))
  for _ in [0:sig.argTys.length + gSig.argTys.length] do
    Tactic.evalTactic (← `(tactic| obtain ⟨_, x⟩ := x))
  Tactic.evalTactic (← `(tactic| rcases t with _ | t))
  let [g0, g1] ← Tactic.getGoals | throwError "wf_agree: unexpected goals"
  -- tag `0`: the equation of `f`
  Tactic.setGoals [g0]
  Tactic.evalTactic (← `(tactic| (
      simp only [↓reduceIte]
      rw [$fEq:ident]
      try simp only [WFLang.fold_eq_rangeLoop])))
  unfoldInlined f
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  rewriteCallees (← calleeInfo f.name).2
  Tactic.evalTactic (← `(tactic| wf_close))
  let rest0 ← Tactic.getGoals
  -- tag `t + 1`: the equation of `g`
  Tactic.setGoals [g1]
  Tactic.evalTactic (← `(tactic| (
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [$gEq:ident]
      try simp only [WFLang.fold_eq_rangeLoop])))
  unfoldInlined gRef
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  Tactic.evalTactic (← `(tactic| wf_close))
  Tactic.setGoals (rest0 ++ (← Tactic.getGoals))
end

/-- The agreement proof for a function `f` captured together with the copy `gRef` of a function
specialised to a function argument that calls `f` (`HOInfo`): the program is one call (tag `0`)
of the global function capturing both, which computes
`F (t, xs, ys, zs) = if t = 0 then f xs else g (spec ys) zs` (`fnSolutionHO`) by uniqueness
(`fixFn_unique`, `hoEqProof`). -/
def hoAgree (f gRef : FnRef) (t : Ident) : Tactic.TacticM Unit := do
  let sig ← fnSig f
  let gSig ← fnSig gRef
  let F ← Tactic.withMainContext do exprToSyntax (← fnSolutionHO f.name sig gRef gSig)
  Tactic.evalTactic (← `(tactic| (
      intros
      simp only [$t:ident, $[$runSimpLemmas:ident],*, WFLang.PCL.eval_gCall,
        WFLang.PCL.Globals.env_defn,
        WFLang.PCL.FnVar.get_here, WFLang.PCL.eval_ret, WFLang.PExpr.eval,
        WFLang.PExprs.eval, WFLang.Var.get]
      refine Eq.trans ($(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?hF _ _) ?heq
      case heq => simp [WFLang.Var.get])))
  hoEqProof f gRef

/-- For a function `f` written with Lean's `while` loops: rewrite `f` into its well-founded
version `f.wf` (`f.eq_wf`). -/
def rewriteWhileFns : Tactic.TacticM Unit := Tactic.withMainContext do
  let goal ← instantiateMVars (← Tactic.getMainTarget)
  let env ← getEnv
  let fns := (goal.getUsedConstants.filter fun c =>
    env.contains (c ++ `eq_wf) && env.contains (c ++ `wf))
  for f in fns do
    Tactic.evalTactic (← `(tactic| simp only [$(mkIdent (f ++ `eq_wf)):ident]))

@[tactic wfAgree] def evalWfAgree : Tactic.Tactic := fun _ => withAgreeOptions do
  rewriteWhileFns
  let (t, f, eqDef, _) ← agreeTarget "wf_agree"
  -- the functions whose values are identified in the proof: the loop callees and
  -- the global functions (also those called only from the function arguments of a
  -- specialised `f`)
  let callees := mergeNames (← calleeInfo f.name).2 (← globalsOf f)
  if (← mutualGroup? f.name).isSome then
    -- a member of a group of mutually recursive functions: the program is one call of the
    -- node capturing the group, whose function is identified like a callee's
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, $[$runSimpLemmas:ident],*, WFLang.PExpr.eval, WFLang.PExprs.eval,
        WFLang.Var.get,
        WFLang.PCL.Handler.push, WFLang.Meta.wfFoldCalls])))
    rewriteCallees (callees.push f.name)
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  if let some gRef ← hoRefOf? f then
    return ← hoAgree f gRef t
  if !(← isWFRec f.name) then
    let f := mkIdent f.name
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, $[$runSimpLemmas:ident],*, wflang_eval, WFLang.PCL.Handler.push,
        WFLang.PCL.toEnv_cons,
        WFLang.PCL.toEnv_one, $[$agreeSimpLemmas:ident],*, $f:ident])))
    unfoldInlined f.getId
    rewriteCallees callees
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  agreeRec f t eqDef (← pclSimp) (rewriteCallees callees)

end WFLang.Capture
