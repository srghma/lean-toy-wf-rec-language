import RequestProject.WFLang.Capture.Meta.Tactics

/-!
# Capture metaprogramming: the skeleton of the agreement tactic

The shape of an agreement goal (`agreeTarget`), the solutions of captured callees
(`fnSolution`), their rewriting by uniqueness (`rewriteCalleesWith`), and `agreeRec`.
-/

namespace WFLang.Meta

open Lean Meta Elab Term

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
        let v ← if sig.specPos.contains i then
            respec d (f.spec[j]!.beta ysV)
          else
            envProj x (k + sig.nExtra)
        if sig.specPos.contains i then
          j := j + 1
        else
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
      mkLambdaFVars #[x, hx] (mkApp4 (mkConst ``Subtype.mk [Level.one]) retD postX v pv)

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
        let F := mkApp4 (mkConst ``Subtype.mk [Level.one]) retD postX v pv
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
      afterLoop
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
