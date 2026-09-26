import RequestProject.WFLang.Capture.LeanWhile.Loops

/-!
# Capturing Lean's own `while` loops

Lean's `while` (and `repeat`) in `do` notation is `forIn Lean.Loop.mk init step`, and
`Lean.Loop.forIn` carries no termination argument (it is defined through `repeatM`, a least
fixed point, and unfolds by `WFLang.loopLaw`).  `lean_while_to_wf f` turns such a function into a
well-founded one that `#lean_wf_func_to_term` captures, and proves that the two agree (by
unfolding `while` with `WFLang.loopLaw` along the well-founded recursion):

```
lean_while_to_wf diagonalWhile
  termination_by (m + n) * (m + n) + m
  decreasing_by …
```

For the `i`-th loop of `f` (in source order) it adds

* `f.body_i fvs : Unit → β → Id (ForInStep β)`: the loop body as written (a closed copy, over
  the variables `fvs` of `f` it reads);
* `f.loop_i fvs x₁ … xₖ : τ₁ × … × τₖ`: the loop as a **tail-recursive well-founded function**
  on the mutable variables `x₁ … xₖ` (named as in the source), returning their final values.
  Its body is the loop body with `ForInStep.yield (x₁', …)` turned into the recursive call
  `f.loop_i fvs x₁' …` and `ForInStep.done (x₁', …)` (the exit, or `break`) into the result
  `(x₁', …)`.  Its termination argument is the `i`-th `termination_by` / `decreasing_by` given
  to `lean_while_to_wf` (by default Lean guesses a measure, as for any `def`); it is marked
  `@[inlinable]`, so the capture turns it into a `PCL` loop (a recursive join point);
* `f.loop_i_eq : ∀ fvs b, forIn Lean.Loop.mk b (f.body_i fvs) = …(f.loop_i fvs b…)`;

and then

* `f.wf`: `f` with every loop replaced by a call of its `f.loop_i` (and every call of a function
  `g` for which `g.wf` exists replaced by `g.wf`), marked `@[inlinable]`;
* `f.eq_wf : ∀ xs, f xs = f.wf xs`.

`#lean_wf_func_to_term f` captures `f.wf` (running `lean_while_to_wf f` with the default
termination arguments first if needed), and `wf_agree` proves `∀ xs, Term.eval t xs = f xs`
(rewriting `f` into `f.wf` with `f.eq_wf`).
-/

namespace WFLang.LeanWhile

open Lean Meta Elab Term

/-! ## Generating the declarations -/

/-- The state of the generation: the function, the termination hints of its loops, the loops
generated so far (names of the loop functions, of their bodies and of their equations). -/
structure GenState where
  fn : Name
  hints : Array TerminationHints
  count : Nat := 0
  loops : Array Name := #[]
  bodies : Array Name := #[]
  eqns : Array Name := #[]
  /-- the equations `g.eq_wf` of the functions `g` replaced by `g.wf` -/
  calleeEqns : Array Name := #[]

/-- The free variables `fvs` of `e` that are in the local context, with the free variables their
types depend on, in the order of the local context. -/
def closureFVars (es : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let mut set : FVarIdSet := {}
  let mut todo : Array FVarId := #[]
  for e in es do
    for fv in (collectFVars {} (← instantiateMVars e)).fvarIds do
      unless set.contains fv do set := set.insert fv; todo := todo.push fv
  while !todo.isEmpty do
    let fv := todo.back!
    todo := todo.pop
    let ty ← instantiateMVars (← fv.getType)
    for fv' in (collectFVars {} ty).fvarIds do
      unless set.contains fv' do set := set.insert fv'; todo := todo.push fv'
  let lctx ← getLCtx
  let decls := lctx.foldl (init := #[]) fun acc d => if set.contains d.fvarId then acc.push d else acc
  return decls.map (·.toExpr)

/-- Add a (non-recursive) definition. -/
def addDef (name : Name) (type value : Lean.Expr) : MetaM Unit := do
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  enableRealizationsForConst name

/-- Add a theorem. -/
def addThm (name : Name) (type value : Lean.Expr) : MetaM Unit := do
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- Mark `n` as `@[inlinable]`. -/
def setInlinable (n : Name) : MetaM Unit := do
  WFLang.Meta.inlinableAttr.setTag n

/-- Prove the goal `mvarId` by the tactic `tac`. -/
def runTac (goal : Lean.Expr) (tac : TSyntax `tactic) : TermElabM Lean.Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar goal
  let rest ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (Tactic.evalTactic tac)
  unless rest.isEmpty do
    throwError "lean_while_to_wf: could not prove{indentExpr goal}\nremaining goals: {rest.map (·.name)}"
  instantiateMVars mv

/-- Does the (non-recursive) function `fn` use a Lean `while` loop, directly or through the
user functions it calls?  (Then it is captured through its well-founded version `fn.wf`.) -/
partial def needsWF (fn : Name) (visited : NameSet := {}) : MetaM Bool := do
  let env ← getEnv
  if env.contains (fn ++ `wf) && env.contains (fn ++ `eq_wf) then return true
  let some (.defnInfo info) := env.find? fn | return false
  if hasLoop info.value then return true
  let visited := visited.insert fn
  for g in info.value.getUsedConstants do
    if visited.contains g || WFLang.Meta.isInternalName g || (← WFLang.Meta.isLibraryConst g) ||
        (← isMatcher g) then continue
    if ← needsWF g visited then return true
  return false

mutual
/-- Process a loop `forIn Lean.Loop.mk init body` of state type `β` (in the current local
context): add its body, its loop function and the loop equation.  Returns the loop function
and the variables `fvs` it is applied to, and the body constant applied to `fvs`. -/
partial def genLoop (st : IO.Ref GenState) (β body : Lean.Expr) :
    TermElabM (Name × Array Lean.Expr × Lean.Expr) := do
  let idx := (← st.get).count + 1
  st.modify fun s => { s with count := idx }
  let fn := (← st.get).fn
  let lay ← stateLayout β body
  let tys := lay.tys
  let k := tys.length
  let names ← stateNames lay body
  -- the loop body, with its inner loops replaced (by the body constants for the copy `bodyC`,
  -- by the loop functions for the tail-recursive version `bodyW`)
  let (bodyC, bodyW) ← lambdaBoundedTelescope body 2 fun zs b => do
    unless zs.size == 2 do throwError "lean_while_to_wf: unexpected loop body{indentExpr body}"
    let (bC, bW) ← process st b
    return (← mkLambdaFVars zs bC, ← mkLambdaFVars zs bW)
  let fvs ← closureFVars #[bodyC, bodyW]
  let bodyName := fn ++ Name.mkSimple s!"body_{idx}"
  let loopName := fn ++ Name.mkSimple s!"loop_{idx}"
  let eqName := fn ++ Name.mkSimple s!"loop_{idx}_eq"
  -- `f.body_i`
  let bodyTy ← inferType bodyC
  addDef bodyName (← mkForallFVars fvs bodyTy) (← mkLambdaFVars fvs bodyC)
  let bodyApp := mkAppN (mkConst bodyName) fvs
  -- `f.loop_i`
  let γ ← mkTupleTy tys
  let stDecls := (names.toArray.zip tys.toArray).map fun (n, t) =>
    (n, BinderInfo.default, fun (_ : Array Lean.Expr) => pure t)
  let (loopTy, loopVal) ← withLocalDecls stDecls fun ss => do
    let st0 ← mkState lay ss.toList
    let b := (mkApp2 bodyW (mkConst ``Unit.unit) st0).headBeta
    let rec_ (v : Lean.Expr) : MetaM Lean.Expr := do
      return mkAppN (mkConst loopName) (fvs ++ (← stateComps lay v).toArray)
    let ret (v : Lean.Expr) : MetaM Lean.Expr := do mkTuple (← stateComps lay v)
    let t ← toTail rec_ ret γ b
    let t ← cleanup t
    return (← mkForallFVars (fvs ++ ss) γ, ← mkLambdaFVars (fvs ++ ss) t)
  let hints := (← st.get).hints
  let termination := hints[idx - 1]?.getD TerminationHints.none
  let termination ← if termination.decreasingBy?.isSome then pure termination else do
    let tac ← `(Lean.Parser.Tactic.tacticSeq| all_goals first
      | decreasing_tactic
      | (simp only [bne_iff_ne, beq_iff_eq, ne_eq, Bool.or_eq_true, Bool.and_eq_true,
          Bool.not_eq_true', decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at *
         omega)
      | (simp_all [bne_iff_ne]; omega))
    pure { termination with decreasingBy? := some { ref := ← getRef, tactic := tac } }
  let preDef : PreDefinition := {
    ref := ← getRef, kind := .def, levelParams := [], modifiers := {},
    declName := loopName, binders := mkNullNode, type := loopTy, value := loopVal, termination }
  -- (Lean reports a failed termination proof as a logged error: turn it into an exception)
  let msgs ← Core.getMessageLog
  Core.resetMessageLog
  try addPreDefinitions ({}, {}) #[preDef]
  catch ex => Core.setMessageLog msgs; throw ex
  let new ← Core.getMessageLog
  Core.setMessageLog msgs
  if new.hasErrors then
    let err := (new.toList.find? (·.severity == .error)).map (·.data) |>.getD m!""
    throwError "lean_while_to_wf: cannot prove that loop {idx} of {fn} terminates: give its measure, `lean_while_to_wf {fn} termination_by …` (and `decreasing_by …`)\n{err}"
  Core.setMessageLog (msgs ++ new)
  setInlinable loopName
  -- `f.body_i.apply : f.body_i fvs u r = …` (by `rfl`)
  let applyTy ← withLocalDeclD `u (mkConst ``Unit) fun u => withLocalDeclD `r β fun r => do
    mkForallFVars (fvs ++ #[u, r]) (← mkEq (mkAppN bodyApp #[u, r]) (mkApp2 bodyC u r).headBeta)
  let applyPf ← forallTelescope applyTy fun xs eq => do
    mkLambdaFVars xs (← mkEqRefl eq.appArg!)
  addThm (bodyName ++ `apply) applyTy applyPf
  -- `f.loop_i_eq : ∀ fvs b, forIn Loop.mk b (f.body_i fvs) = …`
  let forInOf (b : Lean.Expr) : MetaM Lean.Expr :=
    mkAppOptM ``ForIn.forIn #[mkConst ``Id [0], mkConst ``Lean.Loop, mkConst ``Unit, none, β,
      mkConst ``Lean.Loop.mk, b, bodyApp]
  let rhsOf (args : List Lean.Expr) : MetaM Lean.Expr := do
    let p := mkAppN (mkConst loopName) (fvs ++ args.toArray)
    mkState lay (← tupleComps p k)
  let (eqTy, auxTy) ← do
    let general ← withLocalDeclD `b β fun b => do
      mkForallFVars #[b] (← mkEq (← forInOf b) (← rhsOf (← stateComps lay b)))
    let aux ← withLocalDecls stDecls fun ss => do
      mkForallFVars ss (← mkEq (← forInOf (← mkState lay ss.toList)) (← rhsOf ss.toList))
    pure (← mkForallFVars fvs general, ← mkForallFVars fvs aux)
  -- the proof: induction along the loop function, one unfolding of `while` per step
  let s ← st.get
  let hI := mkIdent ``WFLang.loopLaw
  let fvIds := (List.range fvs.size).toArray.map fun i => mkIdent (Name.mkSimple s!"wfv{i}")
  let sIds := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"wfs{i}")
  let simpIds : Array Ident :=
    #[mkIdent (bodyName ++ `apply)] ++ (s.bodies.map fun b => mkIdent (b ++ `apply)) ++
      s.eqns.map mkIdent
  let simpLemmas ← simpIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  let lIdent := mkIdent loopName
  let auxPf ← runTac auxTy (← `(tactic| (
      intro $fvIds* $sIds*
      fun_induction $lIdent:ident $fvIds* $sIds*
      all_goals (rw [$hI:ident]; try simp_all +zetaDelta only [$simpLemmas,*, ↓reduceIte, ↓reduceDIte])
      all_goals (first | rfl | assumption))))
  let eqPf ← forallTelescope eqTy fun xs _ => do
    let b := xs.back!
    let comps ← stateComps lay b
    mkLambdaFVars xs (mkAppN auxPf (xs.pop ++ comps.toArray))
  addThm eqName eqTy eqPf
  st.modify fun s =>
    { s with
      loops := s.loops.push loopName
      bodies := s.bodies.push bodyName
      eqns := s.eqns.push eqName }
  return (loopName, fvs, bodyApp)

/-- `e` with its loops replaced: by the body constants (`eC`, definitionally equal to `e`) and by
calls of the loop functions (`eW`). -/
partial def process (st : IO.Ref GenState) (e : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  -- a loop followed by the rest of the computation: `bind (forIn Loop.mk init body) k`, or
  -- `let r := forIn Loop.mk init body; rest`
  let loopWithRest? : Option (Lean.Expr × Lean.Expr × Lean.Expr × (Lean.Expr → Lean.Expr) ×
      Lean.Expr) :=
    match idBind? e with
    | some (_, _, x, k) =>
      match loopForIn? x.consumeMData with
      | some (β, init, body) => some (β, init, body,
          fun x' => mkAppN e.getAppFn (e.getAppArgs.set! 4 x' |>.set! 5 k), k)
      | none => none
    | none => none
  if let some (β, init, body, _, k) := loopWithRest? then
    let (initC, initW) ← process st init
    let (loopName, fvs, bodyApp) ← genLoop st β body
    let (kC, kW) ← process st k
    let x := e.getArg! 4
    let xC := mkAppN x.consumeMData.getAppFn (x.consumeMData.getAppArgs.set! 6 initC |>.set! 7 bodyApp)
    let eC := mkAppN e.getAppFn (e.getAppArgs.set! 4 xC |>.set! 5 kC)
    let lay ← stateLayout β body
    let tys := lay.tys
    let n := tys.length
    let call := mkAppN (mkConst loopName) (fvs ++ (← stateComps lay initW).toArray)
    let γ ← mkTupleTy tys
    let eW ← withLetDecl `p γ call fun p => do
      let st' ← mkState lay (← tupleComps p n)
      let b ← cleanup (mkApp kW st').headBeta
      return Lean.mkLet `p γ call (b.abstract #[p]) (nondep := true)
    return (eC, eW)
  if let some (β, init, body) := loopForIn? e then
    -- a loop not followed by anything
    let (initC, initW) ← process st init
    let (loopName, fvs, bodyApp) ← genLoop st β body
    let eC := mkAppN e.getAppFn (e.getAppArgs.set! 6 initC |>.set! 7 bodyApp)
    let lay ← stateLayout β body
    let n := lay.size
    let call := mkAppN (mkConst loopName) (fvs ++ (← stateComps lay initW).toArray)
    return (eC, ← cleanup (← mkState lay (← tupleComps call n)))
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut argsC := #[]
    let mut argsW := #[]
    for a in args do
      let (aC, aW) ← process st a
      argsC := argsC.push aC
      argsW := argsW.push aW
    let (fnC, fnW) ← process st fn
    return (mkAppN fnC argsC, mkAppN fnW argsW)
  | .const g lvls =>
    -- a function using `while` loops: its well-founded version `g.wf`
    let fn := (← st.get).fn
    if g == fn || WFLang.Meta.isInternalName g || (← WFLang.Meta.isLibraryConst g) ||
        (← isMatcher g) then return (e, e)
    unless ← needsWF g do return (e, e)
    unless (← getEnv).contains (g ++ `eq_wf) do genWF g #[]
    st.modify fun s => if s.calleeEqns.contains (g ++ `eq_wf) then s
      else { s with calleeEqns := s.calleeEqns.push (g ++ `eq_wf) }
    return (e, Lean.mkConst (g ++ `wf) lvls)
  | .lam n d b bi =>
    withLocalDecl n bi d fun x => do
      let (bC, bW) ← process st (b.instantiate1 x)
      return (← mkLambdaFVars #[x] bC, ← mkLambdaFVars #[x] bW)
  | .letE n t v b nd =>
    let (vC, vW) ← process st v
    withLocalDecl n .default t fun x => do
      let (bC, bW) ← process st (b.instantiate1 x)
      return (Lean.mkLet n t vC (bC.abstract #[x]) nd, Lean.mkLet n t vW (bW.abstract #[x]) nd)
  | .proj s i a =>
    let (aC, aW) ← process st a
    return (.proj s i aC, .proj s i aW)
  | _ => return (e, e)
/-- Generate `f.wf` and `f.eq_wf` (and the loop functions of `f`), with the termination hints
`hints` for the loops of `f` in source order. -/
partial def genWF (fn : Name) (hints : Array TerminationHints) : TermElabM Unit := do
  -- all or nothing
  let saved ← saveState
  try genWFCore fn hints
  catch ex => saved.restore (restoreInfo := true); throw ex

/-- `genWF`, without restoring the state on failure. -/
partial def genWFCore (fn : Name) (hints : Array TerminationHints) : TermElabM Unit := do
  let env ← getEnv
  if env.contains (fn ++ `wf) then
    throwError "lean_while_to_wf: {fn ++ `wf} already exists"
  let info ← getConstInfoDefn fn
  unless info.levelParams.isEmpty do
    throwError "lean_while_to_wf: universe polymorphic functions are not supported"
  let st ← IO.mkRef ({ fn, hints } : GenState)
  let (ty, valW, valC) ← forallTelescope info.type fun xs _ => do
    let body := info.value.beta xs
    if body.find? (fun x => x.isConstOf fn) |>.isSome then
      throwError "lean_while_to_wf: {fn} is recursive; move its `while` loops to a separate (non-recursive) function"
    let (bC, bW) ← process st body
    return (info.type, ← mkLambdaFVars xs (← cleanup bW), ← mkLambdaFVars xs bC)
  let s ← st.get
  if s.loops.isEmpty && s.calleeEqns.isEmpty then
    throwError "lean_while_to_wf: {fn} has no `while` loop"
  if hints.size > s.loops.size then
    throwError "lean_while_to_wf: {hints.size} termination hints given, but {fn} has only {s.loops.size} loops"
  let wfName := fn ++ `wf
  addDef wfName ty valW
  compileDecls #[wfName]
  setInlinable wfName
  -- `f.eq_wf : ∀ xs, f xs = f.wf xs`
  let eqTy ← forallTelescope ty fun xs _ => do
    mkForallFVars xs (← mkEq (mkAppN (mkConst fn) xs) (mkAppN (mkConst wfName) xs))
  -- the goal in the form `eC xs = eW xs` (definitionally equal)
  let goalC ← forallTelescope ty fun xs _ => do
    mkForallFVars xs (← mkEq (valC.beta xs) (valW.beta xs))
  let lemmas ← (s.eqns ++ s.calleeEqns).mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let pf ← runTac goalC (← `(tactic| (
      intros
      (try simp only [$lemmas,*])
      (try rfl))))
  addThm (fn ++ `eq_wf) eqTy pf
end

/-- A termination hint for one loop: `termination_by …` (and optionally `decreasing_by …`), or
just `decreasing_by …`. -/
syntax whileHint := (Lean.Parser.Termination.terminationBy (Lean.Parser.Termination.decreasingBy)?)
  <|> Lean.Parser.Termination.decreasingBy

/-- The termination hints of a `whileHint`. -/
def elabWhileHint (stx : TSyntax ``whileHint) : TermElabM TerminationHints := do
  let (tb, db) : Option Syntax × Option Syntax :=
    if stx.raw[0].getKind == ``Lean.Parser.Termination.decreasingBy then (none, some stx.raw[0])
    else (some stx.raw[0][0], stx.raw[0][1].getOptional?)
  let tb := match tb with
    | some t => if t.getKind == ``Lean.Parser.Termination.terminationBy then some t else
        if t.getNumArgs > 0 && t[0].getKind == ``Lean.Parser.Termination.terminationBy then
          some t[0] else some t
    | none => none
  let suffix := mkNode ``Lean.Parser.Termination.suffix
    #[mkNullNode (tb.toArray), mkNullNode (db.toArray)]
  elabTerminationHints ⟨suffix⟩

/-- `lean_while_to_wf f (termination_by … (decreasing_by …)?)*`: the well-founded version
`f.wf` of a (non-recursive) function `f` written with Lean's `while` loops, and
`f.eq_wf : ∀ xs, f xs = f.wf xs`.  The `i`-th termination hint is the termination
argument of the `i`-th loop of `f` (in source order); it refers to the mutable variables of the
loop by their names (and to the variables of `f` the loop reads).  Without a hint, Lean guesses
the measure. -/
syntax (name := leanWhileToWF) "lean_while_to_wf " ident (ppLine whileHint)* : command

@[command_elab leanWhileToWF] def elabLeanWhileToWF : Command.CommandElab := fun stx => do
  Command.liftTermElabM do
    let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let hints ← stx[2].getArgs.mapM fun h => elabWhileHint ⟨h⟩
    withRef stx (genWF fn hints)

end WFLang.LeanWhile
