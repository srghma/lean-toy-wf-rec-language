import Lean
import RequestProject.WFLang.Common.PExpr

/-!
# Shared metaprogramming for the capture elaborators

Everything that the capture commands of the four grammars (`Wrapper`, `PCL`, `Tail`, `Meas`)
have in common:

* the user-facing syntax `#lean_wf_func_to_term f` and `wf_agree` (each grammar registers
  its own elaborator for them; the expected type / goal selects the grammar);
* reading a Lean function: its signature (`signatureOf`), the right-hand side of its unfolding
  equation (`withEqnRhs`), the `WellFounded.fix` Lean used to define it (`findFixIn`), the
  decreasing proofs at its recursive call sites (`callSiteProofs`), and the pull-back of its
  well-founded relation to environments (`pullBackRel`);
* the skeleton of the agreement tactics (`agreeTarget`, `agreeRec`) and the tactics
  `wf_dec` (one decrease obligation) and `wf_close` (the goals left after unfolding).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-- `#lean_wf_func_to_term f`: capture the well-founded Lean function `f` as a program of the
grammar named by the expected type. -/
syntax (name := wfToTerm) "#lean_wf_func_to_term " ident : term

/-- `wf_agree` proves `∀ x₁ … xₙ, Term.eval f_term x₁ … xₙ = f x₁ … xₙ` for a term produced by
`#lean_wf_func_to_term f`. -/
syntax (name := wfAgree) "wf_agree" : tactic

/-! ## Types and signatures -/

/-- The object type of a Lean type (`Nat` or `Bool`). -/
def tyOf (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfR e
  if e.isConstOf ``Nat then return mkConst ``WFLang.Ty.nat
  if e.isConstOf ``Bool then return mkConst ``WFLang.Ty.bool
  throwError "#lean_wf_func_to_term: unsupported type {e} (only Nat and Bool)"

/-- Build a list literal of object types. -/
def mkTyList (ts : List Lean.Expr) : Lean.Expr :=
  ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``WFLang.Ty) t acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``WFLang.Ty))

/-- The object types of the arguments and of the result of `fn`. -/
def signatureOf (fn : Name) : MetaM (List Lean.Expr × Lean.Expr) := do
  let fnTy ← inferType (← mkConstWithLevelParams fn)
  forallTelescope fnTy fun xs r => do
    return (← xs.toList.mapM (fun x => do tyOf (← inferType x)), ← tyOf r)

/-- Binary `Nat` operators, as `(BinOp constructor, lhs, rhs)`. -/
def natBin? (e : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) :=
  let ops : List (Name × Name) := [(``HAdd.hAdd, ``WFLang.BinOp.add),
    (``HSub.hSub, ``WFLang.BinOp.sub), (``HMul.hMul, ``WFLang.BinOp.mul),
    (``HDiv.hDiv, ``WFLang.BinOp.div), (``HMod.hMod, ``WFLang.BinOp.mod)]
  ops.findSome? fun (n, op) =>
    if e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5) else none

/-! ## The well-founded definition of a Lean function -/

/-- The well-founded definition of a Lean function `fn`, seen at its parameters `xs`:
the `WellFounded.fix` (or `WellFounded.Nat.fix`) application Lean used to define it, with its
domain `dom`, relation `r`, well-foundedness proof `hwf` and functional `F`.  The first
`nFixed` parameters are *fixed*: Lean keeps them outside the fixpoint, so `dom`, `r`, `hwf`
and `F` may mention `xs[0], …, xs[nFixed-1]`. -/
structure FixInfo where
  nFixed : Nat
  dom : Lean.Expr
  r : Lean.Expr
  hwf : Lean.Expr
  F : Lean.Expr

/-- Find the well-founded definition of `fn`, instantiated at the parameters `xs`. -/
def findFixIn (fn : Name) (xs : Array Lean.Expr) : MetaM FixInfo := do
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
  let mkInfo (dom r hwf F : Lean.Expr) : MetaM FixInfo := do
    return { nFixed := xs.size - (← packed dom xs.size), dom, r, hwf, F }
  let rec go (e : Lean.Expr) (i : Nat) (unfoldDepth : Nat) : MetaM FixInfo := do
    let e := e.consumeMData.headBeta
    if e.isLambda then
      if h : i < xs.size then
        return ← go (e.bindingBody!.instantiate1 xs[i]) (i + 1) unfoldDepth
      throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
    let h := e.getAppFn
    if h.isConstOf ``WellFounded.fix && e.getAppNumArgs ≥ 5 then
      return ← mkInfo (e.getArg! 0) (e.getArg! 2) (e.getArg! 3) (e.getArg! 4)
    if h.isConstOf ``WellFounded.Nat.fix && e.getAppNumArgs ≥ 4 then
      let nat := Lean.mkConst ``Nat
      let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
        mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
      let r ← mkAppM ``InvImage #[lt, e.getArg! 2]
      let hwf ← mkAppM ``InvImage.wf #[e.getArg! 2,
        ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
      let hwf ← mkExpectedTypeHint hwf (← mkAppM ``WellFounded #[r])
      return ← mkInfo (e.getArg! 0) r hwf (e.getArg! 3)
    match unfoldDepth, h with
    | d + 1, .const c lvls =>
      -- only the auxiliary definitions of `fn` itself (`fn._unary`, …), not other functions
      unless fn.isPrefixOf c do
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
  go v 0 3

/-- `findFixIn`, or `none` if `fn` is not defined by well-founded recursion. -/
def findFixIn? (fn : Name) (xs : Array Lean.Expr) : MetaM (Option FixInfo) :=
  try some <$> findFixIn fn xs catch _ => pure none

/-- If `fn` is defined by *structural* recursion on one of its (`Nat`) parameters: the position
of that parameter. -/
def structRecArg? (fn : Name) : MetaM (Option Nat) := do
  let some info := Lean.Elab.Structural.eqnInfoExt.find? (← getEnv) fn | return none
  return some info.recArgPos

/-- Is `fn` recursive, i.e. defined by well-founded or by structural recursion? -/
def isWFRec (fn : Name) : MetaM Bool := do
  if (← structRecArg? fn).isSome then return true
  forallTelescope (← inferType (← mkConstWithLevelParams fn)) fun xs _ => do
    return (← findFixIn? fn xs).isSome

/-! ## Calls to other functions -/

/-- Is `c` a constant of a library (`Init`, `Std`, `Lean`, `Mathlib`, `Batteries`)?  Library
functions are primitives of the translation or unsupported, never inlined. -/
def isLibraryConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? c | return false
  let mod := env.header.moduleNames[idx.toNat]!
  return [`Init, `Std, `Lean, `Mathlib, `Batteries].contains mod.getRoot

/-- Is `c` a user-defined first-order function (`Nat`/`Bool` parameters and result), other
than `fn`? -/
def isUserFn (fn c : Name) : MetaM Bool := do
  if c == fn || c.isInternal || (← isLibraryConst c) || (← isMatcher c) then return false
  unless (← getConstInfo c).isDefinition do return false
  try discard <| signatureOf c; return true catch _ => return false

/-- The user-defined first-order functions (other than `fn`) that occur in `e`. -/
def userCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) :=
  e.getUsedConstants.filterM (isUserFn fn)

/-- The recursive user-defined functions called in `e` (other than `fn`).  The grammars with
local recursive functions (`PCL`, `Meas`, and `Tail` outside of loops) capture each of them as a
nested `fix`/`loop` node. -/
def recCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) := do
  (← userCallees fn e).filterM isWFRec

/-- Inline the fully applied calls of *non-recursive* user-defined functions in `e` (using their
unfolding equations `g.eq_def`, transitively).  Returns the new term and the unfolding
equations used. -/
def inlineCalls (fn : Name) (e : Lean.Expr) : MetaM (Lean.Expr × Array Name) := do
  let used ← IO.mkRef (#[] : Array Name)
  let e ← Meta.transform e (post := fun e => do
    let .const c _ := e.getAppFn | return .continue
    unless ← isUserFn fn c do return .continue
    if ← isWFRec c then return .continue
    let (argTys, _) ← signatureOf c
    unless e.getAppNumArgs == argTys.length do return .continue
    let some eqn ← getUnfoldEqnFor? c (nonRec := true) | return .continue
    let ty ← instantiateForall (← inferType (← mkConstWithLevelParams eqn)) e.getAppArgs
    let some (_, _, rhs) := ty.eq? | return .continue
    if (rhs.find? (·.isConstOf c)).isSome then return .continue
    used.modify fun u => if u.contains eqn then u else u.push eqn
    return .visit rhs)
  return (e, ← used.get)

/-- Run `k xs rhs` on the parameters and the right-hand side of the unfolding equation
`fn.eq_def : ∀ xs, fn xs = rhs`, in which the calls of non-recursive user-defined functions are
inlined (`inlineCalls`). -/
def withEqnRhs {α : Type} (fn : Name) (k : Array Lean.Expr → Lean.Expr → TermElabM α) :
    TermElabM α := do
  let some eqn ← getUnfoldEqnFor? fn (nonRec := true) |
    throwError "#lean_wf_func_to_term: no unfolding equation for {fn}"
  forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun xs eq => do
    let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
    k xs (← inlineCalls fn rhs).1

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

/-- The well-founded relation of `fn` (found by `findFixIn fn xs`) as a *closed* relation on
environments `Env argTys`, with its well-foundedness proof.  The fixed parameters become
components that every related pair of environments shares (`WFLang.fixedRel`). -/
def closedRel (argTys : List Lean.Expr) (xs : Array Lean.Expr) (info : FixInfo) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let j := info.nFixed
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

/-- For a function `fn` defined by well-founded (or structural) recursion: its relation and well-foundedness
proof as closed terms over `Env argTys` (`closedRel`), and the decreasing proofs at its
recursive call sites (`callSiteProofs`), closed over what they depend on.  `none` if `fn` is not
defined by well-founded recursion. -/
def closedFixOf (fn : Name) : MetaM (Option (Lean.Expr × Lean.Expr × Array Lean.Expr)) := do
  let (argTys, _) ← signatureOf fn
  forallTelescope (← inferType (← mkConstWithLevelParams fn)) fun xs _ => do
    if let some info ← findFixIn? fn xs then
      let (R, wf) ← closedRel argTys xs info
      return some (R, wf, ← callSiteProofs info.F)
    -- structural recursion on parameter `i`: the relation "parameter `i` decreases"
    let some i ← structRecArg? fn | return none
    let gam := mkTyList argTys
    let proj ← withLocalDeclD `e (mkApp (Lean.mkConst ``WFLang.Env) gam) fun e => do
      let mut v := e
      for _ in [0:i] do v ← mkAppM ``Prod.snd #[v]
      mkLambdaFVars #[e] (← mkAppM ``Prod.fst #[v])
    let nat := Lean.mkConst ``Nat
    let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
      mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
    let R ← mkAppM ``InvImage #[lt, proj]
    let wf ← mkAppM ``InvImage.wf #[proj,
      ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
    return some (R, wf, #[])

/-! ## Tactics -/

/-- `wf_dec [extra simp lemmas]` proves one decrease obligation `∀ e, G e → R (args e) (cur e)`
of a recursive call, from the path condition `G`, the decreasing proofs of the Lean definition
(offered as hypotheses), `omega`, or `decreasing_tactic`. -/
syntax (name := wfDec) "wf_dec" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| wf_dec [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec))
  | `(tactic| wf_dec) => `(tactic| (
      intro e g
      try simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.Ty.beq, WFLang.fixedRel, InvImage] at g ⊢
      first
        | done
        | omega
        | ((simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, Nat.lt_wfRel,
              sizeOf_nat] at *) <;> omega)
        | solve_by_elim
        | (simp_all; done)
        | (simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel, sizeOf_nat] at *
           solve_by_elim)
        | decreasing_tactic))

/-- `wf_close` closes the goals left by an agreement proof after unfolding: split every `if`
and `match`, then simplify, use `omega`, or refute an unreachable (runtime-check) branch. -/
syntax (name := wfClose) "wf_close" : tactic

macro_rules
  | `(tactic| wf_close) => `(tactic| (
      all_goals (repeat' split)
      all_goals first
        | (simp_all [Nat.sub_one_add_one]; done)
        | omega
        | (simp_all [Nat.sub_one_add_one] <;> omega)
        | (simp_all [Nat.sub_one_add_one] <;> congr <;> omega)
        | (exfalso; rename_i hg; exact hg (by omega))
        | (exfalso; rename_i hg; exact hg (by solve_by_elim))))

/-- For an agreement goal `∀ xs, Term.eval t xs = f xs`: the program constant `t`, the function
`f` and its unfolding equation `f.eq_def`, as identifiers. -/
def agreeTarget (who : String) : Tactic.TacticM (Ident × Ident × Ident) :=
  Tactic.withMainContext do
    let goal ← Tactic.getMainTarget
    forallTelescope goal fun _ eq => do
      let some (_, lhs, rhs) := eq.eq? | throwError "{who}: goal must be an equation"
      let some tArg := (lhs.withApp fun _ args => args.toList.find? (fun a =>
          a.getAppFn.isConst && !a.getAppFn.isConstOf ``WFLang.Sig.mk)) |
        throwError "{who}: no program found"
      let .const tName _ := tArg.getAppFn | throwError "{who}: no program found"
      let .const fName _ := rhs.getAppFn |
        throwError "{who}: right-hand side must be a function"
      return (mkIdent tName, mkIdent fName, mkIdent (fName ++ `eq_def))

/-- Unfold, in every goal, the non-recursive functions that the capture of `fn` inlined. -/
def unfoldInlined (fn : Name) : Tactic.TacticM Unit := do
  for eqn in (← calleeInfo fn).1 do
    Tactic.evalTactic (← `(tactic| all_goals try simp only [$(mkIdent eqn):ident]))

/-- Agreement proofs of programs with nested local recursive functions (captured callees).
In the main goal, find an application `fixConst … x` (with `arity` arguments, the first two
being the parameter types and the result type) of the evaluator of a nested recursive node and
replace it by `uncurryEnv g x`, where `g` is one of `callees` with that signature.  This is
justified by the uniqueness lemma of the node (`mkRefine gFn` refines the goal
`∀ x, fixConst … x = gFn x` to the equation of the body), and the equation is proved by
unfolding `g` once and running `step g`.  Repeats until no such application is left. -/
partial def rewriteCalleesWith (fixConst : Name) (arity : Nat)
    (mkRefine : TSyntax `term → Tactic.TacticM (TSyntax `tactic))
    (step : Name → Tactic.TacticM Unit) (callees : Array Name) : Tactic.TacticM Unit := do
  if (← Tactic.getGoals).isEmpty then return
  let tgt ← Tactic.withMainContext do instantiateMVars (← Tactic.getMainTarget)
  let some fx := tgt.find? (·.isAppOfArity fixConst arity) | return
  let fnStx ← Tactic.withMainContext do exprToSyntax fx.appFn!
  for g in callees do
    let (argTys, retTy) ← signatureOf g
    -- only callees with the signature of the node are candidates
    let fits ← Tactic.withMainContext do
      return (← isDefEq (fx.getArg! 0) (mkTyList argTys)) && (← isDefEq (fx.getArg! 1) retTy)
    unless fits do continue
    let saved ← saveState
    try
      let some eqn ← getUnfoldEqnFor? g (nonRec := true) | throwError "no equation"
      let gFn ← `(WFLang.uncurryEnv (ts := $(← exprToSyntax (mkTyList argTys)))
        (r := $(← exprToSyntax retTy)) $(mkIdent g))
      Tactic.withMainContext do
        let hTy ← Term.withoutErrToSorry do
          let t ← Term.elabTerm (← `(∀ x, $fnStx x = $gFn x)) (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars t
        let pf ← mkFreshExprSyntheticOpaqueMVar hTy
        let refineTac ← mkRefine gFn
        let rest ← Term.withoutErrToSorry <| Tactic.run pf.mvarId! <| Tactic.withoutRecover do
          Tactic.evalTactic (← `(tactic| (
            $refineTac:tactic
            intro x
            simp only [WFLang.uncurryEnv]
            rw [$(mkIdent eqn):ident])))
          step g
        unless rest.isEmpty do throwError "could not prove the equation of {g}"
        let (_, mvarId) ← (← (← Tactic.getMainGoal).assert `hcallee hTy
          (← instantiateMVars pf)).intro1P
        Tactic.replaceMainGoal [mvarId]
      let h := mkIdent `hcallee
      Tactic.evalTactic (← `(tactic| (simp only [$h:ident, WFLang.uncurryEnv] at *); try clear $h))
      return ← rewriteCalleesWith fixConst arity mkRefine step callees
    catch _ => restoreState saved
  throwError "wf_agree: could not identify the function computed by{indentExpr fx.appFn!}"

/-- The common skeleton of the agreement proofs for recursive functions: `rwStep` reduces the
goal, by uniqueness of the solution of the recursive equation, to
`∀ x, uncurryEnv f x = ⟦body⟧ (uncurryEnv f) x`; this is closed by unfolding `f` once
(`f.eq_def`), simplifying with `simpStep`, and `wf_close`. -/
def agreeRec (fn : Name) (eqDef : Ident) (rwStep simpStep : TSyntax `tactic)
    (after : Tactic.TacticM Unit := pure ()) : Tactic.TacticM Unit := do
  Tactic.evalTactic (← `(tactic| (
      intros
      $rwStep:tactic
      intro x
      simp only [WFLang.uncurryEnv]
      rw [$eqDef:ident])))
  unfoldInlined fn
  Tactic.evalTactic simpStep
  after
  Tactic.evalTactic (← `(tactic| wf_close))

end WFLang.Meta
