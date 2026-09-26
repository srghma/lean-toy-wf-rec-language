import RequestProject.WFLang.Capture.Meta.Callees

/-!
# Capture metaprogramming: decrease proofs and well-founded relations

The decreasing proofs at the recursive call sites (`callSiteProofs`), and the pull-back of
Lean's well-founded relation to environments (`pullBackRel`, `closedRel`, `closedFixOf`).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

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
    let some i ← recArgOrMeasure? f.name | return none
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
    -- value for `Nat`, its length for a list); for a function defined by `partial_fixpoint`,
    -- the relation "the chosen measure decreases" (`pfixMeasure?`)
    let m ← match ← structRecArg? fn with
      | some i =>
        if (← whnfR (← inferType xs[i]!)).isAppOfArity ``List 1 then pure (some (PFixMeasure.len i))
        else pure (some (PFixMeasure.val i))
      | none => pfixMeasure? fn
    let some m := m | return none
    let obj (i : Nat) : Option Nat := sig.objPos.findIdx? (· == i)
    let gam := mkTyList argTys
    let some proj ← withLocalDeclD `e (mkApp (Lean.mkConst ``WFLang.Env) gam) fun e => do
        match m with
        | .val i =>
          let some j := obj i | return none
          return some (← mkLambdaFVars #[e] (← envProj e j))
        | .len i =>
          let some j := obj i | return none
          return some (← mkLambdaFVars #[e] (← mkAppM ``List.length #[← envProj e j]))
        | .diff a b =>
          let (some ja, some jb) := (obj a, obj b) | return none
          return some (← mkLambdaFVars #[e] (← mkAppM ``HSub.hSub #[← envProj e ja, ← envProj e jb]))
      | return none
    let nat := Lean.mkConst ``Nat
    let lt := mkLambda `a .default nat <| mkLambda `b .default nat <|
      mkApp4 (Lean.mkConst ``LT.lt [0]) nat (Lean.mkConst ``instLTNat) (.bvar 1) (.bvar 0)
    let R ← mkAppM ``InvImage #[lt, proj]
    let wf ← mkAppM ``InvImage.wf #[proj,
      ← mkAppOptM ``WellFoundedRelation.wf #[none, some (Lean.mkConst ``Nat.lt_wfRel)]]
    return some (R, wf, #[])

end WFLang.Meta
