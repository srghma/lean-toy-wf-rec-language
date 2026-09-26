import RequestProject.WFLang.Capture.Meta.WFRel

/-!
# Capture metaprogramming: mutual recursion and recursion through a function argument

The well-founded relation of a group of mutually recursive functions (`groupFixOf`,
`fnSolutionGroup`), and of a function recursing through a function argument (`hoRelOf`,
`fnSolutionHO`).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-! ## Mutual recursion -/

/-- The reference to `fn`, as a member of its group of mutually recursive functions if it has
one. -/
def FnRef.ofName (fn : Name) : MetaM FnRef := do
  match ← mutualGroup? fn with
  | some g => return { name := fn, group := g }
  | none => return { name := fn }

/-- The `i`-th of the `k` summands of a nested `PSum` type. -/
partial def psumSummand (dom : Lean.Expr) (i k : Nat) : MetaM Lean.Expr := do
  if k ≤ 1 then return dom
  let dom ← whnfR dom
  unless dom.isAppOfArity ``PSum 2 do throwError "#lean_wf_func_to_term: unexpected domain {dom}"
  if i == 0 then return dom.getArg! 0
  psumSummand (dom.getArg! 1) (i - 1) (k - 1)

/-- The injection of `payload` into the `i`-th of the `k` summands of a nested `PSum` type. -/
partial def psumInj (dom : Lean.Expr) (i k : Nat) (payload : Lean.Expr) : MetaM Lean.Expr := do
  if k ≤ 1 then return payload
  let dom ← whnfR dom
  unless dom.isAppOfArity ``PSum 2 do throwError "#lean_wf_func_to_term: unexpected domain {dom}"
  let (α, β) := (dom.getArg! 0, dom.getArg! 1)
  if i == 0 then return ← mkAppOptM ``PSum.inl #[α, β, payload]
  mkAppOptM ``PSum.inr #[α, β, ← psumInj β (i - 1) (k - 1) payload]

/-- `if t = 0 then vs[0] else if t = 1 then vs[1] else … vs[k-1]`. -/
def tagSelect (t : Lean.Expr) (vs : Array Lean.Expr) : MetaM Lean.Expr := do
  let mut v := vs.back!
  for i in (List.range (vs.size - 1)).reverse do
    v ← mkAppM ``ite #[← mkEq t (mkNatLit i), vs[i]!, v]
  return v

/-- The relation of the global function capturing a group of mutually recursive
functions, over environments `(tag, xs)`, with its well-foundedness proof and the decreasing
proofs of the calls.  Structural recursion on the same parameter: that parameter decreases.
Well-founded recursion: Lean's relation on the domain `PSum D₀ (PSum D₁ …)` of the combined
definition `f._mutual`, pulled back along `(i, xs) ↦ inj_i (pack xs)`. -/
def groupFixOf (group : Array Name) : MetaM (Lean.Expr × Lean.Expr × Array Lean.Expr) := do
  let sig ← fnSig { name := group[0]!, group }
  let gam := mkTyList sig.argTys
  let env ← getEnv
  if let some i := Lean.Elab.Structural.eqnInfoExt.find? env group[0]! then
    for g in group do
      let some i' := Lean.Elab.Structural.eqnInfoExt.find? env g | throwError "unexpected"
      unless i'.recArgPos == i.recArgPos do
        throwError "#lean_wf_func_to_term: the mutually recursive functions {group} must recurse on the same parameter"
    let some j := sig.objPos.findIdx? (· == i.recArgPos) |
      throwError "#lean_wf_func_to_term: unexpected recursive parameter"
    let isList := (sig.argTys[j + 1]!).isAppOf ``WFLang.Ty.list
    let (R, wf) ← structRel gam (j + 1) isList
    return (R, wf, #[])
  let some info := Lean.Elab.WF.eqnInfoExt.find? env group[0]! |
    throwError "#lean_wf_func_to_term: {group[0]!} is not defined by well-founded recursion"
  let mutualFn := info.declNameNonRec
  forallTelescope (← inferType (← mkConstWithLevelParams mutualFn)) fun ps _ => do
    let fi ← findFixIn mutualFn ps
    unless fi.nFixed == 0 do
      throwError "#lean_wf_func_to_term: mutually recursive functions with fixed parameters are not supported"
    let k := group.size
    let pack ← withLocalDeclD `e (mkApp (mkConst ``WFLang.Env) gam) fun e => do
      let t ← envProj e 0
      let rest ← mkAppM ``Prod.snd #[e]
      let vs ← (List.range k).toArray.mapM fun i => do
        psumInj fi.dom i k (← packE (← psumSummand fi.dom i k) rest)
      mkLambdaFVars #[e] (← tagSelect t vs)
    return (← mkAppM ``InvImage #[fi.r, pack], ← mkAppM ``InvImage.wf #[pack, fi.hwf],
      ← callSiteProofs fi.F)

/-- `fnSolution` for a group: `F (t, xs) _ = ⟨if t = 0 then f₀ xs else if t = 1 then f₁ xs …, _⟩`. -/
def fnSolutionGroup (f : FnRef) : MetaM Lean.Expr := do
  let sig ← fnSig f
  let envTy := mkApp (mkConst ``WFLang.Env) (mkTyList sig.argTys)
  let retD := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
  withLocalDeclD `x envTy fun x => do
    withLocalDeclD `hx (mkConst ``True) fun hx => do
      let t ← envProj x 0
      let rest ← mkAppM ``Prod.snd #[x]
      let args ← (List.range sig.objPos.length).toArray.mapM (envProj rest)
      let vs ← f.group.mapM fun g => do return mkAppN (← mkConstWithLevelParams g) args
      let v ← tagSelect t vs
      let postX := mkLambda `v .default retD (mkConst ``True)
      mkLambdaFVars #[x, hx]
        (mkApp4 (mkConst ``Subtype.mk [Level.one]) retD postX v (Lean.mkConst ``True.intro))

/-! ## Recursion through a function argument -/

/-- The application of the specialised copy `f` (signature `sig`) to the values `ysV` of its
lifted variables and `objV` of its object parameters. -/
def specApp (f : FnRef) (sig : FnSig) (ysV objV : Array Lean.Expr) : MetaM Lean.Expr := do
  let c ← f.const
  let mut ty ← inferType c
  let mut args := #[]
  let mut j := 0
  let mut k := 0
  for i in [0:sig.arity] do
    ty ← whnfR ty
    let .forallE _ d b _ := ty | throwError "#lean_wf_func_to_term: unexpected type of {f.name}"
    let v ← if sig.specPos.contains i then respec d (f.spec[j]!.beta ysV)
      else pure objV[k]!
    if sig.specPos.contains i then j := j + 1 else k := k + 1
    args := args.push v
    ty := b.instantiate1 v
  return mkAppN c args

/-- The tuple `(e.ps[0], (e.ps[1], … ()))` of components of an environment `e`. -/
def envTuple (e : Lean.Expr) (ps : List Nat) : MetaM Lean.Expr := do
  let mut t := Lean.mkConst ``Unit.unit
  for i in ps.reverse do t ← mkAppM ``Prod.mk #[← envProj e i, t]
  return t

/-- The disjunction of `ps` (`False` if empty). -/
def mkDisj : List Lean.Expr → Lean.Expr
  | [] => mkConst ``False
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``Or) p (mkDisj ps)

/-- The relation (and its well-foundedness proof) of the global function capturing
`f` (signature `fSig`, relation `Rf`) together with the copy `gRef` of `g` (signature `gSig`,
relation `Rg`) specialised to function arguments that call `f`: `WFLang.hoRel` pulled back along
`(tag, xs, ys, zs) ↦ if tag = 0 then inl xs else inr (ys, zs)`.  The predicate `Call x k`
(\"the function arguments, at the lifted variables `k`, may call `f x`\") is read off the
function arguments: `∃ zs, x = args₁ ∨ …`, over the parameters `zs` of each function argument
and the arguments of the calls of `f` in its body. -/
def hoRelOf (fName : Name) (fSig : FnSig) (gRef : FnRef) (gSig : FnSig)
    (Rf wff Rg wfg : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let fTys := fSig.argTys
  let gTys := gSig.argTys
  let nF := fTys.length
  let nE := gSig.nExtra
  let envOf (ts : List Lean.Expr) := mkApp (mkConst ``WFLang.Env) (mkTyList ts)
  let X := envOf fTys
  let Y := envOf gTys
  let K := envOf (gTys.take nE)
  let lam ← withLocalDeclD `y Y fun y => do mkLambdaFVars #[y] (← envTuple y (List.range nE))
  let call ← withLocalDeclD `x X fun x => withLocalDeclD `k K fun k => do
    let ysV ← (List.range nE).toArray.mapM (envProj k)
    let props ← gRef.spec.toList.mapM fun v => do
      let a := (v.beta ysV).headBeta
      forallTelescope (← inferType a) fun zs _ => do
        let body ← Core.betaReduce (mkAppN a zs)
        let found ← IO.mkRef (#[] : Array Lean.Expr)
        Meta.forEachExpr body fun o => do
          if o.isAppOf fName && o.getAppNumArgs == fSig.arity then
            if o.hasLooseBVars then
              throwError "#lean_wf_func_to_term: a call of {fName} under a binder inside the function argument of {gRef.name} is not supported"
            unless (← found.get).contains o do found.modify (·.push o)
        let mut eqs := #[]
        for o in ← found.get do
          let args := fSig.objPos.map (o.getAppArgs[·]!)
          let mut t := Lean.mkConst ``Unit.unit
          for a in args.reverse do t ← mkAppM ``Prod.mk #[a, t]
          eqs := eqs.push (← mkEq x t)
        let mut p := mkDisj eqs.toList
        for z in zs.reverse do p ← mkAppM ``Exists #[← mkLambdaFVars #[z] p]
        return p
    mkLambdaFVars #[x, k] (mkDisj props)
  let E := envOf (Lean.mkConst ``WFLang.Ty.nat :: fTys ++ gTys)
  let toSum ← withLocalDeclD `e E fun e => do
    let t ← envProj e 0
    let rest ← mkAppM ``Prod.snd #[e]
    let a ← envTuple rest (List.range nF)
    let b ← envTuple rest ((List.range gTys.length).map (· + nF))
    let inl ← mkAppOptM ``Sum.inl #[X, Y, a]
    let inr ← mkAppOptM ``Sum.inr #[X, Y, b]
    mkLambdaFVars #[e] (← mkAppM ``ite #[← mkEq t (mkNatLit 0), inl, inr])
  let hr ← mkAppOptM ``WFLang.hoRel #[X, Y, K, Rf, Rg, lam, call]
  let hwf ← mkAppOptM ``WFLang.hoRel_wf #[X, Y, K, Rf, Rg, lam, call, wff, wfg]
  return (← mkAppM ``InvImage #[hr, toSum], ← mkAppM ``InvImage.wf #[toSum, hwf])

/-- `fnSolution` for the global function capturing `f` with the specialised `gRef`:
`F (t, xs, ys, zs) _ = ⟨if t = 0 then f xs else g (spec ys) zs, _⟩`. -/
def fnSolutionHO (fName : Name) (fSig : FnSig) (gRef : FnRef) (gSig : FnSig) :
    MetaM Lean.Expr := do
  let nF := fSig.argTys.length
  let nE := gSig.nExtra
  let envTy := mkApp (mkConst ``WFLang.Env)
    (mkTyList (Lean.mkConst ``WFLang.Ty.nat :: fSig.argTys ++ gSig.argTys))
  let retD := mkApp (mkConst ``WFLang.Ty.denote) fSig.retTy
  withLocalDeclD `x envTy fun x => do
    withLocalDeclD `hx (mkConst ``True) fun hx => do
      let t ← envProj x 0
      let rest ← mkAppM ``Prod.snd #[x]
      let fargs ← (List.range nF).toArray.mapM (envProj rest)
      let fapp := mkAppN (← mkConstWithLevelParams fName) fargs
      let ysV ← (List.range nE).toArray.mapM fun i => envProj rest (nF + i)
      let objV ← (List.range (gSig.argTys.length - nE)).toArray.mapM fun i =>
        envProj rest (nF + nE + i)
      let gapp ← specApp gRef gSig ysV objV
      let v ← mkAppM ``ite #[← mkEq t (mkNatLit 0), fapp, gapp]
      let postX := mkLambda `v .default retD (mkConst ``True)
      mkLambdaFVars #[x, hx]
        (mkApp4 (mkConst ``Subtype.mk [Level.one]) retD postX v (Lean.mkConst ``True.intro))

end WFLang.Meta
