module

public meta import LeanScript.ToTerm.Cases
public meta import LeanScript.ToTerm.Match
public meta import LeanScript.ToTerm.Cache
public meta import LeanScript.ToTerm.Brec

@[expose] public section

meta section

/-!
# The translation: applications, dispatches and recursors

The clauses of the translation that meet a recursor, a sparse `casesOn`, or the call of an
inlinable definition.  They are written outside the `mutual` block of
`LeanScript.ToTerm.Trans`: each takes the translation itself as its first argument
`trans`, which it calls on the subexpressions it meets.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The translation itself, as the clauses outside its `mutual` block are given it: the
    term a Lean expression translates to, in a context. -/
abbrev TransFn := TCtx → Expr → MetaM Expr

/-- Apply a translated function to the arguments it is given, dropping the ones the
    language erases (types, instances and proofs). -/
def applyArgs (trans : TransFn) (c : TCtx) (t : Expr) (fn : Expr)
    (args : Array Expr) : MetaM Expr := do
  let mut t := t
  let mut cur := fn
  for a in args do
    let fty ← whnf (← inferType cur)
    let .forallE _ d _ _ := fty
      | throwError "`#leanscript_to_term`: too many arguments for {cur}"
    let next := mkApp cur a
    if ← LeanScript.Deriving.erasedBinder d then
      cur := next
      continue
    let σ ← tyOfType d
    let τ ← tyOfTerm next
    let a' ← trans c a
    t := mkAppN (mkConst `LeanScript.Term.ap) #[c.sg, c.gamma, σ, τ, t, a']
    cur := next
  return t

/-- A branch of a dispatch: the fields it binds become the innermost variables, the
    first field at index `0`. -/
def transBranch (trans : TransFn) (c : TCtx) (minor : Expr) (ctorName : Name)
    (fieldTys : List Expr) : MetaM Expr := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let mut keep : Array Expr := #[]
    for x in xs do
      unless ← LeanScript.Deriving.erasedBinder (← inferType x) do
        keep := keep.push x
    unless keep.size == fieldTys.length do
      throwError "`#leanscript_to_term`: the branch of {ctorName} binds {keep.size} \
        values but its tree has {fieldTys.length} fields"
    let c' := c.pushFields ((keep.zip fieldTys.toArray).map fun (x, t) => (x.fvarId!, t))
    trans c' ((mkAppN minor xs).headBeta)

/-- The member a family selects, with its fields unfolded in the scope of the whole
    family: the index of `mutualRecursiveFamily_mk`, `…_casesOn` and
    `…_casesOnWithDefault`. -/
def famCurrentUnfolded (nE f hwf : Expr) : MetaM Expr := do
  let sc := (← natOfExpr nE) + 2
  let curE := mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.current) (tyWfInE sc) f
  reduceTy (mkAppN (mkConst ``LeanScript.LeanFamMemberSchema.map)
    #[tyWfInE sc, tyE, mkApp3 (mkConst ``LeanScript.TyWfIn.unfoldFam) nE f hwf, curE])

/-- A `_sparseCasesOn_` auxiliary written as the exhaustive `casesOn` it stands for: the
    named constructors keep their branches, every other one takes the `else` branch (when
    that branch does not use the proof that the value is none of the named constructors,
    which the language erases).  Used for a type with no partial dispatch of its own. -/
def sparseAsCasesOn? (n : Name) (args : Array Expr) :
    MetaM (Option Expr) := do
  let some (arity, named, p) ← sparseCasesOnInfo? n | return none
  if args.size < arity then return none
  let motive := args[p]!
  let major := args[p + 1]!
  let mty ← whnf (← inferType major)
  let .const indName indLvls := mty.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? indName | return none
  unless ii.numIndices == 0 do return none
  let ctors := ii.ctors.toArray
  if named.length ≥ ctors.size then return none
  unless (← getEnv).contains (indName ++ `casesOn) do return none
  let motiveLvl ← do
    let mt ← whnf (← inferType motive)
    let .forallE _ _ b _ := mt | return none
    let .sort u := (← whnf b) | return none
    pure u
  let elseArg := args[p + 2 + named.length]!
  let .forallE _ dom _ _ ← whnf (← inferType elseArg) | return none
  let dflt? ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then return none
    return some b
  let some dflt := dflt? | return none
  let params := mty.getAppArgs
  let casesOn := mkAppN (mkConst (indName ++ `casesOn) (motiveLvl :: indLvls))
    (params ++ #[motive, major])
  let mut cur := casesOn
  for i in [0:ctors.size] do
    let minor ← match named.idxOf? i with
      | some j => pure args[p + 2 + j]!
      | none => do
          let .forallE _ d _ _ ← whnf (← inferType cur)
            | throwError "`#leanscript_to_term`: internal: {indName}.casesOn takes too few \
                branches"
          forallTelescopeReducing d fun xs _ => mkLambdaFVars xs dflt
    cur := mkApp cur minor
  let extra := args.extract arity args.size
  return some (mkAppN cur extra)

/-- A `match` that names only some of the constructors, as Lean compiled it: the
    auxiliary `f._sparseCasesOn_i`.  Its branches and its `else` branch are the branches
    and the default of the grammar's partial dispatch, so this is where
    `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` and
    `recTaggedUnion_casesOnWithDefault` are built.

    A type whose tree has no partial dispatch — a record, a terminal type, a one-field
    wrapper — is not handled here: the auxiliary is unfolded and the exhaustive dispatch
    is built instead, which is what `none` means. -/
def transSparseCasesOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM (Option Expr) := do
  let some (arity, named, p) ← sparseCasesOnInfo? n | return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[p]!
  unless motive.isLambda do return none
  let major := args[p + 1]!
  let sty ← tyOfTerm major
  -- the grammar has a partial dispatch for a sum type only
  let view ← tyView sty
  match view with
  | .enum _ | .taggedUnion _ | .recTaggedUnion _ _ | .mutualRecursiveFamily _ _ _ => pure ()
  | _ => return none
  let .const indName _ := (← whnf (← inferType major)).getAppFn | return none
  -- inside the branches of a fold of a family, taking one of its values apart is the
  -- fold's look further down (see `TCtx.foldInds`)
  if view matches .mutualRecursiveFamily .. then
    if c.foldInds.contains indName then return none
  let indInfo ← getConstInfoInduct indName
  let ctors := indInfo.ctors.toArray
  if named.length ≥ ctors.size then return none
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    tyOfType body
  -- the branches, by constructor number, and the default
  let mut minors : Array Expr := ctors.map fun _ => (Lean.mkConst ``True)
  for j in [0:named.length] do
    minors := minors.set! named[j]! args[p + 2 + j]!
  let elseArg := args[p + 2 + named.length]!
  let elseTy ← whnf (← inferType elseArg)
  let .forallE _ dom _ _ := elseTy | return none
  let dflt ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then
      throwError "`#leanscript_to_term`: the default branch of this `match` uses the \
        proof that the value is none of the constructors named, which the language \
        erases"
    return b
  let dfltTerm ← trans c dflt
  let scrut ← trans c major
  let kE := mkNatLit named.length
  let core ← match view with
    | .enum s =>
        let cases ← mkEnumSomeCases (transBranch trans c) c τ s named 0 minors ctors
        let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, nE])
        pure <| mkAppN (mkConst `LeanScript.Term.enum_casesOnWithDefault')
          #[c.sg, c.gamma, τ, s, kE, scrut, cases, dfltTerm, hk]
    | .taggedUnion l =>
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOnWithDefault')
          #[c.sg, c.gamma, τ, l, kE, scrut, cases, dfltTerm, hk]
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ unfE named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOnWithDefault')
          #[c.sg, c.gamma, τ, l, hwf, kE, scrut, cases, dfltTerm, hk]
    | .mutualRecursiveFamily nE f hwf =>
        -- only a member with constructors can be dispatched on partially
        let (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) :=
            (← famCurrentUnfolded nE f hwf).getAppFnArgs
          | return none
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        let someCases := mkAppN (mkConst `LeanScript.FamilyMemberSomeCases.ctors)
          #[c.sg, c.gamma, τ, jnilE, l, kE, cases, hk]
        pure <| mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_casesOnWithDefault')
          #[c.sg, c.gamma, τ, nE, f, hwf, scrut, someCases, dfltTerm]
    | _ => return none
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra)

/-- The case analysis of a value of a **structure the language models by its one kept
    field** (a subtype `{x // p x}`, whose proof is erased): the branch, applied to the
    projections of the value, which is bound once by a `let` unless it is a variable.
    `none` when the type has more than one constructor. -/
def wrapperCasesAsProjs? (major : Expr) (minors : Array Expr) (ctors : Array Name) :
    MetaM (Option Expr) := do
  unless minors.size == 1 && ctors.size == 1 do return none
  let ci ← getConstInfoCtor ctors[0]!
  unless ci.numFields > 0 do return none
  let build (v : Expr) : Expr :=
    (mkAppN minors[0]! ((List.range ci.numFields).toArray.map fun i =>
      Expr.proj ci.induct i v)).headBeta
  if major.consumeMData.isFVar then return some (build major)
  withLetDecl `s (← inferType major) major fun s => do
    return some (← mkLetFVars #[s] (build s))

/-- The eliminator a recursor becomes. -/
def transRecCore (trans : TransFn) (c : TCtx) (ri : RecursorVal) (τ : Expr) (minors : Array Expr)
    (major : Expr) : MetaM Expr := do
  let ind := ri.getMajorInduct

  let scrut ← trans c major
  match ind with
  | ``Nat =>
      -- the fold, or the case analysis when the branch does not use the recursive value
      let natTy ← tyOfType (mkConst ``Nat)
      let z ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 2) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[1]!.fvarId! then
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy), (xs[1]!.fvarId!, τ)]
          return mkAppN (mkConst `LeanScript.Term.nat_rec')
            #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], ← trans c' body]
        else
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy)]
          return mkAppN (mkConst `LeanScript.Term.nat_casesOn')
            #[c.sg, c.gamma, τ, scrut, z, ← trans c' body]
  | ``List =>
      let sty ← tyOfTerm major
      let .recTaggedUnion l hwf ← tyView sty
        | throwError "`#leanscript_to_term`: {major} is not a list"
      let (cp, fieldsNE, restL) ← listSchemaParts l
      -- the head of the payload is written in the scope the binder opens; as a *value*
      -- of the language it is that tree, unfolded — which for an element type that is
      -- not an occurrence is the tree itself
      let σ ← match ← nonEmptyTys fieldsNE with
        | [σ, _] => bundleTyE 0 (← treeOfTyE σ)
        | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
      let nil ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 3) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[2]!.fvarId! then
          -- the fold: the branch is given the value of the fold at the tail
          let c' := c.pushFields
            #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty), (xs[2]!.fvarId!, τ)]
          let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
          let ι := tyWfInE 1
          let depth := mkNatLit 0
          let outerNil := mkApp (mkConst ``List.nil [Level.zero])
            (mkApp (mkConst ``List [Level.zero]) ι)
          let nilFs := mkApp (mkConst ``List.nil [Level.zero]) ι
          let consFs := mkApp2
            (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
            ι fieldsNE
          -- the branches of a depth-zero fold: one answer each, none of them looking
          -- further down
          let nilBranch := mkAppN (mkConst `LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, nilFs, τ, depth, outerNil, nil]
          let consBranch := mkAppN (mkConst `LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, consFs, τ, depth, outerNil, ← trans c' body]
          let restCases := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.nil)
            #[c.sg, l, bindE, c.gamma, τ, depth, outerNil]
          let consCases := mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.here)
            #[c.sg, l, bindE, c.gamma, τ, depth, outerNil, fieldsNE, restL, consBranch, restCases]
          let cases := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.skip)
            #[c.sg, l, bindE, c.gamma, τ, depth, outerNil, cp, nilBranch, consCases]
          return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_rec')
            #[c.sg, c.gamma, τ, l, hwf, depth, scrut, cases]
        else
          -- the case analysis: the branches are over the unfolded schema, in which the
          -- tail is a list again
          let (cpU, fieldsU, restU) ←
            listSchemaParts (← reduceTy
              (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf))
          let c' := c.pushFields #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty)]
          let restCases := mkAppN (mkConst `LeanScript.TaggedUnionFoldCasesRest.nil)
            #[c.sg, tyE, idBindE, c.gamma, τ, jnilE]
          let consCases := mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldCases.here)
            #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, fieldsU, restU, ← trans c' body, restCases]
          let cases := mkAppN (mkConst `LeanScript.TaggedUnionFoldCases.skip)
            #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, cpU, nil, consCases]
          return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOn')
            #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
  | ``Bool =>
      return mkAppN (mkConst `LeanScript.Term.bool_casesOn')
        #[c.sg, c.gamma, τ, scrut, ← trans c minors[1]!, ← trans c minors[0]!]
  | _ =>
      let indInfo ← getConstInfoInduct ind
      if indInfo.isRec then
        throwError "`#leanscript_to_term`: {ind} is a recursive type, and the only folds \
          the translation produces from a recursor are `nat_rec` and `recTaggedUnion_rec`, \
          for `Nat` and `List` (a structural recursion on a recursive record or a \
          recursive tagged union, a recursive newtype or a mutual block, as Lean \
          compiles it, is `recObject_rec`, `recTaggedUnion_rec`, `recAlias_rec` or \
          `mutualRecursiveFamily_rec`)"
      let sty ← tyOfTerm major
      let ctors := indInfo.ctors.toArray
      match ← tyView sty with
      | .record fs =>
          let fieldTys ← recordFieldTys fs
          let body ← transBranch trans c minors[0]! ctors[0]! fieldTys
          return mkAppN (mkConst `LeanScript.Term.record_casesOn')
            #[c.sg, c.gamma, τ, fs, scrut, body]
      | .taggedUnion l =>
          -- a `match` with a wildcard repeats one branch: that is the partial dispatch
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, lenE])
            return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOnWithDefault')
              #[c.sg, c.gamma, τ, l, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkTaggedUnionCases (transBranch trans c) c τ l 0 minors ctors
          return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn')
            #[c.sg, c.gamma, τ, l, scrut, cases]
      | .enum s =>
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkEnumSomeCases (transBranch trans c) c τ s named 0 minors ctors
            let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, nE])
            return mkAppN (mkConst `LeanScript.Term.enum_casesOnWithDefault')
              #[c.sg, c.gamma, τ, s, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkEnumCases (transBranch trans c) c τ s minors ctors
          return mkAppN (mkConst `LeanScript.Term.enum_casesOn')
            #[c.sg, c.gamma, τ, s, scrut, cases]
      | .prim _ =>
          if (← isBoolTy sty) && minors.size == 2 then
            return mkAppN (mkConst `LeanScript.Term.bool_casesOn')
              #[c.sg, c.gamma, τ, scrut, ← transBranch trans c minors[1]! ctors[1]! [],
                ← transBranch trans c minors[0]! ctors[0]! []]
          -- a structure whose tree is a terminal type is the one field the language
          -- keeps (a subtype, whose proof is erased): its case analysis reads the fields
          if let some e' ← wrapperCasesAsProjs? major minors ctors then
            return ← trans c e'
          throwError "`#leanscript_to_term`: a terminal type has no dispatch of its own"
      | _ =>
          if minors.size == 1 then
            -- a one-field wrapper: its case analysis substitutes the value
            return ← transBranch trans c minors[0]! ctors[0]! [← tyOfTerm major]
          throwError "`#leanscript_to_term`: the tree of {ind} has no dispatch in the \
            grammar"

/-- An application of a recursor. -/
def transRecApp (trans : TransFn) (c : TCtx) (e : Expr) (ri : RecursorVal) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  -- the recursor of an indexed family that a `casesOn` was reduced to (by `whnfCore`),
  -- applied to the equations of a `match`: that `casesOn` again, which is translated
  if ri.numIndices != 0 then
    if let some e' ← recAsCasesOn? e then return ← trans c e'
  unless ri.numMotives == 1 && ri.numIndices == 0 do
    throwError "`#leanscript_to_term`: {ri.name} is not an eliminator the language has"
  let arity := ri.numParams + 1 + ri.numMinors + 1
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[ri.numParams]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {ri.name} is not a function"
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {ri.name} is used with a dependent motive, \
        which the language has no eliminator for"
    tyOfType body
  let minors := args.extract (ri.numParams + 1) (ri.numParams + 1 + ri.numMinors)
  let major := args[ri.numParams + 1 + ri.numMinors]!
  let core ← transRecCore trans c ri τ minors major
  let extra := args.extract arity args.size
  if extra.isEmpty then return core
  applyArgs trans c core (mkAppN (mkConst ri.name lvls) (args.extract 0 arity)) extra

/-- Translate a closed definition, once: the translation is stored as a function of the
    context, and two definitions of the same shape share one tree. -/
def transClosedCached (trans : TransFn) (c : TCtx) (v : Expr) : MetaM Expr := do
  if v.hasFVar || v.hasMVar then return ← trans c v
  let st ← cacheRef.get
  if let some entry := st.entries.find? fun en => en.sg == c.sg && en.src == v then
    cacheRef.modify fun s => { s with hits := s.hits + 1 }
    return mkApp entry.fn c.gamma
  let fn ← withLocalDeclD `Γ ctxE fun g => do
    let t ← trans { c with base := g, binders := #[] } v
    mkLambdaFVars #[g] t
  let h := fn.hash
  let st ← cacheRef.get
  let shared? := st.entries.find? fun en => en.hash == h && en.fn == fn
  let fn := match shared? with | some en => en.fn | none => fn
  cacheRef.modify fun s =>
    { s with
      entries := s.entries.push { sg := c.sg, src := v, fn := fn, hash := h },
      shared := if shared?.isSome then s.shared + 1 else s.shared }
  return mkApp fn c.gamma

/-- The de Bruijn index a `DeBruijnProj` expression reads: the number of `tail`s around
    its `head`. -/
partial def deBruijnIndexOf? (e : Expr) : Option Nat :=
  match e.consumeMData.getAppFnArgs with
  | (``LeanScript.DeBruijnProj.head, _) => some 0
  | (``LeanScript.DeBruijnProj.tail, #[_, _, _, _, _, _, v]) => (deBruijnIndexOf? v).map (· + 1)
  | _ => none

/-- A translated function that is the **eta-expansion of a declaration of the
    signature**, `lam … lam (global g (var (k-1)) … (var 0))` (which is what an instance
    such as `instHAdd` unfolds to, when `Nat.add` is declared): the tree and the reference
    of `g`, and the number `k` of its `lam`s.  The body is read under the binder of the
    context the cached translation is a function of, so `g` must not mention it. -/
partial def etaGlobal? (body : Expr) : Option (Expr × Expr × Nat) := Id.run do
  -- the `lam`s
  let mut cur := body
  let mut k := 0
  while cur.isAppOfArity `LeanScript.Term.lam 5 do
    cur := cur.appArg!
    k := k + 1
  if k == 0 then return none
  -- the applications, outermost last: the argument of the `i`-th from the outside is the
  -- variable `i`
  for i in [0:k] do
    unless cur.isAppOfArity `LeanScript.Term.ap 6 do return none
    let a := cur.appArg!
    unless a.isAppOfArity `LeanScript.Term.var 4 do return none
    unless deBruijnIndexOf? a.appArg! == some i do return none
    cur := cur.appFn!.appArg!
  unless cur.isAppOfArity `LeanScript.Term.global 4 do return none
  let args := cur.getAppArgs
  let ty := args[2]!
  let ref := args[3]!
  if ty.hasLooseBVars || ref.hasLooseBVars then return none
  return some (ty, ref, k)

/-- Does the language have no tree for the type of this argument?  An argument the
    language erases (a type, a proof, an instance) is not such an argument. -/
def argHasNoTree (a : Expr) : MetaM Bool := do
  let ty ← inferType a
  if ← LeanScript.Deriving.erasedBinder ty then return false
  try
    let _ ← treeOfType ty
    return false
  catch _ => return true

/-- A dispatch (`match`, `X.casesOn`, `X.rec`) on a **constructor application** whose type
    the language has no tree for — a value of a datatype with existentials that is written
    out, `(Src.gen Nat 4 f).value` once `Src.value` is specialized to it: the branch of that
    constructor, applied to its fields.  The dispatch could not be translated as it stands
    (the scrutinee has no type of the language), and need not be: its constructor is known.
    `none` when `e` is not such a dispatch. -/
def reduceDispatchOnNoTreeCtor? (e : Expr) (n : Name) : MetaM (Option Expr) := do
  if ← Meta.isMatcherApp e then
    let some m ← matchMatcherApp? e | return none
    let mut hit := false
    for d in m.discrs do
      let d' ← whnfR d
      if d'.getAppFn.isConst && (← isConstructorApp d') && (← argHasNoTree d) then hit := true
    unless hit do return none
    match ← Lean.Meta.reduceMatcher? e with
    | ReduceMatcherResult.reduced e' => return some e'.headBeta
    | _ => return none
  unless n.isStr && (n.getString! == "casesOn" || n.getString! == "rec") do return none
  let some (.inductInfo ii) := (← getEnv).find? n.getPrefix | return none
  let args := e.getAppArgs
  let majorIdx := if n.getString! == "casesOn" then ii.numParams + 1 + ii.numIndices
    else ii.numParams + ii.numNested + 1 + ii.ctors.length + ii.numIndices
  let some major := args[majorIdx]? | return none
  unless ← isConstructorApp (← whnfR major) do return none
  unless ← argHasNoTree major do return none
  let e' ← if n.getString! == "casesOn" then
      match ← unfoldDefinition? e with
      | some u => pure u
      | none => return none
    else pure e
  let r ← whnfCore e'
  if r == e' then return none
  return some r

/-- The call `f args`, **specialized** to its arguments that have no tree (values of a
    datatype with existentials): those arguments are substituted into the body of `f`,
    and so are the arguments that cost nothing to read twice (variables, literals, erased
    arguments); every other argument is bound once by a `let`, so nothing is computed
    twice.  `none` when no argument lacks a tree, unless `force` (the call builds a value
    without a tree, which the cache of closed definitions cannot hold). -/
def transSpecialized? (trans : TransFn) (c : TCtx) (f : Expr) (args : Array Expr)
    (force : Bool := false) : MetaM (Option Expr) := do
  let noTree ← args.mapM argHasNoTree
  unless force || noTree.any id do return none
  let rec go (i : Nat) (acc : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let a := args[i]
      let atomic := a.consumeMData.isFVar || isLitLike a ||
        (← LeanScript.Deriving.erasedBinder (← inferType a))
      if noTree[i]! || atomic then
        go (i + 1) (acc.push a)
      else
        withLetDecl `x (← inferType a) a fun x => do
          let b ← go (i + 1) (acc.push x)
          mkLetFVars #[x] b
    else
      return (mkAppN f acc).headBeta
  return some (← trans c (← go 0 #[]))

/-- A call of an inlinable function: its definition is translated, once, and used
    here. -/
def transInline (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let info ← getConstInfo n
  let some val := info.value? |
    throwError "`#leanscript_to_term`: `{n}` has no definition to inline"
  let val := val.instantiateLevelParams info.levelParams lvls
  -- how many leading arguments does the language erase?
  let nLeading ← forallTelescopeReducing info.type fun xs _ => do
    let mut k := 0
    for h : i in [0:xs.size] do
      if i ≥ args.size then break
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then k := k + 1 else break
    return k
  let leading := args.extract 0 nLeading
  let headVal := (mkAppN val leading).headBeta
  if headVal.hasFVar || headVal.hasMVar then
    let some e' ← unfoldHere? e
      | throwError "`#leanscript_to_term`: cannot inline `{n}`"
    return ← trans c e'
  let rest := args.extract nLeading args.size
  -- applied to a value whose Lean type has no tree (a value of a datatype with
  -- existentials, `Unfold`), the definition is **specialized** to that value: it is
  -- substituted, so that its projections (`u.State`, `u.seed`, `u.step`) are those of the
  -- value, which the translation reduces when the value is closed
  if headVal.isLambda then
    if let some t ← transSpecialized? trans c headVal rest (force := ← argHasNoTree e) then
      return t
  -- applied to variables (and literals) only, the definition is substituted rather than
  -- applied: `fibTR t = fibLoopTR t 0 1` is the fold of `t` applied to `0` and `1`, not a
  -- redex whose function is the fold of its own bound variable.  Nothing is duplicated,
  -- since a variable or a literal costs nothing to read twice.  A call on literals alone
  -- is a closed value, which the cache serves.
  if headVal.isLambda && rest.any (·.consumeMData.isFVar) &&
      rest.all (fun a => a.consumeMData.isFVar || isLitLike a) then
    return ← trans c (mkAppN headVal rest).headBeta
  let t ← transClosedCached trans c headVal
  -- an inlined function that is only the eta-expansion of a declaration of the signature
  -- is that declaration, applied directly: `a + b` is `global add a b`, with no redex
  let t := match t.getAppFn with
    | .lam _ _ body _ =>
        match etaGlobal? body with
        | some (ty, ref, k) =>
            if rest.size ≥ k then
              mkAppN (mkConst `LeanScript.Term.global) #[c.sg, c.gamma, ty, ref]
            else t
        | none => t
    | _ => t
  applyArgs trans c t (mkAppN (mkConst n lvls) leading) (args.extract nLeading args.size)

end LeanScript.ToTerm

end

end
