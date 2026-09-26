module

public meta import LeanScript.ToTerm.Trans

@[expose] public section

meta section

/-!
# Functions on a structure with an existential type field

```lean
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

def Unfold.take (u : Unfold α) (fuel : Nat) : List α := …
```

A value of `Unfold α` has no one tree of the language: the tree of its `seed` is the type
the value chose for `State`.  So `Unfold α` has no `LeanScriptTyWf` instance, and there are
two ways a function on it is translated.

* **Specialized to a value.**  A call on a value that is written out (`countdown.take n`,
  `(countFrom k).take n`) is specialized to it: the value is substituted into the function
  (`LeanScript.ToTerm.transSpecialized?`), so `u.State`, `u.seed` and `u.step` are the
  value's own, and the call is an ordinary term.  Such a function cannot be declared in the
  signature (it has no type), so it is specialized whether or not it is `@[inline]`.

* **Generic in the hidden type.**  A function whose argument *is* such a value
  (`#leanscript_to_term (Unfold.take (α := Nat))`) translates to a Lean function of the tree
  of the hidden type:

  ```lean
  fun (State : TyWf) => (… : Term Sg Γ (Unfold.mk.leanScriptLayout (.prim .nat) State ⇒ …))
  ```

  that is, a term **for every** choice of the hidden type — which is what a function out of an
  existential is (`(∃ S, P S) → R` is `∀ S, P S → R`).  The argument is the value built by the
  constructor function of `#leanscript_ctor` (`LeanScript.CtorFn`), its layout; the function
  takes its record apart (`record_casesOn`) and reads the fields as variables, with
  `u.State` the tree `State` (through `LeanScript.TyWf.Hidden`).  Applied to the tree a
  value chose (`f (.prim .nat)`), it is a term that can be applied to that value.

The generic translation is for the arguments of the definition translated (its outer `fun`s),
since the tree is a Lean argument and not a value of the language: it stands outside every
`Term.lam`.  It covers a structure (one constructor, no index) with type fields, and a
**non-recursive datatype of several constructors, or with indices** (`Src`, a GADT `Tag`):
its argument is *one of* the layouts of its constructors, `TyWf.oneOf` in the order of the
constructors (an alternative with no field for a constructor that carries no value), with
one tree per hidden type of every constructor, and the function dispatches on which
(`taggedUnion_casesOn`) — `transGenericUnionLam`.  A datatype whose existentials sit under
its own recursion (`Process`) has values only, through the constructor functions.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- A structure with an existential type field: one constructor, no index, not recursive, and a
    field that is a type.  The constructor, the arguments of the type, and the universe levels
    of the type. -/
def existentialStructure? (d : Expr) : MetaM (Option (ConstructorVal × Array Expr × List Level)) := do
  let d ← whnf d
  let .const ind lvls := d.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? ind | return none
  unless iv.ctors.length == 1 && iv.numIndices == 0 && !iv.isRec do return none
  let args := d.getAppArgs
  if (← LeanScript.Deriving.existentialField? ind args).isNone then return none
  let ci ← getConstInfoCtor iv.ctors[0]!
  return some (ci, args, lvls)

/-- A **non-recursive datatype with existentials** that is not a structure: several
    constructors (`Src`, whose `gen` hides the type of its state), or an index (a GADT,
    `Tag : Type → Type`, whose `wrap {α} (x : α) : Tag (List α)` hides `α`).  Its
    constructors, the arguments of the type, and the universe levels.  A recursive one
    (`Process`, whose hidden types differ from node to node) is not one. -/
def existentialUnion? (d : Expr) :
    MetaM (Option (Array ConstructorVal × Array Expr × List Level)) := do
  let d ← whnf d
  let .const ind lvls := d.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? ind | return none
  if iv.isRec || iv.all.length != 1 then return none
  if iv.ctors.length == 1 && iv.numIndices == 0 then return none
  let args := d.getAppArgs
  unless args.size == iv.numParams + iv.numIndices do return none
  if (← LeanScript.Deriving.existentialField? ind args).isNone then return none
  let cis ← iv.ctors.toArray.mapM getConstInfoCtor
  return some (cis, args, lvls)

/-- The universe of a type field: `u` for a field of type `Sort (u + 1)`. -/
def typeFieldLevel? (t : Expr) : MetaM (Option Level) := do
  match ← whnf t with
  | .sort (.succ u) => return some u
  | _ => return none

/-- The type fields of the constructor of an existential structure, instantiated at the
    arguments of the type: their names. -/
def existentialTypeFields (ci : ConstructorVal) (params : Array Expr) : MetaM (Array Name) := do
  let cty ← instantiateForall ci.type (params.extract 0 ci.numParams)
  forallTelescopeReducing cty fun xs _ => do
    let mut out := #[]
    for x in xs do
      if (← typeFieldLevel? (← inferType x)).isSome then
        out := out.push (← x.fvarId!.getUserName)
    return out

/-- The names of the hidden types of the leading arguments of `val` that are existential
    structures, in order. -/
def hiddenTypeNames (val : Expr) : MetaM (Array Name) :=
  lambdaTelescope val fun xs _ => do
    let mut out := #[]
    for x in xs do
      let t ← inferType x
      if let some (ci, params, _) ← existentialStructure? t then
        out := out ++ (← existentialTypeFields ci params)
      else if let some (cis, args, _) ← existentialUnion? t then
        for ci in cis do
          out := out ++ (← existentialTypeFields ci args)
    return out

/-- The value `ctor params fields` whose type fields are the Lean types standing for the trees
    `hidden` (`TyWf.Hidden`) and whose other fields are fresh variables; `k` is given the
    value, the variables of the fields that carry a value of the language (in order), and what
    is left of `hidden`. -/
partial def withGenericValue {α : Type} (ci : ConstructorVal) (params : Array Expr)
    (lvls : List Level) (hidden : List Expr)
    (k : Expr → Array Expr → List Expr → MetaM α) : MetaM α := do
  let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls)
    (params.extract 0 ci.numParams)
  let rec go (ty : Expr) (vals kept : Array Expr) (hidden : List Expr) : MetaM α := do
    match ← whnf ty with
    | .forallE n d b bi =>
        if let some u ← typeFieldLevel? d then
          let some S := hidden.head?
            | throwError "`#leanscript_to_term`: internal: no tree for the hidden type `{n}`"
          let v := mkApp (mkConst ``LeanScript.TyWf.Hidden [u]) S
          go (b.instantiate1 v) (vals.push v) kept hidden.tail
        else
          withLocalDecl n bi d fun x => do
            let kept ← if ← LeanScript.Deriving.erasedBinder d then pure kept
              else pure (kept.push x)
            go (b.instantiate1 x) (vals.push x) kept hidden
    | _ =>
        k (mkAppN (mkConst ci.name lvls) (params.extract 0 ci.numParams ++ vals)) kept hidden
  go cty #[] #[] hidden

/-- The schema of the tagged union with one constructor per alternative: one field, the
    layout, for `some σ`, and no field for `none` (a constructor that carries no value).  At
    least two alternatives, one of them with a layout. -/
def mkAltSchema (alts : Array (Option Expr)) : MetaM Expr := do
  let listTy := mkApp (mkConst ``List [Level.zero]) tyWfTyE
  let fieldsOf (a : Option Expr) : MetaM Expr := mkListLit tyWfTyE a.toList
  let ne (a : Expr) : MetaM Expr := do
    mkAppM ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk #[a, ← mkListLit tyWfTyE []]
  let rec cwp (as : List (Option Expr)) : MetaM Expr := do
    match as with
    | some a :: rest =>
        mkAppM ``LeanScript.CtorsWithPayload.here
          #[← ne a, ← mkListLit listTy (← rest.mapM fieldsOf)]
    | none :: rest => mkAppM ``LeanScript.CtorsWithPayload.skip #[← cwp rest]
    | [] => throwError "`#leanscript_to_term`: internal: no alternative carries a value"
  match alts.toList with
  | some a :: next :: rest =>
      mkAppM ``LeanScript.LeanTaggedUnionSchema.payloadFirst
        #[← ne a, ← fieldsOf next, ← mkListLit listTy (← rest.mapM fieldsOf)]
  | none :: rest => mkAppM ``LeanScript.LeanTaggedUnionSchema.skip #[← cwp rest]
  | _ => throwError "`#leanscript_to_term`: internal: fewer than two alternatives"

/-- `withGenericValue` for each of the constructors `cis` in turn: `k` is given, per
    constructor, the value and the variables of its kept fields, and what is left of
    `hidden`. -/
def withGenericValues {α : Type} (cis : List ConstructorVal) (params : Array Expr)
    (lvls : List Level) (hidden : List Expr)
    (k : Array (Expr × Array Expr) → List Expr → MetaM α) : MetaM α :=
  go cis #[] hidden
where
  /-- The constructors still to bind, and the values bound so far. -/
  go : List ConstructorVal → Array (Expr × Array Expr) → List Expr → MetaM α
    | [], acc, hidden => k acc hidden
    | ci :: rest, acc, hidden =>
        withGenericValue ci params lvls hidden fun u kept hidden =>
          go rest (acc.push (u, kept)) hidden

/-- The tree of a value of an existential structure whose kept fields have the trees
    `keptTys`: the record of those trees (the one tree, for one field) — which is the layout
    of its constructor function (`#leanscript_layout`), and is written as that layout when the
    two are the same. -/
def layoutOf (c : TCtx) (ci : ConstructorVal) (args : Array Expr) (keptTys : Array Expr) :
    MetaM Expr := do
  let mine ← match keptTys.toList with
    | [t] => pure t
    | a :: b :: rest => do
        let elem := tyWfTyE
        let restE := rest.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem x acc)
          (mkApp (mkConst ``List.nil [Level.zero]) elem)
        pure (mkApp (mkConst ``LeanScript.TyWf.record)
          (mkApp4 (mkConst ``LeanScript.LeanRecordSchema.mk) elem a b restE))
    | [] => throwError "`#leanscript_to_term`: a value of `{ci.induct}` carries no value of \
        the language"
  let layout? ← try
      let vals ← LeanScript.CtorFn.tyVarValues ci args
      let erased ← vals.mapM LeanScript.Deriving.erasedBinder
      let (_, fnName) ← LeanScript.CtorFn.ensureCtorFn ci.name erased
      let kept := (vals.zip erased).filterMap fun (v, er) => if er then none else some v
      let fnC ← mkConstWithFreshMVarLevels fnName
      let mut ty ← instantiateForall (← inferType fnC) #[c.sg, c.gamma]
      for v in kept do
        let .forallE _ _ b _ := ty | failure
        ty := b.instantiate1 (← tyWfOfType v)
      repeat
        let .forallE _ d b _ := ty | break
        if d.isConstOf ``LeanScript.TyWf then
          ty := b.instantiate1 (← mkFreshExprMVar tyWfTyE)
        else
          if b.hasLooseBVars then failure
          ty := b
      let (`LeanScript.Term, #[_, _, resTy, _]) := ty.getAppFnArgs | failure
      if ← isDefEq resTy mine then
        let resTy ← instantiateMVars resTy
        pure (if resTy.hasExprMVar then none else some resTy)
      else pure none
    catch _ => pure none
  return layout?.getD mine

/-- `Term.lam`, of the tree `σ`, around the body `b` of the tree `τ`. -/
def mkLamE (c : TCtx) (σ τ b : Expr) : Expr :=
  mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

mutual

/-- `fun (x : D …) => b` for a non-recursive datatype `D` with existentials and several
    constructors (or an index): the argument is **one of** the layouts of its constructors,
    each at its own hidden types (`TyWf.oneOf`, in the order of the constructors), and the
    function dispatches on which (`taggedUnion_casesOn`).  The branch of a constructor is `b`
    at that constructor applied to its fields as variables — at the constructor's indices,
    when `D` is indexed by earlier arguments (`{β} (t : Tag β)`) — which the translation
    reduces, as for a structure. -/
partial def transGenericUnionLam (c : TCtx) (d b : Expr) (cis : Array ConstructorVal)
    (args : Array Expr) (lvls : List Level) (hidden : List Expr) : MetaM Expr := do
  let nP := cis[0]!.numParams
  let params := args.extract 0 nP
  let idxs := args.extract nP args.size
  -- the indices must be variables bound before, which each constructor then fixes
  for h : i in [0:idxs.size] do
    let x := idxs[i]
    unless x.isFVar && !(idxs.extract 0 i).contains x do
      throwError "`#leanscript_to_term`: the argument of type {d} has the index {x}, which \
        is not a variable of its own; a function of a datatype with existentials is \
        translated for every choice of its hidden types only at indices it is generic in"
  withGenericValues cis.toList params lvls hidden fun vals hidden => do
    -- the layout of each constructor, at the hidden types it reads
    -- (`none` for a constructor that carries no value: an alternative with no field)
    let mut alts : Array (Option Expr) := #[]
    for h : i in [0:vals.size] do
      let (u, kept) := vals[i]
      if kept.isEmpty then
        if vals.size == 1 then
          throwError "`#leanscript_to_term`: the constructor `{cis[i]!.name}` of {d} \
            carries no value, so a function of {d} has no term"
        alts := alts.push none
        continue
      let keptTys ← kept.mapM fun x => do tyOfTerm x
      alts := alts.push (some (← layoutOf c cis[i]! u.getAppArgs keptTys))
    -- `TyWf.oneOf` of the layouts when every constructor has one, and otherwise the tagged
    -- union with a field-less alternative for each constructor that carries no value
    let (σ, l?) ← if alts.all (·.isSome) then
        pure (← mkOneOf (alts.map (·.get!)), none)
      else do
        let l ← mkAltSchema alts
        pure (mkApp (mkConst ``LeanScript.TyWf.taggedUnion) l, some l)
    let whole ← mkFreshFVarId
    let c1 := c.push whole σ
    -- the branch of each constructor, with the value of its layout bound
    let mut branches : Array Expr := #[]
    let mut τ? : Option Expr := none
    for h : i in [0:vals.size] do
      let (u, kept) := vals[i]
      let uIdx := (← whnf (← inferType u)).getAppArgs.extract nP (nP + idxs.size)
      let body := (b.instantiate1 u).replaceFVars idxs uIdx
      let σi := alts[i]!.getD tyWfTyE
      let (t, τi) ← if kept.isEmpty then do
          let t ← transGenericLams c1 body hidden
          pure (t, ← termTyOf t)
        else if kept.size == 1 then do
          let t ← transGenericLams (c1.pushFields #[(kept[0]!.fvarId!, σi)]) body hidden
          pure (t, ← termTyOf t)
        else do
          let part ← mkFreshFVarId
          let cp := c1.pushFields #[(part, σi)]
          let .record fs ← tyView σi
            | throwError "`#leanscript_to_term`: the layout of `{cis[i]!.name}` is not a \
                record of the language"
          let fieldTys ← recordFieldTys fs
          unless fieldTys.length == kept.size do
            throwError "`#leanscript_to_term`: internal: the layout of `{cis[i]!.name}` has \
              {fieldTys.length} fields, not {kept.size}"
          let c2 := cp.pushFields (kept.map (·.fvarId!) |>.zip fieldTys.toArray)
          let t ← transGenericLams c2 body hidden
          let τi ← termTyOf t
          pure (mkAppN (mkConst `LeanScript.Term.record_casesOn')
            #[cp.sg, cp.gamma, τi, fs, ← cp.var part, t], τi)
      match τ? with
      | none => τ? := some τi
      | some τ =>
          unless ← isDefEq τ τi do
            throwError "`#leanscript_to_term`: the branch of `{cis[i]!.name}` answers a value \
              of type{indentExpr τi}\nand an earlier branch one of type{indentExpr τ}\n\
              — the answer of a function of {d} may not depend on the hidden types"
      branches := branches.push t
    let some τ := τ? | throwError "`#leanscript_to_term`: internal: {d} has no constructor"
    let τ ← instantiateMVars τ
    if alts.size == 1 then
      -- one constructor (an indexed structure): its layout is the argument itself
      let t := branches[0]!
      -- (the branch bound the value once more, above `whole`: read it from `whole`)
      let l := mkLamE c σ τ (mkAppN (mkConst `LeanScript.Term.letE')
        #[c1.sg, c1.gamma, σ, τ, ← c1.var whole, t])
      return l
    let l ← match l? with
      | some l => pure l
      | none => do
        let some u ← unfoldDefinition? σ
          | throwError "`#leanscript_to_term`: internal: cannot unfold {σ}"
        let (``LeanScript.TyWf.taggedUnion, #[l]) := u.getAppFnArgs
          | throwError "`#leanscript_to_term`: internal: {σ} is not a tagged union"
        pure l
    let names := (List.range vals.size).toArray.map fun i => Name.mkNum `alt i
    let cases ← mkTaggedUnionCases (fun _ n _ => do
        let .num _ i := n | throwError "`#leanscript_to_term`: internal: no branch {n}"
        pure branches[i]!) c1 τ l 0 (names.map fun _ => mkConst ``Unit) names
    return mkLamE c σ τ (mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn')
      #[c1.sg, c1.gamma, τ, l, ← c1.var whole, cases])

/-- The translation of `e`, whose leading arguments that are existential structures read the
    trees `hidden` for their hidden types. -/
partial def transGenericLams (c : TCtx) (e : Expr) (hidden : List Expr) : MetaM Expr := do
  match e.consumeMData with
  | .lam n d b bi =>
      if let some (cis, args, lvls) ← existentialUnion? d then
        return ← transGenericUnionLam c d b cis args lvls hidden
      if let some (ci, params, lvls) ← existentialStructure? d then
        return ← withGenericValue ci params lvls hidden fun u kept hidden => do
          -- the tree of the argument: the layout of the constructor function, read off the
          -- constructor applied to the fields as variables
          let keptTys ← kept.mapM fun x => do tyOfTerm x
          let σ ← layoutOf c ci (params.extract 0 ci.numParams ++ u.getAppArgs.extract
            ci.numParams u.getAppArgs.size) keptTys
          let body := b.instantiate1 u
          if kept.size == 1 then
            let c1 := c.push kept[0]!.fvarId! σ
            let t ← transGenericLams c1 body hidden
            return mkLamE c σ (← termTyOf t) t
          let .record fs ← tyView σ
            | throwError "`#leanscript_to_term`: the value of `{d}` is not a record of the \
                language"
          let fieldTys ← recordFieldTys fs
          unless fieldTys.length == kept.size do
            throwError "`#leanscript_to_term`: internal: the layout of `{d}` has \
              {fieldTys.length} fields, not {kept.size}"
          let whole ← mkFreshFVarId
          let c1 := c.push whole σ
          let c2 := c1.pushFields (kept.map (·.fvarId!) |>.zip fieldTys.toArray)
          let t ← transGenericLams c2 body hidden
          let τ ← termTyOf t
          let cases := mkAppN (mkConst `LeanScript.Term.record_casesOn')
            #[c1.sg, c1.gamma, τ, fs, ← c1.var whole, t]
          return mkLamE c σ τ cases
      if ← LeanScript.Deriving.erasedBinder d then
        return ← withLocalDecl n bi d fun x => transGenericLams c (b.instantiate1 x) hidden
      let σ ← tyOfType d
      withLocalDecl n bi d fun x => do
        let t ← transGenericLams (c.push x.fvarId! σ) (b.instantiate1 x) hidden
        return mkLamE c σ (← termTyOf t) t
  | e => trans c e

end

/-- The translation of a definition some of whose leading arguments are existential
    structures: the Lean function, of the trees of their hidden types, whose value is the term
    of the definition at those trees.  `none` when no leading argument is one. -/
def translateGeneric? (c : TCtx) (val : Expr) : MetaM (Option Expr) := do
  let names ← hiddenTypeNames val
  if names.isEmpty then return none
  let decls := names.map fun n => (n, fun _ => pure tyWfTyE)
  withLocalDeclsD decls fun Ss => do
    let t ← transGenericLams c val Ss.toList
    return some (← mkLambdaFVars Ss (← instantiateMVars t))

end LeanScript.ToTerm

end

end
