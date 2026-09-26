module

public meta import LeanScript.ToTerm.TransRecObject
public meta import LeanScript.ToTerm.Default

@[expose] public section

meta section

/-!
# The translation: a structural recursion on a recursive tagged union

`transRecUnionBrecOn?`, the clause of the translation for a structural recursion on a
**recursive tagged union** — an inductive type with several constructors whose fields are
either the type itself or values that do not mention it, such as

```lean
inductive Tree where
  | leaf
  | node (left : Tree) (val : Nat) (right : Tree)
```

whose tree is `Ty.recTaggedUnion`.  (`List α` is one too; `List.brecOn` comes here when
the one-step translation of `LeanScript.ToTerm.TransBrec` cannot serve it.)

Lean compiles such a recursion into `Tree.brecOn`, whose branch is handed the whole
history of the recursion; the grammar's fold, `LeanScript.Term.recTaggedUnion_rec' k`,
hands each branch the constructor's fields and the answers at its occurrences of the
union (`TyWf.recBinders`), and lets a branch **look further down**, at most `k` times:
dispatch again on one of those occurrences (`LeanScript.FoldKBranch.deep`), or on an
occurrence at a node above it that it has not looked into (`FoldKBranch.deepOuter`), and
be handed *its* fields and answers.

**How the branch is read.**  The case tree is built top down.  At each node the value's
shape is known down to that node: the constructors dispatched on along the path, and a
variable for every field not descended into.  The Lean branch is instantiated at that
shape and at the history built for it — whose entry at a subvalue that is bound is the
variable standing for the answer there, and whose deeper parts are unknown — and reduced.
If nothing unknown is left, that is the answer (`FoldKBranch.here`).  Otherwise the
unknown parts are the histories below subvalues not looked into yet, each a metavariable
whose type names its subvalue; when the depth allows it, each of those subvalues is tried
in turn as the one to look into — at this node (`FoldKBranch.deep`) or at a node above
(`FoldKBranch.deepOuter`), those furthest up first.  So a recursion that reads the
answers at the grandchildren below **both** children of a binary tree looks into the left
child and then, from there, into the right one: depth `2`.

The depth is the smallest `k` (up to `maxRecUnionRecDepth`) at which every branch is
served.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- One constructor of a recursive tagged union, as the fold reads it. -/
structure RecUnionCtor where
  /-- The Lean constructor. -/
  name : Name
  /-- Its fields: `none` for a field that is the union itself, `some α` for one of the
      Lean type `α`, which does not mention it. -/
  fields : Array (Option Expr)
  /-- Which fields the language erases (a type, a proof, an instance): bound as Lean
      variables, but not by the branch of the language, and absent from `fsL`.  The type
      `α` of `pair {α β : Type} (a : TExpr α) (b : TExpr β)` is one.  Empty when none is. -/
  erased : Array Bool := #[]
  /-- The list of its field trees, as an expression of type `List (TyWfIn 1)` — the index
      of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- Its type at the parameters, `∀ fields, X params indices`: a field of an indexed
      family's constructor may be typed by the ones before it (`v : Vec α n`). -/
  cty : Expr

/-- The type of the next field of a constructor of type `cty`, after the fields `vals`. -/
def ctorFieldTy (cty : Expr) (vals : Array Expr) : MetaM Expr := do
  let t ← whnf (← instantiateForall cty vals)
  let .forallE _ d _ _ := t
    | throwError "`#leanscript_to_term`: internal: the constructor has no more fields"
  return d

/-- What the fold of a recursive tagged union needs to know about it and the recursion. -/
structure RecUnionInfo where
  /-- The inductive type. -/
  ind : Name
  /-- The universe levels. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- The Lean type of the union, at its parameters. -/
  selfTy : Expr
  /-- The constructors, in order. -/
  ctors : Array RecUnionCtor
  /-- The schema of the union. -/
  l : Expr
  /-- The binders of a branch, `TyWf.recBinders ty τ`. -/
  bindE : Expr
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- The Lean branch of the `brecOn`. -/
  brecF : Expr
  /-- The motives of the `brecOn`. -/
  motives : Array Expr
  /-- The number of indices of the type (`0` unless it is an indexed family). -/
  nI : Nat := 0
  /-- The motive of the `brecOn`, reduced to a `fun`. -/
  motive0 : Expr := .bvar 0

/-- The index lists of the branches of a dispatch on this tagged-union schema of
    `TyWfIn sc`, one per constructor, in order: `fields.toList` for a constructor with a
    non-empty payload, `[]` for one without, as `LeanScript.TaggedUnionFoldKCases` (at
    `sc = 1`) and `LeanScript.FamilyTaggedUnionFoldKCases` are indexed. -/
partial def schemaCtorIndices (sc : Nat) (l : Expr) : MetaM (Array Expr) := do
  let ι := tyWfInE sc
  let toListE (ne : Expr) : Expr :=
    mkApp2 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
      ι ne
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) ι
  let rec cps (cp : Expr) : MetaM (Array Expr) := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
        return #[toListE fields] ++ (← listOfExpr rest).toArray
    | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
        return #[nilE] ++ (← cps rest)
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      return #[toListE fields, next] ++ (← listOfExpr rest).toArray
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return #[nilE] ++ (← cps rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- Replace the variables descended into by the shapes found for them, in the order they
    were descended into (a shape may mention variables descended into later). -/
def resolveShape (descend : Array (FVarId × Expr)) (e : Expr) : Expr :=
  descend.foldl (init := e) fun acc (f, s) => acc.replaceFVar (.fvar f) s

/-- The branch of the fold at a node of the case tree: the Lean branch instantiated at the
    shape found so far (`top` resolved through `descend`) and at the history in which the
    answer at a bound subvalue is its variable (`answers`), reduced, and translated in
    `c`.

    When the reduced branch still reads something the fold has not given — the history
    below a subvalue that has not been looked into — the result is `.inr` of those of the
    `pending` subvalues (the occurrences not yet looked into, at this node and at the
    nodes above it) whose history it reads: a deeper look into one of them is what the
    branch needs.  It fails when it reads nothing that a deeper look could give. -/
def recUnionLeaf (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr))
    (pending : Array FVarId) : MetaM (Expr ⊕ Array FVarId) := do
  let shape := resolveShape descend top
  let answers := answers.map fun (s, a) => (resolveShape descend s, a)
  let nP := info.params.size
  -- an indexed family's branch takes the value's indices first
  let idx := (← whnf (← inferType shape)).getAppArgs.extract nP (nP + info.nI)
  let fty ← instantiateForall (← inferType info.brecF) (idx.push shape)
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nM := info.motives.size
  let motiveTys ← info.motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildRecObjHistory ms info.motives answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN info.brecF (idx ++ #[shape, hist]))
  -- a dispatch on an indexed family (another argument, `Vec α n` beside this one) hands
  -- the history through the equations of its `match`: its branches are read first, so
  -- that the history is in plain sight
  let body ← instantiateMVars (← reduceHistoryProjs body)
  let body ← Meta.transform body (pre := fun t => do
    match ← normalizeIndexedCasesOn? t with
    | some t' => return .continue t'
    | none => return .continue t)
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    -- the unknown parts of the history are the histories below the subvalues not looked
    -- into, each a metavariable whose type names its subvalue
    let mut tys : Array Expr := #[]
    for m in ← getMVars body do
      tys := tys.push (← instantiateMVars (← m.getType))
    let needed := pending.filter fun f => tys.any (·.containsFVar f)
    unless needed.isEmpty do return .inr needed
    throwError "`#leanscript_to_term`: this recursion on a recursive tagged union reads \
      the value of the function, or takes a value apart, further down than the fold \
      looks at this depth"
  let indName := (← whnf (← inferType top)).getAppFn.constName?
  return .inl (← trans { c with foldInds := c.foldInds ++ indName.toArray } body)

/-- The pointer at the `p`-th field of this list of field trees, which is an occurrence
    of the union. -/
def mkSelfFieldE (fsL : Array Expr) (p : Nat) : MetaM Expr := do
  let ι := tyWfInE 1
  let mut acc : Option Expr := none
  for r in [0:p + 1] do
    let i := p - r
    let a := fsL[i]!
    let rest ← mkListLit ι (fsL.extract (i + 1) fsL.size).toList
    match acc with
    | none =>
        let h ← mkEqRefl (mkConst ``LeanScript.Ty.self)
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.here)
          #[ι, mkConst ``LeanScript.IsSelfField, a, rest, h])
    | some inner =>
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.there)
          #[ι, mkConst ``LeanScript.IsSelfField, a, rest, inner])
  return acc.get!

/-- The branches of a fold over the schema `l`, in its shape: `pre` are the implicit
    arguments every family of the case tree shares (signature, schema, binders, context,
    answer type, depth), and `branches` one `FoldKBranch` per constructor. -/
partial def mkRecUnionFoldKCases (pre : Array Expr) (l : Expr) (branches : Array Expr) :
    MetaM Expr := do
  let rest (from_ : Nat) (fsLists : List Expr) : MetaM Expr := do
    let mut acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.nil) pre
    let n := fsLists.length
    for i in [0:n] do
      let idx := n - 1 - i
      let fs := fsLists[idx]!
      let more ← mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE 1))
        (fsLists.drop (idx + 1))
      acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.cons)
        (pre ++ #[fs, more, branches[from_ + idx]!, acc])
    return acc
  let rec cpCases (cp : Expr) (i : Nat) : MetaM Expr := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, restL]) =>
        let rs ← listOfExpr restL
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.here)
          (pre ++ #[fields, restL, branches[i]!, ← rest (i + 1) rs])
    | (``LeanScript.CtorsWithPayload.skip, #[_, more]) =>
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.skip)
          (pre ++ #[more, branches[i]!, ← cpCases more (i + 1)])
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, restL]) =>
      let rs ← listOfExpr restL
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.payloadFirst)
        (pre ++ #[fields, next, restL, branches[0]!, branches[1]!, ← rest 2 rs])
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) =>
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.skip)
        (pre ++ #[cp, branches[0]!, ← cpCases cp 1])
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- A node of the case tree the fold has dispatched on: its constructor's field trees
    (`fsE`, with elements `fsL`) and, for each of its occurrences of the union, the
    position of the field and the variable bound for the subvalue there. -/
structure RecUnionFrame where
  /-- The list of the constructor's field trees, the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- The occurrences of the union among the fields: position and variable. -/
  subs : Array (Nat × FVarId)
  deriving Inhabited

/-- The nodes above a branch, innermost first, as the expression of type
    `List (List (TyWfIn 1))` the families of the case tree are indexed by. -/
def recUnionOuterE (outer : List RecUnionFrame) : MetaM Expr :=
  mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE 1)) (outer.map (·.fsE))

/-- The pointer `LeanScript.OuterSelfField` at the occurrence `sf` of the `i`-th node
    above (`0` the innermost). -/
def mkOuterSelfFieldE : List RecUnionFrame → Nat → Expr → MetaM Expr
  | f :: rest, 0, sf => do
      return mkAppN (mkConst ``LeanScript.OuterSelfField.here)
        #[f.fsE, ← recUnionOuterE rest, sf]
  | f :: rest, i + 1, sf => do
      return mkAppN (mkConst ``LeanScript.OuterSelfField.there)
        #[f.fsE, ← recUnionOuterE rest, ← mkOuterSelfFieldE rest i sf]
  | [], _, _ => throwError "`#leanscript_to_term`: internal: no node above to look into"

mutual

/-- The branches of a depth-`j` dispatch on the union, bound at `target` (a variable of
    the Lean type of the union, which each branch's shape is found for), below the nodes
    `outer` (innermost first); `descended` are the subvalues already looked into. -/
partial def recUnionCases (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (j : Nat)
    (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (outer : List RecUnionFrame)
    (descended : Array FVarId) : MetaM Expr := do
  let branches ← info.ctors.mapM fun ct =>
    recUnionBranch trans info c j top target descend answers outer descended ct
  let pre : Array Expr :=
    #[c.sg, info.l, info.bindE, c.gamma, info.τ, mkNatLit j, ← recUnionOuterE outer]
  mkRecUnionFoldKCases pre info.l branches

/-- The branch of one constructor, at depth `j`: the answer, if the Lean branch is served
    by what is known at this node, and otherwise a look into an occurrence whose history
    it reads — one of this node's (`FoldKBranch.deep`) or one of a node above
    (`FoldKBranch.deepOuter`). -/
partial def recUnionBranch (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (j : Nat)
    (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (outer : List RecUnionFrame) (descended : Array FVarId)
    (ct : RecUnionCtor) : MetaM Expr := do
  let bTys := (← listOfExpr (← reduceTy (mkApp info.bindE ct.fsE)))
  -- the Lean variables the branch binds: each field, and after each occurrence the
  -- answer at it
  -- (a field's type is read off the constructor's, at the fields before it: the index of
  -- an occurrence of an indexed family is one of them)
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  let mut fieldPos : Array Nat := #[]
  -- the positions among `decls` of the variables the branch of the language binds
  let mut bound : Array Nat := #[]
  for h : i in [0:ct.fields.size] do
    let before := fieldPos
    let tyAt : Array Expr → MetaM Expr := fun ys => ctorFieldTy ct.cty (before.map (ys[·]!))
    fieldPos := fieldPos.push decls.size
    if ct.erased.getD i false then
      decls := decls.push (Name.mkSimple s!"e{i}", tyAt)
      continue
    match ct.fields[i] with
    | some _ =>
        bound := bound.push decls.size
        decls := decls.push (Name.mkSimple s!"x{i}", tyAt)
    | none =>
        bound := bound.push decls.size
        decls := decls.push (Name.mkSimple s!"sub{i}", tyAt)
        -- (an indexed family's answer is typed at the indices of its subvalue)
        let subPos := decls.size - 1
        bound := bound.push decls.size
        let ansTy : Array Expr → MetaM Expr := fun ys =>
          if info.nI == 0 then pure info.τLean else do
            let sb := ys[subPos]!
            let st ← whnf (← inferType sb)
            let nP := info.params.size
            return info.motive0.beta (st.getAppArgs.extract nP (nP + info.nI) |>.push sb)
        decls := decls.push (Name.mkSimple s!"ans{i}", ansTy)
  unless bound.size == bTys.length do
    throwError "`#leanscript_to_term`: internal: the branch of {ct.name} binds \
      {bound.size} values, its tree {bTys.length}"
  withLocalDeclsD decls fun xs => do
    let c' := c.pushFields (bound.map (xs[·]!) |>.zip bTys.toArray |>.map fun (x, t) =>
      (x.fvarId!, t))
    -- the Lean fields, the subvalues and their answers
    let mut vals : Array Expr := #[]
    let mut subs : Array (Nat × Expr × Expr) := #[]
    let mut pos := 0
    -- (the position of a field among those the tree has: the erased ones are not there)
    let mut kept := 0
    for h : i in [0:ct.fields.size] do
      if ct.erased.getD i false then
        vals := vals.push xs[pos]!
        pos := pos + 1
        continue
      match ct.fields[i] with
      | some _ =>
          vals := vals.push xs[pos]!
          pos := pos + 1
      | none =>
          vals := vals.push xs[pos]!
          subs := subs.push (kept, xs[pos]!, xs[pos + 1]!)
          pos := pos + 2
      kept := kept + 1
    let shape := mkAppN (mkConst ct.name info.lvls) (info.params ++ vals)
    let mut descend' := descend.push (target, shape)
    -- a look into an occurrence of an indexed family (`v : Vec α n`, below a node whose
    -- field `n` is bound) fixes the fields its index is: `n` is the index of the
    -- constructor found there (`m + 1` for `cons (n := m) b w`)
    -- the index at which the constructor cannot be, if the index rules it out
    let mut impossible : Option (Expr × Expr) := none
    if info.nI != 0 && target != top.fvarId! then
      let nP := info.params.size
      let tIdx := (← whnf (resolveShape descend (← inferType (.fvar target)))).getAppArgs
        |>.extract nP (nP + info.nI)
      let sIdx := (← whnf (← inferType shape)).getAppArgs.extract nP (nP + info.nI)
      for (a, b) in tIdx.zip sIdx do
        let a := resolveShape descend' a
        -- (the declaration is read only for a variable: `a` may be a literal, `V 0`)
        let isVar ← if a.isFVar then pure !(← a.fvarId!.getDecl).isLet else pure false
        -- an index the language erases (a type: `α × β` of `fst (p : TExpr (α × β))`)
        -- does not choose the branch of the language; the tree is the same at every one
        let erasedIdx ← LeanScript.Deriving.erasedBinder (← inferType a)
        if isVar then
          descend' := descend'.push (a.fvarId!, b)
        else if erasedIdx then
          pure ()
        else unless ← isDefEq a b do
          impossible := some (a, b)
    let answers' := answers ++ subs.map fun (_, s, a) => (s, a)
    let descended' := descended.push target
    let frame : RecUnionFrame :=
      { fsE := ct.fsE, fsL := ct.fsL, subs := subs.map fun (p, s, _) => (p, s.fvarId!) }
    -- the occurrences not yet looked into: those of the nodes above (`some i`, the
    -- `i`-th innermost), outermost first, then this node's (`none`)
    let mut cands : Array (Option Nat × Nat × FVarId) := #[]
    for h : r in [0:outer.length] do
      let i := outer.length - 1 - r
      for (p, f) in outer[i]!.subs do
        unless descended'.contains f do
          cands := cands.push (some i, p, f)
    for (p, f) in frame.subs do
      cands := cands.push (none, p, f)
    let outerE ← recUnionOuterE outer
    let hereE := mkAppN (mkConst `LeanScript.FoldKBranch.here)
      #[c.sg, info.l, info.bindE, c.gamma, ct.fsE, info.τ, mkNatLit j, outerE]
    -- a constructor the index rules out (`neg : V 1` below a field of type `V 0`) is a
    -- branch of the language that a value of the Lean type never takes: it holds a
    -- default of the answer's type
    if let some (a, b) := impossible then
      let some d ← synthDefault? info.τLean
        | throwError "`#leanscript_to_term`: this recursion on the indexed family \
            {info.ind} looks into an occurrence at the index {a}, where the constructor \
            {ct.name} (of index {b}) cannot be, and the answer's type {info.τLean} has no \
            default to put in the branch of the language for it"
      let d ← whnf d
      let d := d.replace fun t => if t.isConstOf ``Nat.zero then some (mkRawNatLit 0) else none
      return mkApp hereE (← trans c' d)
    -- a look into the occurrence `cand`, whose nested dispatch is at depth `j - 1`
    let look (cand : Option Nat × Nat × FVarId) : MetaM Expr := do
      let (where_, p, f) := cand
      let inner ← recUnionCases trans info c' (j - 1) top f descend' answers'
        (frame :: outer) descended'
      let pre := #[c.sg, info.l, info.bindE, c.gamma, ct.fsE, info.τ, mkNatLit (j - 1),
        outerE]
      match where_ with
      | none =>
          let sf ← mkSelfFieldE ct.fsL p
          return mkAppN (mkConst `LeanScript.FoldKBranch.deep) (pre ++ #[sf, inner])
      | some i =>
          let sf ← mkSelfFieldE outer[i]!.fsL p
          let osf ← mkOuterSelfFieldE outer i sf
          return mkAppN (mkConst `LeanScript.FoldKBranch.deepOuter) (pre ++ #[osf, inner])
    let res ← try
        pure (Except.ok (← recUnionLeaf trans info c' top descend' answers'
          (cands.map (·.2.2))))
      catch ex => pure (Except.error ex)
    match res with
    | .ok (.inl body) => return mkApp hereE body
    | .ok (.inr needed) =>
        -- the branch reads the history below the subvalues `needed`: each of them is
        -- tried in turn as the one to look into, those of the nodes furthest up first
        -- (a branch stuck on a `match` on a sibling can mention the histories below
        -- this node's own occurrences without needing them)
        if j == 0 then
          throwError "`#leanscript_to_term`: this recursion on a recursive tagged union \
            reads the value of the function further down than the fold looks at this \
            depth"
        let mut lastEx : Option Exception := none
        for cand in cands do
          if needed.contains cand.2.2 then
            try
              return ← look cand
            catch ex' => lastEx := some ex'
        match lastEx with
        | some ex' => throw ex'
        | none => throwError "`#leanscript_to_term`: internal: no occurrence to look into"
    | .error ex =>
        -- nothing below is read, but the branch is not translated as it stands: looking
        -- into one of this node's occurrences may still expose what it takes apart
        if j == 0 then throw ex
        let mut lastEx := ex
        for cand in cands do
          if cand.1.isNone then
            try
              return ← look cand
            catch ex' => lastEx := ex'
        throw lastEx

end

/-- How deep a fold of a recursive tagged union the translation looks for: the option
    `leanscript.toTerm.maxRecUnionRecDepth` (`16` by default). -/
def maxRecUnionRecDepth : MetaM Nat :=
  return leanscript.toTerm.maxRecUnionRecDepth.get (← getOptions)

/-- A structural recursion on a **recursive tagged union**, as Lean compiled it: `X.brecOn`
    on a type whose tree is `Ty.recTaggedUnion`.  It becomes
    `LeanScript.Term.recTaggedUnion_rec' k`, at the smallest depth `k` that serves every
    branch (see the module documentation).  `none` when the recursion is not on a
    recursive tagged union. -/
def transRecUnionBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "brecOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  unless ri.numMotives == 1 do return none
  let nP := ii.numParams
  -- an indexed family's `brecOn` takes the indices before the value
  let nI := ii.numIndices
  let arity := nP + nI + 3
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let major := args[nP + 1 + nI]!
  let sty ← tyOfTerm major
  let .recTaggedUnion l _ ← tyView sty | return none
  let params := args.extract 0 nP
  let motives := args.extract nP (nP + 1)
  let brecF := args[nP + 2 + nI]!
  let m0 ← whnf motives[0]!
  unless m0.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  -- the motive may mention the indices (`Vec α n` for a map of `Vec α n`), provided the
  -- language's type of the answers does not: it is the same at every index
  let (τLean, τ) ← lambdaBoundedTelescope m0 (nI + 1) fun xs body => do
    let body ← whnf body
    let dep : MetaM Unit := throwError "`#leanscript_to_term`: {n} is used with a \
      dependent motive, which the language has no eliminator for"
    if xs.size != nI + 1 || body.containsFVar xs[nI]!.fvarId! then dep
    -- (an answer whose type *is* an index, `α` for `eval : TExpr α → α`, has no tree)
    let τ ← try instantiateMVars (← tyOfType body) catch ex =>
      if xs.any (body.containsFVar ·.fvarId!) then do dep; throw ex else throw ex
    if xs.any (τ.containsFVar ·.fvarId!) then dep
    let τLean ← if nI == 0 then pure body else
      pure (m0.beta ((← whnf (← inferType major)).getAppArgs.extract nP (nP + nI)
        |>.push major))
    return (τLean, τ)
  let selfTy ← whnf (← inferType major)
  let ilvls := selfTy.getAppFn.constLevels!
  let idxs ← schemaCtorIndices 1 l
  unless idxs.size == ii.ctors.length do
    throwError "`#leanscript_to_term`: internal: the tree of {ind} has {idxs.size} \
      constructors, the type {ii.ctors.length}"
  -- An occurrence of the type *itself* (same parameters) inside a field; `List (List α)`'s
  -- field `List α` is another type, not an occurrence.
  -- (of an indexed family, at any indices: `Vec α n` inside `Vec α (n + 1)`)
  let selfArgs := selfTy.getAppArgs.extract 0 nP
  let isSelfAt (s : Expr) : Bool :=
    s.getAppFn.isConstOf ind && s.getAppNumArgs == nP + nI &&
      s.getAppArgs.extract 0 nP == selfArgs
  let mentions (t : Expr) : Bool := (t.find? isSelfAt).isSome
  let mut ctors : Array RecUnionCtor := #[]
  for h : i in [0:ii.ctors.length] do
    let cn := ii.ctors[i]
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls) params
    let (fields, erased) ← forallTelescopeReducing cty fun xs _ => do
      let mut out : Array (Option Expr) := #[]
      let mut erased : Array Bool := #[]
      for x in xs do
        let t ← inferType x
        if nI != 0 && isSelfAt t then
          out := out.push none
          erased := erased.push false
          continue
        -- a field the language erases (the type `α` of `pair {α β : Type} …`, a proof) is
        -- a Lean variable of the branch and not a variable of the language
        if ← LeanScript.Deriving.erasedBinder t then
          out := out.push (some t)
          erased := erased.push true
          continue
        erased := erased.push false
        if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
        if ← isDefEq t selfTy then out := out.push none
        else if mentions t then
          throwError "`#leanscript_to_term`: the field of type {t} of {cn} mentions {ind} \
            other than as the type itself"
        else out := out.push (some t)
      return (out, erased)
    let fsE := idxs[i]!
    let fsL := (← listOfExpr (← reduceTy fsE)).toArray
    let nKept := (erased.filter (!·)).size
    unless fsL.size == nKept do
      throwError "`#leanscript_to_term`: internal: {cn} has {nKept} fields, its \
        tree {fsL.size}"
    ctors := ctors.push { name := cn, fields, erased, fsE, fsL, cty }
  let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
  let info : RecUnionInfo :=
    { ind, lvls := ilvls, params, selfTy, ctors, l, bindE, τLean, τ, brecF, motives, nI, motive0 := m0 }
  let .recTaggedUnion _ hwf ← tyView sty | return none
  let scrutT ← trans c major
  let attempt (k : Nat) : MetaM Expr :=
    withLocalDeclD `top selfTy fun top => do
      let cases ← recUnionCases trans info c k top top.fvarId! #[] #[] [] #[]
      return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_rec')
        #[c.sg, c.gamma, τ, l, hwf, mkNatLit k, scrutT, cases]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  let maxK ← maxRecUnionRecDepth
  for k in [0:maxK + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the recursive tagged union \
        {ind} is not the fold of a recursive tagged union at any depth up to \
        {maxK} (the option `leanscript.toTerm.maxRecUnionRecDepth`) — the fold `recTaggedUnion_rec k` gives each branch the \
        constructor's fields and the answers at its occurrences, and may look into an \
        occurrence at most `k` times, so a branch that reads the value of the function \
        further down than that has no term.  At the last depth tried: \
        {lastErr.getD m!"(no error)"}"
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
