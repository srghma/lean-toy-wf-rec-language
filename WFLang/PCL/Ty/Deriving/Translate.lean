module

public meta import Lean.Meta.Tactic.Delta
public meta import LeanScript.Ty.Deriving.Build

@[expose] public section

meta section

/-!
# `deriving LeanScriptTyWf`: translating a declaration

Hoisting a recursive wrapper into a member of a family, and the translation of a
declaration's type into its tree.
-/

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

/-! ## Hoisting a recursive wrapper into a member of a family

A field of type `List T`, where `T` is the declaration being defined, cannot be modelled
by `List`'s tree with the occurrence in the place of the argument: the occurrence would
land inside `List`'s *own* binder and would denote the list.  But the declaration is
still a type of the language, because a nested recursion is a mutual one — which is what
Lean itself does with a nested inductive.  `inductive RoseList | node : List RoseList →
RoseList` is the family

```text
member 0 = RoseList = member 1                 -- the declaration
member 1 = nil | cons (_ : member 0) (_ : member 1)   -- the list of them
```

So the binder that would have captured the occurrence is *hoisted*: it becomes one more
member of the family the declaration is translated in, its own `Ty.self` becomes an
occurrence of that member, and the occurrence it holds becomes an occurrence of the
declaration.  Nothing about the wrapper is re-read from Lean — the tree that is taken
apart is the wrapper's own model, from its instance — and a wrapper nested in a wrapper
(`List (List T)`) adds one member per binder on the path to the occurrence.

When the declaration is alone in its block it becomes member `0` of the new family, so
every `Ty.self` in the trees of its own fields becomes `Ty.familyMember 0`; that is
`selfToMember`. -/

/-- Does this tree mention one of the stand-in parameters? -/
def mentionsHole (holes : Array Expr) (e : Expr) : Bool :=
  holes.any fun h => e.containsFVar h.fvarId!

/-- An occurrence of member `i`, as an expression. -/
def familyMemberE (i : Nat) : Expr :=
  mkApp (mkConst ``LeanScript.Ty.familyMember) (mkNatLit i)

/-- Replace every `Ty.self` written in *this* scope — one that does not stand under a
    binder of its own — by `Ty.familyMember i`.  This is what turns the trees of a lone
    declaration's fields into the trees of member `i` of a family. -/
partial def selfToMember (i : Nat) (e : Expr) : Expr :=
  if e.isConstOf ``LeanScript.Ty.self then familyMemberE i
  else if isBinderCtor e then e
  else
    match e with
    | .app f a => .app (selfToMember i f) (selfToMember i a)
    | .lam n t b bi => .lam n (selfToMember i t) (selfToMember i b) bi
    | .forallE n t b bi => .forallE n (selfToMember i t) (selfToMember i b) bi
    | .mdata d b => .mdata d (selfToMember i b)
    | .proj s k b => .proj s k (selfToMember i b)
    | e => e

mutual

/-- The tree of the wrapper's model `e`, written in the scope of the family the
    declaration is being translated in: a stand-in parameter becomes the tree of what
    stands there, a `Ty.self` of the binder being hoisted becomes `selfIdx`, and a binder
    that holds a stand-in is hoisted into a member of its own.  `none` when the model
    holds a shape this cannot hoist. -/
partial def hoistTree (ctx : Ctx) (holes trees : Array Expr) (selfIdx : Option Nat)
    (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if let some k := holes.idxOf? α then
      -- the argument's tree is written in the declaration's own scope, and the
      -- declaration is member `0` of the family being built
      return some (selfToMember 0 trees[k]!)
  if e.isConstOf ``LeanScript.Ty.self then
    match selfIdx with
    | some i => return some (familyMemberE i)
    | none => return none
  if isBinderCtor e then
    -- a binder that holds no stand-in is a closed subtree and is kept as it is
    if !mentionsHole holes e then return some e
    return ← hoistBinder ctx holes trees e
  match e with
  | .app .. =>
      let mut out := e.getAppFn
      for a in e.getAppArgs do
        let some a' ← hoistTree ctx holes trees selfIdx a | return none
        out := mkApp out a'
      return some out
  | .lam n t b i => do
      let some t' ← hoistTree ctx holes trees selfIdx t | return none
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.lam n t' b' i)
  | .forallE n t b i => do
      let some t' ← hoistTree ctx holes trees selfIdx t | return none
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.forallE n t' b' i)
  | .mdata d b => do
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.mdata d b')
  | .proj s i b => do
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.proj s i b')
  | _ => return some e

/-- Hoist the binder `e`, which holds a stand-in, into a member of the family: the member
    is numbered next, its payload is the binder's payload with the binder's own `Ty.self`
    reading as that member, and the answer is an occurrence of it. -/
partial def hoistBinder (ctx : Ctx) (holes trees : Array Expr) (e : Expr) :
    MetaM (Option Expr) := do
  let k := ctx.baseCount + (← ctx.extra.get).size
  -- the member's number is taken before its payload is converted, so that a binder
  -- nested inside it gets the next one
  ctx.extra.modify (·.push (mkConst ``LeanScript.Ty.self))
  let asMember (ctor : Name) (payload : Expr) : MetaM (Option Expr) := do
    let some p ← hoistTree ctx holes trees (some k) payload | return none
    return some (← mkAppM ctor #[p])
  let member? ←
    match e.getAppFnArgs with
    | (``LeanScript.Ty.recAlias, #[b]) =>
        asMember ``LeanScript.LeanFamMemberSchema.alias b
    | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
        asMember ``LeanScript.LeanFamMemberSchema.ctors l
    | (``LeanScript.Ty.recObject, #[fs]) =>
        asMember ``LeanScript.LeanFamMemberSchema.record fs
    | _ => pure none
  let some member := member? | return none
  ctx.extra.modify (·.set! (k - ctx.baseCount) member)
  return some (familyMemberE k)

end

instance : Inhabited TransRes := ⟨.erased⟩

/-- Run `k` on the model of `fn args` with the arguments at `idxs` replaced by fresh
    stand-in types `hole0, hole1, …`, each with a `LeanScriptTyWf` instance in scope.  `k`
    gets the stand-ins, the instantiated type `fn args'`, and its tree — with the list
    schema (`Ty.listSchema`, which `List`'s model is written with) unfolded, so that a
    binder's payload is visible — or `none` when that type has no `LeanScriptTyWf`
    instance. -/
def withStandInModel {α : Type} [Inhabited α] (fn : Expr) (args : Array Expr) (idxs : Array Nat)
    (k : Array Expr → Expr → Option Expr → MetaM α) : MetaM α := do
  let holeDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    idxs.mapIdx fun i _ =>
      (Name.mkSimple s!"hole{i}", BinderInfo.default,
        fun _ => pure (mkSort (Level.succ Level.zero)))
  withLocalDecls holeDecls fun holes => do
    let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      holes.mapIdx fun i h =>
        (Name.mkSimple s!"holeInst{i}", BinderInfo.instImplicit,
          fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[h])
    withLocalDecls instDecls fun _ => do
      let mut args' := args
      for i in [0:idxs.size] do
        args' := args'.set! idxs[i]! holes[i]!
      let e' := mkAppN fn args'
      let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[e'])
        | k holes e' none
      let tree ← deltaExpand (← whnf (← mkAppOptM ``LeanScript.tyOf #[some e', some inst]))
        (· == ``LeanScript.Ty.listSchema)
      k holes e' (some tree)

mutual

/-- The tree that models the Lean type `e`.

    A type that is **not** the declaration being defined is not read: its instance is, and
    the leaf is that instance's `tyWfOf`.  That is what stops a declaration from being
    translated once per mention of it. -/
partial def tyWfOfType (ctx : Ctx) (e : Expr) : MetaM TransRes := do
  if ← isProp e then return .erased
  let e ← whnf e
  if e.isSort then return .no m!"a type or a proposition, which carries no value"
  if ← isErasedType e then return .erased
  -- a type that *contains* the declaration being defined cannot come from an instance:
  -- an instance's tree is closed, and this one has to hold an occurrence.  The type
  -- formers the language has a shape of its own for are followed into; anything else is
  -- refused, and named in the message.
  let mentionsMember :=
    e.getUsedConstants.any fun c => ctx.members.contains c
  if mentionsMember && !ctx.auxTys.isEmpty then
    -- every auxiliary type of the block is a member of the family: this one is
    -- member `baseCount + j`
    let mut j? : Option Nat := none
    for h : j in [0:ctx.auxTys.size] do
      if j?.isNone then
        if ← withNewMCtxDepth (isDefEq e ctx.auxTys[j]) then j? := some j
    if let some j := j? then
      return ← hoistAux ctx e j
  if mentionsMember then
    if e.isForall then
      return ← forallTelescopeReducing e fun xs body => do
        let mut doms : List Expr := []
        for x in xs do
          let d ← inferType x
          if ← erasedBinder d then continue
          match ← tyWfOfType ctx d with
          | .ok a => doms := doms ++ [a]
          | .erased => pure ()
          | .no r => return .no r
        match ← tyWfOfType ctx body with
        | .ok r => return .ok (← doms.foldrM (fun a b => mkAppM ``LeanScript.Ty.fn #[a, b]) r)
        | .erased => return .no m!"a function answering with a type that carries no value"
        | .no r => return .no r
    let args := e.getAppArgs
    if let .const c _ := e.getAppFn then
      if (c == ``Array || c == ``Thunk) && args.size == 1 then
        match ← tyWfOfType ctx args[0]! with
        | .ok a =>
            return .ok (← mkAppM
              (if c == ``Array then ``LeanScript.Ty.array else ``LeanScript.Ty.thunk) #[a])
        | .erased => return .no m!"`{c}` of a type that carries no value"
        | .no r => return .no r
  if let .const m _ := e.getAppFn then
    if let some i := ctx.members.idxOf? m then
      let args := e.getAppArgs
      if args.size ≥ ctx.params.size && args.extract 0 ctx.params.size == ctx.params then
        if ctx.members.size == 1 then
          return .ok (mkConst ``LeanScript.Ty.self)
        else
          return .ok (mkApp (mkConst ``LeanScript.Ty.familyMember) (mkNatLit i))
      else
        return .no m!"`{m}` at other arguments than its own is not a type this handler \
          can name here"
  if mentionsMember then
    -- a type former the language has no shape of its own for: the occurrence goes into
    -- the former's own model, and a binder of it that would capture the occurrence is
    -- hoisted into a member of a family
    if let some res ← tyWfOfWrapper ctx e then return res
    return .no (← addMessageContext
      m!"`{e}` mentions the declaration being defined through a type this handler cannot \
        recurse through: the occurrence goes where the argument's tree would stand in \
        the type former's own model (`Array`, `Thunk`, `Option`, `×`, `⊕`, a function \
        type, any non-recursive wrapper), and a binder that would capture it there is \
        hoisted into a member of a family (`List`, any recursive wrapper) — but the model \
        of this one is a mutual family, or does not hold the argument as one tree")
  match ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[e]) with
  | .some inst =>
      return .ok (← mkAppOptM ``LeanScript.tyOf #[some e, some inst])
  | _ =>
      return .no (← addMessageContext
        m!"`{e}` has no `LeanScriptTyWf` instance; derive or write one for it first")

/-- The auxiliary type `e` of the block, `ctx.auxTys[j]`, as member `baseCount + j` of the
    family: the wrapper's own model at stand-in parameters, its own `Ty.self` (if it is a
    binder) reading as that member and the stand-ins as the trees of what stands there.
    The member is built once; later occurrences are occurrences of it. -/
partial def hoistAux (ctx : Ctx) (e : Expr) (j : Nat) : MetaM TransRes := do
  let idx := ctx.baseCount + j
  let occ := familyMemberE idx
  -- already built, or being built (an occurrence inside its own payload)
  if !(((← ctx.extra.get)[j]?).getD (mkConst ``Unit)).isConstOf ``Unit then
    return .ok occ
  ctx.extra.modify (·.set! j (mkConst ``LeanScript.Ty.self))
  let fail (r : MessageData) : MetaM TransRes := return .no (← addMessageContext
    m!"`{e}`, an auxiliary type of the nested block, cannot be a member of its family: {r}")
  let fn := e.getAppFn
  let args := e.getAppArgs
  let mut idxs : Array Nat := #[]
  for i in [0:args.size] do
    if args[i]!.getUsedConstants.any (ctx.members.contains ·) then idxs := idxs.push i
  let mut trees : Array Expr := #[]
  for i in idxs do
    unless ← isTypeField (← inferType args[i]!) do return ← fail m!"an argument is not a type"
    match ← tyWfOfType ctx args[i]! with
    | .ok a => trees := trees.push (if ctx.members.size == 1 then selfToMember 0 a else a)
    | .erased => return ← fail m!"it holds a type that carries no value"
    | .no r => return .no r
  withStandInModel fn args idxs fun holes e' tree? => do
    let some tree := tree?
      | return ← fail m!"`{e'}` has no `LeanScriptTyWf` instance"
    -- the member's kind and payload, read off the wrapper's model
    let shapeOf (t : Expr) : Option (Name × Expr) :=
      match t.getAppFnArgs with
      | (``LeanScript.Ty.recTaggedUnion, #[l]) => some (``LeanScript.LeanFamMemberSchema.ctors, l)
      | (``LeanScript.Ty.recObject, #[fs]) => some (``LeanScript.LeanFamMemberSchema.record, fs)
      | (``LeanScript.Ty.recAlias, #[b]) => some (``LeanScript.LeanFamMemberSchema.alias, b)
      | (``LeanScript.Ty.shape, #[s]) =>
          match s.getAppFnArgs with
          | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
              some (``LeanScript.LeanFamMemberSchema.ctors, l)
          | (``LeanScript.TyShape.record, #[_, fs]) =>
              some (``LeanScript.LeanFamMemberSchema.record, fs)
          | _ => none
      | _ => none
    let some (kind, payload) := shapeOf tree
      | return ← fail m!"its model is not a union, a record, a newtype or a recursive one"
    -- the binder's own `Ty.self` is this member; the stand-ins are what stands there
    let payload := selfToMember idx payload
    -- a leaf that models another type built from a stand-in (`tyOf (List hole)`, in
    -- the model of a structure with a field `List α`) is that type's own member
    let back := fun (x : Expr) => x.replaceFVars holes (idxs.map (args[·]!))
    let some payload ← expandHoleLeaves ctx holes back false payload
      | return ← fail m!"a field of the wrapper's model has no tree"
    let some p ← substHoles holes trees false payload
      | return ← fail m!"an argument stands under a binder of the wrapper's own model"
    if holes.any (fun h => p.containsFVar h.fvarId!) then
      return ← fail m!"the wrapper's model does not hold an argument as one tree"
    let member ← mkAppM kind #[p]
    ctx.extra.modify (·.set! j member)
    return .ok occ

/-- In the model `e` of a type former asked for at stand-in parameters, replace each leaf
    that is the model of a type which mentions a stand-in without being one (`tyOf (Option
    hole)`) by the tree of that type at the real arguments (`back` puts them back).  Such a
    leaf is only expanded outside the model's own binders, where an occurrence of the
    declaration keeps its meaning; under one it is left, and refused later.  `none` when
    the type has no tree. -/
partial def expandHoleLeaves (ctx : Ctx) (holes : Array Expr) (back : Expr → Expr)
    (underBinder : Bool) (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if holes.contains α then return some e
    if mentionsHole holes α then
      if underBinder then return some e
      match ← tyWfOfType ctx (back α) with
      | .ok t => return some t
      | _ => return none
    return some e
  match e with
  | .app .. =>
      let under := underBinder || isBinderCtor e
      let mut out := e.getAppFn
      for a in e.getAppArgs do
        let some a' ← expandHoleLeaves ctx holes back under a | return none
        out := mkApp out a'
      return some out
  | .mdata d b => do
      let some b' ← expandHoleLeaves ctx holes back underBinder b | return none
      return some (.mdata d b')
  | _ => return some e

/-- The tree of a type former applied to the declaration being defined: the former's own
    instance, asked for at a stand-in parameter, with the stand-in's leaf replaced by the
    tree of what stands there.  `none` when the former has no instance, when one of the
    arguments is not a type, or when the occurrence would be captured by a binder of the
    former's own model. -/
partial def tyWfOfWrapper (ctx : Ctx) (e : Expr) : MetaM (Option TransRes) := do
  let fn := e.getAppFn
  unless fn.isConst do return none
  let args := e.getAppArgs
  -- the arguments that mention the declaration being defined; the others keep their own
  -- instances, so nothing about them is re-read
  let mut idxs : Array Nat := #[]
  for i in [0:args.size] do
    if args[i]!.getUsedConstants.any (ctx.members.contains ·) then idxs := idxs.push i
  if idxs.isEmpty then return none
  let mut trees : Array Expr := #[]
  for i in idxs do
    unless ← isTypeField (← inferType args[i]!) do return none
    match ← tyWfOfType ctx args[i]! with
    | .ok a => trees := trees.push a
    | .erased => return some (.no m!"`{e}` holds a type that carries no value")
    | .no r => return some (.no r)
  withStandInModel fn args idxs fun holes _ tree? => do
    let some tree := tree? | return none
    -- the occurrence goes where the stand-in is; if it would land inside a binder of
    -- the former's own model, that binder is hoisted into a member of a family instead
    -- a leaf of the former's model that is the model of *another* type built from a
    -- stand-in (`tyOf (Option hole)`, in the model of a structure `Cell α` with a field
    -- `Option α`) is translated in its own right, at the argument that stands there
    let back := fun (x : Expr) => x.replaceFVars holes (idxs.map (args[·]!))
    let some tree ← expandHoleLeaves ctx holes back false tree | return none
    let out? ←
      match ← substHoles holes trees false tree with
      | some out => pure (some out)
      | none => hoistTree ctx holes trees none tree
    let some out := out? | return none
    -- nothing of the stand-ins may be left: an argument that the former's model does
    -- not use as one tree is one this handler cannot put an occurrence into
    if holes.any (fun h => out.containsFVar h.fvarId!) then return none
    return some (.ok out)

end

/-- The field types of each constructor of `ind`, in declaration order, with the erased
    fields dropped and the rest translated. -/
def translateCtors (ctx : Ctx) (ind : InductiveVal) :
    MetaM (Except MessageData (List (List Expr))) := do
  let mut ctors : List (List Expr) := []
  for c in ind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (ctx.params.extract 0 ind.numParams)
    let fields : Except MessageData (List Expr) ← forallTelescopeReducing cty fun xs _ => do
      let mut fs : List Expr := []
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        match ← tyWfOfType ctx t with
        | .ok a => fs := fs ++ [a]
        | .erased => pure ()
        | .no r => return .error r
      return .ok fs
    match fields with
    | .error r => return .error r
    | .ok fs => ctors := ctors ++ [fs]
  return .ok ctors

/-- The shape of `n` followed by the values it caches, which are ordinary fields of a
    record.  A declaration that caches values *is* that record, so an occurrence of the
    declaration inside its own shape denotes the record and the binder is the record. -/
def withComputedFields (n : Name) (isRec : Bool) (base : TransRes) : MetaM TransRes := do
  match base with
  | .no r => return .no r
  | _ =>
    match ← computedFieldTys n with
    | .error r => return .no r
    | .ok [] => return base
    | .ok ctys =>
      let mut cached : List Expr := []
      let closed : Ctx := { members := #[], params := #[], extra := ← IO.mkRef #[] }
      for t in ctys do
        match ← tyWfOfType closed t with
        | .ok a => cached := cached ++ [a]
        | .erased => pure ()
        | .no r => return .no r
      let fields := (match base with | .ok a => [a] | _ => []) ++ cached
      match fields with
      | [] => return .erased
      | [a] => return .ok a
      | fs =>
        match ← mkRecord? fs with
        | none => return .no m!"`{n}` caches values this handler cannot lay out"
        | some sch =>
            return .ok (← mkAppM
              (if isRec then ``LeanScript.Ty.recObject else ``LeanScript.Ty.record) #[sch])

/-- The tree of the declaration `n`, translated at the parameters `params`. -/
def treeOfDecl (n : Name) (ind : InductiveVal) (params : Array Expr) : MetaM TransRes := do
  -- which members of `n`'s `mutual` block are a family with it
  let members : Array Name ←
    if ind.all.length ≤ 1 then pure #[n]
    else do
      let mut edges : List (Name × List Name) := []
      for m in ind.all do
        match ← blockDeps ind.all params m with
        | .error r => return .no r
        | .ok ds => edges := edges ++ [(m, ds)]
      let comp := blockComponent ind.all edges n
      pure (if comp.length ≤ 1 then #[n] else comp.toArray)
  -- every auxiliary type of a nested block is hoisted into a member, in the order of the
  -- recursor's motives, when the block is a family anyway and one of them is the type of
  -- a non-recursive wrapper (`Option Q` inside `P`): otherwise that wrapper's occurrence
  -- would stand inside its shape, with no member, and the family would not be the one
  -- the recursor folds.  (`Array` and `Thunk` keep their own shapes.)
  let auxs ← nestedAuxTypes ind params
  let auxOk ← auxs.allM fun d => do
    let .const h _ := d.getAppFn | return false
    if h == ``Array || h == ``Thunk then return false
    return ((← getEnv).find? h) matches some (.inductInfo _)
  let auxRec ← auxs.anyM fun d => do
    let .const h _ := d.getAppFn | return false
    let some (.inductInfo hi) := (← getEnv).find? h | return false
    return hi.isRec
  let auxPlain := auxs.size > 0 && !(← auxs.allM fun d => do
    let .const h _ := d.getAppFn | return false
    let some (.inductInfo hi) := (← getEnv).find? h | return false
    return hi.isRec)
  let hoistAll := auxOk && auxPlain && members.size == ind.all.length &&
    (members.size > 1 || auxRec)
  let extra ← IO.mkRef (if hoistAll then Array.replicate auxs.size (Lean.mkConst ``Unit)
    else (#[] : Array Expr))
  let ctx : Ctx :=
    { members, params, baseCount := if members.size ≤ 1 then 1 else members.size, extra,
      auxTys := if hoistAll then auxs else #[] }
  if members.size ≤ 1 then
    match ← translateCtors ctx ind with
    | .error r => return .no r
    | .ok ctors =>
        let isRec := ctors.any (·.any mentionsScope)
        -- a wrapper was hoisted: the declaration is member `0` of a family whose other
        -- members are the binders the recursion passes through
        if let hoisted@(_ :: _) := (← extra.get).toList then
          match ← computedFieldTys n with
          | .error r => return .no r
          | .ok (_ :: _) =>
              return .no m!"`{n}` recurses through a type whose own model is recursive \
                and caches values, which this handler has no layout for"
          | .ok [] =>
            let ctors := ctors.map (·.map (selfToMember 0))
            match ← assembleFamMember n ctors with
            | .error r => return .no r
            | .ok m0 =>
              match ← mkFamily? (m0 :: hoisted) 0 with
              | none => return .no m!"`{n}` recurses through a type this handler cannot \
                  lay out as a family"
              | some fam =>
                  return .ok (← mkAppM ``LeanScript.Ty.mutualRecursiveFamily #[fam])
        match ← computedFieldTys n with
        | .error r => return .no r
        | .ok [] => return ← assembleShape n ctors
        | .ok _ =>
            -- the cached values are fields of the record the declaration is, and the
            -- shape is one more field of it
            match ← assembleShape n ctors with
            | .no r => return .no r
            | .erased => return ← withComputedFields n false .erased
            | .ok shape =>
                -- the shape must not be its own binder: the binder is the record
                let bare ← if isRec then stripBinder shape else pure shape
                return ← withComputedFields n isRec (.ok bare)
  else
    let mut memberExprs : List Expr := []
    for m in members do
      let some (.inductInfo mind) := (← getEnv).find? m
        | return .no m!"`{m}` is not an inductive declaration"
      match ← translateCtors ctx mind with
      | .error r => return .no r
      | .ok ctors =>
        match ← computedFieldTys m with
        | .error r => return .no r
        | .ok [] =>
            match ← assembleFamMember m ctors with
            | .error r => return .no r
            | .ok sch => memberExprs := memberExprs ++ [sch]
        | .ok _ =>
            return .no m!"`{m}` is a member of a mutual family and caches values, which \
              this handler has no layout for"
    let some i := members.idxOf? n | return .no m!"`{n}` is not a member of its own block"
    -- the members hoisted out of a recursive wrapper follow the declared ones
    memberExprs := memberExprs ++ (← extra.get).toList
    match ← mkFamily? memberExprs i with
    | none => return .no m!"`{n}` is a mutual block of fewer than two members"
    | some fam => return .ok (← mkAppM ``LeanScript.Ty.mutualRecursiveFamily #[fam])
where
  /-- The payload of a recursive binder, which a declaration that caches values wraps in
      a record instead. -/
  stripBinder (e : Expr) : MetaM Expr := do
    match e.getAppFnArgs with
    | (``LeanScript.Ty.recTaggedUnion, #[l]) => mkAppM ``LeanScript.Ty.taggedUnion #[l]
    | (``LeanScript.Ty.recObject, #[fs]) => mkAppM ``LeanScript.Ty.record #[fs]
    | (``LeanScript.Ty.recAlias, #[b]) => return b
    | _ => return e

end LeanScript.Deriving

end

end
