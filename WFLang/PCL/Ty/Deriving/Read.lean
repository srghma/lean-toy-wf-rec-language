module

public meta import Lean.Elab.Command
public meta import Lean.Util.SCC
public meta import LeanScript.Ty.Class
public meta import LeanScript.Ty.WfTactic

@[expose] public section

meta section

/-!
# `deriving LeanScriptTyWf`: reading a declaration

The table of trees already built, what the handler reads off a Lean declaration, and the
dependency graph of a `mutual` block.  The handler itself is `LeanScript.Ty.Deriving`.
-/

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

/-! ## The table of trees already built -/

/-- A tree this project has already built, with the constant it was stored in and the
    theorem that it is a type. -/
structure SharedTy where
  /-- The hash of the tree, which is what the lookup is keyed on. -/
  hash : UInt64
  /-- The `def` holding the tree. -/
  declName : Name
  /-- The `theorem` that it is a type. -/
  wfName : Name
  deriving Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Every tree `deriving LeanScriptTyWf` has built, in this module and in every module it
    imports.  Sharing spans modules because this does. -/
initialize sharedTyExt : SimplePersistentEnvExtension SharedTy (Array SharedTy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.flatten }

/-- The constants holding this tree, if some declaration has already been given it. -/
def findShared? (value : Expr) : MetaM (Option (Name × Name)) := do
  let env ← getEnv
  let h := value.hash
  for e in sharedTyExt.getState env do
    if e.hash == h then
      if let some ci := env.find? e.declName then
        if ci.value? == some value then return some (e.declName, e.wfName)
  return none

/-! ## Reading a Lean declaration -/

/-- What a Lean type translates to: a tree, nothing (it carries no value), or no tree at
    all, with the reason. -/
inductive TransRes where
  /-- A tree of the language. -/
  | ok : Expr → TransRes
  /-- A type the language erases: it carries no value. -/
  | erased
  /-- No shape of the language describes it, for this reason. -/
  | no : MessageData → TransRes

/-- Is this a type the language erases — a proposition, or a one-value type? -/
def isErasedType (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  match (← whnf e).getAppFn with
  | .const n _ => return n == ``Unit || n == ``PUnit
  | _ => return false

/-- Is this binder a **type field** — a field whose value is a type?  The field itself is
    erased, since a type carries no run-time value; a later field that holds a *value of
    it* is what the handler cannot translate. -/
def isTypeField (t : Expr) : MetaM Bool := do
  let t ← whnf t
  return t.isSort && t != .sort .zero

/-- Is this binder a type field, or a *family* of them — `State : Type`, `Elem : State →
    Type`, `f : Nat → Type`?  A declaration with such a field hides a type from the
    language: a value of it is a value of a type the model does not name, which is what
    the language calls an existential, and which it does not model. -/
def isExistentialField (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ body => isTypeField body

/-- Is this a binder the translation drops — a proof, a type, an instance or a one-value
    type? -/
def erasedBinder (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if (← whnf t).isSort then return true
  if ← isErasedType t then return true
  if (← isClass? t).isSome then return true
  return false

/-- Does the free variable `x` occur in `t` anywhere but in an **index** of an occurrence of
    a declaration of the block `block` (whose declarations have `numParams` parameters)?
    The language erases the indices of an indexed family — `TExpr α` has the same tree at
    every `α` — so a type that only an index mentions is invisible to it. -/
partial def occursOutsideBlockIndices (block : List Name) (numParams : Nat) (x : FVarId) :
    Expr → Bool
  | .fvar y => y == x
  | e@(.app ..) =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const k _ =>
          if block.contains k then
            (args.extract 0 numParams).any (occursOutsideBlockIndices block numParams x)
          else args.any (occursOutsideBlockIndices block numParams x)
      | _ => occursOutsideBlockIndices block numParams x f ||
          args.any (occursOutsideBlockIndices block numParams x)
  | .forallE _ d b _ => occursOutsideBlockIndices block numParams x d ||
      occursOutsideBlockIndices block numParams x b
  | .lam _ d b _ => occursOutsideBlockIndices block numParams x d ||
      occursOutsideBlockIndices block numParams x b
  | .letE _ t v b _ => occursOutsideBlockIndices block numParams x t ||
      occursOutsideBlockIndices block numParams x v || occursOutsideBlockIndices block numParams x b
  | .mdata _ e => occursOutsideBlockIndices block numParams x e
  | .proj _ _ e => occursOutsideBlockIndices block numParams x e
  | _ => false

/-- The first field of `n` that hides a type, if it has one.  The declaration is refused
    as a whole: `LeanScript` has no existential type, so a declaration whose values carry
    a type of their own is not one it models.

    A type field that **no value of the constructor depends on** hides nothing, and is not
    an existential: the type `α` of `pair {α β : Type} (a : TExpr α) (b : TExpr β) : TExpr
    (α × β)` appears only in indices of occurrences of the declaration itself, which the
    language erases, and in the constructor's own index — so the tree of `a` is the same at
    every `α`, and the field is erased like any other type.  A type field is an existential
    when some field that carries a value (not a proof, a type or an instance) mentions it
    outside such an index: `seed : State`, `x : α`, `xs : List α`.  A field that is a
    *family* of types (`f : Nat → Type`) is always one. -/
def existentialField? (n : Name) (params : Array Expr) : MetaM (Option Name) := do
  let some (.inductInfo ind) := (← getEnv).find? n | return none
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let cty ← instantiateForall ci.type (params.extract 0 ind.numParams)
    let hit? ← forallTelescopeReducing cty fun xs _ => do
      for i in [0:xs.size] do
        let x := xs[i]!
        if ← isExistentialField (← inferType x) then
          -- a family of types (`f : Nat → Type`) is not erased: it hides types whatever
          -- depends on it
          let mut hides := !(← isTypeField (← inferType x))
          for y in xs[i+1:] do
            if hides then break
            let t ← instantiateMVars (← inferType y)
            if ← erasedBinder t then continue
            if occursOutsideBlockIndices ind.all ind.numParams x.fvarId! t then
              hides := true
              break
          if hides then return some (← x.fvarId!.getUserName)
      return none
    if let some f := hit? then return some f
  return none

/-- The types of the values the declaration `n` **caches** — a `@[computed_field]` is
    stored in the runtime object, so it is one more field of it — in declaration order.

    Lean records a computed field by building a second inductive, `n._impl`, whose
    constructors carry the cached values ahead of the fields, so the types are read off a
    constructor that has a field.  A declaration all of whose constructors are field-less
    stores its cached values nowhere — they are a function of the constructor number —
    and the types are read off the `@[computed_field]` functions instead. -/
def computedFieldTys (n : Name) : MetaM (Except MessageData (List Expr)) := do
  let env ← getEnv
  if (env.find? (n ++ `_impl)).isNone then return .ok []
  let some (.inductInfo ind) := env.find? n | return .ok []
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    if ci.numFields == 0 then continue
    let some (.ctorInfo cimpl) := env.find? (c ++ `_impl)
      | return .error m!"`{n}` caches values in a way this handler cannot read"
    let k := cimpl.numFields - ci.numFields
    if k == 0 then return .ok []
    return ← forallTelescopeReducing cimpl.type fun xs _ => do
      let mut tys : List Expr := []
      for x in xs[ind.numParams:ind.numParams + k] do
        tys := tys ++ [← inferType x]
      return .ok tys
  -- every constructor is field-less: the cached value is a function of the constructor
  -- number and is stored nowhere, so its type is read off the function that computes it.
  -- Lean gives every computed field `f` of `n` a companion `n.f._override`.
  let mut fields : Array (Nat × Name × Expr) := #[]
  for (m, _) in env.constants.toList do
    let .str base "_override" := m | continue
    unless n.isPrefixOf base && base != n do continue
    if ind.ctors.contains base then continue
    if base == n ++ `casesOn || base == n ++ `rec || base == n ++ `recOn then continue
    let some ci := env.find? base | continue
    let res ← forallTelescopeReducing ci.type fun _ body => whnf body
    if res.hasLooseBVars || res.hasFVar then
      return .error m!"`{n}` caches a value whose type this handler cannot read"
    let line := (← findDeclarationRanges? base).map (·.range.pos.line) |>.getD 0
    fields := fields.push (line, base, res)
  let sorted := fields.qsort fun a b =>
    if a.1 == b.1 then Name.lt a.2.1 b.2.1 else a.1 < b.1
  return .ok (sorted.toList.map (·.2.2))

/-! ## The dependency graph of a `mutual` block

Lean's `mutual` blocks are not always *families*: a block whose members do not each reach
the others is several declarations that happen to be written together, and each of its
strongly connected components can be declared on its own, in dependency order. -/

/-- Which members of the block `names` the member `m` mentions in the types of the fields
    it keeps. -/
def blockDeps (names : List Name) (params : Array Expr) (m : Name) :
    MetaM (Except MessageData (List Name)) := do
  let some (.inductInfo mind) := (← getEnv).find? m
    | return .error m!"`{m}` is not an inductive declaration"
  let mut deps : List Name := []
  for c in mind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (params.extract 0 mind.numParams)
    let ds ← forallTelescopeReducing cty fun xs _ => do
      let mut ds : List Name := []
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        for k in t.getUsedConstants do
          if names.contains k && !ds.contains k then ds := ds ++ [k]
      return ds
    for d in ds do
      if !deps.contains d then deps := deps ++ [d]
  return .ok deps

/-- The members of the block `names` that belong to the same strongly connected component
    as `n` in the graph `edges` (core's `Lean.SCC.scc`), in declaration order. -/
def blockComponent (names : List Name) (edges : List (Name × List Name)) (n : Name) :
    List Name :=
  let succs (m : Name) : List Name := ((edges.find? (·.1 == m)).map (·.2)).getD []
  let comp := ((Lean.SCC.scc names succs).find? (·.contains n)).getD [n]
  names.filter comp.contains

end LeanScript.Deriving

end

end
