module

public meta import LeanScript.CtorFn.FieldTy

@[expose] public section

/-!
# `#leanscript_ctor`: reading the datatype

Which fields of a constructor are types, how the datatype is laid out (one type for all its
constructors, or one layout per constructor), and the built-in model of a datatype.
-/

meta section

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType? mkTyList
  mkTaggedUnion?)

/-- How a datatype is laid out: one type for all constructors, or one layout per
    constructor. -/
structure Classified where
  /-- Every type field of every constructor is a type index of its result. -/
  whole : Bool
  /-- For each constructor, for each field: the type index it is, if it is one. -/
  idxMaps : Array (Array (Option Nat))
  /-- The name a constructor gives each type index, if one does. -/
  idxNames : Array (Option Name)

/-- Classify the constructors of `ind`, at the parameters `params`. -/
def classify (ind : InductiveVal) (params : Array Expr) (typeIdx : Array Bool) :
    MetaM Classified := do
  let mut whole := true
  let mut maps : Array (Array (Option Nat)) := #[]
  let mut names : Array (Option Name) := typeIdx.map fun _ => none
  for d in ind.ctors do
    let di ← getConstInfoCtor d
    let cty ← instantiateForall di.type params
    let (m, ok, ns) ← forallBoundedTelescope cty di.numFields fun xs r => do
      let rArgs := r.getAppArgs.extract ind.numParams r.getAppArgs.size
      let mut m : Array (Option Nat) := #[]
      let mut ok := true
      let mut ns : Array (Nat × Name) := #[]
      for x in xs do
        let t ← inferType x
        if ← isExistentialField t then
          unless ← isTypeField t do
            throwError "`#leanscript_ctor`: the type `{ind.name}` hides a family of types \
              in the field `{← x.fvarId!.getUserName}` of `{d}`, which the language has no \
              shape for"
          match (List.range rArgs.size).find? (fun k => rArgs[k]! == x && typeIdx[k]!) with
          | some k => m := m.push (some k); ns := ns.push (k, ← x.fvarId!.getUserName)
          | none => m := m.push none; ok := false
        else m := m.push none
      -- every type index must be a type field, and no two the same one
      let mut seen : Array Expr := #[]
      for k in [0:rArgs.size] do
        if typeIdx[k]! then
          let a := rArgs[k]!
          unless a.isFVar && xs.contains a && !seen.contains a do ok := false
          seen := seen.push a
      return (m, ok, ns)
    whole := whole && ok
    maps := maps.push m
    for (k, n) in ns do
      if names[k]!.isNone && !n.hasMacroScopes then names := names.set! k (some n)
  return { whole, idxMaps := maps, idxNames := names }

/-- The type variables of the constructor function of `ci` at an application of `ci` to
    `args` (its parameters and at least all its fields): the Lean types they stand for, in
    the order the function takes them — the parameters, then the type indices of the result
    (a datatype without existentials) or the type fields of the constructor (one with
    existentials). -/
def tyVarValues (ci : ConstructorVal) (args : Array Expr) : MetaM (Array Expr) := do
  let ind ← getConstInfoInduct ci.induct
  let params := args.extract 0 ci.numParams
  let (whole, typeIdx) ← forallBoundedTelescope ind.type ind.numParams fun ps indBody =>
    forallTelescopeReducing indBody fun idxs _ => do
      let typeIdx ← idxs.mapM fun x => do isTypeField (← inferType x)
      return ((← classify ind ps typeIdx).whole, typeIdx)
  let mut out := params
  if whole then
    let resTy ← whnf (← instantiateForall ci.type (args.extract 0 (ci.numParams + ci.numFields)))
    let idxArgs := resTy.getAppArgs.extract ind.numParams resTy.getAppArgs.size
    for k in [0:idxArgs.size] do
      if typeIdx.getD k false then out := out.push idxArgs[k]!
  else
    let mut t ← instantiateForall ci.type params
    for i in [0:ci.numFields] do
      let .forallE _ d b _ ← whnf t
        | throwError "`#leanscript_ctor`: the constructor `{ci.name}` has fewer fields than \
            its declaration says"
      let a := args[ci.numParams + i]!
      if ← isTypeField d then out := out.push a
      t := b.instantiate1 a
  return out

/-- Walk the fields of the constructor `di` at `params`, a field that is type index `i`
    becoming `idxVars[i]`, and run `k` on the others. -/
def withCtorFields {α : Type} (di : ConstructorVal) (params idxVars : Array Expr)
    (m : Array (Option Nat)) (k : Array Expr → MetaM α) : MetaM α := do
  go (← instantiateForall di.type params) m.toList #[]
where
  /-- One binder at a time. -/
  go (t : Expr) : List (Option Nat) → Array Expr → MetaM α
    | [], acc => k acc
    | mi :: rest, acc => do
      let t ← whnf t
      let .forallE n d b bi := t
        | throwError "`#leanscript_ctor`: the constructor `{di.name}` has fewer fields than \
            its declaration says"
      match mi with
      | some i => go (b.instantiate1 idxVars[i]!) rest acc
      | none => withLocalDecl n bi d fun x => go (b.instantiate1 x) rest (acc.push x)

/-- The layout of a datatype's values, or of one constructor's. -/
inductive Shape where
  /-- One field: the value is that field. -/
  | newtype
  /-- A record, from this schema. -/
  | record (sch : Expr)
  /-- A tagged union, from this schema. -/
  | union (l : Expr)
  /-- An enum, from this schema. -/
  | enum (s : Expr)
  /-- `Bool`. -/
  | bool

/-- The layout of one constructor's fields. -/
def singleShape (what : MessageData) (fs : Array Expr) : MetaM (Shape × Expr) := do
  match fs.toList with
  | [] => throwError "`#leanscript_ctor`: {what} carries no value — a unit-like type has no \
      constructor function"
  | [a] => return (.newtype, a)
  | a :: b :: rest =>
      let sch ← mkAppM ``LeanScript.LeanRecordSchema.mk #[a, b, ← mkTyList rest tyWfE]
      return (.record sch, mkApp (mkConst ``LeanScript.TyWf.record) sch)

/-- The layout of a datatype with these constructors. -/
def wholeShape (name : Name) (enumOverride : Option Expr) (cls : Array (Array Expr)) :
    MetaM (Shape × Expr) := do
  if h : cls.size = 1 then
    return ← singleShape m!"the only constructor of `{name}`" cls[0]
  if cls.all (·.isEmpty) then
    if cls.size == 2 then
      return (.bool, mkApp (mkConst ``LeanScript.TyWf.prim) (mkConst ``LeanScript.LeanPrimTy.bool))
    let s ← match enumOverride with
      | some s => pure s
      | none => mkAppM ``LeanScript.LeanEnumSchema.mk #[mkNatLit (cls.size - 3), toExpr (0 : Int)]
    return (.enum s, mkApp (mkConst ``LeanScript.TyWf.enum) s)
  let some l ← mkTaggedUnion? (cls.toList.map (·.toList)) tyWfE | throwError "`#leanscript_ctor`: `{name}` has no tagged-union layout"
  return (.union l, mkApp (mkConst ``LeanScript.TyWf.taggedUnion) l)

/-- Refuse a datatype whose model is a terminal type or a built-in type former, and read off
    the numbering of an enum whose instance chooses its own. -/
def builtinModel (ind : InductiveVal) (params : Array Expr) : MetaM (Option Expr) := do
  if ind.numIndices != 0 then return none
  for p in params do
    let .sort (.succ _) ← whnf (← inferType p) | return none
  let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    params.mapIdx fun k p => (Name.mkSimple s!"inst{k}", .instImplicit,
      fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[p])
  withLocalDecls instDecls fun _ => do
    let ty := mkAppN (mkConst ind.name (ind.levelParams.map Level.param)) params
    let cls ← try mkAppM ``LeanScript.LeanScriptTyWf #[ty] catch _ => return none
    let .some inst ← trySynthInstance cls | return none
    match ← shapeView? (← mkAppOptM ``LeanScript.tyOf #[some ty, some inst]) with
    | some (``LeanScript.TyShape.prim, _) =>
        if ind.name == ``Bool then return none
        throwError "`#leanscript_ctor`: `{ind.name}` is modelled by a terminal type of the \
          language, whose values are literals; it has no constructor function"
    | some (``LeanScript.LeanPrimTyCovariant.array, _)
    | some (``LeanScript.LeanPrimTyCovariant.thunk, _)
    | some (``LeanScript.LeanPrimTyCovariant.lazy, _)
    | some (``LeanScript.TyShape.fn, _) =>
        throwError "`#leanscript_ctor`: `{ind.name}` is modelled by a built-in type former of \
          the language, which has an introduction form of its own"
    | some (``LeanScript.TyShape.enum, #[s]) =>
        if s.hasFVar then return none else return some s
    | _ => return none

end LeanScript.CtorFn

end

end
