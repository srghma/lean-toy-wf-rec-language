module

public import LeanScript.Ty.Wf
public import LeanScript.Ty.TyBEq
public meta import LeanScript.Ty.WfTactic

@[expose] public section

namespace LeanScript

/-!
# `TyWf`: a tree of the language together with the proof that it is one

The bundle every context and every term speaks about.  Its proof field defaults to
`by ty_wf`; it has the coercion `CoeOut TyWf Ty`, the equality instances of its tree, and
`Ty.toTyWf` for the direction that needs a proof.
-/

/-- A tree of the language together with the proof that it is one: what a
    `LeanScript.LeanScriptTyWf` instance holds, with the Lean type it models forgotten.

    `Ty` is in `Type` and `Ty.Wf` is a proposition, so `TyWf` is in `Type` as well — not
    in `Type 1`.

    The proof is written by `ty_wf` unless one is given, so a bundled tree is usually
    written as its tree alone: `(⟨.prim .nat⟩ : TyWf)`. -/
structure TyWf where
  /-- The tree. -/
  toTy : Ty
  /-- That the tree is a type of the language. -/
  isWf : Ty.Wf toTy := by ty_wf
  deriving Repr

namespace TyWf

/-- Two bundled trees are equal when their trees are: the other field is a proof. -/
@[ext] theorem ext : ∀ {s t : TyWf}, s.toTy = t.toTy → s = t
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- A bundled tree *is* its tree wherever a tree is wanted: the proof is dropped.  This is
    the only direction that can be a coercion — the other one needs a proof, which no
    instance can supply; `LeanScript.Ty.toTyWf` is that direction, written out. -/
instance : CoeOut TyWf Ty := ⟨toTy⟩

/-- Equality of bundled trees is equality of their trees: the other field is a proof, and
    two proofs of one proposition are equal. -/
instance : BEq TyWf := ⟨fun s t => s.toTy == t.toTy⟩

instance : LawfulBEq TyWf where
  eq_of_beq h := TyWf.ext (eq_of_beq h)
  rfl := Ty.beq_refl _

instance : DecidableEq TyWf := fun s t =>
  if h : s.toTy = t.toTy then .isTrue (TyWf.ext h) else .isFalse fun he => h (he ▸ rfl)

instance : Inhabited TyWf := ⟨⟨.prim .bool, .shape .prim⟩⟩

end TyWf

/-- The other direction: a tree becomes a bundle once it is known to be a type, and
    `ty_wf` writes that proof, so `(Ty.prim .nat).toTyWf` needs nothing written by hand.
    It cannot be a `CoeOut` instance, because an instance has no room for the proof. -/
def Ty.toTyWf (t : Ty) (h : Ty.Wf t := by ty_wf) : TyWf := ⟨t, h⟩

@[simp] theorem Ty.toTy_toTyWf (t : Ty) (h : Ty.Wf t) : (t.toTyWf h).toTy = t := rfl

/-! ## A list, and a schema, of bundles -/

namespace Ty

/-- The trees of a list of types are all types. -/
theorem wfAllIn_map_toTy : ∀ ts : List TyWf, WfAllIn 0 (ts.map TyWf.toTy)
  | [] => .nil
  | t :: rest => .cons t.isWf (wfAllIn_map_toTy rest)

/-- The trees of the fields of a record of types are all types. -/
theorem wfAllIn_record_map_toTy (fs : LeanRecordSchema TyWf) :
    WfAllIn 0 ((fs.map TyWf.toTy).toList) := by
  rw [LeanRecordSchema.toList_map]
  exact wfAllIn_map_toTy fs.toList

/-- The trees of the fields of every constructor of a union of types are all types. -/
theorem wfAllIn_taggedUnion_map_toTy (l : LeanTaggedUnionSchema TyWf) :
    WfAllIn 0 ((l.map TyWf.toTy).toList.flatten) := by
  have : (l.map TyWf.toTy).toList.flatten = l.toList.flatten.map TyWf.toTy := by
    simp only [LeanTaggedUnionSchema.toList_map, List.map_flatten]
  rw [this]
  exact wfAllIn_map_toTy _

end Ty

/-! ## The non-recursive types of the language, at the level of bundles

Each of these is the corresponding `LeanScript.Ty` constructor with the proof composed out
of its arguments': nothing below the node is looked at again.  The *recursive* shapes need
a tree written inside a binder, so they live with `LeanScript.TyWfIn`. -/

namespace TyWf

/-- A terminal type. -/
@[reducible] def prim (p : LeanPrimTy) : TyWf := ⟨.prim p, .shape .prim⟩

/-- A curried function type.  The domain of a function is checked in the closed scope, and
    both of these are closed, so the node is a type. -/
@[reducible] def fn (a b : TyWf) : TyWf := ⟨.fn a.toTy b.toTy, .shape (.fn a.isWf b.isWf)⟩

/-- An array. -/
@[reducible] def array (a : TyWf) : TyWf := ⟨.array a.toTy, .shape (.primCovariant a.isWf)⟩

/-- A memoised delay. -/
@[reducible] def thunk (a : TyWf) : TyWf := ⟨.thunk a.toTy, .shape (.primCovariant a.isWf)⟩

/-- An unmemoised delay. -/
@[reducible] def lazy (a : TyWf) : TyWf := ⟨.lazy a.toTy, .shape (.primCovariant a.isWf)⟩

/-- A field-less enum. -/
@[reducible] def enum (e : LeanEnumSchema) : TyWf := ⟨.enum e, .shape .enum⟩

/-- A record, from the types of its fields. -/
@[reducible] def record (fs : LeanRecordSchema TyWf) : TyWf :=
  ⟨.record (fs.map TyWf.toTy), .shape (.record (Ty.wfAllIn_record_map_toTy fs))⟩

/-- A tagged union, from the types of the fields of each of its constructors. -/
@[reducible] def taggedUnion (l : LeanTaggedUnionSchema TyWf) : TyWf :=
  ⟨.taggedUnion (l.map TyWf.toTy),
    .shape (.taggedUnion (Ty.wfAllIn_taggedUnion_map_toTy l))⟩

@[simp] theorem toTy_prim (p : LeanPrimTy) : (prim p).toTy = .prim p := rfl
@[simp] theorem toTy_fn (a b : TyWf) : (fn a b).toTy = .fn a.toTy b.toTy := rfl
@[simp] theorem toTy_array (a : TyWf) : (array a).toTy = .array a.toTy := rfl
@[simp] theorem toTy_thunk (a : TyWf) : (thunk a).toTy = .thunk a.toTy := rfl
@[simp] theorem toTy_lazy (a : TyWf) : (lazy a).toTy = .lazy a.toTy := rfl
@[simp] theorem toTy_enum (e : LeanEnumSchema) : (enum e).toTy = .enum e := rfl
@[simp] theorem toTy_record (fs : LeanRecordSchema TyWf) :
    (record fs).toTy = .record (fs.map TyWf.toTy) := rfl
@[simp] theorem toTy_taggedUnion (l : LeanTaggedUnionSchema TyWf) :
    (taggedUnion l).toTy = .taggedUnion (l.map TyWf.toTy) := rfl

end TyWf

/-- Notation for a curried function type of bundled types: `σ ⇒ τ` is `TyWf.fn σ τ`. -/
scoped infixr:25 " ⇒ " => TyWf.fn

end LeanScript

end
