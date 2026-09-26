module

public import LeanScript.Ty.Ty

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# Unfolding a recursive type one level

`Ty` has four **binders** — `Ty.recTaggedUnion`, `Ty.recObject`, `Ty.recAlias` and
`Ty.mutualRecursiveFamily` — and two **occurrence leaves** — `Ty.self`, which is the
declaration a lone binder defines, and `Ty.familyMember i`, which is member `i` of the
family a `Ty.mutualRecursiveFamily` defines.  The payload of a binder is written in the
scope the binder opens, so it is *not* a list of types of the language on its own: the
type of a field of a list of naturals is `Ty.self`, and what a value of that field really
is is a list of naturals again.

**Unfolding** is what turns a payload written in a scope into types of the language:
substituting each occurrence leaf by the type it stands for.  It is what an introduction
form and an eliminator of a recursive shape need — `LeanScript.Term.recTaggedUnion_mk`
takes the fields of a constructor *unfolded*, and `LeanScript.Term.recTaggedUnion_casesOn`
branches on the *unfolded* schema — and this module is that substitution.

## A nested binder is not looked into

`LeanScript.Ty.WfIn` checks the payload of a binder in the scope that binder opens, and
checks a *nested* binder's payload in the scope the nested binder opens: an occurrence
inside a nested binder belongs to the nested binder.  So substitution stops at a binder,
exactly as `LeanScript.Ty.OccursIn` does.

## Why the traversal is written out

`Ty` is a nested inductive — its children sit inside `TyShape`, `LeanRecordSchema`,
`LeanTaggedUnionSchema` and `NonEmptyList` — so a traversal written as `s.map subst` is
not structurally recursive as far as Lean is concerned.  As in `LeanScript.Ty.beq`, the
traversal is therefore one function per container, all in one `mutual` block, and
`Ty.substOcc_shape_eq_map` and friends record that the block does agree with the `map`
of each container, which is how the *top-level* unfoldings below are stated.
-/

namespace Ty

mutual

/-- Substitute the occurrence leaves of a tree: `Ty.self` by `s`, and `Ty.familyMember i`
    by `m i`.  A nested binder is left alone — its occurrences are its own. -/
def substOcc (s : Ty) (m : Nat → Ty) : Ty → Ty
  | .self => s
  | .familyMember i => m i
  | .shape sh => .shape (substOccShape s m sh)
  | .recTaggedUnion l => .recTaggedUnion l
  | .recObject fs => .recObject fs
  | .recAlias b => .recAlias b
  | .mutualRecursiveFamily f => .mutualRecursiveFamily f

/-- `Ty.substOcc`, on a node. -/
def substOccShape (s : Ty) (m : Nat → Ty) : TyShape Ty → TyShape Ty
  | .prim p => .prim p
  | .fn a b => .fn a (substOcc s m b)
  | .primCovariant c => .primCovariant (substOccCov s m c)
  | .enum e => .enum e
  | .record fs => .record (substOccRecord s m fs)
  | .taggedUnion l => .taggedUnion (substOccTU s m l)

/-- `Ty.substOcc`, on an array, a thunk or a lazy value. -/
def substOccCov (s : Ty) (m : Nat → Ty) :
    LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty
  | .array a => .array (substOcc s m a)
  | .thunk a => .thunk (substOcc s m a)
  | .lazy a => .lazy (substOcc s m a)

/-- `Ty.substOcc`, on a list of types. -/
def substOccList (s : Ty) (m : Nat → Ty) : List Ty → List Ty
  | [] => []
  | a :: as => substOcc s m a :: substOccList s m as

/-- `Ty.substOcc`, on the fields of each constructor. -/
def substOccCtors (s : Ty) (m : Nat → Ty) : List (List Ty) → List (List Ty)
  | [] => []
  | a :: as => substOccList s m a :: substOccCtors s m as

/-- `Ty.substOcc`, on a list that has at least one entry. -/
def substOccNE (s : Ty) (m : Nat → Ty) : NonEmptyList Ty → NonEmptyList Ty
  | ⟨a, as⟩ => ⟨substOcc s m a, substOccList s m as⟩

/-- `Ty.substOcc`, on the fields of a record. -/
def substOccRecord (s : Ty) (m : Nat → Ty) :
    LeanRecordSchema Ty → LeanRecordSchema Ty
  | ⟨a, b, rest⟩ => ⟨substOcc s m a, substOcc s m b, substOccList s m rest⟩

/-- `Ty.substOcc`, on the constructors of a tagged union. -/
def substOccTU (s : Ty) (m : Nat → Ty) :
    LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty
  | .payloadFirst f n r =>
      .payloadFirst (substOccNE s m f) (substOccList s m n) (substOccCtors s m r)
  | .skip c => .skip (substOccCP s m c)

/-- `Ty.substOcc`, on the constructors that follow a field-less one. -/
def substOccCP (s : Ty) (m : Nat → Ty) :
    CtorsWithPayload Ty → CtorsWithPayload Ty
  | .here f r => .here (substOccNE s m f) (substOccCtors s m r)
  | .skip c => .skip (substOccCP s m c)

end

mutual

/-- Does the tree hold an occurrence `Ty.familyMember i` of a member of the family in scope
    — a leaf `Ty.substOcc` substitutes?  A nested binder is not looked into, and neither is
    the domain of a function, exactly as `Ty.substOcc` does. -/
def hasMemberOcc : Ty → Bool
  | .self => false
  | .familyMember _ => true
  | .shape sh => hasMemberOccShape sh
  | .recTaggedUnion _ => false
  | .recObject _ => false
  | .recAlias _ => false
  | .mutualRecursiveFamily _ => false

/-- `Ty.hasMemberOcc`, on a node. -/
def hasMemberOccShape : TyShape Ty → Bool
  | .prim _ => false
  | .fn _ b => hasMemberOcc b
  | .primCovariant c => hasMemberOccCov c
  | .enum _ => false
  | .record fs => hasMemberOccRecord fs
  | .taggedUnion l => hasMemberOccTU l

/-- `Ty.hasMemberOcc`, on an array, a thunk or a lazy value. -/
def hasMemberOccCov : LeanPrimTyCovariant Ty → Bool
  | .array a => hasMemberOcc a
  | .thunk a => hasMemberOcc a
  | .lazy a => hasMemberOcc a

/-- `Ty.hasMemberOcc`, on a list of types. -/
def hasMemberOccList : List Ty → Bool
  | [] => false
  | a :: as => hasMemberOcc a || hasMemberOccList as

/-- `Ty.hasMemberOcc`, on the fields of each constructor. -/
def hasMemberOccCtors : List (List Ty) → Bool
  | [] => false
  | a :: as => hasMemberOccList a || hasMemberOccCtors as

/-- `Ty.hasMemberOcc`, on a list that has at least one entry. -/
def hasMemberOccNE : NonEmptyList Ty → Bool
  | ⟨a, as⟩ => hasMemberOcc a || hasMemberOccList as

/-- `Ty.hasMemberOcc`, on the fields of a record. -/
def hasMemberOccRecord : LeanRecordSchema Ty → Bool
  | ⟨a, b, rest⟩ => hasMemberOcc a || hasMemberOcc b || hasMemberOccList rest

/-- `Ty.hasMemberOcc`, on the constructors of a tagged union. -/
def hasMemberOccTU : LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst f n r => hasMemberOccNE f || hasMemberOccList n || hasMemberOccCtors r
  | .skip c => hasMemberOccCP c

/-- `Ty.hasMemberOcc`, on the constructors that follow a field-less one. -/
def hasMemberOccCP : CtorsWithPayload Ty → Bool
  | .here f r => hasMemberOccNE f || hasMemberOccCtors r
  | .skip c => hasMemberOccCP c

end

/-! ## The traversal is the `map` of each container -/

theorem substOccList_eq_map (s : Ty) (m : Nat → Ty) :
    ∀ xs : List Ty, substOccList s m xs = xs.map (substOcc s m)
  | [] => rfl
  | _ :: as => by simp only [substOccList, List.map_cons, substOccList_eq_map s m as]

theorem substOccCtors_eq_map (s : Ty) (m : Nat → Ty) :
    ∀ xs : List (List Ty), substOccCtors s m xs = xs.map (·.map (substOcc s m))
  | [] => rfl
  | a :: as => by
      simp only [substOccCtors, List.map_cons, substOccList_eq_map s m a,
        substOccCtors_eq_map s m as]

theorem substOccNE_eq_map (s : Ty) (m : Nat → Ty) (xs : NonEmptyList Ty) :
    substOccNE s m xs = xs.map (substOcc s m) := by
  cases xs
  simp only [substOccNE, NonEmptyList.map, substOccList_eq_map]

theorem substOccRecord_eq_map (s : Ty) (m : Nat → Ty) (fs : LeanRecordSchema Ty) :
    substOccRecord s m fs = fs.map (substOcc s m) := by
  cases fs
  simp only [substOccRecord, LeanRecordSchema.map, substOccList_eq_map, Functor.map]

theorem substOccCP_eq_map (s : Ty) (m : Nat → Ty) :
    ∀ c : CtorsWithPayload Ty, substOccCP s m c = c.map (substOcc s m)
  | .here _ _ => by
      simp only [substOccCP, CtorsWithPayload.map, substOccNE_eq_map, substOccCtors_eq_map,
        Functor.map]
  | .skip c => by
      simp only [substOccCP, CtorsWithPayload.map, substOccCP_eq_map s m c]

theorem substOccTU_eq_map (s : Ty) (m : Nat → Ty) (l : LeanTaggedUnionSchema Ty) :
    substOccTU s m l = l.map (substOcc s m) := by
  cases l with
  | payloadFirst _ _ _ =>
      simp only [substOccTU, LeanTaggedUnionSchema.map, substOccNE_eq_map,
        substOccList_eq_map, substOccCtors_eq_map, Functor.map]
  | skip c =>
      simp only [substOccTU, LeanTaggedUnionSchema.map, substOccCP_eq_map, Functor.map]

/-! ## The two scopes

A lone binder has one thing in scope, the declaration itself, so its unfolding only has
to say what `Ty.self` is; a family has one thing in scope per member, so its unfolding
only has to say what each `Ty.familyMember i` is. -/

/-- The tree `t`, written in the scope of a lone binder, read as a type of the language:
    `Ty.self` is the binder `r` itself. -/
def unfoldSelf (r : Ty) (t : Ty) : Ty := substOcc r .familyMember t

/-- The tree `t`, written in the scope of a mutual family, read as a type of the
    language: `Ty.familyMember i` is the type `mem i`. -/
def unfoldMembers (mem : Nat → Ty) (t : Ty) : Ty := substOcc .self mem t

/-! ## The scope of a mutual family -/

end Ty

namespace LeanMutualRecFamily

variable {α : Type}

/-- The same family, with member `i` selected — and member `0` selected when `i` is not a
    member of it, which `LeanScript.Ty.WfIn` rules out.  Falling back on member `0`, rather
    than on the member `f` selects, makes the member selected depend on the members
    alone, which is what lets a value of `Ty.familyMember i` be a node of the family's
    W-type (`LeanScript.FamW`) without a proof that `i` is in range. -/
def select (f : LeanMutualRecFamily α) (i : Nat) : LeanMutualRecFamily α :=
  match ofMembers? f.members i with
  | some g => g
  | none => (ofMembers? f.members 0).getD f


end LeanMutualRecFamily

namespace Ty

/-- The type of member `i` of the family `f`: the same family, selecting that member. -/
def familyMemberTy (f : LeanMutualRecFamily Ty) (i : Nat) : Ty :=
  .mutualRecursiveFamily (f.select i)

/-- The tree `t`, written in the scope of the family `f`, read as a type of the
    language. -/
def unfoldFamily (f : LeanMutualRecFamily Ty) (t : Ty) : Ty :=
  unfoldMembers (familyMemberTy f) t

/-! ## The unfolding of each recursive shape

Each of the four is the payload of the binder with the binder's own occurrences
substituted away, so the result describes exactly what a *value* of the shape holds. -/

/-- The constructors of a recursive tagged union, unfolded: the field types of a value of
    `Ty.recTaggedUnion l`, constructor by constructor.  The schema has the same shape as
    `l` — the same constructors, in the same order, with the same number of fields — so
    the branches of a dispatch on it are the branches of a dispatch on `l`. -/
def recTaggedUnionUnfold (l : LeanTaggedUnionSchema Ty) : LeanTaggedUnionSchema Ty :=
  l.map (unfoldSelf (.recTaggedUnion l))

/-- The fields of a recursive record, unfolded. -/
def recObjectUnfold (fs : LeanRecordSchema Ty) : LeanRecordSchema Ty :=
  fs.map (unfoldSelf (.recObject fs))

/-- The body of a recursive newtype, unfolded. -/
def recAliasUnfold (b : Ty) : Ty := unfoldSelf (.recAlias b) b

/-- The constructors of a member of a mutual family, unfolded in the scope of that
    family. -/
def famCtorsUnfold (f : LeanMutualRecFamily Ty) (l : LeanTaggedUnionSchema Ty) :
    LeanTaggedUnionSchema Ty :=
  l.map (unfoldFamily f)

/-- The fields of a record member of a mutual family, unfolded in the scope of that
    family. -/
def famRecordUnfold (f : LeanMutualRecFamily Ty) (fs : LeanRecordSchema Ty) :
    LeanRecordSchema Ty :=
  fs.map (unfoldFamily f)

/-! ## What a branch of a fold binds

A `_casesOn` binds the fields of the constructor it matched; a `_rec` binds those *and*
the value of the fold at each field that is an occurrence of the type being folded over.
The value is **given** to the branch rather than computed by it, which is what keeps a
term terminating by construction.

Only a field that is *literally* an occurrence — `Ty.self`, or `Ty.familyMember i` —
comes with the value of the fold.  A field that mentions the type only *inside* another
former (an array of it, say) is bound as it is: the fold of the elements of an array of
the type is a map, not a binding, and the grammar does not have one. -/

/-- The binders a branch of `LeanScript.Term.recTaggedUnion_rec` gets, for a constructor
    whose field types are `fs`: every field, unfolded, and — right after a field that is
    an occurrence of the type `r` being folded over — the value of the fold at that
    field, of the type `motive` the fold answers.

    A recursive **record** and a recursive **newtype** are folded differently: no field of
    a record, and no body of a newtype, is literally an occurrence of it, so this gives
    their branches nothing (`LeanScript.TyWf.recBinders_recObject`,
    `LeanScript.TyWf.recBinders_recAlias`); `LeanScript.Term.recObject_rec` binds
    `LeanScript.TyWf.recObjectRecBinders` and `LeanScript.Term.recAlias_rec` binds
    `LeanScript.TyWf.recAliasRecBinders` instead. -/
def recBinders (r motive : Ty) : List Ty → List Ty
  | [] => []
  | .self :: fs => r :: motive :: recBinders r motive fs
  | a :: fs => unfoldSelf r a :: recBinders r motive fs

/-- The answers of a fold of motive `motive` at the occurrences of members **inside** a
    field `a` (`Array (familyMember i)`, `Nat → familyMember i`, `Thunk (familyMember i)`):
    the field's own shape with every occurrence replaced by `motive`. -/
def famAnswerMap (motive : Ty) (a : Ty) : Ty := substOcc .self (fun _ => motive) a

/-- What a branch of the fold of a family binds after a field `a` that is not literally an
    occurrence of a member, in front of `rest`: the answers at the occurrences inside it
    (`Ty.famAnswerMap`), when it holds any, and nothing otherwise. -/
def famAnswerBinders (motive : Ty) (a : Ty) (rest : List Ty) : List Ty :=
  cond (hasMemberOcc a) (famAnswerMap motive a :: rest) rest

/-- `Ty.recBinders`, in the scope of a mutual family: a field that is an occurrence of
    member `i` is followed by the value of the fold at that field, and a field that holds
    occurrences of members inside it (an array of them, a function into one, a delay of
    one) by the answers at them, in the field's shape (`Ty.famAnswerBinders`). -/
def famRecBinders (f : LeanMutualRecFamily Ty) (motive : Ty) : List Ty → List Ty
  | [] => []
  | .familyMember i :: fs => familyMemberTy f i :: motive :: famRecBinders f motive fs
  | a :: fs => unfoldFamily f a ::
      famAnswerBinders motive a (famRecBinders f motive fs)

end Ty

end LeanScript

end
