module

public import LeanScript.Ty.TyWf
public import LeanScript.Ty.WfSubst
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# Types of the language written inside a binder, bundled

`LeanScript.TyWf` — a tree together with the proof that it is a type of the language — and
the constructors that need nothing but closed types (`TyWf.prim`, `TyWf.fn`, `TyWf.array`,
`TyWf.record`, …) are in `LeanScript.Ty.TyWf`.  This module adds what a *binder* needs:
`LeanScript.TyWfIn`, the same bundle for a tree written **inside a binder**, and the
constructors of the recursive shapes, which take their payload in that form.

## Why there are two

The payload of a recursive binder is written in the scope that binder opens, so a field of
it is not a closed type: `Ty.self` is a field of the schema of `List α`, and it is a type
only once the binder is put back in for it.  `TyWfIn n` is a tree that is well formed *in a
scope of `n` members*, and `TyWfIn.unfold` is the step from one to the other: a field of a
binder's payload (`TyWfIn 1`) becomes a type (`TyWf`) once the binder itself is substituted
for its occurrences, which is `LeanScript.Ty.wf_unfoldSelf`.

So a schema of the language is a schema **of bundles**: `LeanRecordSchema TyWf` for a
record, `LeanTaggedUnionSchema (TyWfIn 1)` for the payload of a recursive union.  The tree
of such a schema is its `map` to trees, and the proof of the whole is composed from the
fields' — there is no list of trees with a side condition anywhere, and no proof carried
inside a list.
-/

/-- A tree that is well formed **in a scope of `n` members**, with its proof: the payload
    of a binder is written in `TyWfIn 1`, where `Ty.self` is legal, and a closed type is
    `LeanScript.TyWf`.

    The proof is written by `ty_wf` unless one is given. -/
structure TyWfIn (n : Nat) where
  /-- The tree. -/
  toTy : Ty
  /-- That the tree is well formed in a scope of `n` members. -/
  isWfIn : Ty.WfIn n toTy := by ty_wf
  deriving Repr

namespace TyWfIn

variable {n : Nat}

/-- Two bundles are equal when their trees are: the other field is a proof. -/
@[ext] theorem ext : ∀ {s t : TyWfIn n}, s.toTy = t.toTy → s = t
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- A bundle *is* its tree wherever a tree is wanted. -/
instance : CoeOut (TyWfIn n) Ty := ⟨toTy⟩

instance : BEq (TyWfIn n) := ⟨fun s t => s.toTy == t.toTy⟩

instance : LawfulBEq (TyWfIn n) where
  eq_of_beq h := TyWfIn.ext (eq_of_beq h)
  rfl := Ty.beq_refl _

instance : DecidableEq (TyWfIn n) := fun s t =>
  if h : s.toTy = t.toTy then .isTrue (TyWfIn.ext h) else .isFalse fun he => h (he ▸ rfl)

instance : Inhabited (TyWfIn n) := ⟨⟨.prim .bool, .closed (.shape .prim)⟩⟩

/-- A tree becomes a bundle once it is known to be well formed in the scope, and `ty_wf`
    writes that proof, so `(Ty.array Ty.self).toTyWfIn` needs nothing written by hand.
    As for `LeanScript.Ty.toTyWf` it cannot be a coercion: an instance has no room for
    the proof. -/
def _root_.LeanScript.Ty.toTyWfIn (t : Ty) {n : Nat} (h : Ty.WfIn n t := by ty_wf) :
    TyWfIn n := ⟨t, h⟩

@[simp] theorem toTy_toTyWfIn (t : Ty) {n : Nat} (h : Ty.WfIn n t) :
    (Ty.toTyWfIn t h).toTy = t := rfl

/-- A closed type is a tree of every scope: this is `Ty.WfIn.closed`, bundled. -/
def ofTyWf (t : TyWf) : TyWfIn n := ⟨t.toTy, .closed t.isWf⟩

@[simp] theorem toTy_ofTyWf (t : TyWf) : (ofTyWf (n := n) t).toTy = t.toTy := rfl

/-- A closed type stands wherever a tree of some scope is wanted. -/
instance : Coe TyWf (TyWfIn n) := ⟨ofTyWf⟩

/-- **A field of a binder's payload, unfolded**: the tree with the binder `S` put back in
    for its occurrences, which `LeanScript.Ty.wf_unfoldSelf` says is a type. -/
def unfold (S : TyWf) (t : TyWfIn 1) : TyWf :=
  ⟨Ty.unfoldSelf S.toTy t.toTy, Ty.wf_unfoldSelf S.isWf t.isWfIn⟩

@[simp] theorem toTy_unfold (S : TyWf) (t : TyWfIn 1) :
    (unfold S t).toTy = Ty.unfoldSelf S.toTy t.toTy := rfl

end TyWfIn

namespace TyWf

/-! ## The recursive shapes

A binder is built from a payload written in the scope it opens — a schema of `TyWfIn 1` —
and the conditions that make it a *type*: that it mentions itself, only positively, and has
values.  Those are not consequences of the payload being well formed, so they stay a proof
argument, written by `ty_wf` unless one is given. -/

/-- The tree of a recursive tagged union with this payload. -/
abbrev recTaggedUnionTy (l : LeanTaggedUnionSchema (TyWfIn 1)) : Ty :=
  .recTaggedUnion (l.map TyWfIn.toTy)

/-- A recursive tagged union: the payload, written in the scope the binder opens, with the
    proof that the binder describes a type. -/
def recTaggedUnion (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l) := by ty_wf) : TyWf :=
  ⟨recTaggedUnionTy l, hwf⟩

/-- The tree of a recursive record with these fields. -/
abbrev recObjectTy (fs : LeanRecordSchema (TyWfIn 1)) : Ty :=
  .recObject (fs.map TyWfIn.toTy)

/-- A recursive record. -/
def recObject (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs) := by ty_wf) : TyWf :=
  ⟨recObjectTy fs, hwf⟩

/-- The tree of a recursive newtype with this body. -/
abbrev recAliasTy (b : TyWfIn 1) : Ty := .recAlias b.toTy

/-- A recursive newtype. -/
def recAlias (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b) := by ty_wf) : TyWf :=
  ⟨recAliasTy b, hwf⟩

@[simp] theorem toTy_recTaggedUnion (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l)) :
    (recTaggedUnion l hwf).toTy = recTaggedUnionTy l := rfl

@[simp] theorem toTy_recObject (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) : (recObject fs hwf).toTy = recObjectTy fs := rfl

@[simp] theorem toTy_recAlias (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b)) :
    (recAlias b hwf).toTy = recAliasTy b := rfl

/-! ## Unfolding a binder

The fields of a value of a binder are the fields of its payload with the binder put back in
for its occurrences.  At the level of bundles that is the `map` of `TyWfIn.unfold`, so it
needs nothing beyond the schema and the binder itself. -/

/-- The constructors of a recursive tagged union, unfolded: what a value of it holds. -/
def recTaggedUnionUnfold (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l) := by ty_wf) : LeanTaggedUnionSchema TyWf :=
  l.map (TyWfIn.unfold (recTaggedUnion l hwf))

/-- The fields of a recursive record, unfolded. -/
def recObjectUnfold (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs) := by ty_wf) : LeanRecordSchema TyWf :=
  fs.map (TyWfIn.unfold (recObject fs hwf))

/-- The body of a recursive newtype, unfolded. -/
def recAliasUnfold (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b) := by ty_wf) : TyWf :=
  TyWfIn.unfold (recAlias b hwf) b

/-! ## A mutual recursive family

A family has **at least two** members, so the scope its payload is written in is written
`n + 2` rather than `n`: that is what makes a member of it never a `Ty.self`, and it is
what `LeanScript.Ty.wf_substOccFam` needs in order to read a member as a type.  The
conditions that make the family a family — that every member is mentioned, positively,
and has values — are not consequences of the members being well formed in that scope, so
they stay a proof argument, written by `ty_wf` unless one is given. -/

/-- The tree of a mutual family with these members. -/
abbrev mutualRecursiveFamilyTy {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2))) : Ty :=
  .mutualRecursiveFamily (f.map TyWfIn.toTy)

/-- A mutual recursive family, with the member it selects. -/
def mutualRecursiveFamily {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f) := by ty_wf) : TyWf :=
  ⟨mutualRecursiveFamilyTy f, hwf⟩

@[simp] theorem toTy_mutualRecursiveFamily {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) :
    (mutualRecursiveFamily f hwf).toTy = mutualRecursiveFamilyTy f := rfl

/-- Member `i` of a family that is a type is a type: the same family, selecting that
    member (`LeanScript.Ty.wf_familyMemberTy`). -/
def famMemberTy {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) (i : Nat) : TyWf :=
  ⟨Ty.familyMemberTy (f.map TyWfIn.toTy) i, Ty.wf_familyMemberTy hwf i⟩

@[simp] theorem toTy_famMemberTy {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) (i : Nat) :
    (famMemberTy f hwf i).toTy = Ty.familyMemberTy (f.map TyWfIn.toTy) i := rfl

end TyWf

namespace TyWfIn

/-- **A field of a member of a family, unfolded**: the tree with each occurrence of a
    member replaced by that member's type, which `LeanScript.Ty.wf_substOccFam` says is a
    type. -/
def unfoldFam {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (t : TyWfIn (n + 2)) : TyWf :=
  ⟨Ty.unfoldFamily (f.map TyWfIn.toTy) t.toTy,
    Ty.wf_substOccFam (fun i => Ty.wf_familyMemberTy hwf i) t.isWfIn (by omega)⟩

@[simp] theorem toTy_unfoldFam {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (t : TyWfIn (n + 2)) :
    (unfoldFam f hwf t).toTy = Ty.unfoldFamily (f.map TyWfIn.toTy) t.toTy := rfl

end TyWfIn

namespace TyWf

/-- The constructors of a member of a family, unfolded in the scope of the family. -/
def famCtorsUnfold {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f))
    (l : LeanTaggedUnionSchema (TyWfIn (n + 2))) : LeanTaggedUnionSchema TyWf :=
  l.map (TyWfIn.unfoldFam f hwf)

/-- The fields of a record member of a family, unfolded in the scope of the family. -/
def famRecordUnfold {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f))
    (fs : LeanRecordSchema (TyWfIn (n + 2))) : LeanRecordSchema TyWf :=
  fs.map (TyWfIn.unfoldFam f hwf)

/-! ## What a branch of a fold binds

A branch of a fold binds every field of its constructor, unfolded, and — right after a
field that is *literally* an occurrence of the type being folded over — the value of the
fold at that field.  These are `LeanScript.Ty.recBinders` and
`LeanScript.Ty.famRecBinders` at the level of bundles. -/

/-- The binders of a branch of a fold over a lone binder: every field, unfolded, with the
    value of the fold after each field that is an occurrence of the binder. -/
def recBinders (r motive : TyWf) : List (TyWfIn 1) → List TyWf
  | [] => []
  | ⟨.self, _⟩ :: fs => r :: motive :: recBinders r motive fs
  | a :: fs => TyWfIn.unfold r a :: recBinders r motive fs

/-! ## What a branch of a fold of a recursive **record** binds

A recursive record is the one binder whose fields can never be an occurrence of it
*literally*: a record has values only when **all** of its fields do, so a field written
`Ty.self` would make the record the equation `T = … × T × …`, which no value satisfies
(`LeanScript.Ty.not_wf_recObject_self`).  Its occurrences of itself therefore always sit
**inside** another former — `Array T`, or a union with a constructor that does not mention
it — and `TyWf.recBinders` hands such a field over as it is, with no value of the fold
beside it (`LeanScript.RecObjectRecFacts.recBinders_recObject`).

So the answers of a fold of a record are given in the **shape of the record's own
fields**: `TyWf.recObjectMap fs X` is the record with every occurrence of the record
replaced by `X`, which for `T = { n : Nat, kids : Array T }` and `X = τ` is
`{ n : Nat, kids : Array τ }` — each subvalue replaced by the value of the fold at it.

That is the whole of a depth-zero fold.  A **depth-`k`** one replaces each subvalue not by
its answer alone but by its `TyWf.recObjectAnswerTree` of depth `k`: the answer at it,
together — in the shape of *its* fields — with the answer trees of depth `k - 1` of its
own subvalues.  So a branch reads the answers at everything `k + 1` levels down, along
the path it descends, exactly as a depth-`k` branch of `Term.recTaggedUnion_rec` does and
as `Term.nat_rec` at depth `k` reads the answers at `n - 1, …, n - 1 - k`. -/

/-- The fields of a recursive record with every occurrence of the record itself replaced
    by `X`: the record's own shape, carrying an `X` wherever a subvalue sat. -/
def recObjectMap (fs : LeanRecordSchema (TyWfIn 1)) (X : TyWf) : TyWf :=
  .record (fs.map (TyWfIn.unfold X))

/-- **The answers at a subvalue of a recursive record and at everything `j` levels below
    it**: at `j = 0` the answer at the subvalue alone, and at `j + 1` that answer paired
    with the answer trees of depth `j` of the subvalue's own subvalues, in the shape of
    the record's fields. -/
def recObjectAnswerTree (fs : LeanRecordSchema (TyWfIn 1)) (motive : TyWf) : Nat → TyWf
  | 0 => motive
  | j + 1 => .record ⟨motive, recObjectMap fs (recObjectAnswerTree fs motive j), []⟩

/-- The binders of the branch of a depth-`k` fold of a recursive record: every field of
    the record, unfolded — what `Term.recObject_casesOn` binds — and then the fold's
    **lookback window**, one binder holding the answer trees of depth `k` of the
    immediate subvalues. -/
def recObjectRecBinders (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) (motive : TyWf) (k : Nat) : List TyWf :=
  (recObjectUnfold fs hwf).toList ++ [recObjectMap fs (recObjectAnswerTree fs motive k)]

/-! ## What a branch of a fold of a recursive **newtype** binds

A recursive newtype is in the same position as a recursive record: its body can never be
*literally* an occurrence of it, since `μX. X` is the equation `T = T`, which no value
satisfies (`LeanScript.Ty.not_wf_recAlias_self`).  So `TyWf.recBinders` hands the body
over as it is, with no value of the fold beside it
(`LeanScript.TyWf.recBinders_recAlias`), and the answers of a fold of a newtype are given
in the **shape of its body**: `TyWf.recAliasMap b X` is the body with every occurrence of
the newtype replaced by `X`, which for `T = Option T` and `X = τ` is `Option τ` — each
subvalue replaced by the value of the fold at it.

That is a depth-zero fold.  A **depth-`k`** one replaces each subvalue not by its answer
alone but by its `TyWf.recAliasAnswerTree` of depth `k`: the answer at it, together — in
the shape of the body — with the answer trees of depth `k - 1` of its own subvalues.  So
a branch reads the answers at everything `k + 1` levels down, along the path it descends,
exactly as the depth-`k` branch of `Term.recObject_rec` does. -/

/-- The body of a recursive newtype with every occurrence of the newtype itself replaced
    by `X`: the body's own shape, carrying an `X` wherever a subvalue sat. -/
def recAliasMap (b : TyWfIn 1) (X : TyWf) : TyWf := TyWfIn.unfold X b

/-- **The answers at a subvalue of a recursive newtype and at everything `j` levels below
    it**: at `j = 0` the answer at the subvalue alone, and at `j + 1` that answer paired
    with the answer trees of depth `j` of the subvalue's own subvalues, in the shape of
    the body. -/
def recAliasAnswerTree (b : TyWfIn 1) (motive : TyWf) : Nat → TyWf
  | 0 => motive
  | j + 1 => .record ⟨motive, recAliasMap b (recAliasAnswerTree b motive j), []⟩

/-- The binders of the branch of a depth-`k` fold of a recursive newtype: the body,
    unfolded — what `Term.recAlias_casesOn` binds — and then the fold's **lookback
    window**, one binder holding the answer trees of depth `k` of the immediate
    subvalues. -/
def recAliasRecBinders (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b)) (motive : TyWf)
    (k : Nat) : List TyWf :=
  [recAliasUnfold b hwf, recAliasMap b (recAliasAnswerTree b motive k)]

/-- The answers of a fold of motive `motive` at the occurrences of members **inside** a
    field `a` of a member of a family (`Array (familyMember i)`, `Nat → familyMember i`,
    `Thunk (familyMember i)`): the field's own shape with every occurrence replaced by
    `motive` (`LeanScript.Ty.famAnswerMap`), which for `Array (familyMember 0)` is
    `Array motive` — each subvalue replaced by the value of the fold at it. -/
def famAnswerMap {n : Nat} (motive : TyWf) (a : TyWfIn (n + 2)) : TyWf :=
  ⟨Ty.famAnswerMap motive.toTy a.toTy,
    Ty.wf_substOccFam (fun _ => motive.isWf) a.isWfIn (by omega)⟩

@[simp] theorem toTy_famAnswerMap {n : Nat} (motive : TyWf) (a : TyWfIn (n + 2)) :
    (famAnswerMap motive a).toTy = Ty.famAnswerMap motive.toTy a.toTy := rfl

/-- What a branch of the fold of a family binds after a field `a` that is not literally an
    occurrence of a member, in front of `rest`: the answers at the occurrences of members
    inside it (`TyWf.famAnswerMap`), when it holds any (`LeanScript.Ty.hasMemberOcc`), and
    nothing otherwise. -/
def famAnswerBinders {n : Nat} (motive : TyWf) (a : TyWfIn (n + 2)) (rest : List TyWf) :
    List TyWf :=
  cond (Ty.hasMemberOcc a.toTy) (famAnswerMap motive a :: rest) rest

/-- `TyWf.recBinders`, in the scope of a mutual family: a field that is an occurrence of
    member `i` is followed by the value of the fold at that field, and a field that holds
    occurrences of members only **inside** it — an array of them, a function into one, a
    delay of one — by the answers at them, in the field's own shape
    (`TyWf.famAnswerBinders`).  A field that mentions no member is followed by nothing. -/
def famRecBinders {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) (motive : TyWf) :
    List (TyWfIn (n + 2)) → List TyWf
  | [] => []
  | ⟨.familyMember i, _⟩ :: fs =>
      famMemberTy f hwf i :: motive :: famRecBinders f hwf motive fs
  | a :: fs => TyWfIn.unfoldFam f hwf a ::
      famAnswerBinders motive a (famRecBinders f hwf motive fs)

end TyWf

end LeanScript

end
