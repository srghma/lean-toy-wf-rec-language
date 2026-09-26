module

public import LeanScript.Den.Rec

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The values of a mutual recursive family

`Ty.Den (.mutualRecursiveFamily f)` is `FamW (Ty.toIPFFamily f) f.memberIdx`: the indexed
W-tree of the containers of the family's members (`LeanScript.Ty.toIPF`), rooted at the
member `f` selects.  A node of member `i` is a value of member `i`'s shape **with its
occurrences of members blanked out**, and one subtree per occurrence, rooted at the member
the occurrence names.  This module is the bridge between that and what a term of the
language sees — the member's constructors, fields or body *unfolded*, where an occurrence
`Ty.familyMember j` is a value of `Ty.familyMemberTy f j` again:

* `Ty.famRoll` / `Ty.famUnroll`: a value of an unfolded field is a shape with a value of
  the right member in each hole, and back; they are `Ty.roll` / `Ty.unroll` in the scope
  of a family.
* `Ty.DenFam.mk` / `Ty.DenFam.unfold`: the introduction form and the one-level
  elimination of a family, and their `TyWf` versions.
* `famBindEnv`: the environment a branch of the fold of a family binds, read off a node
  whose subtrees carry the fold's answers (`IWType.memo`).

The one equation all of it moves along is `Ty.den_familyMemberTy`: a value of member `j`
of `f` is a node of `f`'s own W-type rooted at `selIdx _ j`.  It holds for every `j` —
`LeanMutualRecFamily.select` falls back on member `0`, as `selIdx` does — so nothing here
needs a proof that the family is well formed.  On a concrete family the equation is
between two types that are definitionally equal, so every `cast` reduces and a concrete
run still computes.
-/

/-! ## Selecting a member -/

namespace LeanMutualRecFamily

variable {α : Type}

theorem memberIdx_ofMembers? {ms : List (LeanFamMemberSchema α)} {i : Nat}
    {f : LeanMutualRecFamily α} (h : ofMembers? ms i = some f) : f.memberIdx = i := by
  unfold ofMembers? at h
  split at h
  · exact absurd h (by simp)
  · rename_i m hi
    have hlt : i < ms.length := by
      cases Nat.lt_or_ge i ms.length with
      | inl h' => exact h'
      | inr h' =>
          rw [List.getElem?_eq_none_iff.mpr h'] at hi
          simp at hi
    split at h
    · split at h
      · injection h with h
        subst h
        simp [memberIdx, List.length_take]
        omega
      · exact absurd h (by simp)
    · rename_i hd
      cases hb : ms.take i with
      | nil => simp [hb] at h
      | cons first bs =>
          simp only [hb, Option.some.injEq] at h
          subst h
          have := congrArg List.length hb
          simp only [List.length_take, List.length_cons] at this
          simp only [memberIdx]
          omega

theorem ofMembers?_isSome {ms : List (LeanFamMemberSchema α)} {i : Nat}
    (hi : i < ms.length) (h2 : 2 ≤ ms.length) : (ofMembers? ms i).isSome := by
  unfold ofMembers?
  rw [List.getElem?_eq_getElem hi]
  simp only
  split
  · simp [h2]
  · rename_i hd
    cases hb : ms.take i with
    | nil =>
        have := congrArg List.length hb
        have := congrArg List.length hd
        simp only [List.length_take, List.length_drop, List.length_nil] at *
        omega
    | cons first bs => simp

theorem ofMembers?_eq_none {ms : List (LeanFamMemberSchema α)} {i : Nat}
    (hi : ms.length ≤ i) : ofMembers? ms i = none := by
  unfold ofMembers?
  rw [List.getElem?_eq_none_iff.mpr hi]

/-- The member a family selecting `i` selects: `i` if the family has it, and member `0`
    otherwise. -/
theorem memberIdx_select (f : LeanMutualRecFamily α) (i : Nat) :
    (f.select i).memberIdx = selIdx f.members.length i := by
  unfold select selIdx
  split
  · rename_i g h
    have hi : i < f.members.length := by
      cases Nat.lt_or_ge i f.members.length with
      | inl h' => exact h'
      | inr h' => rw [ofMembers?_eq_none h'] at h; cases h
    simp only [hi, ↓reduceIte]
    exact memberIdx_ofMembers? h
  · rename_i h
    have hi : ¬ i < f.members.length := by
      intro hi
      have := ofMembers?_isSome hi f.two_le_members
      rw [h] at this
      cases this
    simp only [hi, ↓reduceIte]
    have h0 := ofMembers?_isSome (ms := f.members) (i := 0) (by have := f.two_le_members; omega)
      f.two_le_members
    cases h' : ofMembers? f.members 0 with
    | none => rw [h'] at h0; cases h0
    | some g => exact memberIdx_ofMembers? h'

theorem current_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).current = f.current.map g := by
  cases f <;> rfl

theorem memberIdx_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).memberIdx = f.memberIdx := by
  cases f <;> simp [map, memberIdx]

theorem members_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).members = f.members.map (·.map g) := by
  cases f <;> simp [map, members, Functor.map]

end LeanMutualRecFamily

/-! ## The containers of a family -/

namespace IPFunctorFacts

theorem at_map {α : Type} (F : α → IPFunctor) (ms : List α) (i : Nat) (m : α)
    (h : ms[i]? = some m) : IPFunctor.at (ms.map F) i = F m := by
  rw [IPFunctor.at, List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem at_map_of_le {α : Type} (F : α → IPFunctor) (ms : List α) (i : Nat)
    (h : ms.length ≤ i) : IPFunctor.at (ms.map F) i = IPFunctor.const PEmpty := by
  rw [IPFunctor.at, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none h]
  rfl

end IPFunctorFacts

namespace Ty

theorem toIPFMemberList_eq : ∀ ms : List (LeanFamMemberSchema Ty),
    toIPFMemberList ms = ms.map toIPFMember
  | [] => rfl
  | m :: ms => by simp only [toIPFMemberList, List.map_cons, toIPFMemberList_eq ms]

/-- The containers of a family are the containers of its members, in order. -/
theorem toIPFFamily_eq (f : LeanMutualRecFamily Ty) :
    toIPFFamily f = f.members.map toIPFMember := by
  cases f <;> simp [toIPFFamily, LeanMutualRecFamily.members, toIPFMemberList_eq]

theorem length_toIPFFamily (f : LeanMutualRecFamily Ty) :
    (toIPFFamily f).length = f.members.length := by
  rw [toIPFFamily_eq, List.length_map]

/-- The container of the member a family selects. -/
theorem at_toIPFFamily_memberIdx (f : LeanMutualRecFamily Ty) :
    IPFunctor.at (toIPFFamily f) f.memberIdx = toIPFMember f.current := by
  rw [toIPFFamily_eq]
  exact IPFunctorFacts.at_map _ _ _ _ f.getElem?_memberIdx

/-- **A value of member `j` of a family is a node of the family's W-type** rooted at
    `selIdx _ j` — for every `j`, in range or not. -/
theorem den_familyMemberTy (f : LeanMutualRecFamily Ty) (j : Nat) :
    Ty.Den (familyMemberTy f j) = FamW (toIPFFamily f) (selIdx (toIPFFamily f).length j) := by
  show FamW (toIPFFamily (f.select j)) (f.select j).memberIdx = _
  rw [LeanMutualRecFamily.memberIdx_select, toIPFFamily_eq (f.select j),
    LeanMutualRecFamily.members_select, ← toIPFFamily_eq, length_toIPFFamily]

/-! ## `famRoll`: an unfolded field is a shape with a value of a member in each hole -/

section
variable (M : Nat → Ty)

mutual

/-- A value of the tree `a` with each occurrence `Ty.familyMember j` read as the type
    `M j` is a shape of `a` with a value of `M j` in each hole of target `j`. -/
def famRoll : (a : Ty) → Ty.Den (substOcc .self M a) → (Ty.toIPF a).Obj (fun j => Ty.Den (M j))
  | .self, x => ⟨x, fun p => PEmpty.elim p⟩
  | .familyMember _, x => ⟨PUnit.unit, fun _ => x⟩
  | .shape s, x => famRollShape s x
  | .recTaggedUnion _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .recObject _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .recAlias _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .mutualRecursiveFamily _, x => ⟨x, fun p => PEmpty.elim p⟩

/-- `Ty.famRoll`, on a node. -/
def famRollShape : (s : TyShape Ty) → Ty.Den (.shape (substOccShape .self M s)) →
    (Ty.toIPFShape s).Obj (fun j => Ty.Den (M j))
  | .prim _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .fn _ b, f => IPFunctor.Obj.ofPi (fun y => famRoll b (f y))
  | .primCovariant c, x => famRollCov c x
  | .enum _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .record ⟨a, b, rest⟩, ⟨x, y, zs⟩ =>
      IPFunctor.Obj.pair (famRoll a x) (IPFunctor.Obj.pair (famRoll b y) (famRollList rest zs))
  | .taggedUnion l, ⟨t, v⟩ =>
      let r := famRollAt l t.val v
      ⟨⟨⟨t.val, length_substOccTU .self M l ▸ t.isLt⟩, r.1⟩, r.2⟩

/-- `Ty.famRoll`, on an array, a thunk or a lazy value. -/
def famRollCov : (c : LeanPrimTyCovariant Ty) →
    Ty.Den (.primCovariant (substOccCov .self M c)) → (Ty.toIPFCov c).Obj (fun j => Ty.Den (M j))
  | .array a, xs => IPFunctor.Obj.ofArray (fun x => famRoll a x) xs
  | .thunk a, x => famRoll a x
  | .lazy a, x => famRoll a x

/-- `Ty.famRoll`, on a list of trees. -/
def famRollList : (ts : List Ty) → Ty.DenList (substOccList .self M ts) →
    (Ty.toIPFList ts).Obj (fun j => Ty.Den (M j))
  | [], _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | a :: as, ⟨x, xs⟩ => IPFunctor.Obj.pair (famRoll a x) (famRollList as xs)

/-- `Ty.famRoll`, on the fields of constructor `t`. -/
def famRollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    Ty.DenAt (substOccTU .self M l) t → (Ty.toIPFAt l t).Obj (fun j => Ty.Den (M j))
  | .payloadFirst ⟨a, as⟩ _ _, 0, ⟨x, xs⟩ => IPFunctor.Obj.pair (famRoll a x) (famRollList as xs)
  | .payloadFirst _ next _, 1, v => famRollList next v
  | .payloadFirst _ _ rest, n + 2, v => famRollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => famRollAtCP rest n v

/-- `Ty.famRollAt`, on the constructors that follow a field-less one. -/
def famRollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    Ty.DenAtCP (substOccCP .self M c) t → (Ty.toIPFAtCP c t).Obj (fun j => Ty.Den (M j))
  | .here ⟨a, as⟩ _, 0, ⟨x, xs⟩ => IPFunctor.Obj.pair (famRoll a x) (famRollList as xs)
  | .here _ rest, n + 1, v => famRollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => famRollAtCP rest n v

/-- `Ty.famRollAt`, on a plain list of constructors. -/
def famRollAtList : (cs : List (List Ty)) → (t : Nat) →
    Ty.DenAtList (substOccCtors .self M cs) t → (Ty.toIPFAtList cs t).Obj (fun j => Ty.Den (M j))
  | [], _, v => PEmpty.elim v
  | fs :: _, 0, v => famRollList fs v
  | _ :: rest, n + 1, v => famRollAtList rest n v

end

/-! ## `famUnroll`: the other direction -/

mutual

/-- A shape of `a` with a value of `M j` in each hole of target `j` is a value of `a` with
    each occurrence `Ty.familyMember j` read as `M j`. -/
def famUnroll : (a : Ty) → (Ty.toIPF a).Obj (fun j => Ty.Den (M j)) → Ty.Den (substOcc .self M a)
  | .self, x => x.1
  | .familyMember _, x => x.2 PUnit.unit
  | .shape s, x => famUnrollShape s x
  | .recTaggedUnion _, x => x.1
  | .recObject _, x => x.1
  | .recAlias _, x => x.1
  | .mutualRecursiveFamily _, x => x.1

/-- `Ty.famUnroll`, on a node. -/
def famUnrollShape : (s : TyShape Ty) → (Ty.toIPFShape s).Obj (fun j => Ty.Den (M j)) →
    Ty.Den (.shape (substOccShape .self M s))
  | .prim _, x => x.1
  | .fn _ b, x => fun y => famUnroll b ⟨x.1 y, fun p => x.2 ⟨y, p⟩⟩
  | .primCovariant c, x => famUnrollCov c x
  | .enum _, x => x.1
  | .record ⟨a, b, rest⟩, x =>
      (famUnroll a x.prodFst, famUnroll b x.prodSnd.prodFst, famUnrollList rest x.prodSnd.prodSnd)
  | .taggedUnion l, x =>
      ⟨⟨x.1.1.val, (length_substOccTU .self M l).symm ▸ x.1.1.isLt⟩,
        famUnrollAt l x.1.1.val ⟨x.1.2, x.2⟩⟩

/-- `Ty.famUnroll`, on an array, a thunk or a lazy value. -/
def famUnrollCov : (c : LeanPrimTyCovariant Ty) →
    (Ty.toIPFCov c).Obj (fun j => Ty.Den (M j)) → Ty.Den (.primCovariant (substOccCov .self M c))
  | .array a, x => IPFunctor.Obj.toArray (fun y => famUnroll a y) x
  | .thunk a, x => famUnroll a x
  | .lazy a, x => famUnroll a x

/-- `Ty.famUnroll`, on a list of trees. -/
def famUnrollList : (ts : List Ty) → (Ty.toIPFList ts).Obj (fun j => Ty.Den (M j)) →
    Ty.DenList (substOccList .self M ts)
  | [], _ => PUnit.unit
  | a :: as, x => (famUnroll a x.prodFst, famUnrollList as x.prodSnd)

/-- `Ty.famUnroll`, on the fields of constructor `t`. -/
def famUnrollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    (Ty.toIPFAt l t).Obj (fun j => Ty.Den (M j)) → Ty.DenAt (substOccTU .self M l) t
  | .payloadFirst ⟨a, as⟩ _ _, 0, x => (famUnroll a x.prodFst, famUnrollList as x.prodSnd)
  | .payloadFirst _ next _, 1, x => famUnrollList next x
  | .payloadFirst _ _ rest, n + 2, x => famUnrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => famUnrollAtCP rest n x

/-- `Ty.famUnrollAt`, on the constructors that follow a field-less one. -/
def famUnrollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    (Ty.toIPFAtCP c t).Obj (fun j => Ty.Den (M j)) → Ty.DenAtCP (substOccCP .self M c) t
  | .here ⟨a, as⟩ _, 0, x => (famUnroll a x.prodFst, famUnrollList as x.prodSnd)
  | .here _ rest, n + 1, x => famUnrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => famUnrollAtCP rest n x

/-- `Ty.famUnrollAt`, on a plain list of constructors. -/
def famUnrollAtList : (cs : List (List Ty)) → (t : Nat) →
    (Ty.toIPFAtList cs t).Obj (fun j => Ty.Den (M j)) → Ty.DenAtList (substOccCtors .self M cs) t
  | [], _, x => PEmpty.elim x.1
  | fs :: _, 0, x => famUnrollList fs x
  | _ :: rest, n + 1, x => famUnrollAtList rest n x

end

end

/-! ## A member, and the introduction and one-level elimination of a family -/

/-- The values of one member of a family, given by its shape: a tagged union, a record or
    the body of a newtype. -/
@[reducible] def DenMember : LeanFamMemberSchema Ty → Type
  | .ctors l => Ty.DenTU l
  | .record fs => Ty.DenRecord fs
  | .alias b => Ty.Den b

/-- `Ty.substOcc`, on a member. -/
def substOccMember (s : Ty) (m : Nat → Ty) : LeanFamMemberSchema Ty → LeanFamMemberSchema Ty
  | .ctors l => .ctors (substOccTU s m l)
  | .record fs => .record (substOccRecord s m fs)
  | .alias b => .alias (substOcc s m b)

/-- `Ty.famRoll`, on a member. -/
def famRollMember (M : Nat → Ty) : (m : LeanFamMemberSchema Ty) →
    DenMember (substOccMember .self M m) → (Ty.toIPFMember m).Obj (fun j => Ty.Den (M j))
  | .ctors l, ⟨t, v⟩ =>
      let r := famRollAt M l t.val v
      ⟨⟨⟨t.val, length_substOccTU .self M l ▸ t.isLt⟩, r.1⟩, r.2⟩
  | .record ⟨a, b, rest⟩, ⟨x, y, zs⟩ =>
      IPFunctor.Obj.pair (famRoll M a x) (IPFunctor.Obj.pair (famRoll M b y) (famRollList M rest zs))
  | .alias b, x => famRoll M b x

/-- `Ty.famUnroll`, on a member. -/
def famUnrollMember (M : Nat → Ty) : (m : LeanFamMemberSchema Ty) →
    (Ty.toIPFMember m).Obj (fun j => Ty.Den (M j)) → DenMember (substOccMember .self M m)
  | .ctors l, x =>
      ⟨⟨x.1.1.val, (length_substOccTU .self M l).symm ▸ x.1.1.isLt⟩,
        famUnrollAt M l x.1.1.val ⟨x.1.2, x.2⟩⟩
  | .record ⟨a, b, rest⟩, x =>
      (famUnroll M a x.prodFst, famUnroll M b x.prodSnd.prodFst,
        famUnrollList M rest x.prodSnd.prodSnd)
  | .alias b, x => famUnroll M b x

/-- The member a family selects, unfolded in the scope of the family: what a value of it
    holds, with each occurrence of a member read as that member's type. -/
abbrev famCurrentUnfold (f : LeanMutualRecFamily Ty) : LeanFamMemberSchema Ty :=
  substOccMember .self (familyMemberTy f) f.current

/-- Carry a value of member `j` into the family's own W-type. -/
def famIn (f : LeanMutualRecFamily Ty) (j : Nat) (x : Ty.Den (familyMemberTy f j)) :
    FamW (toIPFFamily f) (selIdx (toIPFFamily f).length j) :=
  cast (den_familyMemberTy f j) x

/-- Carry a node of the family's W-type out as a value of member `j`. -/
def famOut (f : LeanMutualRecFamily Ty) (j : Nat)
    (x : FamW (toIPFFamily f) (selIdx (toIPFFamily f).length j)) :
    Ty.Den (familyMemberTy f j) :=
  cast (den_familyMemberTy f j).symm x

/-- **The introduction form** of a mutual family: a value of the member the family selects,
    with its fields *unfolded*. -/
def DenFam.mk (f : LeanMutualRecFamily Ty) (v : DenMember (famCurrentUnfold f)) :
    Ty.Den (.mutualRecursiveFamily f) :=
  FamW.mkAt f.memberIdx (toIPFMember f.current) (at_toIPFFamily_memberIdx f)
    ((famRollMember (familyMemberTy f) f.current v).map (famIn f))

/-- **One level of a value** of a mutual family: the value of the member it selects, with
    its fields unfolded, which is what a dispatch on it binds. -/
def DenFam.unfold (f : LeanMutualRecFamily Ty) (v : Ty.Den (.mutualRecursiveFamily f)) :
    DenMember (famCurrentUnfold f) :=
  famUnrollMember (familyMemberTy f) f.current
    ((FamW.nodeAt f.memberIdx (toIPFMember f.current) (at_toIPFFamily_memberIdx f) v).map
      (famOut f))

end Ty

/-! ## At the level of bundles

`LeanScript.Term` speaks of a family of bundles `f : LeanMutualRecFamily (TyWfIn (n + 2))`
and of the member it selects unfolded as `f.current.map (TyWfIn.unfoldFam f hwf)`, a
member of bundles.  Its trees are the unfolded member of the trees
(`TyWf.famCurrentUnfold_map_toTy`), so the two have the same values. -/

namespace TyWf

/-- The values of one member of a family of bundles. -/
@[reducible] def DenMember (m : LeanFamMemberSchema TyWf) : Type := Ty.DenMember (m.map TyWf.toTy)

variable {n : Nat}

/-- The trees of the unfolded member a family of bundles selects are the unfolded member
    of its trees. -/
theorem famCurrentUnfold_map_toTy (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) :
    (f.current.map (TyWfIn.unfoldFam f hwf)).map TyWf.toTy =
      Ty.famCurrentUnfold (f.map TyWfIn.toTy) := by
  simp only [Ty.famCurrentUnfold, LeanMutualRecFamily.current_map]
  cases f.current with
  | ctors l =>
      simp only [LeanFamMemberSchema.map, Ty.substOccMember, Ty.substOccTU_eq_map]
      congr 1
      show (_ <$> _ <$> l) = (_ <$> _ <$> l)
      rw [Functor.map_map, Functor.map_map]
      rfl
  | record fs =>
      simp only [LeanFamMemberSchema.map, Ty.substOccMember, Ty.substOccRecord_eq_map]
      congr 1
      show (_ <$> _ <$> fs) = (_ <$> _ <$> fs)
      rw [Functor.map_map, Functor.map_map]
      rfl
  | «alias» b => rfl

theorem denMember_famCurrentUnfold (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) :
    TyWf.DenMember (f.current.map (TyWfIn.unfoldFam f hwf)) =
      Ty.DenMember (Ty.famCurrentUnfold (f.map TyWfIn.toTy)) :=
  congrArg Ty.DenMember (famCurrentUnfold_map_toTy f hwf)

/-- **The introduction form** of a mutual family of bundles, from a value of the member it
    selects, unfolded. -/
def DenFam.mk (f : LeanMutualRecFamily (TyWfIn (n + 2))) (hwf : Ty.Wf (mutualRecursiveFamilyTy f))
    (v : TyWf.DenMember (f.current.map (TyWfIn.unfoldFam f hwf))) :
    TyWf.Den (mutualRecursiveFamily f hwf) :=
  Ty.DenFam.mk (f.map TyWfIn.toTy) (cast (denMember_famCurrentUnfold f hwf) v)

/-- **One level of a value** of a mutual family of bundles. -/
def DenFam.unfold (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (mutualRecursiveFamilyTy f)) (v : TyWf.Den (mutualRecursiveFamily f hwf)) :
    TyWf.DenMember (f.current.map (TyWfIn.unfoldFam f hwf)) :=
  cast (denMember_famCurrentUnfold f hwf).symm (Ty.DenFam.unfold (f.map TyWfIn.toTy) v)

end TyWf

/-! ## What a branch of the fold of a family binds

`LeanScript.Term.mutualRecursiveFamily_rec` folds a value by `IWType.memo`: the answer at
every node is computed once, bottom-up, and stored beside the node.  Its branches are
indexed by the members of the family as bundles (`ms₀`), so the fold runs over the W-type
of their containers, `famFs ms₀` — which is the W-type the value lives in
(`famFs_eq`).  A branch is evaluated at a node whose subtrees are *memos*, and the
environment it binds (`LeanScript.TyWf.famRecBinders`) is read off them: a field that is
literally `Ty.familyMember i` is the subtree **and** the answer stored at it, and every
other field is `Ty.famUnroll` of the field with the subtrees put back in its holes —
followed, when it holds occurrences of members inside it (`Array (familyMember i)`), by
`Ty.famUnroll` of the field with the *answers* stored at those subtrees put in its holes. -/

/-- The container of a member of a family of bundles. -/
@[reducible] def famIPF {n : Nat} (m : LeanFamMemberSchema (TyWfIn (n + 2))) : IPFunctor :=
  Ty.toIPFMember (m.map TyWfIn.toTy)

/-- The containers of the members of a family of bundles, in order. -/
abbrev famFs {n : Nat} (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))) : List IPFunctor :=
  ms₀.map famIPF

/-- A value of a family whose members are `ms₀`, with the answer of a fold of motive `τ`
    at every node, at member number `j`. -/
abbrev FamMemoAt {n : Nat} (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))) (τ : TyWf)
    (j : Nat) : Type :=
  FamMemo (famFs ms₀) (TyWf.Den τ) (selIdx (famFs ms₀).length j)

/-- A node of the fold of a family whose members are `ms₀`, at a constructor with fields
    `fs`: the fields' shape, with the memo of a subtree in each hole. -/
abbrev FamFields {n : Nat} (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))) (τ : TyWf)
    (fs : List (TyWfIn (n + 2))) : Type :=
  (Ty.toIPFList (fs.map TyWfIn.toTy)).Obj (FamMemoAt ms₀ τ)

/-- The containers of a family of bundles are the containers of its members. -/
theorem famFs_eq {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2))) :
    Ty.toIPFFamily (f.map TyWfIn.toTy) = famFs f.members := by
  rw [Ty.toIPFFamily_eq, LeanMutualRecFamily.members_map, List.map_map]
  rfl

/-- A value of a family of bundles is a node of the W-type of its members' containers. -/
theorem den_mutualRecursiveFamily {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) :
    TyWf.Den (TyWf.mutualRecursiveFamily f hwf) = FamW (famFs f.members) f.memberIdx := by
  show FamW (Ty.toIPFFamily (f.map TyWfIn.toTy)) (f.map TyWfIn.toTy).memberIdx = _
  rw [famFs_eq, LeanMutualRecFamily.memberIdx_map]

/-- A value of member `j` of a family of bundles is a node of the W-type of its members'
    containers. -/
theorem den_famMemberTy {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (j : Nat) :
    TyWf.Den (TyWf.famMemberTy f hwf j) = FamW (famFs f.members) (selIdx (famFs f.members).length j) := by
  show Ty.Den (Ty.familyMemberTy (f.map TyWfIn.toTy) j) = _
  rw [Ty.den_familyMemberTy, famFs_eq]

/-- The subtree at a hole, as a value of the member it holds. -/
def famSubtree {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (τ : TyWf) (j : Nat)
    (m : FamMemoAt f.members τ j) : TyWf.Den (TyWf.famMemberTy f hwf j) :=
  cast (den_famMemberTy f hwf j).symm (FamMemo.tree m)

/-- The value of a field that is not literally an occurrence of a member: the field
    unrolled, with the subtrees put back in its holes. -/
def famBindField {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (τ : TyWf) (a : TyWfIn (n + 2))
    (e : (Ty.toIPF a.toTy).Obj (FamMemoAt f.members τ)) :
    TyWf.Den (TyWfIn.unfoldFam f hwf a) :=
  Ty.famUnroll (Ty.familyMemberTy (f.map TyWfIn.toTy)) a.toTy
    (e.map (fun j m => famSubtree f hwf τ j m))

/-- The answers at the occurrences of members inside a field `a` that is not literally one:
    the field's shape with the answer stored at each subtree in its hole
    (`LeanScript.TyWf.famAnswerMap`). -/
def famAnswerField {n : Nat} (τ : TyWf) (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2))))
    (a : TyWfIn (n + 2)) (e : (Ty.toIPF a.toTy).Obj (FamMemoAt ms₀ τ)) :
    TyWf.Den (TyWf.famAnswerMap τ a) :=
  Ty.famUnroll (fun _ => τ.toTy) a.toTy (e.map (fun _ m => FamMemo.answer m))

/-- What a branch of the fold of a family binds after a field `a` that is not literally an
    occurrence of a member, in front of the environment `r` of the fields after it: the
    answers at the occurrences inside it (`famAnswerField`), when it holds any
    (`LeanScript.TyWf.famAnswerBinders`). -/
def famAnswerEnv {n : Nat} (τ : TyWf) (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2))))
    (a : TyWfIn (n + 2)) (e : (Ty.toIPF a.toTy).Obj (FamMemoAt ms₀ τ)) {rest : List TyWf}
    (r : TyWf.DenList rest) : TyWf.DenList (TyWf.famAnswerBinders τ a rest) :=
  Bool.casesOn (motive := fun b =>
      TyWf.DenList (cond b (TyWf.famAnswerMap τ a :: rest) rest))
    (Ty.hasMemberOcc a.toTy) r (famAnswerField τ ms₀ a e, r)

/-- The environment a branch of the fold of a family binds, at a constructor with fields
    `fs`. -/
def famBindEnv {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (τ : TyWf) :
    (fs : List (TyWfIn (n + 2))) → FamFields f.members τ fs →
      TyWf.DenList (TyWf.famRecBinders f hwf τ fs)
  | [], _ => PUnit.unit
  | ⟨.familyMember i, _⟩ :: fs, e =>
      let m : FamMemoAt f.members τ i := e.prodFst.2 PUnit.unit
      (famSubtree f hwf τ i m, FamMemo.answer m, famBindEnv f hwf τ fs e.prodSnd)
  | ⟨.self, h⟩ :: _, _ =>
      -- A family's payload holds no `Ty.self` (it is legal only in a scope of one member).
      absurd h (Ty.not_wfIn_self_of_family (by omega))
  | ⟨.shape sh, h⟩ :: fs, e =>
      (famBindField f hwf τ ⟨.shape sh, h⟩ e.prodFst,
        famAnswerEnv τ f.members ⟨.shape sh, h⟩ e.prodFst (famBindEnv f hwf τ fs e.prodSnd))
  | ⟨.recTaggedUnion l', h⟩ :: fs, e =>
      (famBindField f hwf τ ⟨.recTaggedUnion l', h⟩ e.prodFst,
        famAnswerEnv τ f.members ⟨.recTaggedUnion l', h⟩ e.prodFst
          (famBindEnv f hwf τ fs e.prodSnd))
  | ⟨.recObject r, h⟩ :: fs, e =>
      (famBindField f hwf τ ⟨.recObject r, h⟩ e.prodFst,
        famAnswerEnv τ f.members ⟨.recObject r, h⟩ e.prodFst
          (famBindEnv f hwf τ fs e.prodSnd))
  | ⟨.recAlias b, h⟩ :: fs, e =>
      (famBindField f hwf τ ⟨.recAlias b, h⟩ e.prodFst,
        famAnswerEnv τ f.members ⟨.recAlias b, h⟩ e.prodFst
          (famBindEnv f hwf τ fs e.prodSnd))
  | ⟨.mutualRecursiveFamily g, h⟩ :: fs, e =>
      (famBindField f hwf τ ⟨.mutualRecursiveFamily g, h⟩ e.prodFst,
        famAnswerEnv τ f.members ⟨.mutualRecursiveFamily g, h⟩ e.prodFst
          (famBindEnv f hwf τ fs e.prodSnd))

/-- The value in the hole of a field that is `Ty.familyMember i`. -/
def famHoleKid {X : Nat → Type} {i : Nat} (t : Ty) (h : t = .familyMember i)
    (x : (Ty.toIPF t).Obj X) : X i :=
  (h ▸ x : (Ty.toIPF (.familyMember i)).Obj X).2 PUnit.unit

/-- The memo of the subtree at the occurrence a deeper look descends into. -/
def famFieldMemo {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} {τ : TyWf}
    {i : Nat} : {fs : List (TyWfIn (n + 2))} → FamilyMemberField i fs → FamFields ms₀ τ fs →
    FamMemoAt ms₀ τ i
  | a :: _, .here h, e => famHoleKid a.toTy h e.prodFst
  | _ :: _, .there sf, e => famFieldMemo sf e.prodSnd

/-- The nodes a deeper look into a family has dispatched on above the one it stands at,
    innermost first: for each, its fields' shape with the memo of a subtree in each
    hole. -/
def FamFrames {n : Nat} (ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))) (τ : TyWf) :
    List (List (TyWfIn (n + 2))) → Type
  | [] => PUnit
  | fs :: outer => FamFields ms₀ τ fs × FamFrames ms₀ τ outer

/-- No node above: the frames at the root of the fold of a family. -/
def FamFrames.nil {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} {τ : TyWf} :
    FamFrames ms₀ τ [] :=
  PUnit.unit

/-- The memo of the subtree at an occurrence among the fields of a node above, which a
    deeper look (`LeanScript.FamilyFoldKBranch.deepOuter`) descends into. -/
def famOuterFieldMemo {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {τ : TyWf} {i : Nat} :
    {outer : List (List (TyWfIn (n + 2)))} → FamilyOuterMemberField i outer →
      FamFrames ms₀ τ outer → FamMemoAt ms₀ τ i
  | _ :: _, .here sf, fr => famFieldMemo sf fr.1
  | _ :: _, .there o, fr => famOuterFieldMemo o fr.2

theorem FamilyMemberAt.lt {n : Nat} {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {i : Nat} {m : LeanFamMemberSchema (TyWfIn (n + 2))} : FamilyMemberAt ms i m → i < ms.length
  | .here => by simp
  | .there h => by simpa using FamilyMemberAt.lt h

theorem FamilyMemberAt.at_map {n : Nat} {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {i : Nat} {m : LeanFamMemberSchema (TyWfIn (n + 2))} :
    FamilyMemberAt ms i m → IPFunctor.at (famFs ms) i = famIPF m
  | .here => rfl
  | .there h => by have e := FamilyMemberAt.at_map h; exact e

/-- The container of the member a deeper look names is the container of that member. -/
theorem FamilyMemberAt.at_famFs {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {i : Nat} {m : LeanFamMemberSchema (TyWfIn (n + 2))} (h : FamilyMemberAt ms₀ i m) :
    IPFunctor.at (famFs ms₀) (selIdx (famFs ms₀).length i) = famIPF m := by
  have hi : i < (famFs ms₀).length := by simpa using h.lt
  simp only [selIdx, hi, ↓reduceIte]
  exact h.at_map

end LeanScript

end
