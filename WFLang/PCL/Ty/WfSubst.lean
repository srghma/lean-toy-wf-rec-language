module

public import LeanScript.Ty.Wf
public import LeanScript.Ty.WfFacts
public import LeanScript.Ty.Unfold

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# Unfolding a binder keeps every field a type

The payload of a recursive binder is written in the scope that binder opens, so a field of
it — `Ty.self`, or a tree that mentions it — is **not** a type of the language on its own.
What a value of that field is is the field *unfolded*: `Ty.self` replaced by the binder
itself (`LeanScript.Ty.unfoldSelf`).

This module is the proof that unfolding gives types: substituting a **closed** type for the
occurrences of a tree that is well formed in the scope of one binder gives a tree that is
well formed in the closed scope (`Ty.wf_substOcc`).  It is what lets the introduction and
elimination forms of a recursive shape state their fields as types of the language — a
`LeanScript.TyWf` each — rather than as bare trees with a side condition.

The proof is one induction over the three mutually inductive families of
`LeanScript.Ty.Wf`, with one motive each.  Two cases carry it:

* the **domain of a function** is checked in the closed scope already, so the induction
  hypothesis for it is the conclusion;
* a **nested binder** is left alone by the substitution, and its rule proves it well formed
  in *every* scope, so there is nothing to substitute and nothing to prove.
-/

namespace Ty

/-! ## One constructor of a list of lists -/

/-- One entry of a list of lists whose concatenation is all types is all types: this is
    how the fields of *one* constructor are read off the condition a schema states about
    all of them at once. -/
theorem WfAllIn.of_flatten {n : Nat} {xss : List (List Ty)} {i : Nat}
    (h : WfAllIn n xss.flatten) (hi : i < xss.length) : WfAllIn n xss[i] :=
  WfAllIn.iff_forall.2 fun _ ht =>
    WfAllIn.iff_forall.1 h _ (List.mem_flatten.2 ⟨_, List.getElem_mem hi, ht⟩)

/-! ## Substitution -/

/-- **A closed type put in for the occurrences of a tree keeps it a type.**  `t` is well
    formed in the scope of one binder — so its only occurrence leaf is `Ty.self` — and `S`
    is a closed type, so `t` with `S` for `Ty.self` is a closed type.

    A tree that is closed already (`n = 0`) is a special case: the substitution does not
    change it, and the statement says it is still a type. -/
theorem wf_substOcc {S : Ty} (hS : Wf S) {m : Nat → Ty} :
    ∀ {n : Nat} {t : Ty}, WfIn n t → n ≤ 1 → WfIn 0 (substOcc S m t) := by
  intro n t ht
  induction ht using Ty.WfIn.rec
    (motive_2 := fun n s _ => n ≤ 1 → WfShapeIn 0 (substOccShape S m s))
    (motive_3 := fun n ts _ => n ≤ 1 → WfAllIn 0 (substOccList S m ts)) with
  | closed _ ih => (try intro _); exact ih (by omega)
  | self => (try intro _); exact hS
  | familyMember h2 _ => (try intro _); exact absurd h2 (by omega)
  | shape _ ih => (try intro _); exact .shape (ih (by assumption))
  | recTaggedUnion hw ho hh => (try intro _); exact .recTaggedUnion hw ho hh
  | recObject hw ho hh => (try intro _); exact .recObject hw ho hh
  | recAlias hw ho hh => (try intro _); exact .recAlias hw ho hh
  | mutualRecursiveFamily hw ho hh =>
      (try intro _); exact .mutualRecursiveFamily hw ho hh
  | prim => exact .prim
  | enum => exact .enum
  | fn ha _ _ ihb =>
      exact .fn ha (ihb (by assumption))
  | @primCovariant _ s _ ih =>
      cases s with
      | array _ => exact .primCovariant (ih (by assumption))
      | thunk _ => exact .primCovariant (ih (by assumption))
      | lazy _ => exact .primCovariant (ih (by assumption))
  | @record _ fs _ ih =>
      have h := ih (by assumption)
      cases fs with
      | mk a b rest => exact .record h
  | @taggedUnion _ l _ ih =>
      have h := ih (by assumption)
      refine .taggedUnion ?_
      have hflat : (substOccTU S m l).toList.flatten =
          substOccList S m l.toList.flatten := by
        simp only [substOccTU_eq_map, LeanTaggedUnionSchema.toList_map,
          substOccList_eq_map, List.map_flatten]
      rw [hflat]
      exact h
  | nil => exact .nil
  | @cons _ _ _ _ _ ih1 ih2 =>
      exact .cons (ih1 (by assumption)) (ih2 (by assumption))

/-- **The same, for a mutual family.**  A tree written in the scope of a family — where
    the occurrence leaves are `Ty.familyMember i` and `Ty.self` is illegal, which is why
    the scope is not `1` — becomes a closed type when every member of the family is put in
    for its occurrences. -/
theorem wf_substOccFam {S : Ty} {m : Nat → Ty} (hm : ∀ i, Wf (m i)) :
    ∀ {n : Nat} {t : Ty}, WfIn n t → n ≠ 1 → WfIn 0 (substOcc S m t) := by
  intro n t ht
  induction ht using Ty.WfIn.rec
    (motive_2 := fun n s _ => n ≠ 1 → WfShapeIn 0 (substOccShape S m s))
    (motive_3 := fun n ts _ => n ≠ 1 → WfAllIn 0 (substOccList S m ts)) with
  | closed _ ih => (try intro _); exact ih (by omega)
  | self => (try intro _); exact absurd rfl (by assumption)
  | familyMember _ _ => (try intro _); exact hm _
  | shape _ ih => (try intro _); exact .shape (ih (by assumption))
  | recTaggedUnion hw ho hh => (try intro _); exact .recTaggedUnion hw ho hh
  | recObject hw ho hh => (try intro _); exact .recObject hw ho hh
  | recAlias hw ho hh => (try intro _); exact .recAlias hw ho hh
  | mutualRecursiveFamily hw ho hh =>
      (try intro _); exact .mutualRecursiveFamily hw ho hh
  | prim => exact .prim
  | enum => exact .enum
  | fn ha _ _ ihb =>
      exact .fn ha (ihb (by assumption))
  | @primCovariant _ s _ ih =>
      cases s with
      | array _ => exact .primCovariant (ih (by assumption))
      | thunk _ => exact .primCovariant (ih (by assumption))
      | lazy _ => exact .primCovariant (ih (by assumption))
  | @record _ fs _ ih =>
      have h := ih (by assumption)
      cases fs with
      | mk a b rest => exact .record h
  | @taggedUnion _ l _ ih =>
      have h := ih (by assumption)
      refine .taggedUnion ?_
      have hflat : (substOccTU S m l).toList.flatten =
          substOccList S m l.toList.flatten := by
        simp only [substOccTU_eq_map, LeanTaggedUnionSchema.toList_map,
          substOccList_eq_map, List.map_flatten]
      rw [hflat]
      exact h
  | nil => exact .nil
  | @cons _ _ _ _ _ ih1 ih2 =>
      exact .cons (ih1 (by assumption)) (ih2 (by assumption))

/-- Unfolding one field of a binder gives a type: the special case of `Ty.wf_substOcc`
    the recursive shapes use. -/
theorem wf_unfoldSelf {S t : Ty} (hS : Wf S) (ht : WfIn 1 t) : Wf (unfoldSelf S t) :=
  wf_substOcc hS ht (by omega)

/-- Unfolding a list of fields gives types. -/
theorem wfAllIn_substOccList {S : Ty} (hS : Wf S) {m : Nat → Ty} :
    ∀ {ts : List Ty}, WfAllIn 1 ts → WfAllIn 0 (substOccList S m ts)
  | [], _ => .nil
  | _ :: _, .cons h hs =>
      .cons (wf_substOcc hS h (by omega)) (wfAllIn_substOccList hS hs)

/-! ## The payload of each recursive shape

Each of the three lone binders states a condition about its payload *as a whole*; what an
introduction form needs is the condition on the fields of the one constructor it builds,
unfolded.  These are that step. -/

/-- The fields of one constructor of a recursive tagged union, **unfolded**, are types. -/
theorem wfAllIn_recTaggedUnionUnfold {l : LeanTaggedUnionSchema Ty}
    (h : Wf (.recTaggedUnion l)) (t : Nat) (ht : t < (recTaggedUnionUnfold l).length) :
    WfAllIn 0 ((recTaggedUnionUnfold l).get t ht) := by
  have hlen : t < l.length := by
    simpa [recTaggedUnionUnfold, LeanTaggedUnionSchema.length_map] using ht
  have hfields : WfAllIn 1 (l.get t hlen) := by
    have := WfAllIn.of_flatten (n := 1) (xss := l.toList) (i := t)
      (occursIn_of_wfIn_recTaggedUnion h).1 (by simpa using hlen)
    simpa [LeanTaggedUnionSchema.get] using this
  have hmap : (recTaggedUnionUnfold l).get t ht =
      (l.get t hlen).map (unfoldSelf (.recTaggedUnion l)) :=
    LeanTaggedUnionSchema.get_map _ l t hlen
  rw [hmap]
  have hsub := wfAllIn_substOccList (S := .recTaggedUnion l) (m := .familyMember) h hfields
  rwa [substOccList_eq_map] at hsub

/-- The fields of a recursive record, **unfolded**, are types. -/
theorem wfAllIn_recObjectUnfold {fs : LeanRecordSchema Ty} (h : Wf (.recObject fs)) :
    WfAllIn 0 (recObjectUnfold fs).toList := by
  have hmap : (recObjectUnfold fs).toList =
      fs.toList.map (unfoldSelf (.recObject fs)) :=
    LeanRecordSchema.toList_map _ fs
  rw [hmap]
  have hsub := wfAllIn_substOccList (S := .recObject fs) (m := .familyMember) h
    (occursIn_of_wfIn_recObject h).1
  rwa [substOccList_eq_map] at hsub

/-- The body of a recursive newtype, **unfolded**, is a type. -/
theorem wf_recAliasUnfold {b : Ty} (h : Wf (.recAlias b)) : Wf (recAliasUnfold b) :=
  wf_unfoldSelf (S := .recAlias b) h (occursIn_of_wfIn_recAlias h).1

/-! ## A member of a mutual family is a type

`LeanScript.Ty.familyMemberTy f i` is the type of member `i` of the family `f`: the same
family, with that member selected.  Selecting a member changes nothing a family's
well-formedness speaks about — the members, and the types they hold, are the same list —
so every member of a family that is a type is a type, which is what unfolding the scope of
a family needs. -/

/-- Selecting a member of a list of members keeps the list: the zipper `ofMembers?` builds
    is the list it was given. -/
theorem _root_.LeanScript.LeanMutualRecFamily.members_ofMembers? {α : Type}
    {ms : List (LeanFamMemberSchema α)} {i : Nat} {f : LeanMutualRecFamily α}
    (h : LeanMutualRecFamily.ofMembers? ms i = some f) : f.members = ms := by
  unfold LeanMutualRecFamily.ofMembers? at h
  split at h
  · exact absurd h (by simp)
  · rename_i m hi
    have hlt : i < ms.length := by
      cases Nat.lt_or_ge i ms.length with
      | inl h' => exact h'
      | inr h' =>
          rw [List.getElem?_eq_none_iff.mpr h'] at hi
          simp at hi
    have hget : ms[i] = m := by
      rw [List.getElem?_eq_getElem hlt] at hi
      exact Option.some.inj hi
    have hsplit : ms.take i ++ m :: ms.drop (i + 1) = ms := by
      rw [← hget, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
    split at h
    · rename_i next after hd
      split at h
      · injection h with h
        subst h
        rw [hd] at hsplit
        simpa [LeanMutualRecFamily.members] using hsplit
      · exact absurd h (by simp)
    · rename_i hd
      cases hb : ms.take i with
      | nil => simp [hb] at h
      | cons first bs =>
          simp only [hb, Option.some.injEq] at h
          subst h
          rw [hb, hd] at hsplit
          simpa [LeanMutualRecFamily.members] using hsplit

/-- Selecting a member keeps the members of a family. -/
theorem _root_.LeanScript.LeanMutualRecFamily.members_select {α : Type}
    (f : LeanMutualRecFamily α) (i : Nat) : (f.select i).members = f.members := by
  unfold LeanMutualRecFamily.select
  split
  · rename_i g h
    exact LeanMutualRecFamily.members_ofMembers? h
  · cases h : LeanMutualRecFamily.ofMembers? f.members 0 with
    | none => rfl
    | some g => exact LeanMutualRecFamily.members_ofMembers? h

/-- Every member of a family that is a type is a type. -/
theorem wf_familyMemberTy {f : LeanMutualRecFamily Ty}
    (h : Wf (.mutualRecursiveFamily f)) (i : Nat) : Wf (familyMemberTy f i) := by
  obtain ⟨hw, ho, hh⟩ := (wfHere_of_wfIn h).elim id id
  refine .mutualRecursiveFamily ?_ ?_ ?_ <;>
    simp only [familyTys, LeanMutualRecFamily.members_select] at hw ho hh ⊢
  · exact hw
  · exact ho
  · exact hh

/-! ## What a branch of a fold binds

`LeanScript.Ty.recBinders` is the fields of a constructor, unfolded, with the value of the
fold interleaved after each field that is an occurrence of the type being folded over.
Every one of them is a type: a field is one by the theorems above, an occurrence stands for
the binder itself, and the value of the fold has the type the fold answers. -/

/-- The binders of a branch of a fold over a lone binder are all types. -/
theorem wfAllIn_recBinders {r motive : Ty} (hr : Wf r) (hm : Wf motive) :
    ∀ {fs : List Ty}, WfAllIn 1 fs → WfAllIn 0 (recBinders r motive fs)
  | [], _ => .nil
  | .self :: _, .cons _ hs => .cons hr (.cons hm (wfAllIn_recBinders hr hm hs))
  | .familyMember _ :: _, .cons h _ => absurd h not_wfIn_one_familyMember
  | .shape _ :: _, .cons h hs =>
      .cons (wf_unfoldSelf hr h) (wfAllIn_recBinders hr hm hs)
  | .recTaggedUnion _ :: _, .cons h hs =>
      .cons (wf_unfoldSelf hr h) (wfAllIn_recBinders hr hm hs)
  | .recObject _ :: _, .cons h hs =>
      .cons (wf_unfoldSelf hr h) (wfAllIn_recBinders hr hm hs)
  | .recAlias _ :: _, .cons h hs =>
      .cons (wf_unfoldSelf hr h) (wfAllIn_recBinders hr hm hs)
  | .mutualRecursiveFamily _ :: _, .cons h hs =>
      .cons (wf_unfoldSelf hr h) (wfAllIn_recBinders hr hm hs)

end Ty

end LeanScript

end
