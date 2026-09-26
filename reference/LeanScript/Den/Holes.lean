module

public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# What the scope discipline of `Ty.WfIn` buys the containers

`Ty.toPFunctor` and `Ty.toIPF` are defined on **every** tree, well formed or not, so each
of them has a case for the occurrence it is *not* about:

* `Ty.toPFunctor` (the container of a lone binder, whose holes are occurrences `Ty.self`)
  sends `Ty.familyMember j` to the empty constant, and it sends `Ty.self` to one hole even
  where there is no binder to fill it — in a closed type, or in a family;
* `Ty.toIPF` (the container of a family, whose holes are occurrences `Ty.familyMember j`)
  sends `Ty.self` to a constant.

The scope index of `Ty.WfIn` is what makes those cases dead.  This module says so about
the containers themselves:

* `Ty.noSelfHoles_of_wfIn`: a tree that is well formed in a scope that is **not** a lone
  binder's (`n ≠ 1`: a closed type, or the payload of a family) has **no `Ty.self` holes**.
  In particular (`Ty.noSelfHoles_of_wf`) a closed type has none, so the one-hole case of
  `Ty.self` never contributes to the denotation of a type.
* `Ty.noMemberHoles_of_wfIn`: a tree that is well formed in a scope that is **not** a
  family's (`n ≤ 1`: a closed type, or the payload of a lone binder) has **no
  `Ty.familyMember` holes** — the payload of `Ty.recTaggedUnion`, `Ty.recObject` or
  `Ty.recAlias` only ever recurses through `Ty.self`.

Neither is needed to *define* anything: the dead cases are given harmless values
instead (`PEmpty`, `PUnit`), which is what keeps `Ty.Den` structurally recursive and its
equations definitional.  These theorems are what justify that choice.
-/

namespace Ty

/-- The container `Ty.toPFunctor t` has no holes — every shape's type of holes is empty, in
    the sense of Mathlib's `IsEmpty`: `t` holds no occurrence `Ty.self` of an enclosing lone
    binder. -/
def NoSelfHoles (t : Ty) : Prop := ∀ a, IsEmpty ((Ty.toPFunctor t).B a)

/-- The indexed container `Ty.toIPF t` has no holes (every shape's type of holes is
    `IsEmpty`): `t` holds no occurrence `Ty.familyMember j` of an enclosing family. -/
def NoMemberHoles (t : Ty) : Prop := ∀ a, IsEmpty ((Ty.toIPF t).B a)

/-- A list of shapes has no holes when no shape has any. -/
theorem listPos_false {S : Type} {P : S → Type} (h : ∀ s, P s → False) :
    ∀ xs : List S, PFunctor.ListPos P xs → False
  | [], p => nomatch p
  | s :: _, .inl p => h s p
  | _ :: ss, .inr q => listPos_false h ss q

/-! ## No `Ty.self` holes -/

theorem noSelfHoles_list : ∀ ts : List Ty, (∀ t ∈ ts, NoSelfHoles t) →
    ∀ a, (Ty.toPFunctorList ts).B a → False
  | [], _, _, p => nomatch p
  | t :: _, h, a, .inl p => (h t (List.mem_cons_self ..) a.1).false p
  | _ :: ts, h, a, .inr p =>
      noSelfHoles_list ts (fun x hx => h x (List.mem_cons_of_mem _ hx)) a.2 p

theorem noSelfHoles_atList : ∀ cs : List (List Ty), (∀ t ∈ cs.flatten, NoSelfHoles t) →
    ∀ n a, (Ty.toPFunctorAtList cs n).B a → False
  | [], _, _, a, _ => nomatch a
  | fs :: _, h, 0, a, p =>
      noSelfHoles_list fs (fun x hx => h x (List.mem_flatten.2 ⟨fs, List.mem_cons_self .., hx⟩))
        a p
  | fs :: rest, h, n + 1, a, p =>
      noSelfHoles_atList rest (fun x hx => h x (by
        rw [List.flatten_cons]; exact List.mem_append_right _ hx)) n a p

theorem noSelfHoles_atCP : ∀ c : CtorsWithPayload Ty, (∀ t ∈ c.toList.flatten, NoSelfHoles t) →
    ∀ n a, (Ty.toPFunctorAtCP c n).B a → False
  | .here ⟨f, fs⟩ _, h, 0, a, p =>
      noSelfHoles_list (f :: fs) (fun x hx => h x (by
        simp only [CtorsWithPayload.toList, List.flatten_cons]
        exact List.mem_append_left _ hx)) a p
  | .here _ rest, h, n + 1, a, p =>
      noSelfHoles_atList rest (fun x hx => h x (by
        simp only [CtorsWithPayload.toList, List.flatten_cons]
        exact List.mem_append_right _ hx)) n a p
  | .skip _, _, 0, _, p => nomatch p
  | .skip rest, h, n + 1, a, p =>
      noSelfHoles_atCP rest (fun x hx => h x (by
        simpa [CtorsWithPayload.toList] using hx)) n a p

theorem noSelfHoles_at : ∀ l : LeanTaggedUnionSchema Ty, (∀ t ∈ l.toList.flatten, NoSelfHoles t) →
    ∀ n a, (Ty.toPFunctorAt l n).B a → False
  | .payloadFirst ⟨f, fs⟩ _ _, h, 0, a, p =>
      noSelfHoles_list (f :: fs) (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_left _ hx)) a p
  | .payloadFirst _ next _, h, 1, a, p =>
      noSelfHoles_list next (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_left _ hx))) a p
  | .payloadFirst _ _ rest, h, n + 2, a, p =>
      noSelfHoles_atList rest (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_right _ hx))) n a p
  | .skip _, _, 0, _, p => nomatch p
  | .skip rest, h, n + 1, a, p =>
      noSelfHoles_atCP rest (fun x hx => h x (by
        simpa [LeanTaggedUnionSchema.toList] using hx)) n a p

/-- **Only a lone binder's payload holds `Ty.self`.**  A tree that is well formed in a
    scope of `n ≠ 1` members — a closed type (`n = 0`) or a field of a family (`n ≥ 2`) —
    has no holes in `Ty.toPFunctor`: the case of `Ty.toPFunctor` that gives `Ty.self` a
    hole is never reached from it. -/
theorem noSelfHoles_of_wfIn {n : Nat} {t : Ty} (h : WfIn n t) (hn : n ≠ 1) :
    NoSelfHoles t := by
  induction h using Ty.WfIn.rec
    (motive_2 := fun n s _ => n ≠ 1 → ∀ a, (Ty.toPFunctorShape s).B a → False)
    (motive_3 := fun n ts _ => n ≠ 1 → ∀ t ∈ ts, NoSelfHoles t) with
  | closed _ ih => exact ih (by decide)
  | self => exact absurd rfl hn
  | familyMember _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | shape _ ih => exact fun a => ⟨ih hn a⟩
  | recTaggedUnion _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | recObject _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | recAlias _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | mutualRecursiveFamily _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | prim => rename_i _ _ p; exact nomatch p
  | enum => rename_i _ _ p; exact nomatch p
  | fn _ _ _ ihb => rename_i hn f p; exact (ihb hn (f p.1)).false p.2
  | @primCovariant _ c _ ih =>
      rename_i hn a p
      cases c with
      | array _ => exact listPos_false (fun s => (ih hn s).false) _ p
      | thunk _ => exact (ih hn a).false p
      | lazy _ => exact (ih hn a).false p
  | @record _ fs _ ih =>
      rename_i hn a p
      cases fs with
      | mk x y rest => exact noSelfHoles_list (x :: y :: rest) (ih hn) a p
  | @taggedUnion _ l _ ih =>
      rename_i hn a p
      exact noSelfHoles_at l (ih hn) a.1.val a.2 p
  | nil => rename_i _ ht; exact absurd ht List.not_mem_nil
  | cons _ _ ih1 ih2 =>
      rename_i hn x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ih1 hn
      · exact ih2 hn x hx

/-- **A closed type has no `Ty.self` holes**: its container is a constant one, and its
    values `Ty.Den t` are exactly the extension of that container at any type. -/
theorem noSelfHoles_of_wf {t : Ty} (h : Wf t) : NoSelfHoles t :=
  noSelfHoles_of_wfIn h (by decide)

/-- **A field of a family holds no `Ty.self`.** -/
theorem noSelfHoles_of_family {n : Nat} {t : Ty} (h : WfIn (n + 2) t) : NoSelfHoles t :=
  noSelfHoles_of_wfIn h (by omega)

/-! ## No `Ty.familyMember` holes -/

theorem noMemberHoles_list : ∀ ts : List Ty, (∀ t ∈ ts, NoMemberHoles t) →
    ∀ a, (Ty.toIPFList ts).B a → False
  | [], _, _, p => nomatch p
  | t :: _, h, a, .inl p => (h t (List.mem_cons_self ..) a.1).false p
  | _ :: ts, h, a, .inr p =>
      noMemberHoles_list ts (fun x hx => h x (List.mem_cons_of_mem _ hx)) a.2 p

theorem noMemberHoles_atList : ∀ cs : List (List Ty), (∀ t ∈ cs.flatten, NoMemberHoles t) →
    ∀ n a, (Ty.toIPFAtList cs n).B a → False
  | [], _, _, a, _ => nomatch a
  | fs :: _, h, 0, a, p =>
      noMemberHoles_list fs
        (fun x hx => h x (List.mem_flatten.2 ⟨fs, List.mem_cons_self .., hx⟩)) a p
  | fs :: rest, h, n + 1, a, p =>
      noMemberHoles_atList rest (fun x hx => h x (by
        rw [List.flatten_cons]; exact List.mem_append_right _ hx)) n a p

theorem noMemberHoles_atCP : ∀ c : CtorsWithPayload Ty,
    (∀ t ∈ c.toList.flatten, NoMemberHoles t) → ∀ n a, (Ty.toIPFAtCP c n).B a → False
  | .here ⟨f, fs⟩ _, h, 0, a, p =>
      noMemberHoles_list (f :: fs) (fun x hx => h x (by
        simp only [CtorsWithPayload.toList, List.flatten_cons]
        exact List.mem_append_left _ hx)) a p
  | .here _ rest, h, n + 1, a, p =>
      noMemberHoles_atList rest (fun x hx => h x (by
        simp only [CtorsWithPayload.toList, List.flatten_cons]
        exact List.mem_append_right _ hx)) n a p
  | .skip _, _, 0, _, p => nomatch p
  | .skip rest, h, n + 1, a, p =>
      noMemberHoles_atCP rest (fun x hx => h x (by
        simpa [CtorsWithPayload.toList] using hx)) n a p

theorem noMemberHoles_at : ∀ l : LeanTaggedUnionSchema Ty,
    (∀ t ∈ l.toList.flatten, NoMemberHoles t) → ∀ n a, (Ty.toIPFAt l n).B a → False
  | .payloadFirst ⟨f, fs⟩ _ _, h, 0, a, p =>
      noMemberHoles_list (f :: fs) (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_left _ hx)) a p
  | .payloadFirst _ next _, h, 1, a, p =>
      noMemberHoles_list next (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_left _ hx))) a p
  | .payloadFirst _ _ rest, h, n + 2, a, p =>
      noMemberHoles_atList rest (fun x hx => h x (by
        simp only [LeanTaggedUnionSchema.toList, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_right _ hx))) n a p
  | .skip _, _, 0, _, p => nomatch p
  | .skip rest, h, n + 1, a, p =>
      noMemberHoles_atCP rest (fun x hx => h x (by
        simpa [LeanTaggedUnionSchema.toList] using hx)) n a p

/-- **Only a family's payload holds `Ty.familyMember`.**  A tree that is well formed in a
    scope of at most one member — a closed type, or a field of the payload of
    `Ty.recTaggedUnion`, `Ty.recObject` or `Ty.recAlias` — has no holes in `Ty.toIPF`. -/
theorem noMemberHoles_of_wfIn {n : Nat} {t : Ty} (h : WfIn n t) (hn : n ≤ 1) :
    NoMemberHoles t := by
  induction h using Ty.WfIn.rec
    (motive_2 := fun n s _ => n ≤ 1 → ∀ a, (Ty.toIPFShape s).B a → False)
    (motive_3 := fun n ts _ => n ≤ 1 → ∀ t ∈ ts, NoMemberHoles t) with
  | closed _ ih => exact ih (by decide)
  | self => exact fun _ => ⟨fun p => nomatch p⟩
  | familyMember h2 _ => exact absurd hn (by omega)
  | shape _ ih => exact fun a => ⟨ih hn a⟩
  | recTaggedUnion _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | recObject _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | recAlias _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | mutualRecursiveFamily _ _ _ _ => exact fun _ => ⟨fun p => nomatch p⟩
  | prim => rename_i _ _ p; exact nomatch p
  | enum => rename_i _ _ p; exact nomatch p
  | fn _ _ _ ihb => rename_i hn f p; exact (ihb hn (f p.1)).false p.2
  | @primCovariant _ c _ ih =>
      rename_i hn a p
      cases c with
      | array _ => exact listPos_false (fun s => (ih hn s).false) _ p
      | thunk _ => exact (ih hn a).false p
      | lazy _ => exact (ih hn a).false p
  | @record _ fs _ ih =>
      rename_i hn a p
      cases fs with
      | mk x y rest => exact noMemberHoles_list (x :: y :: rest) (ih hn) a p
  | @taggedUnion _ l _ ih =>
      rename_i hn a p
      exact noMemberHoles_at l (ih hn) a.1.val a.2 p
  | nil => rename_i _ ht; exact absurd ht List.not_mem_nil
  | cons _ _ ih1 ih2 =>
      rename_i hn x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ih1 hn
      · exact ih2 hn x hx

/-- **A field of a lone binder's payload holds no `Ty.familyMember`.** -/
theorem noMemberHoles_of_binder {t : Ty} (h : WfIn 1 t) : NoMemberHoles t :=
  noMemberHoles_of_wfIn h (by decide)

/-- **A closed type has no `Ty.familyMember` holes.** -/
theorem noMemberHoles_of_wf {t : Ty} (h : Wf t) : NoMemberHoles t :=
  noMemberHoles_of_wfIn h (by decide)

end Ty

end LeanScript

end
