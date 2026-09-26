module

public import LeanScript.Ty.Wf

@[expose] public section

namespace LeanScript

/-!
# What `Ty.Wf` rules out, proved

`LeanScript.Ty.Wf` is an inductive proposition, so "the tactic refuses this tree" and
"this tree is not a type" are two different statements.  `TyTests/WfTest.lean` pins
the first; this module proves the second, for each mistake the earlier representations of
the type language were found to make.

Everything here is an inversion result: a derivation of `Ty.WfIn n t` can only have ended
with the rule for `t`'s own constructor, possibly after some number of `Ty.WfIn.closed`
steps, and `Ty.WfHere` says what that rule gives.  `Ty.wfHere_of_wfIn` is the one
induction in the file; the rest are corollaries of it and of `cases` on an occurrence.

## Values and positivity

The last two sections prove that a well-formed tree describes a type that *has values*
and contains no negative occurrence: `Ty.not_wf_recAlias_self` and
`Ty.not_wf_recAlias_negative`.  Both used to be the other way round — the two trees were
`Ty.Wf`, and excluding them was left to the front end, which is not enough, since Lean
itself accepts `inductive Bad | mk : Bad → Bad`.  `Ty.WfIn` now carries an inhabitation
condition (`Ty.HabIn`) and checks the domain of an arrow in the closed scope, and the two
theorems below are the proofs that those conditions bite.
-/

namespace Ty

/-! ## Inversion

A derivation of `Ty.WfIn n t` ends with the rule for `t`'s constructor, at scope `n` or —
if it went through `Ty.WfIn.closed` — at scope `0`.  `Ty.WfHere n t` is what that rule
gives; note that for a binder it does not mention `n` at all, since a binder is well
formed in every scope. -/

/-- What the last non-`Ty.WfIn.closed` rule of a derivation of `Ty.WfIn n t` provides. -/
def WfHere (n : Nat) : Ty → Prop
  | .self => n = 1
  | .familyMember i => 2 ≤ n ∧ i < n
  | .shape s => WfShapeIn n s
  | .recTaggedUnion l =>
      WfAllIn 1 l.toList.flatten ∧ OccursSomeIn 0 l.toList.flatten ∧ HabSomeIn [] l.toList
  | .recObject fs =>
      WfAllIn 1 fs.toList ∧ OccursSomeIn 0 fs.toList ∧ HabAllIn [] fs.toList
  | .recAlias b => WfIn 1 b ∧ OccursIn 0 b ∧ HabIn [] b
  | .mutualRecursiveFamily f =>
      WfAllIn f.members.length (familyTys f) ∧ MembersOccur f.members.length (familyTys f) ∧
        FamHab f.members

/-- Inversion for `Ty.WfIn`: the scope is either the one the last rule was applied at, or
    `0` because the tree was closed. -/
theorem wfHere_of_wfIn {n : Nat} {t : Ty} (h : WfIn n t) : WfHere n t ∨ WfHere 0 t := by
  induction h using Ty.WfIn.rec
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True) with
  | closed _ ih => exact Or.inr (ih.elim id id)
  | self => exact Or.inl rfl
  | familyMember h1 h2 => exact Or.inl ⟨h1, h2⟩
  | shape h _ => exact Or.inl h
  | recTaggedUnion h1 h2 h3 _ => exact Or.inl ⟨h1, h2, h3⟩
  | recObject h1 h2 h3 _ => exact Or.inl ⟨h1, h2, h3⟩
  | recAlias h1 h2 h3 _ => exact Or.inl ⟨h1, h2, h3⟩
  | mutualRecursiveFamily h1 h2 h3 _ => exact Or.inl ⟨h1, h2, h3⟩
  | _ => trivial

/-! ## An occurrence needs a scope that has it

The two occurrence leaves cannot be confused for one another, and neither can be written
outside a binder.  In the two-language representation these were the same token told
apart by nesting depth, so a member number captured by a non-mutual binder was accepted
with a silently different meaning; here `Ty.self` is a type only in a scope of exactly one
member and `Ty.familyMember i` only in a family that has member `i`. -/

/-- `Ty.self` is a type only in the scope of a binder that recurses on its own. -/
theorem scope_of_wfIn_self {n : Nat} (h : WfIn n .self) : n = 1 := by
  rcases wfHere_of_wfIn h with h | h
  · exact h
  · exact absurd (show (0 : Nat) = 1 from h) (by omega)

/-- A tree that is nothing but an occurrence is not a closed type. -/
theorem not_wf_self : ¬ Wf .self := fun h => by
  have := scope_of_wfIn_self h; omega

/-- `Ty.self` cannot be captured by the binder of a mutual family: a family of `n ≥ 2`
    members has no unnumbered member to point at. -/
theorem not_wfIn_self_of_family {n : Nat} (hn : 2 ≤ n) : ¬ WfIn n .self := fun h => by
  have := scope_of_wfIn_self h; omega

/-- A member occurrence is a type only in a family that has that member. -/
theorem bounds_of_wfIn_familyMember {n i : Nat} (h : WfIn n (.familyMember i)) :
    2 ≤ n ∧ i < n := by
  rcases wfHere_of_wfIn h with h | h
  · exact h
  · exact absurd h.1 (by omega)

/-- A member occurrence is not a closed type. -/
theorem not_wf_familyMember {i : Nat} : ¬ Wf (.familyMember i) := fun h => by
  have := (bounds_of_wfIn_familyMember h).1; omega

/-- A member occurrence cannot be captured by a binder that recurses on its own: the
    silent scope confusion of the two-language representation is not expressible. -/
theorem not_wfIn_one_familyMember {i : Nat} : ¬ WfIn 1 (.familyMember i) := fun h => by
  have := (bounds_of_wfIn_familyMember h).1; omega

/-- A member number out of range is not a type: member `i` of a family of `n ≤ i`
    members cannot be written. -/
theorem not_wfIn_familyMember_of_le {n i : Nat} (hi : n ≤ i) :
    ¬ WfIn n (.familyMember i) := fun h => by
  have := (bounds_of_wfIn_familyMember h).2; omega

/-! ## A recursive binder is really recursive -/

/-- A recursive newtype mentions itself. -/
theorem occursIn_of_wfIn_recAlias {n : Nat} {b : Ty} (h : WfIn n (.recAlias b)) :
    WfIn 1 b ∧ OccursIn 0 b := by
  have h := (wfHere_of_wfIn h).elim id id
  exact ⟨h.1, h.2.1⟩

/-- A recursive record mentions itself. -/
theorem occursIn_of_wfIn_recObject {n : Nat} {fs : LeanRecordSchema Ty}
    (h : WfIn n (.recObject fs)) : WfAllIn 1 fs.toList ∧ OccursSomeIn 0 fs.toList := by
  have h := (wfHere_of_wfIn h).elim id id
  exact ⟨h.1, h.2.1⟩

/-- A recursive sum mentions itself. -/
theorem occursIn_of_wfIn_recTaggedUnion {n : Nat} {l : LeanTaggedUnionSchema Ty}
    (h : WfIn n (.recTaggedUnion l)) :
    WfAllIn 1 l.toList.flatten ∧ OccursSomeIn 0 l.toList.flatten := by
  have h := (wfHere_of_wfIn h).elim id id
  exact ⟨h.1, h.2.1⟩

/-- Every member of a mutual family is mentioned by the family: a `mutual` block whose
    members do not depend on each other is not one family. -/
theorem membersOccur_of_wfIn_family {n : Nat} {f : LeanMutualRecFamily Ty}
    (h : WfIn n (.mutualRecursiveFamily f)) :
    WfAllIn f.members.length (familyTys f) ∧
      MembersOccur f.members.length (familyTys f) := by
  have h := (wfHere_of_wfIn h).elim id id
  exact ⟨h.1, h.2.1⟩

/-- `Ty.MembersOccur` on `k + 1` members says in particular that the last one is
    mentioned. -/
theorem occursSomeIn_of_membersOccur {k : Nat} {ts : List Ty}
    (h : MembersOccur (k + 1) ts) : OccursSomeIn k ts := by
  cases h with
  | succ _ h => exact h

/-! ## Where an occurrence can be seen from

`Ty.OccursIn` looks through a shape and stops at a binder, because the children of a
shape are written in the *same* scope as the shape and the payload of a binder is not.
This is the property that `LeanScript.TyShape` names: `Ty.children` is the children of a
node, `TyShape.children` is the children that are in the node's own scope, and only the
second one can be traversed while looking for an occurrence. -/

/-- A shape is transparent to an occurrence: exactly the children see it. -/
theorem occursIn_shape_iff {i : Nat} {s : TyShape Ty} :
    OccursIn i (.shape s) ↔ OccursSomeIn i s.children :=
  ⟨fun h => by cases h with | shape h => exact h, fun h => .shape h⟩

/-- A binder is opaque to an occurrence: what its payload mentions belongs to the scope
    the binder opens. -/
theorem not_occursIn_recAlias {i : Nat} {b : Ty} : ¬ OccursIn i (.recAlias b) :=
  fun h => by cases h

/-- A binder is opaque to an occurrence. -/
theorem not_occursIn_recObject {i : Nat} {fs : LeanRecordSchema Ty} :
    ¬ OccursIn i (.recObject fs) := fun h => by cases h

/-- A binder is opaque to an occurrence. -/
theorem not_occursIn_recTaggedUnion {i : Nat} {l : LeanTaggedUnionSchema Ty} :
    ¬ OccursIn i (.recTaggedUnion l) := fun h => by cases h

/-- A binder is opaque to an occurrence. -/
theorem not_occursIn_mutualRecursiveFamily {i : Nat} {f : LeanMutualRecFamily Ty} :
    ¬ OccursIn i (.mutualRecursiveFamily f) := fun h => by cases h

/-- `Ty.children` is *not* the traversal an occurrence follows: it crosses a binder.  The
    tree `μX. X` has `Ty.self` among its `Ty.children`, and no occurrence of the scope it
    sits in.  This is why the shapes are a language of their own. -/
theorem children_crosses_binder :
    OccursSomeIn 0 (children (.recAlias .self)) ∧ ¬ OccursIn 0 (.recAlias .self) :=
  ⟨.head .self, not_occursIn_recAlias⟩

/-! ## Nothing is mentioned by nothing -/

/-- No tree in an empty list mentions anything. -/
theorem not_occursSomeIn_nil {i : Nat} : ¬ OccursSomeIn i [] := fun h => by cases h

/-- A terminal type mentions nothing. -/
theorem not_occursIn_prim {i : Nat} {p : LeanPrimTy} : ¬ OccursIn i (.prim p) := by
  intro h
  exact not_occursSomeIn_nil (occursIn_shape_iff.mp h)

/-- An occurrence of one member is not an occurrence of another. -/
theorem not_occursIn_familyMember {i j : Nat} (hij : i ≠ j) :
    ¬ OccursIn i (.familyMember j) := fun h => by cases h; exact hij rfl

/-! ## A type has values

A binder carries its own inhabitation condition (`Ty.HabIn`), checked with nothing about
the declaration being defined assumed — which is what "the least fixpoint of `F` is not
empty iff `F ∅` is not" comes to, once positivity makes `F` monotone.  So the equation
`T = T` is not a type. -/

/-- Nothing is known to have a value when nothing is assumed to: `Ty.self` alone is not
    an inhabited payload. -/
theorem not_habIn_nil_self : ¬ HabIn [] .self := fun h => by
  cases h with | self h => cases h

/-- The payload of a recursive newtype has a value without the newtype having one. -/
theorem habIn_of_wfIn_recAlias {n : Nat} {b : Ty} (h : WfIn n (.recAlias b)) :
    HabIn [] b := (wfHere_of_wfIn h).elim (fun h => h.2.2) (fun h => h.2.2)

-- Before `Ty.WfIn` carried an inhabitation condition this was the theorem
-- `Ty.wf_recAlias_self : Wf (.recAlias .self)`, and excluding `μX. X` was left to the
-- front end.  That was not enough: Lean accepts `inductive Bad | mk : Bad → Bad`, whose
-- tree is exactly this one, so the tree language has to refuse it — and now does.

/-- `μX. X` — the equation `T = T`, which no value satisfies — is **not** a type. -/
theorem not_wf_recAlias_self : ¬ Wf (.recAlias .self) := fun h =>
  not_habIn_nil_self (habIn_of_wfIn_recAlias h)

/-- `μX. X × Nat` — a recursive record with no base case — is not a type either. -/
theorem not_wf_recObject_self :
    ¬ Wf (.recObject ⟨.self, .prim .nat, []⟩) := fun h => by
  rcases (wfHere_of_wfIn h).elim (fun h => h.2.2) (fun h => h.2.2) with _ | ⟨hself, _⟩
  exact not_habIn_nil_self hself

/-! ## An occurrence is positive

The domain of an arrow is checked in the closed scope, so the declaration being defined
never stands to the left of one. -/

/-- A function type's domain is a closed type. -/
theorem wfIn_domain_of_wfIn_fn {n : Nat} {a b : Ty} (h : WfIn n (.fn a b)) : WfIn 0 a := by
  have hs : WfShapeIn n (.fn a b) ∨ WfShapeIn 0 (.fn a b) := wfHere_of_wfIn h
  rcases hs with h | h <;> cases h with | fn ha _ => exact ha

-- Before the domain of an arrow was checked in the closed scope this was the theorem
-- `Ty.wf_recAlias_negative : Wf (.recAlias (.fn .self (.prim .nat)))`, and positivity was
-- said to be the front end's business.

/-- A negative occurrence — `μX. X → Nat`, at which a term language diverges — is **not**
    a type. -/
theorem not_wf_recAlias_negative : ¬ Wf (.recAlias (.fn .self (.prim .nat))) := fun h => by
  have hb : WfIn 1 (.fn .self (.prim .nat)) :=
    (wfHere_of_wfIn h).elim (fun h => h.1) (fun h => h.1)
  exact not_wf_self (wfIn_domain_of_wfIn_fn hb)

end Ty

end LeanScript

end
