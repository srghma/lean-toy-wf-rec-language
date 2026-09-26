module

public import LeanScript.Ty.Schema.Sum

@[expose] public section

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# The schemas: mutual families

`LeanFamMemberSchema`, one member of a mutual recursive family, and
`LeanMutualRecFamily`, the family with the member being defined selected.
-/

/-- One member of a mutual recursive family: the shape it contributes, which is one of
    the three shapes a member can have.  There is deliberately no *enum* member: an enum
    mentions no other member, so a block containing one is not a family but a `mutual`
    block of independent declarations. -/
inductive LeanFamMemberSchema (α : Type) where
  /-- A member with at least two constructors, one of which carries a field. -/
  | ctors (schema : LeanTaggedUnionSchema α)
  /-- A single-constructor member with at least two fields. -/
  | record (schema : LeanRecordSchema α)
  /-- A newtype member: it has no object of its own, and a value of it is a value of
      this, its single field. -/
  | alias (body : α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Traversable

/-- The payload of one member of a **mutual recursive family**: the bodies of *all* of
    its members, in declaration order, and which of them this type is.

    It is a zipper — the members before this one, this one, and the members after it —
    so the member number is in range by construction, and the family has at least two
    members by construction: a block of one member is not mutual, and is the ordinary
    recursive shape it is. -/
inductive LeanMutualRecFamily (α : Type) where
  /-- The selected member is followed by at least one further member. -/
  | selectedThenMore (before : List (LeanFamMemberSchema α)) (current : LeanFamMemberSchema α)
      (next : LeanFamMemberSchema α) (after : List (LeanFamMemberSchema α))
  /-- The selected member is the last one, and at least one member precedes it. -/
  | selectedLast (first : LeanFamMemberSchema α) (before : List (LeanFamMemberSchema α))
      (current : LeanFamMemberSchema α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Traversable

namespace LeanMutualRecFamily

variable {α β : Type}

/-- All the members of the family, in declaration order. -/
def members : LeanMutualRecFamily α → List (LeanFamMemberSchema α)
  | .selectedThenMore before current next after => before ++ current :: next :: after
  | .selectedLast first before current => first :: before ++ [current]

/-- Which member of the family this type is. -/
def memberIdx : LeanMutualRecFamily α → Nat
  | .selectedThenMore before _ _ _ => before.length
  | .selectedLast _ before _ => before.length + 1

/-- The member this type is. -/
def current : LeanMutualRecFamily α → LeanFamMemberSchema α
  | .selectedThenMore _ current _ _ => current
  | .selectedLast _ _ current => current

theorem two_le_members (f : LeanMutualRecFamily α) : 2 ≤ f.members.length := by
  cases f with
  | selectedThenMore before _ _ after =>
      simp only [members, List.length_append, List.length_cons]
      omega
  | selectedLast _ before _ =>
      simp only [members, List.length_cons, List.length_append]
      omega

theorem memberIdx_lt (f : LeanMutualRecFamily α) : f.memberIdx < f.members.length := by
  cases f with
  | selectedThenMore before _ _ after =>
      simp only [members, memberIdx, List.length_append, List.length_cons]
      omega
  | selectedLast _ before _ =>
      simp only [members, memberIdx, List.length_cons, List.length_append]
      omega

theorem getElem?_memberIdx (f : LeanMutualRecFamily α) :
    f.members[f.memberIdx]? = some f.current := by
  cases f with
  | selectedThenMore before _ _ _ =>
      simp [members, memberIdx, current]
  | selectedLast _ before _ =>
      simp [members, memberIdx, current]

/-- The family with these members, selecting member `i` — if there are at least two of
    them and `i` is one of them. -/
def ofMembers? (ms : List (LeanFamMemberSchema α)) (i : Nat) :
    Option (LeanMutualRecFamily α) :=
  match ms[i]? with
  | none => none
  | some m =>
    let before := ms.take i
    match ms.drop (i + 1) with
    | next :: after =>
        if 2 ≤ ms.length then some (.selectedThenMore before m next after) else none
    | [] =>
        match before with
        | first :: bs => some (.selectedLast first bs m)
        | [] => none

end LeanMutualRecFamily

end LeanScript

end
