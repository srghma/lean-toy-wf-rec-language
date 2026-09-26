module

public import Init.Data.List.Lemmas
public import NonEmpty.ListCorrectByConstruction.Basic
public import NonEmpty.ListCorrectByConstruction.Ops
public import NonEmpty.ListCorrectByConstruction.Instances
public import NonEmpty.ListCorrectByConstruction.Notation
public import Mathlib.Tactic.DeriveTraversable
public import Mathlib.Control.Traversable.Instances

@[expose] public section

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- Apply an effectful function to every element of a non-empty list, left to right. -/
def _root_.NonEmpty.ListCorrectByConstruction.NonEmptyList.traverse {m : Type u → Type u}
    [Applicative m] {α β : Type u} (f : α → m β) (xs : NonEmptyList α) : m (NonEmptyList β) :=
  NonEmptyList.mk <$> f xs.head <*> Traversable.traverse f xs.tail

/-- `NonEmptyList` is traversable, with its existing `Functor` instance: this is what the
    schemas below need to derive theirs.  It lives here so that the `NonEmpty` library
    itself needs no Mathlib. -/
instance : Traversable NonEmptyList where
  traverse := NonEmptyList.traverse

/-!
# The schemas: generic containers

The payload of a record (`LeanRecordSchema`), non-empty lists, and the constructors of a
sum type (`CtorsWithPayload`).  The overview of the schemas is in `LeanScript.Ty.Schema`.
-/

structure LeanRecordSchema (α : Type) where
  /-- The first element. -/
  fst : α
  /-- The second element. -/
  snd : α
  /-- Everything after the second. -/
  rest : List α
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Traversable

namespace LeanRecordSchema

variable {α β : Type}

/-- The elements, in order. -/
def toList (xs : LeanRecordSchema α) : List α := xs.fst :: xs.snd :: xs.rest

/-- How many elements there are — at least two. -/
def length (xs : LeanRecordSchema α) : Nat := xs.rest.length + 2

@[simp] theorem length_toList (xs : LeanRecordSchema α) : xs.toList.length = xs.length := by
  simp only [toList, length, List.length_cons]

theorem two_le_length (xs : LeanRecordSchema α) : 2 ≤ xs.toList.length := by
  simp only [length_toList, length]
  omega

/-- The list, if it has at least two elements. -/
def ofList? : List α → Option (LeanRecordSchema α)
  | a :: b :: rest => some ⟨a, b, rest⟩
  | _ => none

@[simp] theorem ofList?_toList (xs : LeanRecordSchema α) : ofList? xs.toList = some xs := rfl

theorem toList_ofList? : ∀ {xs : List α} {s : LeanRecordSchema α},
    ofList? xs = some s → s.toList = xs
  | _ :: _ :: _, _, h => by injection h with h; subst h; rfl
  | [], _, h => by simp [ofList?] at h
  | [_], _, h => by simp [ofList?] at h

theorem toList_injective {xs ys : LeanRecordSchema α} (h : xs.toList = ys.toList) : xs = ys := by
  cases xs; cases ys; simp_all [toList]

@[simp] theorem toList_map (f : α → β) (xs : LeanRecordSchema α) :
    (xs.map f).toList = xs.toList.map f := rfl

/-- Mapping the field types keeps the fields: a mapped record has as many of them. -/
@[simp] theorem length_map (f : α → β) (xs : LeanRecordSchema α) :
    (xs.map f).length = xs.length := by
  simp [map, length]

/-- The `i`-th element, if there is one. -/
def get? (xs : LeanRecordSchema α) (i : Nat) : Option α := xs.toList[i]?

end LeanRecordSchema

/-! ## The constructors of a sum type -/

/-- The constructors of a sum type **of which at least one carries a field**, as the
    position of the *first* such constructor: `skip` is a constructor with no fields,
    and `here` is the first constructor that has some, followed by whatever comes after
    it.

    The encoding is canonical — a list of constructors in which some constructor has a
    field has exactly one encoding — so `toList` is injective and equality of two of
    these is equality of the constructor lists they denote. -/
inductive CtorsWithPayload (α : Type) where
  /-- This constructor carries at least one field; `rest` is what follows it. -/
  | here (fields : NonEmptyList α) (rest : List (List α))
  /-- This constructor carries no fields, and the one that does comes later. -/
  | skip (rest : CtorsWithPayload α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Traversable

namespace CtorsWithPayload

variable {α β : Type}

/-- One entry per constructor, in declaration order, each holding its field types. -/
def toList : CtorsWithPayload α → List (List α)
  | .here fields rest => fields.toList :: rest
  | .skip rest => [] :: toList rest

/-- How many constructors there are — at least one. -/
def length : CtorsWithPayload α → Nat
  | .here _ rest => rest.length + 1
  | .skip rest => length rest + 1

@[simp] theorem length_toList (c : CtorsWithPayload α) : c.toList.length = c.length := by
  induction c with
  | here _ _ => simp [toList, length]
  | skip _ ih => simp [toList, length, ih]

/-- These constructors, if at least one of them has a field. -/
def ofList? : List (List α) → Option (CtorsWithPayload α)
  | [] => none
  | [] :: rest => (ofList? rest).map .skip
  | (f :: fs) :: rest => some (.here ⟨f, fs⟩ rest)

@[simp] theorem ofList?_toList (c : CtorsWithPayload α) : ofList? c.toList = some c := by
  induction c with
  | here fields _ => cases fields; rfl
  | skip _ ih => simp [toList, ofList?, ih]

theorem toList_ofList? : ∀ {l : List (List α)} {c : CtorsWithPayload α},
    ofList? l = some c → c.toList = l
  | [], _, h => by simp [ofList?] at h
  | (_ :: _) :: _, _, h => by injection h with h; subst h; rfl
  | [] :: rest, c, h => by
      simp only [ofList?, Option.map_eq_some_iff] at h
      obtain ⟨c', hc', rfl⟩ := h
      simp [toList, toList_ofList? hc']

/-- Some constructor of this sum carries a field. -/
theorem exists_nonempty (c : CtorsWithPayload α) : ∃ fs ∈ c.toList, fs ≠ [] := by
  induction c with
  | here fields rest =>
      exact ⟨fields.toList, by simp [toList], by simp⟩
  | skip rest ih =>
      obtain ⟨fs, hmem, hne⟩ := ih
      exact ⟨fs, by simp [toList, hmem], hne⟩

@[simp] theorem toList_map (f : α → β) (c : CtorsWithPayload α) :
    (c.map f).toList = c.toList.map (·.map f) := by
  induction c with
  | here _ _ => simp [toList, map]
  | skip _ ih => simp [toList, map, ih]

/-- Mapping the field types keeps the constructors: a mapped sum has as many of them. -/
@[simp] theorem length_map (f : α → β) (c : CtorsWithPayload α) :
    (c.map f).length = c.length := by
  induction c with
  | here _ _ => simp [map, length]
  | skip _ ih => simp [map, length, ih]

end CtorsWithPayload

end LeanScript

end
