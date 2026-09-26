module

public import LeanScript.Ty.Schema.Containers

@[expose] public section

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# The schemas: enums and tagged unions

`LeanEnumSchema`, a sum whose constructors have no fields, and `LeanTaggedUnionSchema`, a
sum of at least two constructors one of which has a field.
-/

/-- The payload of an **enum**: a sum whose constructors all have no fields, printed as
    the plain numbers `shift`, `shift + 1`, ….

    The number of constructors is held as `extraConstructors`, the number *beyond the
    three an enum must have*, so an enum of fewer than three constructors is
    unwritable — see the header of `LeanScript.Ty.Schema` for why the three smaller cases
    are other types rather than small enums.  `shift` is an arbitrary `Int`, which is what unites
    an ordinary enum (`shift = 0`) with the ones whose numbering Lean fixes (`Ordering`
    is three constructors at `shift = -1`, printing as `-1 | 0 | 1`). -/
structure LeanEnumSchema where
  /-- How many constructors the enum has **beyond** the three it has at minimum. -/
  extraConstructors : Nat := 0
  /-- The number the first constructor prints as. -/
  shift : Int := 0
  deriving DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq

namespace LeanEnumSchema

/-- How many constructors the enum has: at least three. -/
def nOfConstructors (s : LeanEnumSchema) : Nat := s.extraConstructors + 3

theorem three_le_nOfConstructors (s : LeanEnumSchema) : 3 ≤ s.nOfConstructors := by
  simp only [nOfConstructors]
  omega

/-- An enum has at least three constructors, so it has at least one: a constructor of it
    can be written as a plain numeral, `(2 : Fin s.nOfConstructors)`. -/
instance instNeZeroNOfConstructors (s : LeanEnumSchema) : NeZero s.nOfConstructors :=
  ⟨by simp only [nOfConstructors]; omega⟩

/-- The enum with this many constructors, if that is a number of constructors an enum
    can have. -/
def ofCount? (n : Nat) (shift : Int) : Option LeanEnumSchema :=
  if 3 ≤ n then some ⟨n - 3, shift⟩ else none

@[simp] theorem ofCount?_nOfConstructors (s : LeanEnumSchema) :
    ofCount? s.nOfConstructors s.shift = some s := by
  cases s with
  | mk e sh =>
    simp [ofCount?, nOfConstructors]

theorem nOfConstructors_ofCount? {n : Nat} {shift : Int} {s : LeanEnumSchema}
    (h : ofCount? n shift = some s) : s.nOfConstructors = n ∧ s.shift = shift := by
  unfold ofCount? at h
  split at h
  · next hn => cases h; simp [nOfConstructors]; omega
  · simp at h

end LeanEnumSchema

/-- The payload of a **tagged union**: at least two constructors, at least one of which
    carries a field.  (With one constructor it is a record, a newtype or a unit type;
    with no field anywhere it is an enum or a boolean.)

    As with `CtorsWithPayload`, the encoding names the *first* constructor with fields,
    so it is canonical. -/
inductive LeanTaggedUnionSchema (α : Type) where
  /-- Constructor `0` carries fields, and at least one further constructor follows. -/
  | payloadFirst (fields : NonEmptyList α) (next : List α) (rest : List (List α))
  /-- Constructor `0` carries no fields; the constructors after it are at least one,
      and one of them carries a field. -/
  | skip (rest : CtorsWithPayload α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, Traversable

namespace LeanTaggedUnionSchema

variable {α β : Type}

/-- One entry per constructor, in declaration order, each holding its field types. -/
def toList : LeanTaggedUnionSchema α → List (List α)
  | .payloadFirst fields next rest => fields.toList :: next :: rest
  | .skip rest => [] :: rest.toList

/-- How many constructors there are — at least two. -/
def length : LeanTaggedUnionSchema α → Nat
  | .payloadFirst _ _ rest => rest.length + 2
  | .skip rest => rest.length + 1

@[simp] theorem length_toList (c : LeanTaggedUnionSchema α) : c.toList.length = c.length := by
  cases c with
  | payloadFirst _ _ _ =>
      simp only [toList, length, List.length_cons]
  | skip rest =>
      simp only [toList, length, List.length_cons, CtorsWithPayload.length_toList]

theorem two_le_length (c : LeanTaggedUnionSchema α) : 2 ≤ c.toList.length := by
  cases c with
  | payloadFirst _ _ rest =>
      simp only [toList, List.length_cons]
      omega
  | skip rest =>
      simp only [toList, List.length_cons, CtorsWithPayload.length_toList]
      cases rest <;> simp only [CtorsWithPayload.length] <;> omega

theorem two_le_length' (c : LeanTaggedUnionSchema α) : 2 ≤ c.length := by
  have := c.two_le_length
  simpa using this

/-- The field types of constructor `t`, in declaration order.  The bound is stated
    against `length` — the number of constructors — rather than against the length of
    `toList`, so that a caller never has to see the list. -/
def get (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) : List α :=
  c.toList[t]'(by rw [length_toList]; exact ht)

@[simp] theorem get_eq_getElem (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) :
    c.get t ht = c.toList[t]'(by rw [length_toList]; exact ht) := rfl

/-- Some constructor of this union carries a field. -/
theorem exists_nonempty (c : LeanTaggedUnionSchema α) : ∃ fs ∈ c.toList, fs ≠ [] := by
  cases c with
  | payloadFirst fields _ _ =>
      exact ⟨fields.toList, by simp [toList], by simp⟩
  | skip rest =>
      obtain ⟨fs, hmem, hne⟩ := rest.exists_nonempty
      exact ⟨fs, by simp [toList, hmem], hne⟩

/-- These constructors, if they are the constructors of a tagged union. -/
def ofList? : List (List α) → Option (LeanTaggedUnionSchema α)
  | (f :: fs) :: next :: rest => some (.payloadFirst ⟨f, fs⟩ next rest)
  | [] :: rest => (CtorsWithPayload.ofList? rest).map .skip
  | _ => none

@[simp] theorem ofList?_toList (c : LeanTaggedUnionSchema α) : ofList? c.toList = some c := by
  cases c with
  | payloadFirst fields _ _ => cases fields; rfl
  | skip rest => simp [toList, ofList?]

theorem toList_ofList? : ∀ {l : List (List α)} {c : LeanTaggedUnionSchema α},
    ofList? l = some c → c.toList = l
  | (_ :: _) :: _ :: _, _, h => by injection h with h; subst h; rfl
  | [] :: rest, c, h => by
      simp only [ofList?, Option.map_eq_some_iff] at h
      obtain ⟨c', hc', rfl⟩ := h
      simp [toList, CtorsWithPayload.toList_ofList? hc']
  | [], _, h => by simp [ofList?] at h
  | [_ :: _], _, h => by simp [ofList?] at h

@[simp] theorem toList_map (f : α → β) (c : LeanTaggedUnionSchema α) :
    (c.map f).toList = c.toList.map (·.map f) := by
  cases c <;> simp [toList, map, Functor.map]

/-- Mapping the field types keeps the constructors: a mapped union has as many of them,
    in the same order, so a number that is a constructor of one is a constructor of the
    other. -/
@[simp] theorem length_map (f : α → β) (c : LeanTaggedUnionSchema α) :
    (c.map f).length = c.length := by
  cases c <;> simp [map, length, Functor.map]

/-- The fields of constructor `t` of a mapped union are the fields of constructor `t`,
    mapped. -/
theorem get_map (f : α → β) (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) :
    (c.map f).get t (by simpa using ht) = (c.get t ht).map f := by
  simp only [get, toList_map]
  rw [List.getElem_map]

end LeanTaggedUnionSchema

end LeanScript

end
