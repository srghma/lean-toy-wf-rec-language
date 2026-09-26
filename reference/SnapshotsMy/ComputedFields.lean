import LeanScript.Term.Elab
import LeanScript.Term.Compile

/-!
# Datatypes that cache a value computed from themselves

A Lean declaration may cache a value that is a **function of the value itself**, declared
`@[computed_field]` in the `with` block of the inductive: `Lean.Name` stores its own
`hash`.  A cached value is not a field — it carries no information the value does not
already have — but it does decide the object the runtime holds, and so the JavaScript
that is printed, which is why the type language records it: `Ty.withComputedFields`, and
the seven names `Ty.enum_withComputedFields`, `Ty.recTaggedUnion_withComputedFields`, …
for the shapes the base may be.

`#leanjs_schema_for` decides, for a Lean datatype, which schema it has and whether that
schema carries computed fields.  Nothing here is declared by hand: the types of the
cached values are read off the declaration.
-/

/-- A list of numbers that caches its own sum and its own length. -/
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
with
  /-- The sum of the elements, cached in every `cons`. -/
  @[computed_field] sum : NatList → Nat
    | .nil => 0
    | .cons x l => x + l.sum
  /-- How many elements there are, cached in every `cons`. -/
  @[computed_field] length : NatList → Nat
    | .nil => 0
    | .cons _ l => l.length + 1

/-- A pair of numbers, which caches nothing. -/
structure Pt where
  /-- The first coordinate. -/
  x : Nat
  /-- The second coordinate. -/
  y : Nat

-- `Lean.Name` is a recursive tagged union of three constructors that caches its own
-- `hash`, a `UInt64`.
/--
info: Lean.Name
  schema    : LeanTaggedUnionSchema (recursive)
  shape     : (recTaggedUnion [] [self string] [self nat])
  computed  : uint64
-/
#guard_msgs in
#leanjs_schema_for Lean.Name

-- The same shape, with two cached values of its own.
/--
info: NatList
  schema    : LeanTaggedUnionSchema (recursive)
  shape     : (recTaggedUnion [] [nat self])
  computed  : nat nat
-/
#guard_msgs in
#leanjs_schema_for NatList

-- A datatype that caches nothing reports a plain schema.
/--
info: Pt
  schema    : LeanRecordSchema
  shape     : (record nat nat)
  computed  : -
-/
#guard_msgs in
#leanjs_schema_for Pt

-- A list caches nothing either, so it is the recursive tagged union and no more.
/--
info: List Nat
  schema    : LeanTaggedUnionSchema (recursive)
  shape     : (recTaggedUnion [] [nat self])
  computed  : -
-/
#guard_msgs in
#leanjs_schema_for List Nat

-- The `Ty` the translation gives `Lean.Name` is the one written out as `Ty.name`: the
-- recursive tagged union `anonymous | str | num`, caching a `UInt64`.
example : (leanscript_ty% Lean.Name) = LeanScript.Ty.name := by rfl
