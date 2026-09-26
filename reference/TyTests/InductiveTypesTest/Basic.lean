module

public import LeanScript.Ty.Ty
public import LeanScript.Ty.Wf
public import LeanScript.Ty.WfFacts
public import LeanScript.Ty.TyWf
public import LeanScript.Ty.Class
public meta import LeanScript.Ty.WfTactic
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving

@[expose] public section

/-!
# `deriving LeanScriptTyWf`: the `Ty` of a Lean inductive type

Every `example` below is checked by the kernel, so this file *is* the expectation: what
`LeanScript.tyWfOf α` is for each shape of Lean declaration, and what the handler says about
the declarations it refuses.

Two notes.

* The file deliberately does **not** start with `module`.  An inductive with
  `@[computed_field]`s cannot be declared inside a module-system file (its automatic
  `_impl` machinery lives in a private namespace the module header rejects), and computed
  fields are one of the things this test is about.

* Everything is declared inside `namespace InductiveTypesTest` so that names such as
  `MProd` do not collide with the ones the core library already has.
-/

open LeanScript

namespace InductiveTypesTest

/-! ## Functions -/

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Nat → Bool) = .fn (.prim .nat) (.prim .bool) := by rfl

/-! ## `Option`: a non-recursive sum -/

/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev expected_ty_option (α : Ty) : Ty := .taggedUnion (.skip (.here ⟨α, []⟩ []))

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Option Nat) = expected_ty_option (.prim .nat) := by rfl

-- `Opt` is a fresh copy of `Option`, and `deriving LeanScriptTyWf` gives it the same tree —
-- the *same constant*, in fact, because the handler stores one tree per shape.
inductive Opt (α : Type) where
  | none
  | some : α → Opt α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Opt Nat) = expected_ty_option (.prim .nat) := by rfl

/-! ## Pairs: one constructor with two fields -/

/-- `α × β`: one constructor with two fields. -/
abbrev expected_ty_prod (α β : Ty) : Ty := .record ⟨α, β, []⟩

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Nat × Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

structure MProd (α : Type u) (β : Type v) where
  fst : α
  snd : β
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (MProd Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

structure Pair (α β : Type) where
  first  : α
  second : β
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Pair Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

inductive Tuple2 (α β : Type) where
  | mk : α → β → Tuple2 α β
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Tuple2 Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

-- `And` is a `Prop`: its proofs carry nothing at run time, so it has no `Ty` at all —
-- which the handler says rather than inventing a type for it.
/--
error: the type `And` carries no value, so it has no `Ty`
-/
#guard_msgs in
deriving instance LeanScriptTyWf for And

/-! ## Computed fields are ordinary fields

A `@[computed_field]` is a value the runtime representation *stores*, so it is one more
field of the object: the tree of the declaration is a record holding the shape the
declaration would otherwise have, followed by the terminal types of the cached values, in
declaration order.  When the shape itself is erased — a single-constructor, field-less
declaration — only the cached values are left. -/

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Bool = .prim .bool := by rfl

-- A computed field needs at least two constructors (with one constructor there is no tag
-- to store the cached value beside), which is why this is a two-constructor declaration.
inductive BoolWithComputed where
  | mk : Bool → BoolWithComputed
  | mk2 : Bool → BoolWithComputed
with
  @[computed_field] foo : BoolWithComputed → Nat
    | .mk b => if b then 0 else 1
    | .mk2 _ => 2

deriving instance LeanScriptTyWf for BoolWithComputed

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf BoolWithComputed
-- [SKIPPED BY PROFILE_LAKE]       = .record ⟨.taggedUnion (.payloadFirst ⟨.prim .bool, []⟩ [.prim .bool] []),
-- [SKIPPED BY PROFILE_LAKE]                  .prim .nat, []⟩ := by rfl

-- A `Unit` field carries nothing, so `MyUnit` has exactly one value and no `Ty`.
inductive MyUnit where
  | mk : Unit → MyUnit

/--
error: the type `InductiveTypesTest.MyUnit` carries no value, so it has no `Ty`
-/
#guard_msgs in
deriving instance LeanScriptTyWf for MyUnit

-- 1. two-constructor enum
inductive Dir where
  | north
  | south
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Dir = .prim .bool := by rfl

inductive DirWithComputed where
  | north
  | south
with
  @[computed_field] foo : DirWithComputed → Nat
    | .north => 0
    | .south => 1

deriving instance LeanScriptTyWf for DirWithComputed

-- [SKIPPED BY PROFILE_LAKE] example : tyOf DirWithComputed = .record ⟨.prim .bool, .prim .nat, []⟩ := by rfl

-- 2. three-constructor enum
inductive Dir3 where
  | n
  | s
  | e
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Dir3 = .enum ⟨0, 0⟩ := by rfl

inductive Dir3WithComputed where
  | n
  | s
  | e
with
  @[computed_field] foo : Dir3WithComputed → Nat
    | .n => 0
    | .s => 1
    | .e => 2

deriving instance LeanScriptTyWf for Dir3WithComputed

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Dir3WithComputed = .record ⟨.enum ⟨0, 0⟩, .prim .nat, []⟩ := by rfl

/-! ## A model that is a decision, not a translation

`Ordering` is mechanically a field-less sum of three constructors, so a translation would
number them `0`, `1`, `2`.  Its instance says otherwise — the enum is shifted, so that
`lt`, `eq` and `gt` are `-1`, `0` and `1` — and because the answer lives in an instance,
every declaration that mentions an `Ordering` gets *that* model. -/

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Ordering = .enum ⟨0, -1⟩ := by rfl

structure Comparison where
  how : Ordering
  weight : Nat
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Comparison = .record ⟨.enum ⟨0, -1⟩, .prim .nat, []⟩ := by rfl

/-! ## Records and newtypes -/

-- 3. record
structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Point = .record ⟨.prim .nat, .prim .nat, []⟩ := by rfl

-- 4. newtype: the wrapper is erased, so a `Wrap` *is* a `Nat`.
structure Wrap where
  v : Nat
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Wrap = .prim .nat := by rfl

/-! ## Recursive declarations -/

-- 6. recursive tagged union
inductive T where
  | leaf
  | node : T → T → T
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf T = .recTaggedUnion (.skip (.here ⟨.self, [.self]⟩ [])) := by rfl

-- 7. recursive object (nested through `Array`)
structure Tree where
  n : Nat
  kids : Array Tree
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Tree = .recObject ⟨.prim .nat, .array .self, []⟩ := by rfl

-- 8. recursive alias (newtype, nested through `Array`)
structure Rose where
  kids : Array Rose
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Rose = .recAlias (.array .self) := by rfl

-- 9. mutual family.  Member `0` is `Ev`, member `1` is `Od`, and inside the bodies
--    `Ty.familyMember i` is an occurrence of member `i`.
mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

deriving instance LeanScriptTyWf for Ev
deriving instance LeanScriptTyWf for Od

/-- Member `0`: `Ev`, the two-constructor sum `zero | succ (_ : Od)`. -/
abbrev evMember : LeanFamMemberSchema Ty :=
  .ctors (.skip (.here ⟨.familyMember 1, []⟩ []))
/-- Member `1`: `Od`, a newtype around an `Ev`. -/
abbrev odMember : LeanFamMemberSchema Ty := .alias (.familyMember 0)

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Ev = .mutualRecursiveFamily (.selectedThenMore [] evMember odMember []) := by rfl

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Od = .mutualRecursiveFamily (.selectedLast evMember [] odMember) := by rfl

-- 10. the original example
inductive Foo where
  | a : Foo
  | b : Nat → Foo → Foo
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Foo = .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])) := by rfl

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

deriving instance LeanScriptTyWf for NatList

-- The cached values are *part of* a `NatList`, so the tail a `cons` holds is a whole
-- `NatList` — the union together with its sum and length — and not the bare union.  The
-- binder is therefore the record: `self` inside the union denotes the record it is a
-- field of.
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf NatList
-- [SKIPPED BY PROFILE_LAKE]       = .recObject ⟨.taggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]                     .prim .nat, [.prim .nat]⟩ := by rfl

-- `Lean.Name` is the recursive tagged union `anonymous | str | num` caching a `UInt64`,
-- so it is the recursive record of that union and the cached value; the `self`s inside
-- the union are occurrences of the record, which is what a `Name` field holds.
deriving instance LeanScriptTyWf for Lean.Name

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Lean.Name
-- [SKIPPED BY PROFILE_LAKE]       = .recObject
-- [SKIPPED BY PROFILE_LAKE]           ⟨.taggedUnion (.skip (.here ⟨.self, [.prim .string]⟩ [[.self, .prim .nat]])),
-- [SKIPPED BY PROFILE_LAKE]            .prim .uint64, []⟩ := by rfl

/-! ## The same declaration at two different arguments

A list is modelled by its instance, so `List (List Nat)` holds the tree of `List Nat`
**by reference** — the leaf is that instance's own `tyOf`, and the inner list is not
translated, copied or checked again. -/

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (List Nat) = .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])) := by rfl

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf (List (List Nat))
-- [SKIPPED BY PROFILE_LAKE]       = .recTaggedUnion (.skip (.here ⟨tyOf (List Nat), [.self]⟩ [])) := by rfl

end InductiveTypesTest
