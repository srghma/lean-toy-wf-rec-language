module

public import TyTests.InductiveTypesTest.Basic

@[expose] public section

/-!
# `deriving LeanScriptTyWf`: type parameters, recursion through a shape, refusals

Part of the `deriving LeanScriptTyWf` suite that starts in `TyTests.InductiveTypesTest.Basic`; like it, this
file deliberately does not start with `module`.
-/

open LeanScript

namespace InductiveTypesTest

/-! ## Type parameters -/

-- `Box` is a newtype, so it is optimised away: a `Box α` *is* an `α`.
inductive Box (α : Type) where
  | mk : α → Box α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Box Nat) = .prim .nat := by rfl

inductive Box2 (α : Type) where
  | mk : α → α → Box2 α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Box2 Nat) = .record ⟨.prim .nat, .prim .nat, []⟩ := by rfl

inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Expr
-- [SKIPPED BY PROFILE_LAKE]       = .recTaggedUnion (.payloadFirst ⟨.self, [.self]⟩ [.self, .self] [[.self], []]) := by rfl

inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α
  | Mul : α → α → ExprF α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf (ExprF Bool)
-- [SKIPPED BY PROFILE_LAKE]       = .taggedUnion (.payloadFirst ⟨.prim .int, []⟩ [.prim .bool, .prim .bool]
-- [SKIPPED BY PROFILE_LAKE]           [[.prim .bool, .prim .bool]]) := by rfl

-- A parametric *recursive* declaration is a tree with a hole for each parameter, and the
-- hole is filled with the parameter's own tree.
inductive PTree (α : Type) where
  | leaf
  | node : PTree α → α → PTree α → PTree α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf (PTree Nat)
-- [SKIPPED BY PROFILE_LAKE]       = .recTaggedUnion (.skip (.here ⟨.self, [.prim .nat, .self]⟩ [])) := by rfl

/-! ## Recursion through a type former that is a shape

The children of a *shape* are written in the same scope as the shape, so a shape may hold
an occurrence of the declaration being defined: `Option`, `×` and `⊕` can be recursed
through, as `Array`, `Thunk` and `→` already could.  A *binder* — `List`, or any other
recursive declaration — cannot; see the last section. -/

/-- A list written the other way round: `T = Option (Nat × T)`. -/
inductive Chain where
  | mk : Option (Nat × Chain) → Chain
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Chain
-- [SKIPPED BY PROFILE_LAKE]       = .recAlias (.taggedUnion (.skip (.here ⟨.record ⟨.prim .nat, .self, []⟩, []⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]   := by rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The model the handler builds for `Option` of the declaration is the model `Option`
-- [SKIPPED BY PROFILE_LAKE]     has everywhere else, with the occurrence in the place of the argument's tree. -/
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Option Nat) = .taggedUnion (.skip (.here ⟨tyOf Nat, []⟩ [])) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Nat × Bool) = .record ⟨tyOf Nat, tyOf Bool, []⟩ := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Nat ⊕ Bool) = .taggedUnion (.payloadFirst ⟨tyOf Nat, []⟩ [tyOf Bool] []) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

/-- A binary tree whose children are one value of a sum. -/
inductive SumTree where
  | mk : String ⊕ (SumTree × SumTree) → SumTree
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf SumTree
-- [SKIPPED BY PROFILE_LAKE]       = .recAlias (.taggedUnion
-- [SKIPPED BY PROFILE_LAKE]           (.payloadFirst ⟨.prim .string, []⟩ [.record ⟨.self, .self, []⟩] [])) := by rfl

/-! ### A wrapper of one's own

Nothing about this is special to the library's type formers: the tree is the wrapper's own
instance with the occurrence in the place of its parameter's tree, so a wrapper the user
wrote works exactly as `Option` does — as long as the wrapper is not itself recursive. -/

/-- A non-recursive wrapper: its model is a record, which is a shape. -/
structure Labelled (α : Type) where
  label : String
  value : α
  deriving LeanScriptTyWf

inductive LabelledTree where
  | leaf
  | node : Labelled LabelledTree → LabelledTree
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] /-- The occurrence sits inside the record, not directly in a field, and the declaration
-- [SKIPPED BY PROFILE_LAKE]     has several constructors: its tree is a recursive newtype whose body is the union of
-- [SKIPPED BY PROFILE_LAKE]     its constructors (the fold of a recursive tagged union hands over answers only at the
-- [SKIPPED BY PROFILE_LAKE]     fields that *are* the union; that of a newtype, wherever an occurrence sits). -/
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf LabelledTree
-- [SKIPPED BY PROFILE_LAKE]       = .recAlias (.taggedUnion
-- [SKIPPED BY PROFILE_LAKE]           (.skip (.here ⟨.record ⟨.prim .string, .self, []⟩, []⟩ []))) := by rfl

/-- A recursive wrapper of one's own: its model is a binder, so an occurrence inside it
    would be an occurrence of *it*.  The binder is therefore hoisted into a member of a
    family — exactly as `List` is, and for the same reason. -/
inductive Bag (α : Type) where
  | nil
  | cons : α → Bag α → Bag α
  deriving LeanScriptTyWf

inductive BagTree where
  | node : Bag BagTree → BagTree
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf BagTree
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.alias (.familyMember 1))
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]             []) := by rfl

structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

-- `deriving LeanScriptTyWf` on the declaration itself is refused for the same reason as
-- the `deriving instance` below, which pins the message; a `deriving` clause cannot carry
-- a `#guard_msgs`, so it is written out here instead.

/--
error: the type `InductiveTypesTest.Unfold` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Unfold

/-! ## What cannot be derived -/

-- 1. A field whose type has no instance: the handler names it and stops, rather than
--    translating a second copy of it.
structure NeedsInstance where
  x : Nat
  y : Except String Nat

/--
error: the type `InductiveTypesTest.NeedsInstance` has no `Ty`: `Except String
  ℕ` has no `LeanScriptTyWf` instance; derive or write one for it first
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NeedsInstance

deriving instance LeanScriptTyWf for Except

deriving instance LeanScriptTyWf for NeedsInstance -- now should pass

-- 2. A declaration one of whose fields has no `Ty` at all: a function *answering* with a
--    type has no instance either, and the handler names what it could not model.
structure NoValue where
  f : Nat → Type

/--
error: the type `InductiveTypesTest.NoValue` has no `Ty`: existential typing is not yet supported, `f` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NoValue

end InductiveTypesTest
