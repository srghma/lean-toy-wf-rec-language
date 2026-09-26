module

public import TyTests.InductiveTypesTest.Parameters

@[expose] public section

/-!
# `deriving LeanScriptTyWf`: recursion through a type whose own model is recursive

Part of the `deriving LeanScriptTyWf` suite that starts in `TyTests.InductiveTypesTest.Basic`; like it, this
file deliberately does not start with `module`.
-/

open LeanScript

namespace InductiveTypesTest

/-! ## Recursion through a type whose own model is recursive

`inductive RoseList | node : List RoseList → RoseList` and
`structure Rose where kids : Array Rose` describe the same values — a node holds a
sequence of nodes — so both have a model, and the difference is only in *how* the
sequence is written.

* `Array`'s model is a shape, so the occurrence can stand inside it directly:
  `Rose = μX. Array X`.
* `List`'s model is a binder of its own (`nil | cons α self`), so an occurrence placed
  inside it would read as an occurrence of the *list*.  The binder is therefore hoisted
  into a member of a mutual family — the nested recursion becomes a mutual one, which is
  what Lean itself does with a nested inductive:

  ```text
  member 0 = RoseList = member 1
  member 1 = nil | cons (_ : member 0) (_ : member 1)
  ```
-/

/-- `Rose` (declared above) holds its children in an `Array`, whose model is a shape, so
    the occurrence stands inside it and no family is needed. -/
theorem tyWfOf_rose : tyOf Rose = .recAlias (.array .self) := by rfl

inductive RoseList where
  | node : List RoseList → RoseList
  deriving LeanScriptTyWf

/-- `RoseList` is modelled by the family its nested recursion unfolds to: member `0` is
    the declaration, member `1` is the list of them. -/
theorem tyWfOf_roseList :
    tyOf RoseList
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.alias (.familyMember 1))
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            []) := by rfl

-- A wrapper inside a wrapper adds one member per binder on the path to the occurrence.
inductive RoseListList where
  | node : List (List RoseListList) → RoseListList
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf RoseListList
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.alias (.familyMember 2))
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]             [.ctors (.skip (.here ⟨.familyMember 1, [.familyMember 2]⟩ []))]) := by rfl

-- The declaration keeps its own shape: here a sum with a base case, whose recursive
-- constructor holds the list.
inductive Forest where
  | tip : Nat → Forest
  | branch : List Forest → Forest
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Forest
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 1] []))
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]             []) := by rfl

-- A parameter is no obstacle: the list is of the declaration at *its own* arguments.
inductive TreeL (α : Type) where
  | node : α → List (TreeL α) → TreeL α
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf (TreeL Nat)
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.record ⟨.prim .nat, .familyMember 1, []⟩)
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]             []) := by rfl

-- What is still refused: a wrapper whose *own* model is a mutual family.  Hoisting turns
-- one binder into one member, and there is no member a whole family can become.
mutual
inductive ListA (α : Type) where
  | nil
  | cons : α → ListB α → ListA α
inductive ListB (α : Type) where
  | mk : ListA α → Nat → ListB α
end

deriving instance LeanScriptTyWf for ListA, ListB

inductive ViaFamily where
  | node : ListA ViaFamily → ViaFamily

/--
error: the type `InductiveTypesTest.ViaFamily` has no `Ty`: `ListA
  ViaFamily` mentions the declaration being defined through a type this handler cannot recurse through: the occurrence goes where the argument's tree would stand in the type former's own model (`Array`, `Thunk`, `Option`, `×`, `⊕`, a function type, any non-recursive wrapper), and a binder that would capture it there is hoisted into a member of a family (`List`, any recursive wrapper) — but the model of this one is a mutual family, or does not hold the argument as one tree
-/
#guard_msgs in
deriving instance LeanScriptTyWf for ViaFamily

-- A `mutual` family may recurse through a wrapper too: the hoisted members follow the
-- declared ones.
mutual
inductive EvList where
  | mk : List OdList → EvList
inductive OdList where
  | mk : List EvList → OdList
end

deriving instance LeanScriptTyWf for EvList, OdList

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf EvList
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.alias (.familyMember 2))
-- [SKIPPED BY PROFILE_LAKE]             (.alias (.familyMember 3))
-- [SKIPPED BY PROFILE_LAKE]             [.ctors (.skip (.here ⟨.familyMember 1, [.familyMember 2]⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]              .ctors (.skip (.here ⟨.familyMember 0, [.familyMember 3]⟩ []))]) := by rfl

end InductiveTypesTest
