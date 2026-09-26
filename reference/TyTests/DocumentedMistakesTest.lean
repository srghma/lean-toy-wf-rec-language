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
# The mistakes the earlier type languages made, one by one

Every defect recorded in the design documents of the previous representations is listed
here with the evidence that it cannot happen now, in the order of `docs/DesignAnswers.md`
§2.  Three kinds of evidence appear:

* **a theorem** — the tree is not `LeanScript.Ty.Wf`, so no instance and no front end can
  produce it, whatever it does;
* **a witness** — the case the old representation rejected or mistranslated is a type
  here, and `ty_wf` proves it;
* **an error message** — the case is one Lean itself cannot express or one the deriving
  handler refuses, pinned with `#guard_msgs`.

Two defects are *not* excluded by `Ty.Wf`, deliberately; they are at the end, with proofs
that the trees are well formed, so that nothing here is claimed that is not true.
-/

open LeanScript

namespace DocumentedMistakesTest

/-! ## 1. A free occurrence: `self` outside any declaration

The tree language has the leaf, so a tree can be written; it is not a type. -/

example : ¬ Ty.Wf .self := Ty.not_wf_self
example (i : Nat) : ¬ Ty.Wf (.familyMember i) := Ty.not_wf_familyMember

/-! ## 2. Scope confusion between a lone binder and a family

The two occurrence leaves were one token in the two-language representation, told apart
by nesting depth, so a member number captured by a non-mutual binder was accepted with a
silently different meaning.  Each leaf is now a type in exactly one kind of scope. -/

/-- A member number cannot be captured by a binder that recurses on its own. -/
example (i : Nat) : ¬ Ty.WfIn 1 (.familyMember i) := Ty.not_wfIn_one_familyMember

/-- `Ty.self` cannot be captured by the binder of a family. -/
example (n : Nat) (hn : 2 ≤ n) : ¬ Ty.WfIn n .self := Ty.not_wfIn_self_of_family hn

/-! ## 3. A member number the family does not have -/

/-- Member `5` of a family of two members. -/
def outOfRange : Ty :=
  .mutualRecursiveFamily
    (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 5, []⟩ [])))
      (.alias (.familyMember 0)) [])

-- [SKIPPED BY PROFILE_LAKE] example : ¬ Ty.Wf outOfRange := by
-- [SKIPPED BY PROFILE_LAKE]   intro h
-- [SKIPPED BY PROFILE_LAKE]   have hall := (Ty.membersOccur_of_wfIn_family h).1
-- [SKIPPED BY PROFILE_LAKE]   cases hall with
-- [SKIPPED BY PROFILE_LAKE]   | cons h1 _ => exact Ty.not_wfIn_familyMember_of_le (by decide) h1

/-! ## 4. A binder that is not recursive

A "recursive" record that mentions nothing is the record, and the language does not let
the two be different types. -/

example : ¬ Ty.Wf (.recObject ⟨.prim .nat, .prim .bool, []⟩) := by
  intro h
  have hocc := (Ty.occursIn_of_wfIn_recObject h).2
  cases hocc with
  | head h => exact Ty.not_occursIn_prim h
  | tail h =>
    cases h with
    | head h => exact Ty.not_occursIn_prim h
    | tail h => exact Ty.not_occursSomeIn_nil h

/-! ## 5. A `mutual` block that is not one family

Two declarations that happen to be written in one `mutual` block, but of which one can be
moved out, are not a family: the second member is mentioned by nobody. -/

/-- A "family" whose second member is a `Nat` alias nobody refers to. -/
def strangers : Ty :=
  .mutualRecursiveFamily
    (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 0, []⟩ [])))
      (.alias (.prim .nat)) [])

example : ¬ Ty.Wf strangers := by
  intro h
  have hocc := Ty.occursSomeIn_of_membersOccur (k := 1)
    (Ty.membersOccur_of_wfIn_family h).2
  cases hocc with
  | head h => exact Ty.not_occursIn_familyMember (by omega) h
  | tail h =>
    cases h with
    | head h => exact Ty.not_occursIn_prim h
    | tail h => exact Ty.not_occursSomeIn_nil h

-- The handler does not build one either: a `mutual` block is split into strongly
-- connected components first, so each of these is modelled on its own — `Stranger₂` is a
-- plain record and `Stranger₁` a recursive one, and neither tree is a family.
-- `Stranger₁` recurses through an `Array`, which is what gives it values: written with a
-- bare `Stranger₁` field it would denote `T = T × Nat`, which has none and which §12
-- shows is not a type.
mutual
  inductive Stranger₁ where
    | mk : Array Stranger₁ → Nat → Stranger₁
  inductive Stranger₂ where
    | mk : Nat → Nat → Stranger₂
end

deriving instance LeanScriptTyWf for Stranger₁
deriving instance LeanScriptTyWf for Stranger₂

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Stranger₁ = .recObject ⟨.array .self, .prim .nat, []⟩ := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Stranger₂ = .record ⟨.prim .nat, .prim .nat, []⟩ := rfl

/-! ## 6. Degenerate shapes

A record of one field, an enum of two constructors and a family of one member are not
rejected — they cannot be written, because the schemas count in their types. -/

-- [SKIPPED BY PROFILE_LAKE] example : Ty.enumOfCount? 2 = none := rfl
-- [SKIPPED BY PROFILE_LAKE] example : Ty.enumOrBool? 2 = some (.prim .bool) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : Ty.enumOfCount? 3 = some (.enum ⟨0, 0⟩) := rfl

/-! ## 7. A family nested inside a declaration that recurses on its own

`inductive Baz | leaf | node : Baz → Ev → Baz`, with `Ev` from a `mutual` block, had no
`Ty` at all in the two-language representation: the nested family was re-read in the
enclosing scope and blamed.  A nested binder is opaque now — its payload is written in
the scope *it* opens — so the tree is a type, and the handler builds it. -/

/-- The family `Ev`/`Od`, as a closed tree. -/
def evOd : Ty :=
  .mutualRecursiveFamily
    (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 1, []⟩ [])))
      (.ctors (.skip (.here ⟨.familyMember 0, []⟩ []))) [])

example : Ty.Wf evOd := by ty_wf

/-- A self-recursive declaration with that family inside it. -/
example : Ty.Wf (.recTaggedUnion (.skip (.here ⟨.self, [evOd]⟩ []))) := by ty_wf

mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

inductive Baz where
  | leaf
  | node : Baz → Ev → Baz

deriving instance LeanScriptTyWf for Ev
deriving instance LeanScriptTyWf for Baz

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Baz = .recTaggedUnion (.skip (.here ⟨.self, [tyOf Ev]⟩ [])) := rfl

/-! ## 8. The same declaration at two different arguments

`List (List Nat)` was read as an occurrence of the outer `List`.  Nothing is read now: a
type that is not the declaration being derived contributes its instance's tree. -/

structure TwoLists where
  xs : List Nat
  yss : List (List Nat)
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf TwoLists = .record ⟨tyOf (List Nat), tyOf (List (List Nat)), []⟩ := rfl

/-! ## 9. A depth limit

The translation used to give up at depth 12, and later at a documented bound of 64.
There is no traversal to bound: a field's tree is the constant an instance already
names, so the tree below it is never visited. -/

example : Ty.Wf (tyOf (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Nat)))))))))))))))))))))) := tyWf _

/-! ## 10. A computed field changing what `self` means

`NatList` and `Lean.Name` were modelled as `record ⟨recTaggedUnion …, cached…⟩`, so an
occurrence inside the union denoted the bare union rather than the whole cached value — a
wrong answer, not a rejection.  A `@[computed_field]` is an ordinary field now, so the
declaration is one recursive *record* and `Ty.self` inside it is that record; the two
cases are pinned in `TyTests/InductiveTypesTest/` (`NatList`, `Lean.Name`). -/

/-! ## 11. Recursion through another type constructor — fixed

`inductive RoseList | node : List RoseList → RoseList` used to be refused: an occurrence
placed inside `List`'s model would land inside `List`'s own binder and denote the list,
and the tree has no leaf that counts scopes.  It does not need one.  A nested recursion
*is* a mutual recursion — which is how Lean itself compiles a nested inductive — so the
binder that would capture the occurrence is hoisted into one more member of the family
the declaration is translated in.

This is why the declaration below and `structure Rose where kids : Array Rose` are both
types: they describe the same values, and only the *way the sequence is written* differs.
`Array`'s model is a shape, so the occurrence stands inside it (`μX. Array X`); `List`'s
model is a binder, so the family is used instead. -/

inductive RoseList where
  | node : List RoseList → RoseList
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf RoseList
-- [SKIPPED BY PROFILE_LAKE]       = .mutualRecursiveFamily
-- [SKIPPED BY PROFILE_LAKE]           (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]             (.alias (.familyMember 1))
-- [SKIPPED BY PROFILE_LAKE]             (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]             []) := by rfl

structure RoseArray where
  kids : Array RoseArray
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf RoseArray = .recAlias (.array .self) := by rfl

/-! ## 12. A type without values, and a negative occurrence

These two used to be the exceptions: both trees were well formed, and refusing them was
left to the front end.  That was not enough — Lean accepts `inductive Bad | mk : Bad →
Bad`, whose tree is `μX. X` exactly — so `Ty.Wf` now carries an inhabitation condition and
checks the domain of an arrow in the closed scope.  Neither tree is a type any more, and
the handler refuses the declarations that would produce them. -/

example : ¬ Ty.Wf (.recAlias .self) := Ty.not_wf_recAlias_self
example : ¬ Ty.Wf (.recObject ⟨.self, .prim .nat, []⟩) := Ty.not_wf_recObject_self
example : ¬ Ty.Wf (.recAlias (.fn .self (.prim .nat))) := Ty.not_wf_recAlias_negative

/-- The declaration `T = T`, which Lean does accept. -/
inductive NoValues where
  | mk : NoValues → NoValues

/--
error: the type `DocumentedMistakesTest.NoValues` has no `Ty`: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NoValues

/-- A recursive record with no base case: `T = T × Nat`, which Lean also accepts. -/
inductive NoValuesRecord where
  | mk : NoValuesRecord → Nat → NoValuesRecord

/--
error: the type `DocumentedMistakesTest.NoValuesRecord` has no `Ty`: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NoValuesRecord

end DocumentedMistakesTest
