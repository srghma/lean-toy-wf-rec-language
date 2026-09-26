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
# What `Ty.Wf` says, and what `ty_wf` refuses

`LeanScript.Ty` is a plain tree, so a tree can be written that is not a type: an
occurrence of a declaration where no declaration is being defined, a member number a
family does not have, a "recursive" binder that mentions nothing.  `LeanScript.Ty.Wf` is
the proposition that excludes those, and `ty_wf` is the tactic that proves it — by walking
the tree, and by *reusing* the proof of any subtree that already has one.

This file pins both halves: the trees `ty_wf` proves, and the ones it refuses, with the
message it refuses them with.
-/

open LeanScript

namespace WfTest

/-! ## Trees that are types -/

example : Ty.Wf (.prim .nat) := by ty_wf
example : Ty.Wf (.record ⟨.prim .nat, .array (.prim .bool), []⟩) := by ty_wf
example : Ty.Wf (.recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ []))) := by ty_wf
example : Ty.Wf (.recObject ⟨.prim .nat, .array .self, []⟩) := by ty_wf
example : Ty.Wf (.recAlias (.array .self)) := by ty_wf

/-- A family of two members, each of which is mentioned. -/
example :
    Ty.Wf (.mutualRecursiveFamily
      (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 1, []⟩ [])))
        (.alias (.familyMember 0)) [])) := by ty_wf

/-! ## The proof of a subtree that has one is reused

The leaf here is `tyOf (List Nat)`, and the tactic closes it with that instance's own
`isWf` — it does not look at the tree behind it. -/

example : Ty.Wf (.record ⟨tyOf (List Nat), .prim .string, []⟩) := by ty_wf

/-- A tree with a hole, as `deriving LeanScriptTyWf` generates for a parametric type: the
    hole is closed by the hypothesis about it, again without looking at any tree. -/
example (a : Ty) (ha : Ty.Wf a) : Ty.Wf (.recObject ⟨a, .array .self, []⟩) := by ty_wf

/-! ## Trees that are not types -/

-- An occurrence needs a declaration to occur in.
/-- error: ty_wf: `Ty.self` is not a type in a scope of 0 members -/
#guard_msgs in
example : Ty.Wf .self := by ty_wf

-- A member number a family does not have.
/-- error: ty_wf: member 5 is not a member of a scope of 2 members -/
#guard_msgs in
example :
    Ty.Wf (.mutualRecursiveFamily
      (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 5, []⟩ [])))
        (.alias (.familyMember 0)) [])) := by ty_wf

-- A recursive binder that does not mention itself is not a recursive declaration; it is
-- the type inside it.
/-- error: ty_wf: nothing here mentions member 0 -/
#guard_msgs in
example : Ty.Wf (.recObject ⟨.prim .nat, .prim .bool, []⟩) := by ty_wf

-- A `mutual` block whose second member is mentioned by nobody is not one family.
/-- error: ty_wf: nothing here mentions member 1 -/
#guard_msgs in
example :
    Ty.Wf (.mutualRecursiveFamily
      (.selectedThenMore [] (.ctors (.skip (.here ⟨.familyMember 0, []⟩ [])))
        (.alias (.prim .nat)) [])) := by ty_wf

-- An occurrence of a family member inside a declaration that recurses on its own.
/-- error: ty_wf: member 0 is not a member of a scope of 1 members -/
#guard_msgs in
example : Ty.Wf (.recAlias (.array (.familyMember 0))) := by ty_wf

/-! ## Trees that describe no values

A binder is a least fixpoint, so its payload has to have a value without the declaration
being defined having one.  `μX. Array X` above does — the empty array — and these do
not. -/

-- `μX. X`: the equation `T = T`.
/--
error: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs in
example : Ty.Wf (.recAlias .self) := by ty_wf

-- `μX. X × Nat`: a recursive record with no base case.
/--
error: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs in
example : Ty.Wf (.recObject ⟨.self, .prim .nat, []⟩) := by ty_wf

-- A recursive sum every constructor of which needs a value of the sum.
/-- error: ty_wf: no constructor here can be built, so the type has no values -/
#guard_msgs in
example :
    Ty.Wf (.recTaggedUnion (.payloadFirst ⟨.self, []⟩ [.self] [])) := by ty_wf

-- `μX. Thunk X`: delaying a value that does not exist does not make one.
/--
error: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs in
example : Ty.Wf (.recAlias (.thunk .self)) := by ty_wf

-- A family each of whose members needs the other: `A = B`, `B = A`.
/-- error: ty_wf: member 0 of this family has no values, so the family describes no type -/
#guard_msgs in
example :
    Ty.Wf (.mutualRecursiveFamily
      (.selectedThenMore [] (.alias (.familyMember 1)) (.alias (.familyMember 0)) []))
    := by ty_wf

-- The same family with a base case in one member is a type: the iteration needs two
-- rounds, the second member first.
example :
    Ty.Wf (.mutualRecursiveFamily
      (.selectedThenMore [] (.alias (.familyMember 1))
        (.ctors (.skip (.here ⟨.familyMember 0, []⟩ []))) [])) := by ty_wf

/-! ## A negative occurrence

The domain of an arrow is checked in the closed scope, so the declaration being defined
may not stand to the left of one — while `Nat → self` is an ordinary field. -/

/--
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs in
example : Ty.Wf (.recAlias (.fn .self (.prim .nat))) := by ty_wf

-- It is not only the bare occurrence that is refused: anything the occurrence is inside
-- of is refused in a domain as well.
/--
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs in
example : Ty.Wf (.recAlias (.fn (.array .self) (.prim .nat))) := by ty_wf

-- `μX. ⊥ | (Nat → X)`: the occurrence is to the *right* of the arrow, and the first
-- constructor is the base case that gives the type its values.
example :
    Ty.Wf (.recTaggedUnion (.skip (.here ⟨.fn (.prim .nat) .self, []⟩ []))) := by ty_wf

/-! ## The conditions on their own

`ty_wf` proves each of the propositions `Ty.Wf` is built from, not only the whole; these
are the inhabitation ones. -/

example : Ty.HabIn [] (.array .self) := by ty_wf
example : Ty.HabIn [0] .self := by ty_wf
example : Ty.HabIn [] (tyOf (List Nat)) := by ty_wf

end WfTest
