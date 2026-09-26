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
# One tree per shape, and one check per type

This file pins the two things that make `deriving LeanScriptTyWf` cheap, by printing the
declarations it generates.

* **A mention of a type is a reference to it.**  The tree of a declaration holds the
  *instances* of its field types, not copies of their trees, so a type is translated once
  however often it is mentioned.
* **Two declarations with the same tree share one constant.**  The handler keeps a table
  of the trees it has built — an environment extension, so it spans modules — and a
  declaration whose tree is already there gets an instance and nothing else: no second
  tree, and no second proof.
-/

open LeanScript

namespace SharedTreesTest

structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

/-- info: @[expose] def SharedTreesTest.Point.leanScriptTyOf : Ty :=
Ty.record { fst := tyOf ℕ, snd := tyOf ℕ, rest := [] } -/
#guard_msgs in
#print Point.leanScriptTyOf

/-- A different declaration whose tree is the same one. -/
structure Offset where
  dx : Nat
  dy : Nat
  deriving LeanScriptTyWf

-- No `Offset.leanScriptTyOf` is added: the instance is `Point`'s tree and `Point`'s
-- proof.
/-- info: @[reducible, expose] def SharedTreesTest.Offset.instLeanScriptTyWf : LeanScriptTyWf Offset :=
{ tyWfOf := { toTy := Point.leanScriptTyOf, isWf := Point.leanScriptTyOf_wf } } -/
#guard_msgs in
#print Offset.instLeanScriptTyWf

/-- error: Unknown constant `Offset.leanScriptTyOf` -/
#guard_msgs in
#print Offset.leanScriptTyOf

/-! ## Two mutual families that differ only in their names -/

mutual
  inductive EvA where
    | zero
    | succ : OdA → EvA
  inductive OdA where
    | succ : EvA → OdA
end

mutual
  inductive EvB where
    | zero
    | succ : OdB → EvB
  inductive OdB where
    | succ : EvB → OdB
end

deriving instance LeanScriptTyWf for EvA
deriving instance LeanScriptTyWf for EvB

/-- info: @[reducible, expose] def SharedTreesTest.EvB.instLeanScriptTyWf : LeanScriptTyWf EvB :=
{ tyWfOf := { toTy := EvA.leanScriptTyOf, isWf := EvA.leanScriptTyOf_wf } } -/
#guard_msgs in
#print EvB.instLeanScriptTyWf

/-! ## A field's type is held by reference

`Holder` mentions `List Point`; its tree holds that instance, so neither `List` nor
`Point` is translated again here — and neither is *checked* again, because the proof the
handler writes closes that leaf with the instance's own `isWf`. -/

structure Holder where
  points : List Point
  name : String
  deriving LeanScriptTyWf

/-- info: @[expose] def SharedTreesTest.Holder.leanScriptTyOf : Ty :=
Ty.record { fst := tyOf (List Point), snd := tyOf String, rest := [] } -/
#guard_msgs in
#print Holder.leanScriptTyOf

-- and it still is the tree it should be, once everything is unfolded
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Holder
-- [SKIPPED BY PROFILE_LAKE]       = .record ⟨.recTaggedUnion (.skip (.here ⟨.record ⟨.prim .nat, .prim .nat, []⟩,
-- [SKIPPED BY PROFILE_LAKE]                                                 [.self]⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]                  .prim .string, []⟩ := by rfl

end SharedTreesTest
