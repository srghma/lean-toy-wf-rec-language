module

public import TyTests.SharedTreesTest

@[expose] public section

/-!
# Sharing spans modules

The table of trees `deriving LeanScriptTyWf` keeps is an environment extension, so a
declaration in *this* module whose tree was already built in an imported one gets that
module's constant and that module's proof — no second tree, and no second check.
-/

open LeanScript

namespace CrossModuleSharingTest

/-- The same tree as `SharedTreesTest.Point`, in another module. -/
structure Coord where
  u : Nat
  v : Nat
  deriving LeanScriptTyWf

/-- info: @[reducible, expose] def CrossModuleSharingTest.Coord.instLeanScriptTyWf : LeanScriptTyWf Coord :=
{ tyWfOf := { toTy := SharedTreesTest.Point.leanScriptTyOf, isWf := SharedTreesTest.Point.leanScriptTyOf_wf } } -/
#guard_msgs in
#print Coord.instLeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Coord = .record ⟨.prim .nat, .prim .nat, []⟩ := by rfl

end CrossModuleSharingTest
