module

public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 2` on a family that holds another family: two looks

Part of the cross-family tests; see
`TermTests/MutualFamilyToTermTest/CrossBlock/Common.lean`.  At depth `2` the branch of a
`C` node may look into its `D` and then into that `D`'s `C`. -/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## Fibonacci on the number of nodes: two looks, into the `D` and into its `C`

The answer at a node reads the answers at the next node (one look into its `D`) and at
the node after (a second look, into that `D`'s `C`). -/

mutual
def cFib_with_k2 : C → Nat
  | .leaf _ => 0
  | .node (.mk (.leaf _) _) => 1
  | .node (.mk (.node d) _) => cFib_with_k2 (.node d) + dFib_with_k2 d
def dFib_with_k2 : D → Nat
  | .mk c _ => cFib_with_k2 c
end

def cFib_with_k2_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cFib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cFib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFib_with_k2_term (chainOf 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFib_with_k2_term (chainOf 12) = cFib_with_k2 (C.chain 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFib_with_k2_term (runAdd c1_term) = cFib_with_k2 c1 := by kernel_rfl

/-! ## Two arguments: Fibonacci from a start value before the value -/

mutual
def cFibFrom_with_k2 (s : Nat) : C → Nat
  | .leaf _ => 0
  | .node (.mk (.leaf _) _) => s
  | .node (.mk (.node d) _) => cFibFrom_with_k2 s (.node d) + dFibFrom_with_k2 s d
def dFibFrom_with_k2 (s : Nat) : D → Nat
  | .mk c _ => cFibFrom_with_k2 s c
end

def cFibFrom_with_k2_term : Term sigAdd [] (natT ⇒ cT ⇒ natT) :=
  #leanscript_to_term cFibFrom_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cFibFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFibFrom_with_k2_term 3 (chainOf 10) = 165 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFibFrom_with_k2_term 2 (chainOf 9) = cFibFrom_with_k2 2 (C.chain 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: Fibonacci from two start values after the value -/

mutual
def cFibAB_with_k2 : C → Nat → Nat → Nat
  | .leaf _, a, _ => a
  | .node (.mk (.leaf _) _), _, b => b
  | .node (.mk (.node d) _), a, b => cFibAB_with_k2 (.node d) a b + dFibAB_with_k2 d a b
def dFibAB_with_k2 : D → Nat → Nat → Nat
  | .mk c _, a, b => cFibAB_with_k2 c a b
end

def cFibAB_with_k2_term : Term sigAdd [] (cT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cFibAB_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cFibAB_with_k2_term = some 2 := by kernel_rfl
-- the Lucas numbers
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFibAB_with_k2_term (chainOf 7) 2 1 = 29 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cFibAB_with_k2 (C.chain 7) 2 1 = 29 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cFibAB_with_k2_term (chainOf 6) 4 7 = cFibAB_with_k2 (C.chain 6) 4 7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.CrossBlock

end
