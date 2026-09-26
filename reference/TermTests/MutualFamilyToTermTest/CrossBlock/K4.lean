module

public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 4` on a family that holds another family: four looks

Part of the cross-family tests; see
`TermTests/MutualFamilyToTermTest/CrossBlock/Common.lean`.  At depth `4` the branch of a
`C` node reads down to the answer of the `D` of the third node below it. -/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## Tribonacci on the number of nodes: four looks

The answer at a node reads the answers at the next three nodes; the third is the answer
at a `D`, five occurrences down (a node is a `C` and a `D`). -/

mutual
def cTrib_with_k4 : C → Nat
  | .leaf _ => 0
  | .node (.mk (.leaf _) _) => 0
  | .node (.mk (.node (.mk (.leaf _) _)) _) => 1
  | .node (.mk (.node (.mk (.node d) b')) _) =>
      cTrib_with_k4 (.node (.mk (.node d) b')) + dTrib_with_k4 (.mk (.node d) b') +
        dTrib_with_k4 d
def dTrib_with_k4 : D → Nat
  | .mk c _ => cTrib_with_k4 c
end

def cTrib_with_k4_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cTrib_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cTrib_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTrib_with_k4_term (chainOf 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTrib_with_k4_term (chainOf 12) = cTrib_with_k4 (C.chain 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTrib_with_k4_term (runAdd c1_term) = cTrib_with_k4 c1 := by kernel_rfl

/-! ## Two arguments: tribonacci from a start value, plus the `B` chains read on the way -/

mutual
def cTribB_with_k4 (s : Nat) : C → Nat
  | .leaf _ => 0
  | .node (.mk (.leaf _) _) => 0
  | .node (.mk (.node (.mk (.leaf _) _)) _) => s
  | .node (.mk (.node (.mk (.node d) b')) b) =>
      cTribB_with_k4 s (.node (.mk (.node d) b')) + dTribB_with_k4 s (.mk (.node d) b') +
        dTribB_with_k4 s d + bLen b
def dTribB_with_k4 (s : Nat) : D → Nat
  | .mk c _ => cTribB_with_k4 s c
end

def cTribB_with_k4_term : Term sigAdd [] (natT ⇒ cT ⇒ natT) :=
  #leanscript_to_term cTribB_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cTribB_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTribB_with_k4_term 2 (chainOf 10) = 258 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTribB_with_k4_term 1 (chainOf 12) = cTribB_with_k4 1 (C.chain 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: tribonacci from start values before and after the value -/

mutual
def cTribMixed_with_k4 (s : Nat) : C → Nat → Nat
  | .leaf _, _ => 0
  | .node (.mk (.leaf _) _), _ => 0
  | .node (.mk (.node (.mk (.leaf _) _)) _), t => s + t
  | .node (.mk (.node (.mk (.node d) b')) _), t =>
      cTribMixed_with_k4 s (.node (.mk (.node d) b')) t +
        dTribMixed_with_k4 s (.mk (.node d) b') t + dTribMixed_with_k4 s d t
def dTribMixed_with_k4 (s : Nat) : D → Nat → Nat
  | .mk c _, t => cTribMixed_with_k4 s c t
end

def cTribMixed_with_k4_term : Term sigAdd [] (natT ⇒ cT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cTribMixed_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cTribMixed_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTribMixed_with_k4_term 1 (chainOf 7) 1 = 26 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cTribMixed_with_k4 1 (C.chain 7) 1 = 26 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cTribMixed_with_k4_term 2 (chainOf 6) 3 = cTribMixed_with_k4 2 (C.chain 6) 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.CrossBlock

end
