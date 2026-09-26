module

public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 3` on a family that holds another family: three looks

Part of the cross-family tests; see
`TermTests/MutualFamilyToTermTest/CrossBlock/Common.lean`.  At depth `3` the branch of a
`C` node reads down to the `C` of the second node below it: `D`, `C`,
`D`, `C`. -/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## Three looks, and the other family folded at the bottom

The branch of a node reads the `B` chains of the next two nodes and the `C` below them —
`D`, `C`, `D`, then the `C`, whose answer it reads — and folds the `A` chain of the leaf,
if it is within reach. -/

mutual
def cDeepB_with_k3 : C → Nat
  | .leaf a => aSum a
  | .node (.mk (.leaf a) b) => aLen a + bSum b
  | .node (.mk (.node (.mk c b')) b) => cDeepB_with_k3 c + bSum b + bLen b'
def dDeepB_with_k3 : D → Nat
  | .mk c b => cDeepB_with_k3 c + bSum b
end

def cDeepB_with_k3_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cDeepB_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cDeepB_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepB_with_k3_term (runAdd c1_term) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepB_with_k3_term (chainOf 11) = 35 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepB_with_k3_term (chainOf 11) = cDeepB_with_k3 (C.chain 11) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments: the scale before the value -/

mutual
def cDeepScaled_with_k3 (m : Nat) : C → Nat
  | .leaf a => m * aSum a
  | .node (.mk (.leaf a) b) => aLen a + m * bSum b
  | .node (.mk (.node (.mk c b')) b) => cDeepScaled_with_k3 m c + bSum b + m * bLen b'
def dDeepScaled_with_k3 (m : Nat) : D → Nat
  | .mk c b => cDeepScaled_with_k3 m c + m * bSum b
end

def cDeepScaled_with_k3_term : Term sigAdd [] (natT ⇒ cT ⇒ natT) :=
  #leanscript_to_term cDeepScaled_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cDeepScaled_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepScaled_with_k3_term 3 (runAdd c1_term) = 22 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepScaled_with_k3_term 2 (chainOf 10) =
-- [SKIPPED BY PROFILE_LAKE]     cDeepScaled_with_k3 2 (C.chain 10) := by kernel_rfl

/-! ## Three arguments: one before and one after the value -/

mutual
def cDeepMixed_with_k3 (s : Nat) : C → Nat → Nat
  | .leaf a, t => s + t * aLen a
  | .node (.mk (.leaf a) b), t => t + s * aSum a + bLen b
  | .node (.mk (.node (.mk c b')) b), t =>
      cDeepMixed_with_k3 s c (t + 2) + t * bSum b + s * bSum b'
def dDeepMixed_with_k3 (s : Nat) : D → Nat → Nat
  | .mk c b, t => cDeepMixed_with_k3 s c t + bLen b
end

def cDeepMixed_with_k3_term : Term sigAdd [] (natT ⇒ cT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cDeepMixed_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cDeepMixed_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepMixed_with_k3_term 2 (runAdd c1_term) 1 = 37 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cDeepMixed_with_k3_term 1 (chainOf 9) 3 = cDeepMixed_with_k3 1 (C.chain 9) 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.CrossBlock

end
