module

public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 1` on a family that holds another family: one look

Part of the cross-family tests; see
`TermTests/MutualFamilyToTermTest/CrossBlock/Common.lean`.  At depth `1` the branch of a
`C` node may look into its `D` record, and the branch of a `D` into its `C`, and fold or
take apart the values of the other family found there. -/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The branch of a `C` node looks into its `D`

`C.node d` reads the `C` and the `B` inside `d`, one look down, and folds the `B` there. -/

mutual
def cLook_with_k1 : C → Nat
  | .leaf a => aLen a
  | .node (.mk c b) => cLook_with_k1 c + 2 * bSum b
def dLook_with_k1 : D → Nat
  | .mk c b => cLook_with_k1 c + bSum b
end

def cLook_with_k1_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cLook_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cLook_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLook_with_k1_term (runAdd c1_term) = 38 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLook_with_k1_term (chainOf 10) = 90 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLook_with_k1_term (chainOf 11) = cLook_with_k1 (C.chain 11) := by kernel_rfl

/-! ## The branch of a `D` looks into its `C` and reads the head of its `A` -/

/-- A `D` whose `C` is a node. -/
def d2 : D :=
  .mk (.node (.mk (.leaf (.next 4 (.next 1 .stop))) (.next 5 .stop))) (.next 2 (.next 3 .stop))
/-- `d2`, as a term. -/
def d2_term : Term sigAdd [] dT := #leanscript_to_term d2

def dLeafHead_with_k1 : D → Nat
  | .mk (.leaf a) b => aHead a * bLen b
  | .mk (.node d) b => dLeafHead_with_k1 d + bLen b

def dLeafHead_with_k1_term : Term sigAdd [] (dT ⇒ natT) := #leanscript_to_term dLeafHead_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? dLeafHead_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd dLeafHead_with_k1_term (runAdd d1_term) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd dLeafHead_with_k1_term (runAdd d2_term) = dLeafHead_with_k1 d2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments, the scale before the value -/

mutual
def cLookScaled_with_k1 (m : Nat) : C → Nat
  | .leaf a => m + aLen a
  | .node (.mk c b) => cLookScaled_with_k1 m c + m * bSum b
def dLookScaled_with_k1 (m : Nat) : D → Nat
  | .mk c b => cLookScaled_with_k1 m c + bSum b
end

def cLookScaled_with_k1_term : Term sigAdd [] (natT ⇒ cT ⇒ natT) :=
  #leanscript_to_term cLookScaled_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cLookScaled_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLookScaled_with_k1_term 3 (runAdd c1_term) = 59 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLookScaled_with_k1_term 2 (chainOf 9) = cLookScaled_with_k1 2 (C.chain 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments, one before and one after the value -/

mutual
def cLookMixed_with_k1 (s : Nat) : C → Nat → Nat
  | .leaf a, t => s + t * aLen a
  | .node (.mk c b), t => cLookMixed_with_k1 s c (t + 1) + t * bSum b
def dLookMixed_with_k1 (s : Nat) : D → Nat → Nat
  | .mk c b, t => cLookMixed_with_k1 s c t + bSum b
end

def cLookMixed_with_k1_term : Term sigAdd [] (natT ⇒ cT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cLookMixed_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cLookMixed_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLookMixed_with_k1_term 10 (runAdd c1_term) 1 = 45 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLookMixed_with_k1_term 1 (chainOf 8) 2 = cLookMixed_with_k1 1 (C.chain 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.CrossBlock

end
