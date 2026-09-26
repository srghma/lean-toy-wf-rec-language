module

public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 0` on a family that holds another family

Part of the cross-family tests; see
`TermTests/MutualFamilyToTermTest/CrossBlock/Common.lean` for the families and for what
is checked.  At depth `0` a branch reads the answers at its own occurrences, and folds or
takes apart the values of `A` and `B` it holds. -/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The sum of all labels: a fold of `A`/`B` inside each branch

The branch of `C.leaf` folds its `A` chain and the branch of `D.mk` folds its `B` chain:
the term is a `mutualRecursiveFamily_rec 0` of `C`/`D` whose branches hold
`mutualRecursiveFamily_rec 0`s of `A`/`B`. -/

mutual
def cSum_with_k0 : C → Nat
  | .leaf a => aSum a
  | .node d => dSum_with_k0 d
def dSum_with_k0 : D → Nat
  | .mk c b => cSum_with_k0 c + bSum b
end

def cSum_with_k0_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cSum_with_k0
def dSum_with_k0_term : Term sigAdd [] (dT ⇒ natT) := #leanscript_to_term dSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? dSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cSum_with_k0_term (runAdd c1_term) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cSum_with_k0_term (chainOf 10) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cSum_with_k0_term (chainOf 12) = cSum_with_k0 (C.chain 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd dSum_with_k0_term (runAdd d1_term) = dSum_with_k0 d1 := by kernel_rfl

/-! ## The number of nodes: the other family is not read at all -/

mutual
def cNodes_with_k0 : C → Nat
  | .leaf _ => 0
  | .node d => dNodes_with_k0 d
def dNodes_with_k0 : D → Nat
  | .mk c _ => cNodes_with_k0 c + 1
end

def cNodes_with_k0_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cNodes_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cNodes_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cNodes_with_k0_term (chainOf 9) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cNodes_with_k0_term (runAdd c1_term) = cNodes_with_k0 c1 := by kernel_rfl

/-! ## The head labels: a `casesOn` of `A` and of `B` inside each branch -/

mutual
def cHeads_with_k0 : C → Nat
  | .leaf a => aHead a
  | .node d => dHeads_with_k0 d
def dHeads_with_k0 : D → Nat
  | .mk c b => cHeads_with_k0 c + bHead b
end

def cHeads_with_k0_term : Term sigAdd [] (cT ⇒ natT) := #leanscript_to_term cHeads_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cHeads_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cHeads_with_k0_term (runAdd c1_term) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cHeads_with_k0_term (chainOf 10) = cHeads_with_k0 (C.chain 10) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments: the weighted sum, the weight before the value -/

mutual
def cWeighted_with_k0 (w : Nat) : C → Nat
  | .leaf a => w * aSum a
  | .node d => dWeighted_with_k0 w d
def dWeighted_with_k0 (w : Nat) : D → Nat
  | .mk c b => cWeighted_with_k0 w c + w * bLen b
end

def cWeighted_with_k0_term : Term sigAdd [] (natT ⇒ cT ⇒ natT) :=
  #leanscript_to_term cWeighted_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cWeighted_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cWeighted_with_k0_term 3 (runAdd c1_term) = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cWeighted_with_k0_term 2 (chainOf 8) = cWeighted_with_k0 2 (C.chain 8) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: an accumulator and a depth after the value -/

mutual
def cAcc_with_k0 : C → Nat → Nat → Nat
  | .leaf a, acc, d => acc + d * aLen a
  | .node e, acc, d => dAcc_with_k0 e acc (d + 1)
def dAcc_with_k0 : D → Nat → Nat → Nat
  | .mk c b, acc, d => cAcc_with_k0 c (acc + bSum b) d
end

def cAcc_with_k0_term : Term sigAdd [] (cT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? cAcc_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cAcc_with_k0_term (runAdd c1_term) 0 1 = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cAcc_with_k0_term (chainOf 7) 5 0 = cAcc_with_k0 (C.chain 7) 5 0 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.CrossBlock

end
