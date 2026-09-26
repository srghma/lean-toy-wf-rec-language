module

public import TermTests.MutualFamilyToTermTest.BothSubtrees.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec k` on alternating binary trees: below both children

Part of the tests of looks into several subvalues; see
`TermTests/MutualFamilyToTermTest/BothSubtrees/Common.lean` for the family and for what is
checked. -/

namespace TermTests.MutualFamilyToTerm.BothSubtrees

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The sum of the labels at even levels

The answer at a node is its label plus the answers at its grandchildren, below **both**
children: a look into the left child, then one into the right child — the family version
of `evenLevelSum` in `TermTests/RecUnionToTermTest/BothSubtrees.lean`. -/

mutual
def eEven : ETree → Nat
  | .leaf => 0
  | .node .leaf v .leaf => v
  | .node .leaf v (.node rl _ rr) => v + eEven rl + eEven rr
  | .node (.node ll _ lr) v .leaf => v + eEven ll + eEven lr
  | .node (.node ll _ lr) v (.node rl _ rr) =>
      v + eEven ll + eEven lr + eEven rl + eEven rr
def oEven : OTree → Nat
  | .leaf => 0
  | .node l _ r => eEven l + eEven r
end

def eEven_term : Term sigAdd [] (etreeT ⇒ natT) := #leanscript_to_term eEven

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? eEven_term = some 2 := by kernel_rfl
-- levels 0, 2 and 4 of `et1`: `1 + (4 + 5 + 6 + 7) + 11`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEven_term (runAdd et1_term) = 34 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEven_term (runAdd et1_term) = eEven et1 := by kernel_rfl
-- `full 4`: the root, labelled `4`, the four nodes at level `2`, labelled `2`, and the
-- sixteen leaves at level `4`, labelled `0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEven_term (fullOf 4) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEven_term (fullOf 6) = eEven (ETree.full 6) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEven_term (spineOf 7) = eEven (ETree.spine 7) := by kernel_rfl

/-! ## The same, with a weight per level (two arguments)

The motive is a function, so the answers the fold gives are functions too: the answer at
a grandchild is applied to the weight two levels down. -/

mutual
def eEvenW : ETree → Nat → Nat
  | .leaf, _ => 0
  | .node .leaf v .leaf, w => v * w
  | .node .leaf v (.node rl _ rr), w => v * w + eEvenW rl (w + 2) + eEvenW rr (w + 2)
  | .node (.node ll _ lr) v .leaf, w => v * w + eEvenW ll (w + 2) + eEvenW lr (w + 2)
  | .node (.node ll _ lr) v (.node rl _ rr), w =>
      v * w + eEvenW ll (w + 2) + eEvenW lr (w + 2) + eEvenW rl (w + 2) +
        eEvenW rr (w + 2)
def oEvenW : OTree → Nat → Nat
  | .leaf, _ => 0
  | .node l _ r, w => eEvenW l (w + 1) + eEvenW r (w + 1)
end

def eEvenW_term : Term sigAdd [] (etreeT ⇒ natT ⇒ natT) := #leanscript_to_term eEvenW

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? eEvenW_term = some 2 := by kernel_rfl
-- `1 * 1 + (4 + 5 + 6 + 7) * 3 + 11 * 5`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEvenW_term (runAdd et1_term) 1 = 122 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eEvenW_term (fullOf 5) 2 = eEvenW (ETree.full 5) 2 := by kernel_rfl

/-! ## Across: from the left child's right child to the right child's left child -/

mutual
def eZig : ETree → Nat
  | .leaf => 1
  | .node (.node _ _ lr) v (.node rl _ _) => v + eZig lr * eZig rl
  | .node l v r => v + oZig l + oZig r
def oZig : OTree → Nat
  | .leaf => 1
  | .node (.node _ _ lr) v (.node rl _ _) => v + oZig lr * oZig rl
  | .node l v r => v + eZig l + eZig r
end

def eZig_term : Term sigAdd [] (etreeT ⇒ natT) := #leanscript_to_term eZig

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? eZig_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eZig_term (runAdd et1_term) = eZig et1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eZig_term (fullOf 6) = eZig (ETree.full 6) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eZig_term (spineOf 5) = eZig (ETree.spine 5) := by kernel_rfl

/-! ## Three levels down both outer spines

The answer reads the great-grandchild at the end of the left spine and the one at the end
of the right spine: two looks down each side, four in all. -/

mutual
def eSpines : ETree → Nat
  | .node (.node (.node lll _ _) _ _) v (.node _ _ (.node _ _ rrr)) =>
      v + oSpines lll + oSpines rrr
  | .node l v r => v + oSpines l + oSpines r
  | .leaf => 0
def oSpines : OTree → Nat
  | .node l v r => v + eSpines l + eSpines r
  | .leaf => 0
end

def eSpines_term : Term sigAdd [] (etreeT ⇒ natT) := #leanscript_to_term eSpines

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? eSpines_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eSpines_term (runAdd et1_term) = eSpines et1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eSpines_term (fullOf 7) = eSpines (ETree.full 7) := by kernel_rfl

end TermTests.MutualFamilyToTerm.BothSubtrees

end
