module

public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 1` on mutual trees: one look

Part of the tree-and-forest tests; see
`TermTests/MutualFamilyToTermTest/TreeForest/Common.lean`.  At depth `1` the branch of a
node may look into its forest (to see whether it is empty, or its first tree's answer),
and the branch of a forest may look into its first tree. -/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The number of leaves: the branch of a node looks into its forest

A node is a leaf when its forest is empty, which the branch of `Tree.node` sees only by
looking into the forest. -/

mutual
def treeLeaves_with_k1 : Tree → Nat
  | .node _ .nil => 1
  | .node _ (.cons t r) => treeLeaves_with_k1 t + forestLeaves_with_k1 r
def forestLeaves_with_k1 : Forest → Nat
  | .nil => 0
  | .cons t r => treeLeaves_with_k1 t + forestLeaves_with_k1 r
end

def treeLeaves_with_k1_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeLeaves_with_k1
def forestLeaves_with_k1_term : Term sigAdd [] (forestT ⇒ natT) :=
  #leanscript_to_term forestLeaves_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeLeaves_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? forestLeaves_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k1_term (fullOf 5) = 32 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k1_term (runAdd tree1_term) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k1_term (spineOf 7) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k1_term (fullOf 4) = treeLeaves_with_k1 (Tree.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestLeaves_with_k1_term (leavesOf 9) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestLeaves_with_k1_term (runAdd forest1_term) =
-- [SKIPPED BY PROFILE_LAKE]     forestLeaves_with_k1 forest1 := by kernel_rfl

/-! ## The labels of the roots of a forest: the branch of a forest looks into its tree

A function on `Forest` alone (it never calls itself on a tree), so Lean compiles it with
the motive of `Tree` set to `PUnit`. -/

def rootLabels_with_k1 : Forest → Nat
  | .nil => 0
  | .cons (.node l _) r => l + rootLabels_with_k1 r

def rootLabels_with_k1_term : Term sigAdd [] (forestT ⇒ natT) :=
  #leanscript_to_term rootLabels_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? rootLabels_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rootLabels_with_k1_term (leavesOf 10) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rootLabels_with_k1_term (runAdd forest1_term) = 11 := by kernel_rfl

/-! ## Two arguments: the leaves weighted by a value before the tree -/

mutual
def treeLeavesW_with_k1 (w : Nat) : Tree → Nat
  | .node l .nil => w * l
  | .node _ (.cons t r) => treeLeavesW_with_k1 w t + forestLeavesW_with_k1 w r
def forestLeavesW_with_k1 (w : Nat) : Forest → Nat
  | .nil => 0
  | .cons t r => treeLeavesW_with_k1 w t + forestLeavesW_with_k1 w r
end

def treeLeavesW_with_k1_term : Term sigAdd [] (natT ⇒ treeT ⇒ natT) :=
  #leanscript_to_term treeLeavesW_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeLeavesW_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeavesW_with_k1_term 3 (runAdd tree1_term) = 69 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeavesW_with_k1_term 2 (fullOf 4) = treeLeavesW_with_k1 2 (Tree.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: the depth of the leaves, with a start depth and a step after the tree -/

mutual
def treeLeafDepths_with_k1 : Tree → Nat → Nat → Nat
  | .node _ .nil, d, _ => d
  | .node _ (.cons t r), d, s =>
      treeLeafDepths_with_k1 t (d + s) s + forestLeafDepths_with_k1 r (d + s) s
def forestLeafDepths_with_k1 : Forest → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .cons t r, d, s => treeLeafDepths_with_k1 t d s + forestLeafDepths_with_k1 r d s
end

def treeLeafDepths_with_k1_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeLeafDepths_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeLeafDepths_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeafDepths_with_k1_term (runAdd tree1_term) 0 1 = 8 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeafDepths_with_k1_term (fullOf 3) 1 2 =
-- [SKIPPED BY PROFILE_LAKE]     treeLeafDepths_with_k1 (Tree.full 3) 1 2 := by kernel_rfl

end TermTests.MutualFamilyToTerm.TreeForest

end
