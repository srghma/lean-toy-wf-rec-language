module

public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 0` on mutual trees

Part of the tree-and-forest tests; see
`TermTests/MutualFamilyToTermTest/TreeForest/Common.lean` for the family and for what is
checked.  At depth `0` a branch reads only the answers at the occurrences it holds: a
node's answer from its forest's, a forest's from its first tree's and the rest's.  Sums
and sizes, a sum by level (the level after the tree, so the fold answers a function), a
three-argument version, and a `match` that does not recurse (a `casesOn`, no fold). -/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The sum of the labels, and the number of nodes -/

mutual
def treeSum_with_k0 : Tree → Nat
  | .node l f => l + forestSum_with_k0 f
def forestSum_with_k0 : Forest → Nat
  | .nil => 0
  | .cons t r => treeSum_with_k0 t + forestSum_with_k0 r
end

def treeSum_with_k0_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term treeSum_with_k0
def forestSum_with_k0_term : Term sigAdd [] (forestT ⇒ natT) :=
  #leanscript_to_term forestSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? forestSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (runAdd tree1_term) = 36 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (fullOf 4) = 26 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (fullOf 5) = treeSum_with_k0 (Tree.full 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestSum_with_k0_term (leavesOf 10) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestSum_with_k0_term (runAdd forest1_term) = forestSum_with_k0 forest1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

mutual
def treeSize_with_k0 : Tree → Nat
  | .node _ f => forestSize_with_k0 f + 1
def forestSize_with_k0 : Forest → Nat
  | .nil => 0
  | .cons t r => treeSize_with_k0 t + forestSize_with_k0 r
end

def treeSize_with_k0_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term treeSize_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeSize_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSize_with_k0_term (fullOf 5) = 63 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSize_with_k0_term (spineOf 9) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSize_with_k0_term (runAdd tree1_term) = treeSize_with_k0 tree1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments: the sum of `level · label`, the level after the tree

The level is in Lean's motive, so the fold answers a function `Nat → Nat`, and the
forest passes the *same* level to all its trees while a node passes the next one down. -/

mutual
def treeLevelSum_with_k0 : Tree → Nat → Nat
  | .node l f, d => d * l + forestLevelSum_with_k0 f (d + 1)
def forestLevelSum_with_k0 : Forest → Nat → Nat
  | .nil, _ => 0
  | .cons t r, d => treeLevelSum_with_k0 t d + forestLevelSum_with_k0 r d
end

def treeLevelSum_with_k0_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeLevelSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeLevelSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLevelSum_with_k0_term (runAdd tree1_term) 1 = 110 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLevelSum_with_k0_term (fullOf 4) 0 =
-- [SKIPPED BY PROFILE_LAKE]     treeLevelSum_with_k0 (Tree.full 4) 0 := by kernel_rfl

/-! ## Three arguments: a weight before the tree, a level and a bound after it

`treeBounded_with_k0 w t d b` adds `w · label` for the nodes of level at most `b`. -/

mutual
def treeBounded_with_k0 (w : Nat) : Tree → Nat → Nat → Nat
  | .node l f, d, b => (if d ≤ b then w * l else 0) + forestBounded_with_k0 w f (d + 1) b
def forestBounded_with_k0 (w : Nat) : Forest → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .cons t r, d, b => treeBounded_with_k0 w t d b + forestBounded_with_k0 w r d b
end

def treeBounded_with_k0_term : Term sigAdd [] (natT ⇒ treeT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeBounded_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeBounded_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeBounded_with_k0_term 10 (runAdd tree1_term) 0 1 = 140 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeBounded_with_k0_term 2 (fullOf 4) 0 2 =
-- [SKIPPED BY PROFILE_LAKE]     treeBounded_with_k0 2 (Tree.full 4) 0 2 := by kernel_rfl

/-! ## A `match` that does not recurse is a `casesOn`

The label of the first child: a record `casesOn` of the tree, then a `casesOn` of the
forest, then a record `casesOn` of its first tree — no fold. -/

def firstChildLabel : Tree → Nat
  | .node _ (.cons (.node l _) _) => l
  | .node l .nil => l

def firstChildLabel_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term firstChildLabel

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? firstChildLabel_term = none := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstChildLabel_term (runAdd tree1_term) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstChildLabel_term (spineOf 5) = firstChildLabel (Tree.spine 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.TreeForest

end
