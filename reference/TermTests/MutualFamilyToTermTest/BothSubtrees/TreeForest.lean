module

public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec k` on mutual trees: below the tree and the rest at once

Part of the tests of looks into several subvalues; see
`TermTests/MutualFamilyToTermTest/BothSubtrees/Common.lean`.  The family is the tree and
its forest of `TermTests/MutualFamilyToTermTest/TreeForest/Common.lean`: a
`Forest.cons t rest` holds two occurrences, and these programs read below **both**: below
the first tree `t`, and then below the rest of the forest. -/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The labels of two neighbouring trees

A look into the first tree (its label), a look into the rest of the forest, and a look
into the tree there (its label): depth `3`. -/

mutual
def treeNeighbours : Tree → Nat
  | .node _ kids => forestNeighbours kids
def forestNeighbours : Forest → Nat
  | .nil => 0
  | .cons (.node a _) (.cons (.node b _) r) => a * b + forestNeighbours r
  | .cons t r => treeNeighbours t + forestNeighbours r
end

def forestNeighbours_term : Term sigAdd [] (forestT ⇒ natT) :=
  #leanscript_to_term forestNeighbours
def treeNeighbours_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term treeNeighbours

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? forestNeighbours_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeNeighbours_term = some 3 := by kernel_rfl
-- `9 * 2`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestNeighbours_term (runAdd forest1_term) = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestNeighbours_term (runAdd forest1_term) = forestNeighbours forest1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestNeighbours_term (leavesOf 5) = forestNeighbours (Forest.leaves 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeNeighbours_term (runAdd tree1_term) = treeNeighbours tree1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeNeighbours_term (fullOf 4) = treeNeighbours (Tree.full 4) := by kernel_rfl

/-! ## Below the first tree and below the rest

The answer at the first child of the first tree, and the answer at the second tree of the
forest: a look into the first tree, one into its children, and one into the rest. -/

mutual
def treeCross : Tree → Nat
  | .node v kids => v + forestCross kids
def forestCross : Forest → Nat
  | .nil => 1
  | .cons (.node a (.cons t _)) (.cons u _) => a + treeCross t * treeCross u
  | .cons t r => treeCross t + forestCross r
end

def forestCross_term : Term sigAdd [] (forestT ⇒ natT) := #leanscript_to_term forestCross
def treeCross_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term treeCross

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? forestCross_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestCross_term (runAdd forest1_term) = forestCross forest1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeCross_term (runAdd tree1_term) = treeCross tree1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeCross_term (fullOf 5) = treeCross (Tree.full 5) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeCross_term (spineOf 5) = treeCross (Tree.spine 5) := by kernel_rfl

end TermTests.MutualFamilyToTerm.TreeForest

end
