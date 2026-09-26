module

public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 2` on mutual trees: two looks

Part of the tree-and-forest tests; see
`TermTests/MutualFamilyToTermTest/TreeForest/Common.lean`.  At depth `2` the branch of a
node may read its first child — a look into the forest and a look into its first tree —
or the answers at its first two children. -/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The label of the first child: two looks, into the forest and into its first tree -/

mutual
def treeFirstKid_with_k2 : Tree → Nat
  | .node l .nil => l
  | .node l (.cons (.node m _) r) => l * m + forestFirstKid_with_k2 r
def forestFirstKid_with_k2 : Forest → Nat
  | .nil => 0
  | .cons t r => treeFirstKid_with_k2 t + forestFirstKid_with_k2 r
end

def treeFirstKid_with_k2_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeFirstKid_with_k2
def forestFirstKid_with_k2_term : Term sigAdd [] (forestT ⇒ natT) :=
  #leanscript_to_term forestFirstKid_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeFirstKid_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? forestFirstKid_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeFirstKid_with_k2_term (runAdd tree1_term) = 29 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeFirstKid_with_k2_term (spineOf 6) = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeFirstKid_with_k2_term (fullOf 4) = treeFirstKid_with_k2 (Tree.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd forestFirstKid_with_k2_term (runAdd forest1_term) =
-- [SKIPPED BY PROFILE_LAKE]     forestFirstKid_with_k2 forest1 := by kernel_rfl

/-! ## Two arguments: the tribonacci-like count down the first-child spine

The answer at a node reads the answers at its first child and at its second child, both
two looks down. -/

mutual
def treeKids2_with_k2 (s : Nat) : Tree → Nat
  | .node _ .nil => s
  | .node _ (.cons t .nil) => treeKids2_with_k2 s t + 1
  | .node _ (.cons t (.cons u r)) =>
      treeKids2_with_k2 s t + treeKids2_with_k2 s u + forestKids2_with_k2 s r
def forestKids2_with_k2 (s : Nat) : Forest → Nat
  | .nil => 0
  | .cons t r => treeKids2_with_k2 s t + forestKids2_with_k2 s r
end

def treeKids2_with_k2_term : Term sigAdd [] (natT ⇒ treeT ⇒ natT) :=
  #leanscript_to_term treeKids2_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeKids2_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeKids2_with_k2_term 1 (runAdd tree1_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeKids2_with_k2_term 1 (fullOf 4) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeKids2_with_k2_term 3 (spineOf 8) = treeKids2_with_k2 3 (Tree.spine 8) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: the first-child products, scaled and shifted after the tree -/

mutual
def treeFirstKidAff_with_k2 : Tree → Nat → Nat → Nat
  | .node l .nil, m, c => m * l + c
  | .node l (.cons (.node k _) r), m, c => m * l * k + c + forestFirstKidAff_with_k2 r m c
def forestFirstKidAff_with_k2 : Forest → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .cons t r, m, c => treeFirstKidAff_with_k2 t m c + forestFirstKidAff_with_k2 r m c
end

def treeFirstKidAff_with_k2_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeFirstKidAff_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeFirstKidAff_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeFirstKidAff_with_k2_term (runAdd tree1_term) 2 1 = 62 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeFirstKidAff_with_k2_term (fullOf 3) 3 5 =
-- [SKIPPED BY PROFILE_LAKE]     treeFirstKidAff_with_k2 (Tree.full 3) 3 5 := by kernel_rfl

end TermTests.MutualFamilyToTerm.TreeForest

end
