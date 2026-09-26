module

public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 3` on mutual trees: three looks

Part of the tree-and-forest tests; see
`TermTests/MutualFamilyToTermTest/TreeForest/Common.lean`.  At depth `3` the branch of a
node may read the answers at its first grandchild: into the forest, into its first tree,
into that tree's forest. -/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## Fibonacci down the first-child spine: three looks

The answer at a node reads the answers at its first child and at *that* child's first
child: into the forest, into its first tree, and into that tree's forest. -/

mutual
def treeSpineFib_with_k3 : Tree → Nat
  | .node _ .nil => 0
  | .node _ (.cons (.node _ .nil) _) => 1
  | .node _ (.cons (.node m (.cons g r')) r) =>
      treeSpineFib_with_k3 (.node m (.cons g r')) + treeSpineFib_with_k3 g +
        forestSpineFib_with_k3 r
def forestSpineFib_with_k3 : Forest → Nat
  | .nil => 0
  | .cons t r => treeSpineFib_with_k3 t + forestSpineFib_with_k3 r
end

def treeSpineFib_with_k3_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeSpineFib_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeSpineFib_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFib_with_k3_term (spineOf 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFib_with_k3_term (spineOf 12) =
-- [SKIPPED BY PROFILE_LAKE]     treeSpineFib_with_k3 (Tree.spine 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFib_with_k3_term (runAdd tree1_term) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFib_with_k3_term (fullOf 4) = treeSpineFib_with_k3 (Tree.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments: the first grandchild's answer, from a start value -/

mutual
def treeGrand_with_k3 (s : Nat) : Tree → Nat
  | .node l .nil => s + l
  | .node l (.cons (.node m .nil) r) => l + m + forestGrand_with_k3 s r
  | .node l (.cons (.node m (.cons g _)) r) =>
      l + m + treeGrand_with_k3 s g + forestGrand_with_k3 s r
def forestGrand_with_k3 (s : Nat) : Forest → Nat
  | .nil => 0
  | .cons t r => treeGrand_with_k3 s t + forestGrand_with_k3 s r
end

def treeGrand_with_k3_term : Term sigAdd [] (natT ⇒ treeT ⇒ natT) :=
  #leanscript_to_term treeGrand_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeGrand_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeGrand_with_k3_term 100 (runAdd tree1_term) = 236 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeGrand_with_k3_term 1 (fullOf 4) = treeGrand_with_k3 1 (Tree.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: Fibonacci down the spine from two start values after the tree -/

mutual
def treeSpineFibFrom_with_k3 : Tree → Nat → Nat → Nat
  | .node _ .nil, a, _ => a
  | .node _ (.cons (.node _ .nil) _), _, b => b
  | .node _ (.cons (.node m (.cons g r')) r), a, b =>
      treeSpineFibFrom_with_k3 (.node m (.cons g r')) a b + treeSpineFibFrom_with_k3 g a b +
        forestSpineFibFrom_with_k3 r a b
def forestSpineFibFrom_with_k3 : Forest → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .cons t r, a, b => treeSpineFibFrom_with_k3 t a b + forestSpineFibFrom_with_k3 r a b
end

def treeSpineFibFrom_with_k3_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeSpineFibFrom_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? treeSpineFibFrom_with_k3_term = some 3 := by kernel_rfl
-- the Lucas numbers
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFibFrom_with_k3_term (spineOf 7) 2 1 = 29 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : treeSpineFibFrom_with_k3 (Tree.spine 7) 2 1 = 29 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSpineFibFrom_with_k3_term (runAdd tree1_term) 2 1 =
-- [SKIPPED BY PROFILE_LAKE]     treeSpineFibFrom_with_k3 tree1 2 1 := by kernel_rfl

end TermTests.MutualFamilyToTerm.TreeForest

end
