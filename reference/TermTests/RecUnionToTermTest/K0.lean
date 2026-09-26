module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec 0`

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
At depth `0` a branch is given the constructor's fields and the answers at its
occurrences, and nothing below them. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `List Nat`: the sum of a list, and the same sum with an accumulator -/

def listSum_with_k0 : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum_with_k0 xs

def listSum_with_k0_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listSum_with_k0_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listSum_with_k0_term (natList [3, 1, 4, 1, 5]) = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listSum_with_k0_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     listSum_with_k0 [3, 1, 4, 1, 5, 9, 2, 6] := by kernel_rfl

def listSumAcc_with_k0 : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => listSumAcc_with_k0 xs (acc + x)

def listSumAcc_with_k0_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT ⇒ natT) :=
  #leanscript_to_term listSumAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listSumAcc_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listSumAcc_with_k0_term (natList [3, 1, 4]) 10 = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listSumAcc_with_k0_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) 7 =
-- [SKIPPED BY PROFILE_LAKE]     listSumAcc_with_k0 [3, 1, 4, 1, 5, 9, 2, 6] 7 := by kernel_rfl

/-! ## `Tree`: the sum of the labels, the number of leaves, and an accumulator loop -/

def treeSum_with_k0 : Tree → Nat
  | .leaf => 0
  | .node l v r => treeSum_with_k0 l + v + treeSum_with_k0 r

def treeSum_with_k0_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? treeSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (runAdd tree7_term) = 36 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (runAdd full_term 3) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_with_k0_term (runAdd full_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     treeSum_with_k0 (Tree.full 5) := by kernel_rfl

def treeLeaves_with_k0 : Tree → Nat
  | .leaf => 1
  | .node l _ r => treeLeaves_with_k0 l + treeLeaves_with_k0 r

def treeLeaves_with_k0_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeLeaves_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? treeLeaves_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k0_term (runAdd full_term 4) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeLeaves_with_k0_term (runAdd tree7_term) = treeLeaves_with_k0 tree7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The labels in order, summed from the left with an accumulator: the fold returns a
    function. -/
def treeSumAcc_with_k0 : Tree → Nat → Nat
  | .leaf, acc => acc
  | .node l v r, acc => treeSumAcc_with_k0 r (treeSumAcc_with_k0 l acc + v)

def treeSumAcc_with_k0_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeSumAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? treeSumAcc_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSumAcc_with_k0_term (runAdd tree7_term) 100 = 136 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSumAcc_with_k0_term (runAdd full_term 4) 3 =
-- [SKIPPED BY PROFILE_LAKE]     treeSumAcc_with_k0 (Tree.full 4) 3 := by kernel_rfl

/-! ## `Tree3`: the sum of the leaves, and the number of nodes -/

def leafSum_with_k0 : Tree3 → Nat
  | .leaf v => v
  | .node a b c => leafSum_with_k0 a + leafSum_with_k0 b + leafSum_with_k0 c

def leafSum_with_k0_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term leafSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? leafSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leafSum_with_k0_term (runAdd tree3a_term) = 28 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leafSum_with_k0_term (runAdd full3_term 4) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leafSum_with_k0_term (runAdd midSpine_term 6) =
-- [SKIPPED BY PROFILE_LAKE]     leafSum_with_k0 (Tree3.midSpine 6) := by kernel_rfl

def nodes_with_k0 : Tree3 → Nat
  | .leaf _ => 0
  | .node a b c => nodes_with_k0 a + nodes_with_k0 b + nodes_with_k0 c + 1

def nodes_with_k0_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term nodes_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? nodes_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nodes_with_k0_term (runAdd full3_term 3) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nodes_with_k0_term (runAdd tree3a_term) = nodes_with_k0 tree3a := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.RecUnionToTerm

end
