module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec 1`

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
At depth `1` a branch may look once into one of its occurrences. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `List Nat`: `fib` of the length, and the sum of the products of neighbours -/

def listFib_with_k1 : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ :: y :: rest => listFib_with_k1 rest + listFib_with_k1 (y :: rest)

def listFib_with_k1_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listFib_with_k1_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listFib_with_k1_term (natList [7]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listFib_with_k1_term (natList (List.replicate 10 0)) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listFib_with_k1_term (natList (List.range 12)) =
-- [SKIPPED BY PROFILE_LAKE]     listFib_with_k1 (List.range 12) := by kernel_rfl

def listNeighbourProducts_with_k1 : List Nat → Nat
  | x :: y :: rest => x * y + listNeighbourProducts_with_k1 (y :: rest)
  | _ => 0

def listNeighbourProducts_with_k1_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listNeighbourProducts_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listNeighbourProducts_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listNeighbourProducts_with_k1_term (natList [7]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listNeighbourProducts_with_k1_term (natList [1, 2, 3, 4]) = 20 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listNeighbourProducts_with_k1_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     listNeighbourProducts_with_k1 [3, 1, 4, 1, 5, 9, 2, 6] := by kernel_rfl

/-! ## `Tree`: `fib` down the left spine, and down the right spine -/

/-- `fib` of the length of the left spine. -/
def leftFib_with_k1 : Tree → Nat
  | .leaf => 0
  | .node .leaf _ _ => 1
  | .node (.node ll v lr) _ _ => leftFib_with_k1 ll + leftFib_with_k1 (.node ll v lr)

def leftFib_with_k1_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? leftFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftFib_with_k1_term (runAdd leftSpine_term 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftFib_with_k1_term (runAdd leftSpine_term 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftFib_with_k1_term (runAdd full_term 6) = leftFib_with_k1 (Tree.full 6) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftFib_with_k1_term (runAdd tree7_term) = leftFib_with_k1 tree7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- Down the right spine: the label of each node times the label of its right child, plus
    the answers at the left subtree and at the right child.  The deeper look goes into the
    *second* occurrence of the tree. -/
def rightProducts_with_k1 : Tree → Nat
  | .leaf => 0
  | .node l _ .leaf => rightProducts_with_k1 l
  | .node l v (.node rl w rr) =>
      v * w + rightProducts_with_k1 l + rightProducts_with_k1 (.node rl w rr)

def rightProducts_with_k1_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term rightProducts_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? rightProducts_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightProducts_with_k1_term (runAdd tree7_term) = 34 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightProducts_with_k1_term (runAdd rightSpine_term 4) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightProducts_with_k1_term (runAdd full_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     rightProducts_with_k1 (Tree.full 5) := by kernel_rfl

/-! ## `Tree3`: `fib` down the middle child, and the sum of the leaves through the last
grandchildren -/

def midFib_with_k1 : Tree3 → Nat
  | .leaf _ => 0
  | .node _ (.leaf _) _ => 1
  | .node _ (.node a b c) _ => midFib_with_k1 b + midFib_with_k1 (.node a b c)

def midFib_with_k1_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term midFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? midFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midFib_with_k1_term (runAdd midSpine_term 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midFib_with_k1_term (runAdd midSpine_term 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midFib_with_k1_term (runAdd tree3a_term) = midFib_with_k1 tree3a := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midFib_with_k1_term (runAdd full3_term 4) =
-- [SKIPPED BY PROFILE_LAKE]     midFib_with_k1 (Tree3.full 4) := by kernel_rfl

/-- The sum of the leaves again, but a node whose last child is a node adds up the answers
    at that child's own children: the deeper look goes into the *third* occurrence. -/
def lastGrandSum_with_k1 : Tree3 → Nat
  | .leaf v => v
  | .node a b (.leaf v) => lastGrandSum_with_k1 a + lastGrandSum_with_k1 b + v
  | .node a b (.node x y z) =>
      lastGrandSum_with_k1 a + lastGrandSum_with_k1 b +
        (lastGrandSum_with_k1 x + lastGrandSum_with_k1 y + lastGrandSum_with_k1 z)

def lastGrandSum_with_k1_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term lastGrandSum_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? lastGrandSum_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastGrandSum_with_k1_term (runAdd tree3a_term) = 28 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastGrandSum_with_k1_term (runAdd lastSpine_term 7) =
-- [SKIPPED BY PROFILE_LAKE]     lastGrandSum_with_k1 (Tree3.lastSpine 7) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastGrandSum_with_k1_term (runAdd full3_term 4) =
-- [SKIPPED BY PROFILE_LAKE]     lastGrandSum_with_k1 (Tree3.full 4) := by kernel_rfl

end TermTests.RecUnionToTerm

end
