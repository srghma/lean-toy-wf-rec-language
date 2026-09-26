module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec 2`

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
At depth `2` a branch may look twice; the programs here look along one path (see
`BothSubtrees.lean` for looks into several subvalues). -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `List Nat`: the tribonacci numbers of the length -/

def listTrib_with_k2 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 1
  | _ :: y :: z :: rest =>
      listTrib_with_k2 rest + listTrib_with_k2 (z :: rest) + listTrib_with_k2 (y :: z :: rest)

def listTrib_with_k2_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTrib_with_k2_term (natList [5, 5]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTrib_with_k2_term (natList (List.replicate 10 0)) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTrib_with_k2_term (natList (List.range 12)) =
-- [SKIPPED BY PROFILE_LAKE]     listTrib_with_k2 (List.range 12) := by kernel_rfl

/-! ## `Tree`: the tribonacci numbers down the left spine, plus the right subtrees -/

def leftTrib_with_k2 : Tree → Nat
  | .leaf => 0
  | .node .leaf _ r => leftTrib_with_k2 r
  | .node (.node .leaf _ _) _ r => 1 + leftTrib_with_k2 r
  | .node (.node (.node a x b) y c) _ r =>
      leftTrib_with_k2 a + leftTrib_with_k2 (.node a x b) +
        leftTrib_with_k2 (.node (.node a x b) y c) + leftTrib_with_k2 r

def leftTrib_with_k2_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? leftTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftTrib_with_k2_term (runAdd leftSpine_term 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftTrib_with_k2_term (runAdd tree7_term) = leftTrib_with_k2 tree7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftTrib_with_k2_term (runAdd full_term 6) =
-- [SKIPPED BY PROFILE_LAKE]     leftTrib_with_k2 (Tree.full 6) := by kernel_rfl

/-! ## `Tree3`: the tribonacci numbers down the first child -/

def firstTrib_with_k2 : Tree3 → Nat
  | .leaf _ => 0
  | .node (.leaf _) _ _ => 0
  | .node (.node (.leaf _) _ _) _ _ => 1
  | .node (.node (.node a b c) y z) _ _ =>
      firstTrib_with_k2 a + firstTrib_with_k2 (.node a b c) +
        firstTrib_with_k2 (.node (.node a b c) y z)

def firstTrib_with_k2_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term firstTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? firstTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstTrib_with_k2_term (runAdd firstSpine_term 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstTrib_with_k2_term (runAdd firstSpine_term 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstTrib_with_k2_term (runAdd full3_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     firstTrib_with_k2 (Tree3.full 5) := by kernel_rfl

end TermTests.RecUnionToTerm

end
