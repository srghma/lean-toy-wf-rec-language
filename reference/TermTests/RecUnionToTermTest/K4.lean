module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec 4`

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
At depth `4` a branch may look four times; the programs here look along one path (see
`BothSubtrees.lean` for looks into several subvalues). -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `List Nat`: the pentanacci numbers of the length -/

def listPenta_with_k4 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 0
  | [_, _, _] => 0
  | [_, _, _, _] => 1
  | _ :: y :: z :: w :: v :: rest =>
      listPenta_with_k4 rest + listPenta_with_k4 (v :: rest) +
        listPenta_with_k4 (w :: v :: rest) + listPenta_with_k4 (z :: w :: v :: rest) +
        listPenta_with_k4 (y :: z :: w :: v :: rest)

def listPenta_with_k4_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listPenta_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listPenta_with_k4_term (natList [1, 2, 3, 4]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listPenta_with_k4_term (natList (List.replicate 10 0)) = 31 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listPenta_with_k4_term (natList (List.range 13)) =
-- [SKIPPED BY PROFILE_LAKE]     listPenta_with_k4 (List.range 13) := by kernel_rfl

/-! ## `Tree`: the pentanacci numbers down the left spine, reading the labels -/

def leftPenta_with_k4 : Tree → Nat
  | .leaf => 0
  | .node .leaf v _ => v
  | .node (.node .leaf _ _) _ _ => 0
  | .node (.node (.node .leaf _ _) _ _) _ _ => 0
  | .node (.node (.node (.node .leaf _ _) _ _) _ _) _ _ => 1
  | .node (.node (.node (.node (.node a x b) y c) z d) w e) _ _ =>
      leftPenta_with_k4 a + leftPenta_with_k4 (.node a x b) +
        leftPenta_with_k4 (.node (.node a x b) y c) +
        leftPenta_with_k4 (.node (.node (.node a x b) y c) z d) +
        leftPenta_with_k4 (.node (.node (.node (.node a x b) y c) z d) w e)

def leftPenta_with_k4_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftPenta_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? leftPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftPenta_with_k4_term (runAdd leftSpine_term 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftPenta_with_k4_term (runAdd leftSpine_term 12) =
-- [SKIPPED BY PROFILE_LAKE]     leftPenta_with_k4 (Tree.leftSpine 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftPenta_with_k4_term (runAdd full_term 7) =
-- [SKIPPED BY PROFILE_LAKE]     leftPenta_with_k4 (Tree.full 7) := by kernel_rfl

/-! ## `Tree3`: the pentanacci numbers down the last child, reading the leaves -/

def lastPenta_with_k4 : Tree3 → Nat
  | .leaf v => v
  | .node _ _ (.leaf _) => 0
  | .node _ _ (.node _ _ (.leaf _)) => 0
  | .node _ _ (.node _ _ (.node _ _ (.leaf _))) => 0
  | .node _ _ (.node _ _ (.node _ _ (.node _ _ (.leaf _)))) => 1
  | .node _ _ (.node p1 q1 (.node p2 q2 (.node p3 q3 (.node a b c)))) =>
      lastPenta_with_k4 c + lastPenta_with_k4 (.node a b c) +
        lastPenta_with_k4 (.node p3 q3 (.node a b c)) +
        lastPenta_with_k4 (.node p2 q2 (.node p3 q3 (.node a b c))) +
        lastPenta_with_k4 (.node p1 q1 (.node p2 q2 (.node p3 q3 (.node a b c))))

def lastPenta_with_k4_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term lastPenta_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? lastPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastPenta_with_k4_term (runAdd lastSpine_term 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastPenta_with_k4_term (runAdd lastSpine_term 12) =
-- [SKIPPED BY PROFILE_LAKE]     lastPenta_with_k4 (Tree3.lastSpine 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lastPenta_with_k4_term (runAdd full3_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     lastPenta_with_k4 (Tree3.full 5) := by kernel_rfl

end TermTests.RecUnionToTerm

end
