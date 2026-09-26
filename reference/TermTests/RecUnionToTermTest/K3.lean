module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec 3`

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
At depth `3` a branch may look three times; the programs here look along one path (see
`BothSubtrees.lean` for looks into several subvalues). -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `List Nat`: the tetranacci numbers of the length -/

def listTetra_with_k3 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 0
  | [_, _, _] => 1
  | _ :: y :: z :: w :: rest =>
      listTetra_with_k3 rest + listTetra_with_k3 (w :: rest) +
        listTetra_with_k3 (z :: w :: rest) + listTetra_with_k3 (y :: z :: w :: rest)

def listTetra_with_k3_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? listTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTetra_with_k3_term (natList [1, 2, 3]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTetra_with_k3_term (natList (List.replicate 10 0)) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd listTetra_with_k3_term (natList (List.range 12)) =
-- [SKIPPED BY PROFILE_LAKE]     listTetra_with_k3 (List.range 12) := by kernel_rfl

/-! ## `Tree`: the tetranacci numbers down the right spine -/

def rightTetra_with_k3 : Tree → Nat
  | .leaf => 0
  | .node _ _ .leaf => 0
  | .node _ _ (.node _ _ .leaf) => 0
  | .node _ _ (.node _ _ (.node _ _ .leaf)) => 1
  | .node _ _ (.node l1 v1 (.node l2 v2 (.node a x b))) =>
      rightTetra_with_k3 b + rightTetra_with_k3 (.node a x b) +
        rightTetra_with_k3 (.node l2 v2 (.node a x b)) +
        rightTetra_with_k3 (.node l1 v1 (.node l2 v2 (.node a x b)))

def rightTetra_with_k3_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term rightTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? rightTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightTetra_with_k3_term (runAdd rightSpine_term 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightTetra_with_k3_term (runAdd rightSpine_term 10) =
-- [SKIPPED BY PROFILE_LAKE]     rightTetra_with_k3 (Tree.rightSpine 10) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rightTetra_with_k3_term (runAdd full_term 7) =
-- [SKIPPED BY PROFILE_LAKE]     rightTetra_with_k3 (Tree.full 7) := by kernel_rfl

/-! ## `Tree3`: the tetranacci numbers down the middle child, plus the leaves beside it -/

def midTetra_with_k3 : Tree3 → Nat
  | .leaf _ => 0
  | .node _ (.leaf _) _ => 0
  | .node _ (.node _ (.leaf _) _) _ => 0
  | .node a (.node _ (.node _ (.leaf _) _) _) c => 1 + midTetra_with_k3 a + midTetra_with_k3 c
  | .node _ (.node p (.node q (.node x y z) r) s) _ =>
      midTetra_with_k3 y + midTetra_with_k3 (.node x y z) +
        midTetra_with_k3 (.node q (.node x y z) r) +
        midTetra_with_k3 (.node p (.node q (.node x y z) r) s)

def midTetra_with_k3_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term midTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? midTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midTetra_with_k3_term (runAdd midSpine_term 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midTetra_with_k3_term (runAdd midSpine_term 10) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midTetra_with_k3_term (runAdd tree3a_term) = midTetra_with_k3 tree3a := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd midTetra_with_k3_term (runAdd full3_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     midTetra_with_k3 (Tree3.full 5) := by kernel_rfl

end TermTests.RecUnionToTerm

end
