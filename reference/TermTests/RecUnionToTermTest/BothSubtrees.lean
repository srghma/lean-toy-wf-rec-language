module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k`: looks into several subvalues

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.

The programs of `K0.lean` … `K4.lean` read below one subvalue at a time.  These read
below **several**: after a deeper look into one child, a branch looks into a sibling of
it (`LeanScript.FoldKBranch.deepOuter`), whose node the fold dispatched on further up.
Each look costs one unit of depth, so reading the grandchildren below both children of a
binary tree is depth `2`. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-! ## `Tree`: the sum of the labels at even levels

The answer at a node is its label plus the answers at its grandchildren, below **both**
children: a look into the left child, then one into the right child. -/

def evenLevelSum : Tree → Nat
  | .leaf => 0
  | .node .leaf v .leaf => v
  | .node .leaf v (.node rl _ rr) => v + evenLevelSum rl + evenLevelSum rr
  | .node (.node ll _ lr) v .leaf => v + evenLevelSum ll + evenLevelSum lr
  | .node (.node ll _ lr) v (.node rl _ rr) =>
      v + evenLevelSum ll + evenLevelSum lr + evenLevelSum rl + evenLevelSum rr

def evenLevelSum_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term evenLevelSum

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? evenLevelSum_term = some 2 := by kernel_rfl
-- levels 0 and 2 of `tree7`: `1 + (4 + 5 + 6 + 7)`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelSum_term (runAdd tree7_term) = 23 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelSum_term (runAdd tree7_term) = evenLevelSum tree7 := by kernel_rfl
-- `full 4`: the root, labelled `4`, and the four nodes at level `2`, labelled `2`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelSum_term (runAdd full_term 4) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelSum_term (runAdd full_term 6) = evenLevelSum (Tree.full 6) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelSum_term (runAdd rightSpine_term 7) =
-- [SKIPPED BY PROFILE_LAKE]     evenLevelSum (Tree.rightSpine 7) := by kernel_rfl

/-! ## `Tree`: the same, with a weight per level (two arguments)

The motive is a function, so the answers the fold gives are functions too: the answer at
a grandchild is applied to the weight two levels down. -/

def evenLevelWeighted : Tree → Nat → Nat
  | .leaf, _ => 0
  | .node .leaf v .leaf, w => v * w
  | .node .leaf v (.node rl _ rr), w =>
      v * w + evenLevelWeighted rl (w + 2) + evenLevelWeighted rr (w + 2)
  | .node (.node ll _ lr) v .leaf, w =>
      v * w + evenLevelWeighted ll (w + 2) + evenLevelWeighted lr (w + 2)
  | .node (.node ll _ lr) v (.node rl _ rr), w =>
      v * w + evenLevelWeighted ll (w + 2) + evenLevelWeighted lr (w + 2) +
        evenLevelWeighted rl (w + 2) + evenLevelWeighted rr (w + 2)

def evenLevelWeighted_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term evenLevelWeighted

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? evenLevelWeighted_term = some 2 := by kernel_rfl
-- `1 * 1 + (4 + 5 + 6 + 7) * 3`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelWeighted_term (runAdd tree7_term) 1 = 67 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evenLevelWeighted_term (runAdd full_term 5) 2 =
-- [SKIPPED BY PROFILE_LAKE]     evenLevelWeighted (Tree.full 5) 2 := by kernel_rfl

/-! ## `Tree`: across, from the left child's right child to the right child's left child -/

def zigzag : Tree → Nat
  | .leaf => 1
  | .node (.node _ _ lr) v (.node rl _ _) => v + zigzag lr * zigzag rl
  | .node l v r => v + zigzag l + zigzag r

def zigzag_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term zigzag

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? zigzag_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd zigzag_term (runAdd tree7_term) = zigzag tree7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd zigzag_term (runAdd full_term 6) = zigzag (Tree.full 6) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd zigzag_term (runAdd leftSpine_term 5) = zigzag (Tree.leftSpine 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `Tree`: three levels down both outer spines

The answer reads the great-grandchild at the end of the left spine and the one at the
end of the right spine: two looks down each side, four in all. -/

def outerSpines : Tree → Nat
  | .node (.node (.node lll _ _) _ _) v (.node _ _ (.node _ _ rrr)) =>
      v + outerSpines lll + outerSpines rrr
  | .node l v r => v + outerSpines l + outerSpines r
  | .leaf => 0

def outerSpines_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term outerSpines

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? outerSpines_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd outerSpines_term (runAdd tree7_term) = outerSpines tree7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd outerSpines_term (runAdd full_term 7) = outerSpines (Tree.full 7) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `Tree3`: the first grandchild below the first two children -/

def firstGrand3 : Tree3 → Nat
  | .leaf v => v
  | .node (.node x _ _) (.node y _ _) _ => firstGrand3 x + firstGrand3 y
  | .node a b c => firstGrand3 a + firstGrand3 b + firstGrand3 c

def firstGrand3_term : Term sigAdd [] (tree3T ⇒ natT) := #leanscript_to_term firstGrand3

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? firstGrand3_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstGrand3_term (runAdd tree3a_term) = firstGrand3 tree3a := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstGrand3_term (runAdd full3_term 4) = firstGrand3 (Tree3.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstGrand3_term (runAdd midSpine_term 5) =
-- [SKIPPED BY PROFILE_LAKE]     firstGrand3 (Tree3.midSpine 5) := by kernel_rfl

end TermTests.RecUnionToTerm

end
