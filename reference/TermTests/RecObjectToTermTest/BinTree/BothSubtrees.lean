module

public import TermTests.RecObjectToTermTest.BinTree.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

-- The translations below are large terms; compiling them needs a deeper recursion than
-- the default.
set_option maxRecDepth 40000

/-! # `recObject_rec k` on a binary recursive record: below both children

Part of the binary-tree tests; see `TermTests/RecObjectToTermTest/BinTree/Common.lean`
for the tree and for what is checked.

The programs of `TermTests/RecUnionToTermTest/BothSubtrees.lean` read below **both**
children of a node, which a fold of a recursive tagged union reaches by a look into one
child and then one into its sibling.  A fold of a recursive record needs nothing more for
them: its window (`LeanScript.TyWf.recObjectRecBinders`) is given in the shape of the
record's own fields, so at depth `k` it holds the answers at *every* subvalue `k + 1`
levels down, below all the children at once, and the fields of a child are read off the
child itself.  So a program that reads the answers at the grandchildren below both
children is a `recObject_rec 1`. -/

namespace TermTests.RecObjectToTerm.BinTree

open LeanScript TermTests.RecObjectToTerm

/-! ## The sum of the labels at the even levels of the full part

The answer at a node whose two children both have two children is its label plus the
answers at its four grandchildren, below both children: the record version of
`evenLevelSum`, on the nodes where it is written out. -/

def bEvenLevelSum : BNode → Nat
  | .mk v (some (.mk _ (some ll) (some lr))) (some (.mk _ (some rl) (some rr))) =>
      v + bEvenLevelSum ll + bEvenLevelSum lr + bEvenLevelSum rl + bEvenLevelSum rr
  | .mk v _ _ => v

def bEvenLevelSum_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bEvenLevelSum

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bEvenLevelSum_term = some 1 := by kernel_rfl
-- `t1` is not full below the root: its label alone
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenLevelSum_term (run t1_term) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenLevelSum_term (run t1_term) = bEvenLevelSum t1 := by kernel_rfl
-- `full 4`: `4 + 4 * 2 + 16 * 0`
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenLevelSum_term (fullOf 4) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenLevelSum_term (fullOf 6) = bEvenLevelSum (BNode.full 6) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenLevelSum_term (combOf 7) = bEvenLevelSum (BNode.comb 7) := by kernel_rfl

/-! ## The two outer grandchildren

The answer at the left child's left child and at the right child's right child. -/

def bOuter : BNode → Nat
  | .mk v (some (.mk _ (some ll) _)) (some (.mk _ _ (some rr))) => v + bOuter ll + bOuter rr
  | .mk v _ _ => v

def bOuter_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bOuter

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bOuter_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bOuter_term (run t1_term) = bOuter t1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bOuter_term (fullOf 6) = bOuter (BNode.full 6) := by kernel_rfl

/-! ## Across, with the labels of the grandchildren

The labels of the left child's right child and of the right child's left child, and the
answers at them.  Taking the grandchildren apart to read their labels is a look one level
further down than their answers, so this is depth `2`. -/

def bZigLabels : BNode → Nat
  | .mk v (some (.mk _ _ (some (.mk a al ar)))) (some (.mk _ (some (.mk b bl br)) _)) =>
      v + a * b + bZigLabels (.mk a al ar) + bZigLabels (.mk b bl br)
  | .mk v _ _ => v

def bZigLabels_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bZigLabels

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bZigLabels_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bZigLabels_term (run t1_term) = bZigLabels t1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bZigLabels_term (fullOf 5) = bZigLabels (BNode.full 5) := by kernel_rfl

/-! ## Two arguments: a weight per level -/

def bEvenWeighted : BNode → Nat → Nat
  | .mk v (some (.mk _ (some ll) (some lr))) (some (.mk _ (some rl) (some rr))), w =>
      v * w + bEvenWeighted ll (w + 2) + bEvenWeighted lr (w + 2) +
        bEvenWeighted rl (w + 2) + bEvenWeighted rr (w + 2)
  | .mk v _ _, w => v * w

def bEvenWeighted_term : Term sig0 [] (bnodeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bEvenWeighted

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bEvenWeighted_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenWeighted_term (fullOf 5) 1 = bEvenWeighted (BNode.full 5) 1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bEvenWeighted_term (run t1_term) 3 = bEvenWeighted t1 3 := by kernel_rfl

end TermTests.RecObjectToTerm.BinTree

end
