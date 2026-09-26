module

public import TermTests.RecObjectToTermTest.BinTree.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recObject_rec 0` on a binary recursive record

Part of the binary-tree tests; see `TermTests/RecObjectToTermTest/BinTree/Common.lean`
for the tree and for what is checked. -/

namespace TermTests.RecObjectToTerm.BinTree

open LeanScript TermTests.RecObjectToTerm

/-! ## `k = 0`: the answers at both children

The window of `recObject_rec 0` holds the label and, for each child that is there, the
answer at it. -/

/-! ### The sum of the labels -/

def bSum_with_k0 : BNode → Nat
  | .mk a none none => a
  | .mk a (some l) none => a + bSum_with_k0 l
  | .mk a none (some r) => a + bSum_with_k0 r
  | .mk a (some l) (some r) => a + bSum_with_k0 l + bSum_with_k0 r

def bSum_with_k0_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bSum_with_k0_term (run t1_term) = 28 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bSum_with_k0_term (fullOf 4) = 26 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bSum_with_k0_term (combOf 9) = bSum_with_k0 (BNode.comb 9) := by kernel_rfl

/-! ### The height: a `max` of the answers at the children -/

def bHeight_with_k0 : BNode → Nat
  | .mk _ none none => 0
  | .mk _ (some l) none => bHeight_with_k0 l + 1
  | .mk _ none (some r) => bHeight_with_k0 r + 1
  | .mk _ (some l) (some r) => max (bHeight_with_k0 l) (bHeight_with_k0 r) + 1

def bHeight_with_k0_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bHeight_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bHeight_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bHeight_with_k0_term (run t1_term) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bHeight_with_k0_term (combOf 7) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bHeight_with_k0_term (fullOf 5) = bHeight_with_k0 (BNode.full 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### Two arguments: the weighted sum, the weight before the tree -/

def bWeighted_with_k0 (w : Nat) : BNode → Nat
  | .mk a none none => w * a
  | .mk a (some l) none => w * a + bWeighted_with_k0 w l
  | .mk a none (some r) => w * a + bWeighted_with_k0 w r
  | .mk a (some l) (some r) => w * a + bWeighted_with_k0 w l + bWeighted_with_k0 w r

def bWeighted_with_k0_term : Term sig0 [] (natT ⇒ bnodeT ⇒ natT) :=
  #leanscript_to_term bWeighted_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bWeighted_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bWeighted_with_k0_term 3 (run t1_term) = 84 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bWeighted_with_k0_term 2 (fullOf 4) = bWeighted_with_k0 2 (BNode.full 4) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### Three arguments: the labels weighted by their depth, an accumulator and the depth
after the tree -/

def bDepthSum_with_k0 : BNode → Nat → Nat → Nat
  | .mk a none none, acc, d => acc + d * a
  | .mk a (some l) none, acc, d => bDepthSum_with_k0 l (acc + d * a) (d + 1)
  | .mk a none (some r), acc, d => bDepthSum_with_k0 r (acc + d * a) (d + 1)
  | .mk a (some l) (some r), acc, d =>
      bDepthSum_with_k0 r (bDepthSum_with_k0 l (acc + d * a) (d + 1)) (d + 1)

def bDepthSum_with_k0_term : Term sig0 [] (bnodeT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bDepthSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bDepthSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bDepthSum_with_k0_term (run t1_term) 0 1 = 69 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bDepthSum_with_k0_term (combOf 6) 10 0 = bDepthSum_with_k0 (BNode.comb 6) 10 0 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.RecObjectToTerm.BinTree

end
