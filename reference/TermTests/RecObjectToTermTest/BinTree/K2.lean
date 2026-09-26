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

/-! # `recObject_rec 2` on a binary recursive record

Part of the binary-tree tests; see `TermTests/RecObjectToTermTest/BinTree/Common.lean`
for the tree and for what is checked. -/

namespace TermTests.RecObjectToTerm.BinTree

open LeanScript TermTests.RecObjectToTerm

/-! ## `k = 2`: three levels down -/

/-! ### Tribonacci along the left spine -/

def bLeftTrib_with_k2 : BNode → Nat
  | .mk _ none _ => 0
  | .mk _ (some (.mk _ none _)) _ => 0
  | .mk _ (some (.mk _ (some (.mk _ none _)) _)) _ => 1
  | .mk _ (some (.mk l (some (.mk l' (some g) r')) r)) _ =>
      bLeftTrib_with_k2 (.mk l (some (.mk l' (some g) r')) r) +
        bLeftTrib_with_k2 (.mk l' (some g) r') + bLeftTrib_with_k2 g

def bLeftTrib_with_k2_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bLeftTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTrib_with_k2_term (combOf 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTrib_with_k2_term (fullOf 6) = bLeftTrib_with_k2 (BNode.full 6) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTrib_with_k2_term (run t1_term) = bLeftTrib_with_k2 t1 := by kernel_rfl

/-! ### Two arguments: tribonacci from a start value -/

def bLeftTribFrom_with_k2 (s : Nat) : BNode → Nat
  | .mk _ none _ => 0
  | .mk _ (some (.mk _ none _)) _ => 0
  | .mk _ (some (.mk _ (some (.mk _ none _)) _)) _ => s
  | .mk _ (some (.mk l (some (.mk l' (some g) r')) r)) _ =>
      bLeftTribFrom_with_k2 s (.mk l (some (.mk l' (some g) r')) r) +
        bLeftTribFrom_with_k2 s (.mk l' (some g) r') + bLeftTribFrom_with_k2 s g

def bLeftTribFrom_with_k2_term : Term sig0 [] (natT ⇒ bnodeT ⇒ natT) :=
  #leanscript_to_term bLeftTribFrom_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftTribFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTribFrom_with_k2_term 2 (combOf 10) = 162 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTribFrom_with_k2_term 3 (fullOf 5) = bLeftTribFrom_with_k2 3 (BNode.full 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### Three arguments: start values before and after the tree -/

def bLeftTribMixed_with_k2 (s : Nat) : BNode → Nat → Nat
  | .mk _ none _, _ => 0
  | .mk _ (some (.mk _ none _)) _, t => t
  | .mk _ (some (.mk _ (some (.mk _ none _)) _)) _, t => s + t
  | .mk _ (some (.mk l (some (.mk l' (some g) r')) r)) _, t =>
      bLeftTribMixed_with_k2 s (.mk l (some (.mk l' (some g) r')) r) t +
        bLeftTribMixed_with_k2 s (.mk l' (some g) r') t + bLeftTribMixed_with_k2 s g t

def bLeftTribMixed_with_k2_term : Term sig0 [] (natT ⇒ bnodeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bLeftTribMixed_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftTribMixed_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTribMixed_with_k2_term 1 (combOf 7) 1 = 37 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bLeftTribMixed_with_k2 1 (BNode.comb 7) 1 = 37 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftTribMixed_with_k2_term 2 (combOf 6) 3 =
-- [SKIPPED BY PROFILE_LAKE]     bLeftTribMixed_with_k2 2 (BNode.comb 6) 3 := by kernel_rfl

end TermTests.RecObjectToTerm.BinTree

end
