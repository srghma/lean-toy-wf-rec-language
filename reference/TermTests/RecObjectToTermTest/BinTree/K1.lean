module

public import TermTests.RecObjectToTermTest.BinTree.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recObject_rec 1` on a binary recursive record

Part of the binary-tree tests; see `TermTests/RecObjectToTermTest/BinTree/Common.lean`
for the tree and for what is checked. -/

namespace TermTests.RecObjectToTerm.BinTree

open LeanScript TermTests.RecObjectToTerm

/-! ## `k = 1`: two levels down

The window of `recObject_rec 1` holds, for each child that is there, the answer at it
*and* its own fields: its label and the answers at its children. -/

/-! ### Fibonacci along the left spine -/

def bLeftFib_with_k1 : BNode → Nat
  | .mk _ none _ => 0
  | .mk _ (some (.mk _ none _)) _ => 1
  | .mk _ (some (.mk l (some g) r)) _ => bLeftFib_with_k1 (.mk l (some g) r) + bLeftFib_with_k1 g

def bLeftFib_with_k1_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bLeftFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFib_with_k1_term (combOf 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFib_with_k1_term (run t1_term) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFib_with_k1_term (fullOf 6) = bLeftFib_with_k1 (BNode.full 6) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### The labels of both children: their product where there are two -/

def bKids_with_k1 : BNode → Nat
  | .mk _ none none => 0
  | .mk _ (some (.mk b l r)) none => b + bKids_with_k1 (.mk b l r)
  | .mk _ none (some (.mk c l r)) => c + bKids_with_k1 (.mk c l r)
  | .mk _ (some (.mk b l r)) (some (.mk c l' r')) =>
      b * c + bKids_with_k1 (.mk b l r) + bKids_with_k1 (.mk c l' r')

def bKids_with_k1_term : Term sig0 [] (bnodeT ⇒ natT) := #leanscript_to_term bKids_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bKids_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bKids_with_k1_term (run t1_term) = 27 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bKids_with_k1_term (fullOf 3) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bKids_with_k1_term (combOf 8) = bKids_with_k1 (BNode.comb 8) := by kernel_rfl

/-! ### Two arguments: Fibonacci along the left spine from a start value -/

def bLeftFibFrom_with_k1 (s : Nat) : BNode → Nat
  | .mk _ none _ => 0
  | .mk _ (some (.mk _ none _)) _ => s
  | .mk _ (some (.mk l (some g) r)) _ =>
      bLeftFibFrom_with_k1 s (.mk l (some g) r) + bLeftFibFrom_with_k1 s g

def bLeftFibFrom_with_k1_term : Term sig0 [] (natT ⇒ bnodeT ⇒ natT) :=
  #leanscript_to_term bLeftFibFrom_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftFibFrom_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFibFrom_with_k1_term 3 (combOf 10) = 165 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFibFrom_with_k1_term 2 (fullOf 5) = bLeftFibFrom_with_k1 2 (BNode.full 5) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### Three arguments: two start values, before and after the tree -/

def bLeftFibAB_with_k1 (a : Nat) : BNode → Nat → Nat
  | .mk _ none _, _ => a
  | .mk _ (some (.mk _ none _)) _, b => b
  | .mk _ (some (.mk l (some g) r)) _, b =>
      bLeftFibAB_with_k1 a (.mk l (some g) r) b + bLeftFibAB_with_k1 a g b

def bLeftFibAB_with_k1_term : Term sig0 [] (natT ⇒ bnodeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bLeftFibAB_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? bLeftFibAB_with_k1_term = some 1 := by kernel_rfl
-- the Lucas numbers
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFibAB_with_k1_term 2 (combOf 7) 1 = 29 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bLeftFibAB_with_k1 2 (BNode.comb 7) 1 = 29 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run bLeftFibAB_with_k1_term 4 (combOf 6) 7 = bLeftFibAB_with_k1 4 (BNode.comb 6) 7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.RecObjectToTerm.BinTree

end
