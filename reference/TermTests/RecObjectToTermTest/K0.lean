module

public import TermTests.RecObjectToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! Part of the `recObject_rec k` translation tests; see
`TermTests/RecObjectToTermTest/Common.lean` for what is checked. -/

namespace TermTests.RecObjectToTerm

open LeanScript

/-! ## `k = 0`: programs that read the value one cell down

The window of `recObject_rec 0` holds the label and, for the cell below, the value of the
recursion there — the plain fold of the record. -/

/-! ### The sum of the labels -/

def cellSum : Cell → Nat
  | .mk a none => a
  | .mk a (some c) => a + cellSum c

def cellSum_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellSum

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellSum_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (run chain3_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOfNat 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOf 7 []) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOf 3 [1, 4, 1, 5]) = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (run chain3_term) = cellSum chain3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOfNat 10) = cellSum (Cell.ofNat 10) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellSum_term (cellOf 3 [1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     cellSum (Cell.ofList 3 [1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

/-! ### The number of cells below the top one -/

def cellLen : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some c) => cellLen c + 1

def cellLen_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellLen

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellLen_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (run chain3_term) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (cellOfNat 12) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (cellOf 3 [1, 4, 1, 5]) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (cellOfNat 12) = cellLen (Cell.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellLen_term (cellOf 3 [1, 4, 1, 5]) = cellLen (Cell.ofList 3 [1, 4, 1, 5]) :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

/-! ### The tail-recursive `fib` loop: the value of the fold is a function

The recursion takes two accumulators, so Lean compiles it with them in the motive: the
fold answers a `nat ⇒ nat ⇒ nat` at each cell. -/

def cellFibLoop : Cell → Nat → Nat → Nat
  | .mk _ none, a, _ => a
  | .mk _ (some c), a, b => cellFibLoop c b (a + b)

def cellFibLoop_term : Term sig0 [] (cellT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term cellFibLoop

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellFibLoop_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOfNat 0) 0 1 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOfNat 1) 0 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOfNat 10) 0 1 = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOfNat 5) 2 1 = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOfNat 10) 0 1 = cellFibLoop (Cell.ofNat 10) 0 1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFibLoop_term (cellOf 3 [1, 4, 1, 5, 9]) 2 7 =
-- [SKIPPED BY PROFILE_LAKE]     cellFibLoop (Cell.ofList 3 [1, 4, 1, 5, 9]) 2 7 := by kernel_rfl

/-! ### The pair recursion: the value of the fold is a pair -/

def cellFibPair : Cell → Nat × Nat
  | .mk _ none => (0, 1)
  | .mk _ (some c) => let (a, b) := cellFibPair c; (b, a + b)

def cellFibPair_term := #leanscript_to_term (sig := sig0) cellFibPair

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellFibPair_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run cellFibPair_term (cellOfNat 10)).1 = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run cellFibPair_term (cellOfNat 10)).2.1 = 89 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run cellFibPair_term (cellOfNat 10)).1 = (cellFibPair (Cell.ofNat 10)).1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run cellFibPair_term (cellOf 3 [1, 4, 1])).2.1 =
-- [SKIPPED BY PROFILE_LAKE]     (cellFibPair (Cell.ofList 3 [1, 4, 1])).2 := by kernel_rfl

end TermTests.RecObjectToTerm
