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

/-! ## `k = 1`: programs that read two cells down

The window of `recObject_rec 1` holds, for the cell below, the value of the recursion
there *and* that cell's own fields — its label, and the value at the cell below it. -/

/-! ### `fib`, on a chain: `fib (n + 2) = fib n + fib (n + 1)` -/

def cellFib : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 1
  | .mk _ (some (.mk l (some g))) => cellFib (.mk l (some g)) + cellFib g

def cellFib_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellFib

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellFib_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (run chain3_term) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 7) = cellFib (Cell.ofNat 7) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOfNat 12) = cellFib (Cell.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellFib_term (cellOf 3 [1, 4, 1, 5, 9]) =
-- [SKIPPED BY PROFILE_LAKE]     cellFib (Cell.ofList 3 [1, 4, 1, 5, 9]) := by kernel_rfl

/-! ### The continuant of the labels: reads the labels two cells down too

`K ⟨a⟩ = a`, `K ⟨a, b⟩ = a * b + 1` and `K ⟨a, b, …⟩ = a * K ⟨b, …⟩ + K ⟨…⟩`. -/

def cellCont : Cell → Nat
  | .mk a none => a
  | .mk a (some (.mk b none)) => a * cellCont (.mk b none) + 1
  | .mk a (some (.mk b (some g))) => a * cellCont (.mk b (some g)) + cellCont g

def cellCont_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellCont

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellCont_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (cellOf 7 []) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (cellOf 2 [3]) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (run chain3_term) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (cellOf 1 [2, 3, 4]) = 43 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (run chain3_term) = cellCont chain3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellCont_term (cellOf 3 [1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     cellCont (Cell.ofList 3 [1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

/-! ### The sum of the products of neighbouring labels

The branch reads the label of the cell below — which is in the window only at depth
`1` — and the value of the recursion there. -/

def cellNeighbourProducts : Cell → Nat
  | .mk _ none => 0
  | .mk a (some (.mk b n)) => a * b + cellNeighbourProducts (.mk b n)

def cellNeighbourProducts_term : Term sig0 [] (cellT ⇒ natT) :=
  #leanscript_to_term cellNeighbourProducts

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellNeighbourProducts_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellNeighbourProducts_term (cellOf 7 []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellNeighbourProducts_term (run chain3_term) = 8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellNeighbourProducts_term (cellOf 1 [2, 3, 4]) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellNeighbourProducts_term (cellOf 3 [1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     cellNeighbourProducts (Cell.ofList 3 [1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

end TermTests.RecObjectToTerm
