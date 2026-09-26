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

/-! ## `k = 2`: the tribonacci numbers, three cells down -/

def cellTrib : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some g))))) =>
      cellTrib (.mk l₂ (some (.mk l₃ (some g)))) + cellTrib (.mk l₃ (some g)) + cellTrib g

def cellTrib_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellTrib

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellTrib_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 1) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 8) = cellTrib (Cell.ofNat 8) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTrib_term (cellOfNat 12) = cellTrib (Cell.ofNat 12) := by kernel_rfl

end TermTests.RecObjectToTerm
