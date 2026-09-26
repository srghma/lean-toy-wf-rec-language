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

/-! ## `k = 3`: the tetranacci numbers, four cells down -/

def cellTetra : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some g))))))) =>
      cellTetra (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some g)))))) +
      cellTetra (.mk l₃ (some (.mk l₄ (some g)))) + cellTetra (.mk l₄ (some g)) + cellTetra g

def cellTetra_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellTetra

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellTetra_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 2) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 10) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 9) = cellTetra (Cell.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellTetra_term (cellOfNat 12) = cellTetra (Cell.ofNat 12) := by kernel_rfl

end TermTests.RecObjectToTerm
