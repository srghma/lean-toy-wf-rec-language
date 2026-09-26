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

/-! ## `k = 4`: the pentanacci numbers, five cells down -/

def cellPenta : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g))))))))) =>
      cellPenta (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g)))))))) +
      cellPenta (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g)))))) +
      cellPenta (.mk l₄ (some (.mk l₅ (some g)))) + cellPenta (.mk l₅ (some g)) + cellPenta g

def cellPenta_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellPenta

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellPenta_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 3) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 5) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 10) = 31 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 9) = cellPenta (Cell.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellPenta_term (cellOfNat 12) = cellPenta (Cell.ofNat 12) := by kernel_rfl

end TermTests.RecObjectToTerm
