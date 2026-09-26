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

/-! ## `k = 5`: the hexanacci numbers, six cells down -/

def cellHexa : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none))))))))))
      => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅
      (some (.mk l₆ (some g))))))))))) =>
      cellHexa
          (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))))))
        + cellHexa (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))))
        + cellHexa (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))
        + cellHexa (.mk l₅ (some (.mk l₆ (some g)))) + cellHexa (.mk l₆ (some g)) + cellHexa g

def cellHexa_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term cellHexa

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? cellHexa_term = some 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 4) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 5) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 6) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 10) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 9) = cellHexa (Cell.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run cellHexa_term (cellOfNat 12) = cellHexa (Cell.ofNat 12) := by kernel_rfl

end TermTests.RecObjectToTerm
