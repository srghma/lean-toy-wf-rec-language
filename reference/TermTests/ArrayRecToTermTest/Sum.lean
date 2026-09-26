module

public import TermTests.ArrayRecToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! Part of the `array_rec k` translation tests; see
`TermTests/ArrayRecToTermTest/Common.lean` for what is checked. -/

namespace TermTests.ArrayRecToTerm

open LeanScript

/-! ## `k = 0`: the sum of an array

`go` descends one element: the branch at `x :: xs` reads `x` and `go xs`. -/

def sumArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | x :: xs => x + go xs

def sumArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? sumArr_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumArr_term #[5] = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumArr_term #[1, 2, 3, 4] = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumArr_term #[1, 2, 3, 4] = sumArr #[1, 2, 3, 4] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumArr_term #[7, 0, 9, 1, 1] = sumArr #[7, 0, 9, 1, 1] := by kernel_rfl

end TermTests.ArrayRecToTerm
