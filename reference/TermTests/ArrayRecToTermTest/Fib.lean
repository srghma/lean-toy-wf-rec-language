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

/-! ## `k = 1`: a Fibonacci recursion on the elements

`go (x :: y :: xs)` reads `go (y :: xs)` and `go xs`: two suffixes, so `k = 1`, and the
lists `[]` and `[x]` are the base answers. -/

def fibArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | x :: y :: xs => x + go (y :: xs) + go xs

def fibArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? fibArr_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[4] = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[1, 2] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[1, 2, 3, 4] = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[1, 1, 1, 1, 1, 1] = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[1, 2, 3, 4] = fibArr #[1, 2, 3, 4] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fibArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = fibArr #[3, 1, 4, 1, 5, 9, 2, 6] :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

end TermTests.ArrayRecToTerm
