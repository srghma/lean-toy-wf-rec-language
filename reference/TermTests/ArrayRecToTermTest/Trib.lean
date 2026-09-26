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

/-! ## `k = 2`: a tribonacci recursion on the elements

Three suffixes: `go (y :: z :: xs)`, `go (z :: xs)` and `go xs`.  The base answers are
the lists of at most two elements; the answer at `[x, y]` itself reads `go [y]`. -/

def tribArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | [x, y] => x + go [y]
    | x :: y :: z :: xs => x + go (y :: z :: xs) + go (z :: xs) + go xs

def tribArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tribArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? tribArr_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[6] = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[1, 2] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[1, 2, 3] = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[1, 1, 1, 1, 1, 1] = 28 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[1, 2, 3, 4, 5] = tribArr #[1, 2, 3, 4, 5] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] -- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
-- [SKIPPED BY PROFILE_LAKE] example : run tribArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = tribArr #[3, 1, 4, 1, 5, 9, 2, 6] :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

end TermTests.ArrayRecToTerm
