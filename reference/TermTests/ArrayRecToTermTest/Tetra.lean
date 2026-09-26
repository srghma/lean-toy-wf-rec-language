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

/-! ## `k = 3`: a tetranacci recursion on the elements

Four suffixes, and the lists of at most three elements as base answers. -/

def tetraArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | [x, y] => x + y
    | [x, y, z] => x + y + z + go [z]
    | x :: y :: z :: w :: xs =>
        x + go (y :: z :: w :: xs) + go (z :: w :: xs) + go (w :: xs) + go xs

def tetraArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tetraArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? tetraArr_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[2] = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[1, 2] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[1, 2, 3] = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[1, 1, 1, 1] = 8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] -- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[1, 2, 3, 4, 5] = tetraArr #[1, 2, 3, 4, 5] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] -- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
-- [SKIPPED BY PROFILE_LAKE] example : run tetraArr_term #[3, 1, 4, 1, 5] = tetraArr #[3, 1, 4, 1, 5] := by kernel_rfl

end TermTests.ArrayRecToTerm
