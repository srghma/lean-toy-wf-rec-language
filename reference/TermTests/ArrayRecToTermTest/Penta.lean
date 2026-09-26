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

/-! ## `k = 4`: a pentanacci recursion on the elements -/

def pentaArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [_] => 0
    | [_, _] => 0
    | [_, _, _] => 0
    | [x, _, _, _] => x
    | x :: y :: z :: w :: v :: xs =>
        x + go (y :: z :: w :: v :: xs) + go (z :: w :: v :: xs) + go (w :: v :: xs)
          + go (v :: xs) + go xs

def pentaArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term pentaArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? pentaArr_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pentaArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pentaArr_term #[1, 2, 3] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pentaArr_term #[7, 2, 3, 4] = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pentaArr_term #[1, 1, 1, 1, 1, 1] = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pentaArr_term #[3, 1, 4, 1, 5, 9] = pentaArr #[3, 1, 4, 1, 5, 9] := by kernel_rfl

end TermTests.ArrayRecToTerm
