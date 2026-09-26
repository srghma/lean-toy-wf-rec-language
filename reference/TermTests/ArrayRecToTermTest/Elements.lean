module

public import TermTests.ArrayRecToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! Part of the `array_rec k` translation tests; see
`TermTests/ArrayRecToTermTest/Common.lean` for what is checked.

## Reading past the head, and skipping a level

An array has one subvalue at each step, its tail, so there is no "both subtrees" for a
fold of an array to reach: the window of `array_rec k` already holds the answers at all
the `k + 1` nearest suffixes.  The analogue of reading *into* a subvalue is reading the
elements after the head: at depth `k` the branch at `x :: y₁ :: … :: yₖ :: rest` may read
`y₁ … yₖ`, which the translation takes off the tail (the array the branch binds) by
nested `array_casesOn`s.  The tail has at least `k` elements there, so their empty cases
are never taken. -/

namespace TermTests.ArrayRecToTerm

open LeanScript

/-! ### Skipping an element: only the answer two suffixes down -/

def skipArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | x :: _ :: xs => x + go xs

def skipArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term skipArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? skipArr_term = some 1 := by kernel_rfl
-- `3 + 4 + 5 + 2`
-- [SKIPPED BY PROFILE_LAKE] example : run skipArr_term #[3, 1, 4, 1, 5, 9, 2] = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run skipArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = skipArr #[3, 1, 4, 1, 5, 9, 2, 6] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### The second element: the products of neighbouring pairs -/

def pairArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | x :: y :: xs => x * y + go xs

def pairArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term pairArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? pairArr_term = some 1 := by kernel_rfl
-- `3 * 1 + 4 * 1 + 5 * 9 + 2`
-- [SKIPPED BY PROFILE_LAKE] example : run pairArr_term #[3, 1, 4, 1, 5, 9, 2] = 54 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pairArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pairArr_term #[7] = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pairArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = pairArr #[3, 1, 4, 1, 5, 9, 2, 6] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### The next two elements, and the answers at every suffix of the window -/

def windowArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 1
    | [x] => x
    | [x, y] => x + y
    | x :: y :: z :: xs => x * y * z + go (y :: z :: xs) + go (z :: xs) + go xs

def windowArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term windowArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? windowArr_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run windowArr_term #[1, 2, 3] = 6 + 5 + 3 + 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run windowArr_term #[3, 1, 4, 1, 5, 9] = windowArr #[3, 1, 4, 1, 5, 9] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ### The third element only -/

def thirdArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | x :: _ :: z :: xs => x + z + go xs
    | _ => 0

def thirdArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term thirdArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? thirdArr_term = some 2 := by kernel_rfl
-- `3 + 4 + 1 + 9`
-- [SKIPPED BY PROFILE_LAKE] example : run thirdArr_term #[3, 1, 4, 1, 5, 9, 2] = 17 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run thirdArr_term #[3, 1, 4, 1, 5, 9, 2, 6, 5] = thirdArr #[3, 1, 4, 1, 5, 9, 2, 6, 5] :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

end TermTests.ArrayRecToTerm

end
