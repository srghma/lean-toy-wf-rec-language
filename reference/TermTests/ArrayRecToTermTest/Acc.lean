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

/-! ## `k = 0` at a function type: an accumulator

A `go` that takes more arguments than the list is compiled with them in the motive, so
the fold is at the function type `nat ⇒ nat`, and the accumulator is passed on the way
down. -/

def sumAccArr (a : Array Nat) : Nat := go a.toList 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => go xs (acc + x)

def sumAccArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumAccArr

-- [SKIPPED BY PROFILE_LAKE] example : run sumAccArr_term #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumAccArr_term #[1, 2, 3, 4] = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumAccArr_term #[1, 2, 3, 4] = sumAccArr #[1, 2, 3, 4] := by kernel_rfl

/-! ## Reading the second element

The branch of `array_rec k` is given the head, the tail and the values of the fold at the
suffixes, and it may read the first `k` elements of the tail
(`TermTests/ArrayRecToTermTest/Elements.lean`).  A `go` that reads the second element is a
depth-`1` fold. -/

def adjArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [_] => 0
    | x :: y :: xs => x + y + go (y :: xs)

def adjArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term adjArr

-- [SKIPPED BY PROFILE_LAKE] example : arrayRecDepth? adjArr_term = some 1 := by kernel_rfl
-- `(1 + 2) + (2 + 3) + (3 + 4)`
-- [SKIPPED BY PROFILE_LAKE] example : run adjArr_term #[1, 2, 3, 4] = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run adjArr_term #[3, 1, 4, 1, 5] = adjArr #[3, 1, 4, 1, 5] := by kernel_rfl

/-! ## What is refused

A `go` that reads the rest of the list itself — here its length — reads something no
depth of `array_rec` gives its branch: the tail is an array, not the Lean list. -/

def lenArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | x :: xs => x * xs.length + go xs

/--
error: `#leanscript_to_term`: this recursion on the elements of an array is not the fold of an array at any depth up to 64 (the option `leanscript.toTerm.maxNatRecDepth`) — the fold `array_rec k` gives its branch the head, the tail and the values at the `k + 1` nearest suffixes of the tail, and the branch may read the first `k` elements of the tail, so a branch that reads the rest of the list after them, or the value at a list that is not a suffix, has no term
-/
#guard_msgs in
def lenArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term lenArr

end TermTests.ArrayRecToTerm
