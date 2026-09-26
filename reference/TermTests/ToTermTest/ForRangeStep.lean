module

public import TermTests.ToTermTest.ForReturn
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `for` over a range with a start or a step: `[a:n]`, `[:n:k]`, `[a:n:k]`

A `for i in [start:stop:step]` in the identity monad (`Id.run do …`), translated by
`#leanscript_to_term` and run by `Term.run`.

The indices of such a range are `start + j * step` for `j < size`, where
`size = (stop - start + step - 1) / step` is `Std.Legacy.Range.size`.  So the loop is the
loop over `[:size]` whose body reads the index `start + j * step`
(`LeanScript.ListLibrary.forIn_range_step_eq`), and that loop is translated as any loop over
`[:n]`: as `nat_rec` of the state, or of the step `ForInStep β` when the body can `break` or
`return`.  The arithmetic (`-`, `+`, `*`, `/` on `Nat`) is the language's externs.

Lean's own `for` over a range is defined by well-founded recursion, which the kernel does
not evaluate.  So each program's value is checked twice: the translated program by
`kernel_rfl` against the value written out, and the Lean function by `#guard` (the
compiler) against the same value. -/

namespace TermTests.ToTerm.ForRangeStep

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary
  TermTests.ToTerm.ForBreak

/-! ## A step: `[0:n:2]`, `[:n:3]` -/

/-- The sum of the even numbers below `n`. -/
def sumEvens (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n:2] do
    s := s + i
  return s

def sumEvens_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumEvens

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 1 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 2 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 3 = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 10 = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvens_term 11 = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [0, 1, 2, 3, 10, 11].map sumEvens == [0, 0, 0, 2, 20, 30]

/-- The multiples of `3` below `n`, largest first: `[:n:3]`, without a start. -/
def multiplesOf3 (n : Nat) : List Nat := Id.run do
  let mut acc := []
  for i in [:n:3] do
    acc := i :: acc
  return acc

def multiplesOf3_term : Term sigAdd [] (natT ⇒ natListT) := #leanscript_to_term multiplesOf3

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd multiplesOf3_term 0) = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd multiplesOf3_term 1) = [0] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd multiplesOf3_term 9) = [6, 3, 0] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd multiplesOf3_term 10) = [9, 6, 3, 0] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [0, 1, 9, 10].map multiplesOf3 == [[], [0], [6, 3, 0], [9, 6, 3, 0]]

/-- A step larger than the bound: only the index `0`. -/
def countStep5 (n : Nat) : Nat := Id.run do
  let mut c := 0
  for _ in [0:n:5] do
    c := c + 1
  return c

def countStep5_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term countStep5

-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStep5_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStep5_term 3 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStep5_term 5 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStep5_term 6 = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStep5_term 21 = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [0, 3, 5, 6, 21].map countStep5 == [0, 1, 1, 2, 5]

/-- The bound is an expression: `[0:2 * n:2]` has the `n` indices `0, 2, …, 2n - 2`. -/
def sumEvensBelowDouble (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:2 * n:2] do
    s := s + i
  return s

def sumEvensBelowDouble_term : Term sigAdd [] (natT ⇒ natT) :=
  #leanscript_to_term sumEvensBelowDouble

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvensBelowDouble_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvensBelowDouble_term 4 = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [0, 4].map sumEvensBelowDouble == [0, 12]

/-! ## A start: `[a:n]`, `[1:n:2]`, `[k:n:2]` -/

/-- The sum of `k, k + 1, …, n - 1`; nothing when `n ≤ k`. -/
def sumFrom (k n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [k:n] do
    s := s + i
  return s

def sumFrom_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term sumFrom

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFrom_term 2 5 = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFrom_term 5 2 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFrom_term 3 3 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFrom_term 0 4 = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [sumFrom 2 5, sumFrom 5 2, sumFrom 3 3, sumFrom 0 4] == [9, 0, 0, 6]

/-- The sum of the odd numbers below `n`: `[1:n:2]`. -/
def sumOdds (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1:n:2] do
    s := s + i
  return s

def sumOdds_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumOdds

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumOdds_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumOdds_term 1 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumOdds_term 2 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumOdds_term 10 = 25 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumOdds_term 11 = 25 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [0, 1, 2, 10, 11].map sumOdds == [0, 0, 1, 25, 25]

/-- A start that is a variable: `k, k + 2, …` below `n`. -/
def sumFromStep2 (k n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [k:n:2] do
    s := s + i
  return s

def sumFromStep2_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term sumFromStep2

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFromStep2_term 3 10 = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFromStep2_term 3 11 = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFromStep2_term 3 12 = 35 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFromStep2_term 10 3 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [sumFromStep2 3 10, sumFromStep2 3 11, sumFromStep2 3 12, sumFromStep2 10 3] ==
-- [SKIPPED BY PROFILE_LAKE]   [24, 24, 35, 0]

/-- A step that is not a literal, written as the structure: indices `0, k + 1, …`. -/
def countStepSucc (k n : Nat) : Nat := Id.run do
  let mut c := 0
  for _ in ({ stop := n, step := k + 1, step_pos := Nat.succ_pos k } : Std.Legacy.Range) do
    c := c + 1
  return c

def countStepSucc_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term countStepSucc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStepSucc_term 0 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStepSucc_term 2 7 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStepSucc_term 2 9 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countStepSucc_term 2 10 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [countStepSucc 0 7, countStepSucc 2 7, countStepSucc 2 9, countStepSucc 2 10] ==
-- [SKIPPED BY PROFILE_LAKE]   [7, 3, 3, 4]

/-! ## With `break`, `continue` and `return` -/

/-- `break` in a stepped loop: the sum of the even numbers below `n`, stopping before the
    first one whose square is above `k`. -/
def sumEvensUntil (k n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n:2] do
    if i * i > k then break
    s := s + i
  return s

def sumEvensUntil_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term sumEvensUntil

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvensUntil_term 20 100 = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumEvensUntil_term 1000 10 = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [sumEvensUntil 20 100, sumEvensUntil 1000 10] == [6, 20]

/-- `continue` in a loop with a start and a step: the numbers `1, 4, 7, …` below `n`
    except `7`. -/
def sumSkip7 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1:n:3] do
    if i == 7 then continue
    s := s + i
  return s

def sumSkip7_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumSkip7

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSkip7_term 5 = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSkip7_term 14 = 28 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [sumSkip7 5, sumSkip7 14] == [5, 28]

/-- An early `return` without a `let mut`: the first odd `i < n` with `i * i > k`, or
    `0`. -/
def firstOddSquareAbove (k n : Nat) : Nat := Id.run do
  for i in [1:n:2] do
    if i * i > k then return i
  return 0

def firstOddSquareAbove_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term firstOddSquareAbove

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstOddSquareAbove_term 10 20 = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstOddSquareAbove_term 30 20 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstOddSquareAbove_term 30 6 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [firstOddSquareAbove 10 20, firstOddSquareAbove 30 20, firstOddSquareAbove 30 6] ==
-- [SKIPPED BY PROFILE_LAKE]   [5, 7, 0]

/-! ## Nested loops -/

/-- A stepped loop inside a stepped loop: `∑ i ∈ {0, 2, …} (< n), ∑ j ∈ {i, i + 3, …} (< n), 1`,
    the number of pairs. -/
def pairsNested (n : Nat) : Nat := Id.run do
  let mut c := 0
  for i in [0:n:2] do
    for _ in [i:n:3] do
      c := c + 1
  return c

def pairsNested_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term pairsNested

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pairsNested_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pairsNested_term 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard [pairsNested 0, pairsNested 7] == [0, 7]

end TermTests.ToTerm.ForRangeStep
