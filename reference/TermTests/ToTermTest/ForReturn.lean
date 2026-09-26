module

public import TermTests.ToTermTest.ForBreak
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Early `return` from a `for` loop

A `return v` inside a `for` loop in the identity monad (`Id.run do …`), translated by
`#leanscript_to_term` and run by `Term.run`.

`do` compiles it to a `break` (`ForInStep.done`) whose loop state also records `some v`,
and after the loop reads that record: `some v` answers `v`, `none` goes on with the code
after the loop.  So a loop with a `return` is a loop that can `break`, translated as in
`TermTests/ToTermTest/ForBreak.lean` (the fold of the step `ForInStep β`).  The state `β`
is

* `MProd (Option ρ) σ` (or a pair) when the loop updates `let mut` variables `σ`;
* `Option ρ × Unit` when it does not.  The language erases `Unit`, and a pair one
  component of which is `Unit` is modelled as the other component, so this state is
  `Option ρ` (the instance `LeanScriptTyWf (α × Unit)` in `LeanScript/Ty/Instances.lean`).

Every program is run on inputs and compared with the Lean function it came from, by
`kernel_rfl` (the kernel's evaluation, no `native_decide`). -/

namespace TermTests.ToTerm.ForReturn

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary
  TermTests.ToTerm.ForBreak

/-! ## Without a `let mut` variable -/

/-- The first element above `10`, or `0`. -/
def firstBig (l : List Nat) : Nat := Id.run do
  for x in l do
    if x > 10 then return x
  return 0

def firstBig_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term firstBig

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBig_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBig_term (natList [1, 20, 30]) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBig_term (natList [1, 2]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBig_term (natList [11]) = firstBig [11] := by kernel_rfl

/-- `List.contains`, written with an early `return`: the answer is a `Bool`. -/
def containsRet (k : Nat) (l : List Nat) : Bool := Id.run do
  for x in l do
    if x == k then return true
  return false

def containsRet_term : Term sigAdd [] (natT ⇒ natListT ⇒ .prim .bool) :=
  #leanscript_to_term containsRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsRet_term 3 (natList [1, 3, 5]) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsRet_term 4 (natList [1, 3, 5]) = false := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsRet_term 4 (natList []) = false := by kernel_rfl

/-- The answer is computed from the element: twice the first element above `k`, or `k`. -/
def doubleFirstAbove (k : Nat) (l : List Nat) : Nat := Id.run do
  for x in l do
    if x > k then return x + x
  return k

def doubleFirstAbove_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term doubleFirstAbove

-- [SKIPPED BY PROFILE_LAKE] example : runAdd doubleFirstAbove_term 2 (natList [1, 2, 3, 4]) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd doubleFirstAbove_term 9 (natList [1, 2, 3, 4]) = 9 := by kernel_rfl

/-- A `return` in a `match` arm, and a list as the answer: the predecessor of the first
    non-zero element, twice. -/
def firstPredTwice (l : List Nat) : List Nat := Id.run do
  for x in l do
    match x with
    | 0 => pure ()
    | k + 1 => return [k, k]
  return []

def firstPredTwice_term : Term sigAdd [] (natListT ⇒ natListT) :=
  #leanscript_to_term firstPredTwice

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd firstPredTwice_term (natList [0, 0, 5, 7])) = [4, 4] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd firstPredTwice_term (natList [0, 0])) = [] := by kernel_rfl

/-- A `return` together with `continue`. -/
def firstBigOdd (l : List Nat) : Nat := Id.run do
  for x in l do
    if x < 10 then continue
    if x == 12 then continue
    if x == 14 then continue
    return x
  return 0

def firstBigOdd_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term firstBigOdd

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBigOdd_term (natList [1, 12, 14, 15, 16]) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstBigOdd_term (natList [1, 12]) = 0 := by kernel_rfl

/-! ## With `let mut` variables -/

/-- The index of the first occurrence of `k`, returned from inside the loop. -/
def indexOfRet (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut i := 0
  for x in l do
    if x == k then return i
    i := i + 1
  return 1000

def indexOfRet_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) := #leanscript_to_term indexOfRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd indexOfRet_term 5 (natList [3, 5, 7]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd indexOfRet_term 3 (natList [3, 5, 7]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd indexOfRet_term 4 (natList [3, 5, 7]) = 1000 := by kernel_rfl

/-- `return` and `break` in the same loop: `return` leaves the function, `break` only the
    loop. -/
def returnOrBreak (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x == 0 then break
    if x > 10 then return 1000 + s
    s := s + x
  return s

def returnOrBreak_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term returnOrBreak

-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnOrBreak_term (natList [1, 2, 0, 20]) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnOrBreak_term (natList [1, 2, 20, 0]) = 1003 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnOrBreak_term (natList [1, 2]) = 3 := by kernel_rfl

/-- Two `let mut` variables. -/
def sumAndCountRet (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut s := 0
  let mut n := 0
  for x in l do
    if s + x > k then return s * 100 + n
    s := s + x
    n := n + 1
  return s * 1000 + n

def sumAndCountRet_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term sumAndCountRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumAndCountRet_term 5 (natList [1, 2, 3, 4]) = 302 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumAndCountRet_term 50 (natList [1, 2, 3, 4]) = 10004 := by kernel_rfl

/-! ## Over a range, a computed list, and `for h : x in l` -/

/-- The first `i < n` with `i * i > k`, or `n`, without a `let mut` variable. -/
def firstSquareAboveRet (k n : Nat) : Nat := Id.run do
  for i in [:n] do
    if i * i > k then return i
  return n

def firstSquareAboveRet_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term firstSquareAboveRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAboveRet_term 20 10 = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAboveRet_term 200 10 = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAboveRet_term 0 0 = 0 := by kernel_rfl
-- Lean's own `for` over a range is defined by well-founded recursion, which the kernel does
-- not evaluate, so the loops over a range are checked against their values written out.
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAboveRet_term 30 8 = 6 := by kernel_rfl

/-- Over a range, with a `let mut` variable. -/
def rangeSumRet (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [:n] do
    if i * i > 20 then return 100 + s
    s := s + i
  return s

def rangeSumRet_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term rangeSumRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd rangeSumRet_term 3 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rangeSumRet_term 10 = 110 := by kernel_rfl

/-- Over `List.range n`. -/
def firstMultipleRet (k n : Nat) : Nat := Id.run do
  for i in List.range n do
    if i * k > 20 then return i
  return 0

def firstMultipleRet_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term firstMultipleRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstMultipleRet_term 7 10 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstMultipleRet_term 1 10 = 0 := by kernel_rfl

/-- `for h : x in l`, with the membership proof passed on. -/
def succUntilZeroRet (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : x in l do
    if x == 0 then return s
    s := s + succOfMem l x h
  return s + 100

def succUntilZeroRet_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term succUntilZeroRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd succUntilZeroRet_term (natList [1, 2, 0, 5]) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd succUntilZeroRet_term (natList [1, 2]) = 105 := by kernel_rfl

/-- `for h : x in l` without a `let mut` variable, the proof passed on. -/
def firstSuccBigRet (l : List Nat) : Nat := Id.run do
  for h : x in l do
    if x > 10 then return succOfMem l x h
  return 0

def firstSuccBigRet_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term firstSuccBigRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSuccBigRet_term (natList [1, 20, 30]) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSuccBigRet_term (natList [1]) = 0 := by kernel_rfl

/-! ## Nested loops

A `return` in the inner loop leaves both loops, and the function. -/

/-- The first pair with `x + y > 10`, as `x * 100 + y`, without a `let mut` variable. -/
def firstPairRet (l m : List Nat) : Nat := Id.run do
  for x in l do
    for y in m do
      if x + y > 10 then return x * 100 + y
  return 0

def firstPairRet_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term firstPairRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstPairRet_term (natList [1, 9, 20]) (natList [1, 2, 3]) = 902 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstPairRet_term (natList [1, 2]) (natList [1, 2, 3]) = 0 := by kernel_rfl

/-- With a `let mut` variable counting the pairs visited before the `return`. -/
def countPairsRet (l m : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    for y in m do
      if x + y > 10 then return s
      s := s + 1
  return s + 100

def countPairsRet_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term countPairsRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd countPairsRet_term (natList [1, 9]) (natList [1, 2, 3]) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countPairsRet_term (natList [1, 2]) (natList [1, 2, 3]) = 106 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- A `return` in the outer loop, the inner loop running to its end. -/
def outerRet (l m : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x == 0 then return s
    for y in m do
      s := s + x * y
  return s + 1000

def outerRet_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) := #leanscript_to_term outerRet

-- [SKIPPED BY PROFILE_LAKE] example : runAdd outerRet_term (natList [1, 2, 0, 3]) (natList [1, 1]) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd outerRet_term (natList [1, 2]) (natList [1, 1]) = 1006 := by kernel_rfl

/-! ## Against the Lean functions -/

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstPairRet_term (natList [3, 8]) (natList [2, 4]) =
-- [SKIPPED BY PROFILE_LAKE]     firstPairRet [3, 8] [2, 4] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countPairsRet_term (natList [3, 8]) (natList [2, 4]) =
-- [SKIPPED BY PROFILE_LAKE]     countPairsRet [3, 8] [2, 4] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnOrBreak_term (natList [4, 11, 0]) = returnOrBreak [4, 11, 0] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsRet_term 7 (natList [7]) = containsRet 7 [7] := by kernel_rfl

end TermTests.ToTerm.ForReturn
