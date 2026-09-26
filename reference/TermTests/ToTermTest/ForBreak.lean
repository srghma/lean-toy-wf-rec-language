module

public import TermTests.ToTermTest.ListLibrary
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `break` in a `for` loop

A `for` loop in the identity monad (`Id.run do …`) whose body can leave the loop with
`break`, translated by `#leanscript_to_term` and run by `Term.run`.

`do` compiles `break` to `ForInStep.done s` (and going on to `ForInStep.yield s`).  A loop
whose body can reach `done` is still a fold, whose state is the **step** `ForInStep β`
instead of the state `β`: it starts from `yield init`; at each element a `done` step is
kept as it is, and from `yield s` the body's step at `s` is taken; the answer is the state
the last step carries.  So over a list the loop is `List.foldl` of the step
(`LeanScript.ToTerm.listForInAsFoldl`), and over `[:n]` it is `Nat.rec` of the step
(`LeanScript.ToTerm.rangeForInBreakAsNatRec`).  `ForInStep β` is the tagged union
`done (_ : β) | yield (_ : β)`, the same tree as `β ⊕ β`.  The rewriting is proved an
equation of Lean's logic in `LeanScript/ListLibraryFacts.lean` (`forIn_id_eq_foldl_step`,
`forIn'_id_eq_foldl_attach_step`, `forIn'_id_eq_foldl_step`,
`forIn_range_id_eq_natRec_step`).

The elements after a `break` are still visited by the fold, but they do nothing: the
value is that of the loop that stopped.

A `return` from inside the loop is compiled by `do` to a `break` that also records the
value returned; it is translated the same way (last section, and
`TermTests/ToTermTest/ForReturn.lean`).

Every program is run on inputs and compared with the Lean function it came from, by
`kernel_rfl` (the kernel's evaluation, no `native_decide`). -/

namespace TermTests.ToTerm.ForBreak

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary

/-! ## Over a list -/

/-- The sum of the elements before the first `0`. -/
def sumUntilZero (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x == 0 then break
    s := s + x
  return s

def sumUntilZero_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumUntilZero

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZero_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZero_term (natList [1, 2, 3]) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZero_term (natList [1, 2, 0, 5]) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZero_term (natList [0, 7]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZero_term (natList [4, 9, 0, 1, 0]) = sumUntilZero [4, 9, 0, 1, 0] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- `break` after the state is updated: the element that stops the loop is counted. -/
def sumThrough (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    s := s + x
    if s ≥ k then break
  return s

def sumThrough_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) := #leanscript_to_term sumThrough

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumThrough_term 5 (natList [1, 2, 3, 4]) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumThrough_term 100 (natList [1, 2, 3, 4]) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumThrough_term 0 (natList [7, 8]) = 7 := by kernel_rfl

/-- The state is a list: the prefix before the first element above `k`, reversed. -/
def takeWhileLe (k : Nat) (l : List Nat) : List Nat := Id.run do
  let mut out := []
  for x in l do
    if x > k then break
    out := x :: out
  return out

def takeWhileLe_term : Term sigAdd [] (natT ⇒ natListT ⇒ natListT) :=
  #leanscript_to_term takeWhileLe

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd takeWhileLe_term 3 (natList [1, 2, 5, 3])) = [2, 1] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd takeWhileLe_term 9 (natList [1, 2, 5, 3])) = [3, 5, 2, 1] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd takeWhileLe_term 0 (natList [1, 2])) = [] := by kernel_rfl

/-- Several `let mut` variables, and a `Bool` found flag. -/
def findIndex (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut i := 0
  let mut found := false
  for x in l do
    if x == k then
      found := true
      break
    i := i + 1
  return if found then i else 1000

def findIndex_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) := #leanscript_to_term findIndex

-- [SKIPPED BY PROFILE_LAKE] example : runAdd findIndex_term 5 (natList [3, 5, 7]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd findIndex_term 3 (natList [3, 5, 7]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd findIndex_term 4 (natList [3, 5, 7]) = 1000 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd findIndex_term 7 (natList [7, 7]) = findIndex 7 [7, 7] := by kernel_rfl

/-- `break` together with `continue`, and an `if` without `else`. -/
def breakContinue (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x == 0 then break
    if x > 5 then continue
    s := s + x
  return s

def breakContinue_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term breakContinue

-- [SKIPPED BY PROFILE_LAKE] example : runAdd breakContinue_term (natList [1, 7, 3, 9, 5]) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd breakContinue_term (natList [1, 7, 3, 0, 5]) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd breakContinue_term (natList [8, 9]) = 0 := by kernel_rfl

/-- `break` in one arm of a `match` on the element. -/
def matchBreak (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    match x with
    | 0 => break
    | n + 1 => s := s + n
  return s

def matchBreak_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term matchBreak

-- [SKIPPED BY PROFILE_LAKE] example : runAdd matchBreak_term (natList [1, 5, 0, 7]) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd matchBreak_term (natList [2, 3]) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd matchBreak_term (natList [0, 1]) = 0 := by kernel_rfl

/-- A `Bool` state: is some element above `k`?  The loop stops at the first one. -/
def anyAbove (k : Nat) (l : List Nat) : Bool := Id.run do
  let mut found := false
  for x in l do
    if x > k then
      found := true
      break
  return found

def anyAbove_term : Term sigAdd [] (natT ⇒ natListT ⇒ .prim .bool) := #leanscript_to_term anyAbove

-- [SKIPPED BY PROFILE_LAKE] example : runAdd anyAbove_term 3 (natList [1, 2, 3]) = false := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd anyAbove_term 2 (natList [1, 2, 3]) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd anyAbove_term 0 (natList []) = false := by kernel_rfl

/-! ## Nested loops

A `break` leaves the innermost loop only. -/

/-- The inner loop stops at the first element of `m` above `x`; the outer one goes on. -/
def nestedInnerBreak (l m : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    for y in m do
      if y > x then break
      s := s + y
  return s

def nestedInnerBreak_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term nestedInnerBreak

-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestedInnerBreak_term (natList [1, 3]) (natList [1, 2, 3, 4]) = 7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestedInnerBreak_term (natList [0, 5]) (natList [2, 1]) = 3 := by kernel_rfl

/-- The outer loop stops, the inner one always goes on. -/
def nestedOuterBreak (l m : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x == 0 then break
    for y in m do
      s := s + x * y
  return s

def nestedOuterBreak_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term nestedOuterBreak

-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestedOuterBreak_term (natList [1, 2, 0, 3]) (natList [1, 1]) = 6 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Over a computed list, and `for h : x in l` -/

/-- A loop over `List.range n` that stops at the first square above `k`. -/
def firstSquareAbove (k n : Nat) : Nat := Id.run do
  let mut r := 0
  for i in List.range n do
    r := i
    if i * i > k then break
  return r

def firstSquareAbove_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term firstSquareAbove

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAbove_term 10 20 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstSquareAbove_term 100 5 = 4 := by kernel_rfl

/-- The membership proof is named but not read. -/
def sumUntilZeroMem (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for _h : x in l do
    if x == 0 then break
    s := s + x
  return s

def sumUntilZeroMem_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term sumUntilZeroMem

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUntilZeroMem_term (natList [1, 2, 0, 5]) = 3 := by kernel_rfl

/-- A function that asks for a proof that its argument is in the list. -/
@[inline] def succOfMem (l : List Nat) (x : Nat) (_h : x ∈ l) : Nat := x + 1

/-- The membership proof is passed on: the fold of the step is over `l.attach`. -/
def sumSuccUntilZeroMem (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : x in l do
    if x == 0 then break
    s := s + succOfMem l x h
  return s

def sumSuccUntilZeroMem_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term sumSuccUntilZeroMem

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSuccUntilZeroMem_term (natList [1, 2, 0, 5]) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSuccUntilZeroMem_term (natList []) = 0 := by kernel_rfl

/-! ## Over a range -/

/-- `for i in [:n]` that stops at `i = 4`. -/
def rangeBreak (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [:n] do
    if i == 4 then break
    s := s + i
  return s

def rangeBreak_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term rangeBreak

-- [SKIPPED BY PROFILE_LAKE] example : runAdd rangeBreak_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rangeBreak_term 3 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rangeBreak_term 10 = 6 := by kernel_rfl

/-- The smallest `i < n` with `i * i ≥ k`, or `n`: the loop counts until it stops. -/
def isqrtCeil (k n : Nat) : Nat := Id.run do
  let mut r := n
  for i in [:n] do
    if i * i ≥ k then
      r := i
      break
  return r

def isqrtCeil_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term isqrtCeil

-- [SKIPPED BY PROFILE_LAKE] example : runAdd isqrtCeil_term 10 20 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd isqrtCeil_term 16 20 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd isqrtCeil_term 50 5 = 5 := by kernel_rfl

/-! ## `return` from inside the loop

`do` compiles `return v` inside a loop to a `break` whose state also records `some v`, and
reads it after the loop.  With a `let mut` variable the state is a pair, which is
translated like the loops above; without one it is `Option ρ × Unit`, which the language
models as `Option ρ` (`Unit` is erased). -/

/-- The sum before the first element above `10`, returned from inside the loop; `100` more
    when the loop runs to its end. -/
def returnFromLoop (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x > 10 then return s
    s := s + x
  return s + 100

def returnFromLoop_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term returnFromLoop

-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnFromLoop_term (natList [1, 20, 30]) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd returnFromLoop_term (natList [1, 2]) = 103 := by kernel_rfl

/-! More loops that `return` from inside, without a `let mut` variable, over a range, in
nested loops and with `for h :`, are in `TermTests/ToTermTest/ForReturn.lean`. -/

end TermTests.ToTerm.ForBreak

end
