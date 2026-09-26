module

public import TermTests.ToTermTest.ListLibrary
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `for x in l` over a list

A `for` loop over a **list**, in the identity monad (`Id.run do …`), translated by
`#leanscript_to_term` and run by `Term.run`.

A loop whose body always goes on to the next iteration is a fold: its value is the state
(the `let mut` variables) after the last element.  The translation reads the body as the
next state and emits `l.foldl`, which is then translated like any other `List.foldl`
(`LeanScript.ToTerm.listForInAsFoldl`; the rewriting is proved an equation of Lean's
logic in `LeanScript/ListLibraryFacts.lean`, `forIn_id_yield_eq_foldl` and its
neighbours).  Inside the body:

* several `let mut` variables (the state is their tuple);
* `if` with or without `else`, `continue`, `match`, local `let`s;
* a list of pairs taken apart in the binder (`for (a, b) in l`);
* reading the other arguments of the function, and the list itself;
* a loop inside a loop, and a loop over a list that is computed (`List.range n`);
* `for h : x in l`, with the membership proof `h` unused or passed to a function (the
  fold is then over `l.attach`, which the language represents as `l`).

A loop that leaves early (`break`, or `return` from inside it) is a fold of the step
`ForInStep β` instead of the state: see `TermTests/ToTermTest/ForBreak.lean`.

Every program is run on inputs and compared with the Lean function it came from, by
`kernel_rfl` (the kernel's evaluation, no `native_decide`). -/

namespace TermTests.ToTerm.ForList

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary

/-! ## One mutable variable -/

def sumFor (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    s := s + x
  return s

def sumFor_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumFor

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFor_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFor_term (natList [1, 2, 3]) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFor_term (natList [4, 0, 9, 1]) = sumFor [4, 0, 9, 1] := by kernel_rfl

/-- The state is a list: the loop reverses its input. -/
def revFor (l : List Nat) : List Nat := Id.run do
  let mut out := []
  for x in l do
    out := x :: out
  return out

def revFor_term : Term sigAdd [] (natListT ⇒ natListT) := #leanscript_to_term revFor

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd revFor_term (natList [])) = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd revFor_term (natList [1, 2, 3])) = [3, 2, 1] := by kernel_rfl

/-! ## Several mutable variables

The continuant `K [] = 1`, `K [a] = a`, `K (a :: b :: as) = a * K (b :: as) + K as`, as
the loop of `TermTests/ArrayRecDepthTest.lean` (`contLoop`), there proved equal to the
continuant at every list. -/

def contFor (l : List Nat) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a

def contFor_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term contFor

-- [SKIPPED BY PROFILE_LAKE] example : runAdd contFor_term (natList []) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd contFor_term (natList [3, 4]) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd contFor_term (natList [1, 2, 3]) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] /-- On a list of ones, the continuant is a Fibonacci number. -/
-- [SKIPPED BY PROFILE_LAKE] example : runAdd contFor_term (natList [1, 1, 1, 1, 1, 1]) = 13 := by kernel_rfl

/-- Two accumulators, both read after the loop. -/
def sumAndCount (l : List Nat) : Nat := Id.run do
  let mut s := 0
  let mut n := 0
  for x in l do
    s := s + x
    n := n + 1
  return s * 10 + n

def sumAndCount_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumAndCount

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumAndCount_term (natList [2, 3, 4]) = 93 := by kernel_rfl

/-! ## Control flow inside the body -/

/-- `if` without `else`, `else if`, and `continue`. -/
def ifContinue (l : List Nat) : Nat := Id.run do
  let mut s := 0
  let mut t := 1
  for x in l do
    if x > 2 then
      s := s + x
    else if x == 0 then continue
    t := t + s
  return s + t

def ifContinue_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term ifContinue

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ifContinue_term (natList []) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ifContinue_term (natList [1, 0, 3, 5, 2]) = ifContinue [1, 0, 3, 5, 2] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ifContinue_term (natList [0, 0, 7]) = ifContinue [0, 0, 7] := by kernel_rfl

/-- A `match` on the element. -/
def matchFor (l : List Nat) : List Nat := Id.run do
  let mut out := []
  for x in l do
    match x with
    | 0 => out := 7 :: out
    | n + 1 => out := n :: out
  return out

def matchFor_term : Term sigAdd [] (natListT ⇒ natListT) := #leanscript_to_term matchFor

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd matchFor_term (natList [0, 3, 1])) = [0, 2, 7] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd matchFor_term (natList [5, 0])) = matchFor [5, 0] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- A test that gives a `Bool` state. -/
def allNonZero (l : List Nat) : Bool := Id.run do
  let mut ok := true
  for x in l do
    if x == 0 then ok := false
  return ok

def allNonZero_term : Term sigAdd [] (natListT ⇒ .prim .bool) := #leanscript_to_term allNonZero

-- [SKIPPED BY PROFILE_LAKE] example : runAdd allNonZero_term (natList []) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd allNonZero_term (natList [1, 5]) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd allNonZero_term (natList [1, 0, 5]) = false := by kernel_rfl

/-- A list of pairs, taken apart in the binder of the loop. -/
def dotFor (l : List (Nat × Nat)) : Nat := Id.run do
  let mut s := 0
  for (a, b) in l do
    s := s + a * b
  return s

def dotFor_term : Term sigAdd [] (tyWfOf (List (Nat × Nat)) ⇒ natT) := #leanscript_to_term dotFor

-- [SKIPPED BY PROFILE_LAKE] example : runAdd dotFor_term (Ty.DenRec.ofList (tyWfOf (Nat × Nat)).toTy
-- [SKIPPED BY PROFILE_LAKE]     [((2, 3, ()) : Nat × Nat × PUnit), ((4, 5, ()) : Nat × Nat × PUnit)]) = 26 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Reading the rest of the program -/

/-- The body reads another argument of the function. -/
def countBelow (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x < k then s := s + 1
  return s

def countBelow_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) := #leanscript_to_term countBelow

-- [SKIPPED BY PROFILE_LAKE] example : runAdd countBelow_term 3 (natList [1, 5, 2, 3]) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd countBelow_term 0 (natList [1, 5, 2, 3]) = 0 := by kernel_rfl

/-- The body reads the list it loops over. -/
def plusLength (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    s := s + x + l.length
  return s

def plusLength_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term plusLength

-- [SKIPPED BY PROFILE_LAKE] example : runAdd plusLength_term (natList [1, 2]) = 7 := by kernel_rfl

/-- A loop inside a loop. -/
def nestedFor (l m : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    for y in m do
      s := s + x * y
  return s

def nestedFor_term : Term sigAdd [] (natListT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term nestedFor

-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestedFor_term (natList [1, 2]) (natList [3, 4]) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestedFor_term (natList []) (natList [3, 4]) = 0 := by kernel_rfl

/-- A loop over a list that is computed: `List.range n`. -/
def sumRange (n : Nat) : Nat := Id.run do
  let mut s := 0
  for x in List.range n do
    s := s + x
  return s

def sumRange_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumRange

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumRange_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumRange_term 5 = 10 := by kernel_rfl

/-! ## `for h : x in l` -/

/-- The membership proof is named but not used. -/
def sumForMem (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for _h : x in l do
    s := s + x
  return s

def sumForMem_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumForMem

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumForMem_term (natList [1, 2, 3]) = 6 := by kernel_rfl

/-- A function that asks for a proof that its argument is in the list. -/
@[inline] def succOfMem (l : List Nat) (x : Nat) (_h : x ∈ l) : Nat := x + 1

/-- The membership proof is passed on: the fold is over `l.attach`. -/
def sumSuccMem (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : x in l do
    s := s + succOfMem l x h
  return s

def sumSuccMem_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumSuccMem

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSuccMem_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumSuccMem_term (natList [1, 2]) = 5 := by kernel_rfl

end TermTests.ToTerm.ForList

end
