module

public import TermTests.StructRecTest.SplitRecursion
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Functions of the `List` library

Programs written with the list functions of Lean's library, as they are, translated by
`#leanscript_to_term` and run by `Term.run`:

* `List.map`, `List.foldl`, `List.contains` and `List.range` are structural recursions
  (`List.range` through `List.range.loop`, on a `Nat`), inlined at the call like any other
  (`TermTests/StructRecTest/SplitRecursion.lean`);
* `List.getD` is `l[i]?.getD d`, and `l[i]?` is `List.get?Internal`, a recursion whose
  `match` has a catch-all pattern (`| _, _ => none`).  Lean compiles such a `match` to a
  `_sparseCasesOn_` auxiliary whose motive mentions the history of the recursion; the
  shape the fold instantiates the branch at fixes its constructor, so it is reduced away
  (`LeanScript.ToTerm.reduceSparseCasesOnCtor?`);
* `l[i]!` is `List.get!Internal`, whose out-of-range branch is `panic!`.  In Lean's logic
  `panic! msg` *is* `default` (the message is an effect of compiled code only), and that
  is its translation: `l[i]!` out of range is `0` for a list of `Nat`, as in Lean;
* `(List.range n).attach` is a list of the subtype `{i // i ∈ List.range n}`.  A subtype
  has the tree of its values (the proof is erased, as every proof is), so `l.attach` and
  `l.attachWith P h` are `l` itself, and a `match` on `⟨i, h⟩` reads `i`;
* `l[i]` with its proof (`h : i < l.length`, from the membership proof of the attached
  list) is `l.getD i d` for a default `d` of the elements, which is equal to it whenever
  the proof holds.

Every program is run on inputs and compared with the Lean function it came from, by
`kernel_rfl` (the kernel's evaluation, no `native_decide`). -/

namespace TermTests.ToTerm.ListLibrary

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

/-- A list of natural numbers of the language. -/
abbrev natListT : TyWf := tyWfOf (List Nat)

/-- A Lean list of natural numbers, as a value of the language. -/
abbrev natList (l : List Nat) := Ty.DenRec.ofList (.prim .nat) l

/-- A value of the language of type `natListT`, read back as a Lean list. -/
abbrev readNatList (v : Ty.Den natListT.toTy) : List Nat := Ty.DenRec.toList (.prim .nat) v

/-! ## `List.map` -/

def mapInc (l : List Nat) : List Nat := l.map (· + 1)

def mapInc_term : Term sigAdd [] (natListT ⇒ natListT) := #leanscript_to_term mapInc

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd mapInc_term (natList [])) = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd mapInc_term (natList [0, 4, 9])) = [1, 5, 10] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd mapInc_term (natList [3, 1, 2])) = mapInc [3, 1, 2] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The function mapped reads a variable of the program. -/
def mapAddK (k : Nat) (l : List Nat) : List Nat := l.map fun x => x + k

def mapAddK_term : Term sigAdd [] (natT ⇒ natListT ⇒ natListT) := #leanscript_to_term mapAddK

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd mapAddK_term 10 (natList [1, 2, 3])) = [11, 12, 13] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `List.foldl` -/

def sumFoldl (l : List Nat) : Nat := l.foldl (· + ·) 0

def sumFoldl_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumFoldl

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFoldl_term (natList []) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumFoldl_term (natList [1, 2, 3, 4]) = 10 := by kernel_rfl

/-- A fold whose order matters: the list read as the binary digits of a number, the most
    significant first. -/
def binFoldl (l : List Nat) : Nat := l.foldl (fun acc b => acc + acc + b) 0

def binFoldl_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term binFoldl

-- [SKIPPED BY PROFILE_LAKE] example : runAdd binFoldl_term (natList [1, 0, 1, 1]) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd binFoldl_term (natList [1, 1, 0, 0, 1]) = binFoldl [1, 1, 0, 0, 1] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `List.contains` -/

def hasThree (l : List Nat) : Bool := l.contains 3

def hasThree_term : Term sigAdd [] (natListT ⇒ .prim .bool) := #leanscript_to_term hasThree

-- [SKIPPED BY PROFILE_LAKE] example : runAdd hasThree_term (natList []) = false := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd hasThree_term (natList [1, 2, 3]) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd hasThree_term (natList [4, 5, 6]) = false := by kernel_rfl

/-- The element looked for is an argument. -/
def containsArg (l : List Nat) (x : Nat) : Bool := l.contains x

def containsArg_term : Term sigAdd [] (natListT ⇒ natT ⇒ .prim .bool) :=
  #leanscript_to_term containsArg

-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsArg_term (natList [7, 8]) 8 = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd containsArg_term (natList [7, 8]) 9 = false := by kernel_rfl

/-! ## `List.getD` -/

def getDOr7 (l : List Nat) (i : Nat) : Nat := l.getD i 7

def getDOr7_term : Term sigAdd [] (natListT ⇒ natT ⇒ natT) := #leanscript_to_term getDOr7

-- [SKIPPED BY PROFILE_LAKE] example : runAdd getDOr7_term (natList [10, 20, 30]) 0 = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getDOr7_term (natList [10, 20, 30]) 2 = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getDOr7_term (natList [10, 20, 30]) 3 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getDOr7_term (natList []) 0 = 7 := by kernel_rfl

/-- `l[i]?`, the function `List.getD` is written with, taken apart by a `match`. -/
def getOpt (l : List Nat) (i : Nat) : Nat :=
  match l[i]? with
  | some x => x + 1
  | none => 0

def getOpt_term : Term sigAdd [] (natListT ⇒ natT ⇒ natT) := #leanscript_to_term getOpt

-- [SKIPPED BY PROFILE_LAKE] example : runAdd getOpt_term (natList [5, 6]) 1 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getOpt_term (natList [5, 6]) 2 = 0 := by kernel_rfl

/-- The same shape written by hand: a recursion whose `match` has a catch-all pattern. -/
def nth? : List Nat → Nat → Option Nat
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n
  | _, _ => none

/-- `nth?`, with `none` read as `0` and `some x` as `x + 1`. -/
def nthOr0 (l : List Nat) (i : Nat) : Nat := (nth? l i).elim 0 (· + 1)

def nthOr0_term : Term sigAdd [] (natListT ⇒ natT ⇒ natT) := #leanscript_to_term nthOr0

-- [SKIPPED BY PROFILE_LAKE] example : runAdd nthOr0_term (natList [5, 6, 7]) 2 = 8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nthOr0_term (natList [5, 6, 7]) 3 = 0 := by kernel_rfl

/-! ## `l[i]!` -/

def getBang (l : List Nat) (i : Nat) : Nat := l[i]!

def getBang_term : Term sigAdd [] (natListT ⇒ natT ⇒ natT) := #leanscript_to_term getBang

-- [SKIPPED BY PROFILE_LAKE] example : runAdd getBang_term (natList [10, 20, 30]) 1 = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getBang_term (natList [10, 20, 30]) 2 = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] /-- Out of range: `default`, which is what `l[i]!` is in Lean's logic. -/
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getBang_term (natList [10, 20, 30]) 5 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd getBang_term (natList [10, 20, 30]) 5 = getBang [10, 20, 30] 5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- `panic!` written by hand, in a recursion. -/
def nthBang : List Nat → Nat → Nat
  | a :: _, 0 => a
  | _ :: as, n + 1 => nthBang as n
  | _, _ => panic! "index out of range"

def nthBang_term : Term sigAdd [] (natListT ⇒ natT ⇒ natT) := #leanscript_to_term nthBang

-- [SKIPPED BY PROFILE_LAKE] example : runAdd nthBang_term (natList [4, 5]) 1 = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nthBang_term (natList [4, 5]) 2 = 0 := by kernel_rfl

/-! ## `List.range` and `List.attach` -/

def rangeOnly (n : Nat) : List Nat := List.range n

def rangeOnly_term : Term sigAdd [] (natT ⇒ natListT) := #leanscript_to_term rangeOnly

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeOnly_term 0) = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeOnly_term 5) = [0, 1, 2, 3, 4] := by kernel_rfl

/-- `(List.range n).attach`, taken apart by a pattern that names the proof. -/
def rangeDouble (n : Nat) : List Nat := (List.range n).attach.map fun ⟨i, _⟩ => i + i

def rangeDouble_term : Term sigAdd [] (natT ⇒ natListT) := #leanscript_to_term rangeDouble

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeDouble_term 0) = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeDouble_term 4) = [0, 2, 4, 6] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeDouble_term 6) = rangeDouble 6 := by kernel_rfl

/-- The value of each element read by a projection. -/
def attachVal (l : List Nat) : List Nat := l.attach.map fun x => x.1 + 1

def attachVal_term : Term sigAdd [] (natListT ⇒ natListT) := #leanscript_to_term attachVal

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd attachVal_term (natList [3, 1, 4])) = [4, 2, 5] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The proof of membership used, to index the list without a check: `l[i]` with
    `i < l.length`, which `List.mem_range` gives.  `l[i]` on a list is translated as
    `l.getD i 0`, which is equal to it whenever the proof holds. -/
def rangeIndex (l : List Nat) : List Nat :=
  (List.range l.length).attach.map fun ⟨i, h⟩ => l[i]'(List.mem_range.mp h) + 1

def rangeIndex_term : Term sigAdd [] (natListT ⇒ natListT) := #leanscript_to_term rangeIndex

-- [SKIPPED BY PROFILE_LAKE] example : readNatList (runAdd rangeIndex_term (natList [7, 8, 9])) = [8, 9, 10] := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- `List.attachWith`, and a fold over the attached list. -/
def attachWithSum (l : List Nat) : Nat :=
  (l.attachWith (fun _ => True) (fun _ _ => trivial)).foldl (fun acc x => acc + x.1) 0

def attachWithSum_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term attachWithSum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd attachWithSum_term (natList [1, 2, 3]) = 6 := by kernel_rfl

end TermTests.ToTerm.ListLibrary
