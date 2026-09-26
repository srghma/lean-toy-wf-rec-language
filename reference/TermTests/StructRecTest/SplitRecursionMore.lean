module

public import TermTests.StructRecTest.SplitRecursion
public import TermTests.MutualFamilyToTermTest.CrossBlock.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # More recursions split across top-level definitions

The shapes of `TermTests/StructRecTest/SplitRecursion.lean`, extended.  None of the
helpers below is `@[inline]`, and none is declared in the signature (`sigAdd` declares only
`add`): each is a structural recursion, or a wrapper of one, and is inlined at the call.

* a chain of wrappers of **any** length (`w6 … w1`, then `go`);
* wrappers and recursions of **another file** (`callGo`, `go` and `Tree.sumAcc` of
  `SplitRecursion.lean`), and a chain that crosses files;
* a helper declared with `where` (a top-level definition `withWhere.loop`);
* the recursion **partially applied** or **eta-reduced** (`callGoPartial n := go n`,
  `goAlias := go`), and passed to `List.map`;
* a recursion written with the **recursor itself** (`Nat.rec`, `List.rec`), rather than
  by pattern matching;
* a member of a `mutual` block that Lean compiles on its own because it only calls the
  other member (`oddParity`), and a `mutual` pair on `C`/`D` whose branches call
  separately defined recursions on the other family `A`/`B`;
* a recursion whose branch calls a *wrapper* of another recursion.

A non-recursive helper that no recursion is reached from is still refused (end of file):
a higher-order helper applied to a recursion (`applyTwice (go 2)`) is such a helper. -/

namespace TermTests.StructRec.SplitMore

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

/-! ## A chain of six wrappers -/

def w1 (n : Nat) : Nat := go n 0
def w2 (n : Nat) : Nat := w1 (n + 1)
def w3 (n : Nat) : Nat := w2 n
def w4 (n : Nat) : Nat := w3 n + 1
def w5 (n : Nat) : Nat := w4 n
def w6 (n : Nat) : Nat := w5 (n + 2)

def w6_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term w6

-- [SKIPPED BY PROFILE_LAKE] example : hasFold w6_term = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd w6_term 1 = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd w6_term 10 = w6 10 := by kernel_rfl

/-! ## Across files

`callGo` and `go` are defined in `SplitRecursion.lean`. -/

/-- A wrapper, in this file, of a wrapper of another file. -/
def useCallGo (n : Nat) : Nat := callGo n + 1

def useCallGo_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term useCallGo

-- [SKIPPED BY PROFILE_LAKE] example : runAdd useCallGo_term 4 = 9 := by kernel_rfl

/-- A wrapper, in this file, of the recursion of another file… -/
def goFrom5 (n : Nat) : Nat := go n 5
/-- … and a wrapper of that wrapper. -/
def useGoFrom5 (n : Nat) : Nat := goFrom5 n + goFrom5 (n + 1)

def useGoFrom5_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term useGoFrom5

-- [SKIPPED BY PROFILE_LAKE] example : runAdd useGoFrom5_term 3 = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd useGoFrom5_term 8 = useGoFrom5 8 := by kernel_rfl

/-- A recursion on the tree of another file, through its wrapper `treeSum`. -/
def treeSumTwice (t : Tree) : Nat := treeSum t + treeSum t

def treeSumTwice_term : Term sigAdd [] (tyWfOf Tree ⇒ natT) :=
  #leanscript_to_term treeSumTwice

-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSumTwice_term (runAdd tree1_term) = 20 := by kernel_rfl

/-! ## A `where` helper -/

def withWhere (n : Nat) : Nat := loop n 1
where
  /-- Doubling `n` times. -/
  loop : Nat → Nat → Nat
    | 0, a => a
    | n + 1, a => loop n (a + a)

def withWhere_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term withWhere

-- [SKIPPED BY PROFILE_LAKE] example : runAdd withWhere_term 5 = 32 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd withWhere_term 9 = withWhere 9 := by kernel_rfl

/-! ## Partial application and eta-reduction -/

/-- The recursion, applied to its first argument only. -/
def callGoPartial (n : Nat) : Nat → Nat := go n

def callGoPartial_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term callGoPartial

-- [SKIPPED BY PROFILE_LAKE] example : runAdd callGoPartial_term 3 4 = 10 := by kernel_rfl

/-- The recursion under another name, applied to nothing. -/
def goAlias : Nat → Nat → Nat := go

def goAlias_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term goAlias

-- [SKIPPED BY PROFILE_LAKE] example : runAdd goAlias_term 6 1 = 13 := by kernel_rfl

/-- The recursion, partially applied, handed to `List.map`. -/
def mapGo (l : List Nat) : List Nat := l.map (go 2)

def mapGo_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term mapGo

-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (runAdd mapGo_term (Ty.DenRec.ofList (.prim .nat) [0, 5]))
-- [SKIPPED BY PROFILE_LAKE]     = [4, 9] := by kernel_rfl

/-! ## A recursion written with the recursor -/

/-- `2 * n`, by `Nat.rec`. -/
def natFold (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) n

def callNatFold (n : Nat) : Nat := natFold n + 1

def callNatFold_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term callNatFold

-- [SKIPPED BY PROFILE_LAKE] example : hasFold callNatFold_term = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd callNatFold_term 6 = 13 := by kernel_rfl

/-- The sum of a list, by `List.rec`. -/
def listFold (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => x + ih) l

def callListFold (l : List Nat) : Nat := listFold l + listFold (7 :: l)

def callListFold_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term callListFold

-- [SKIPPED BY PROFILE_LAKE] example : runAdd callListFold_term (Ty.DenRec.ofList (.prim .nat) [1, 2, 3]) = 19 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `mutual` blocks split by Lean

`oddParity` only calls `evenParity`, and `evenParity` never calls `oddParity`, so Lean
compiles them as two separate definitions: `oddParity` is a wrapper of the recursion
`evenParity`. -/

mutual
def evenParity : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => evenParity n
def oddParity (n : Nat) : Bool := evenParity (n + 1)
end

def oddParity_term : Term sigAdd [] (natT ⇒ .prim .bool) := #leanscript_to_term oddParity

-- [SKIPPED BY PROFILE_LAKE] example : runAdd oddParity_term 7 = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd oddParity_term 10 = false := by kernel_rfl

section CrossBlock

open TermTests.MutualFamilyToTerm TermTests.MutualFamilyToTerm.CrossBlock

/-- The sum of the labels of an `A` chain — **not** `@[inline]` (compare `aSum` of
    `CrossBlock/Common.lean`). -/
def aTotal : A → Nat
  | .stop => 0
  | .next l b => l + bTotal b
where
  /-- The sum of the labels of a `B` chain. -/
  bTotal : B → Nat
    | .stop => 0
    | .next l a => l + aTotal a

-- A fold of `C`/`D` whose branches call the separate recursion on `A`/`B`.  `dLook` is
-- not called by `cLook`, so Lean splits it off as a definition of its own, a wrapper of
-- `cLook`.
mutual
def cLook : C → Nat
  | .leaf a => aTotal a
  | .node (.mk c b) => cLook c + 2 * aTotal.bTotal b
def dLook : D → Nat
  | .mk c b => cLook c + aTotal.bTotal b
end

def cLook_term : Term sigAdd [] (cT ⇒ Split.natT) := #leanscript_to_term cLook
def dLook_term : Term sigAdd [] (dT ⇒ Split.natT) := #leanscript_to_term dLook

-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLook_term (runAdd c1_term) = cLook c1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cLook_term (chainOf 6) = cLook (C.chain 6) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd dLook_term (runAdd d1_term) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd dLook_term (runAdd d1_term) = dLook d1 := by kernel_rfl

end CrossBlock

/-! ## A branch that calls a wrapper of another recursion -/

/-- One more than the length, a wrapper of `lenList` of `SplitRecursion.lean`. -/
def lenPlus (l : List Nat) : Nat := lenList l + 1

def sumLensPlus : List (List Nat) → Nat
  | [] => 0
  | l :: ls => lenPlus l + sumLensPlus ls

def sumLensPlus_term : Term sigAdd [] (tyWfOf (List (List Nat)) ⇒ natT) :=
  #leanscript_to_term sumLensPlus

-- [SKIPPED BY PROFILE_LAKE] example : hasFold sumLensPlus_term = true := by kernel_rfl

/-! ## Still refused

`applyTwice` is not a recursion, and calls none: that its argument is one does not make it
part of the recursion. -/

def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def useTwice (n : Nat) : Nat := applyTwice (go 2) n

/-- error: `#leanscript_to_term`: `TermTests.StructRec.SplitMore.applyTwice` is not declared in the signature and is not inlinable, so a term cannot call it.  Either add a `GlobalDecl` named "applyTwice" (or "TermTests.StructRec.SplitMore.applyTwice") to the signature, or mark `TermTests.StructRec.SplitMore.applyTwice` `@[inline]`.  (A structural recursion is inlined without either.) -/
#guard_msgs (error) in
example : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term useTwice

end TermTests.StructRec.SplitMore

end
