module

public import TermTests.MutualFamilyToTermTest.ThreeMembers.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 0` on three members: programs that read 1 link down

Part of the three-member family tests; see
`TermTests/MutualFamilyToTermTest/ThreeMembers/Common.lean` for the families and for what
is checked.  At depth `0` a branch reads only the answer at the link right below it: sums
with one, two and three arguments, and a fold of `M1`/`M2`/`M3`, whose members have
three different shapes.
The last section checks that a `match` that does not recurse is a `casesOn`, not a fold. -/

namespace TermTests.MutualFamilyToTerm.ThreeMembers

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## The sum of the labels -/

mutual
def xSum_with_k0 : X → Nat
  | .stop => 0
  | .next l y => l + ySum_with_k0 y
def ySum_with_k0 : Y → Nat
  | .stop => 0
  | .next l z => l + zSum_with_k0 z
def zSum_with_k0 : Z → Nat
  | .stop => 0
  | .next l x => l + xSum_with_k0 x
end

def xSum_with_k0_term : Term sigAdd [] (xT ⇒ natT) := #leanscript_to_term xSum_with_k0
def ySum_with_k0_term : Term sigAdd [] (yT ⇒ natT) := #leanscript_to_term ySum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? ySum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSum_with_k0_term (xOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSum_with_k0_term (xOfNat 10) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSum_with_k0_term (runAdd x7_term) = 25 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSum_with_k0_term (xOfNat 13) = xSum_with_k0 (X.ofNat 13) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ySum_with_k0_term (runAdd y5_term) = ySum_with_k0 y5 := by kernel_rfl

/-! ## Two arguments: a weighted sum, the weight before the chain -/

mutual
def xWeighted_with_k0 (w : Nat) : X → Nat
  | .stop => 0
  | .next l y => w * l + yWeighted_with_k0 w y
def yWeighted_with_k0 (w : Nat) : Y → Nat
  | .stop => 0
  | .next l z => w * l + zWeighted_with_k0 w z
def zWeighted_with_k0 (w : Nat) : Z → Nat
  | .stop => 0
  | .next l x => w * l + xWeighted_with_k0 w x
end

def xWeighted_with_k0_term : Term sigAdd [] (natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xWeighted_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xWeighted_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xWeighted_with_k0_term 3 (runAdd x7_term) = 75 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xWeighted_with_k0_term 2 (xOfNat 9) = xWeighted_with_k0 2 (X.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments: an accumulator and a weight, both after the chain

Lean puts both in the motive, so the fold answers a function of two arguments. -/

mutual
def xAcc_with_k0 : X → Nat → Nat → Nat
  | .stop, acc, _ => acc
  | .next l y, acc, w => yAcc_with_k0 y (acc + w * l) (w + 1)
def yAcc_with_k0 : Y → Nat → Nat → Nat
  | .stop, acc, _ => acc
  | .next l z, acc, w => zAcc_with_k0 z (acc + w * l) (w + 1)
def zAcc_with_k0 : Z → Nat → Nat → Nat
  | .stop, acc, _ => acc
  | .next l x, acc, w => xAcc_with_k0 x (acc + w * l) (w + 1)
end

def xAcc_with_k0_term : Term sigAdd [] (xT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xAcc_with_k0_term = some 0 := by kernel_rfl
-- 3·1 + 1·2 + 4·3 + 1·4 + 5·5 + 9·6 + 2·7
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xAcc_with_k0_term (runAdd x7_term) 0 1 = 114 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xAcc_with_k0_term (xOfNat 11) 5 2 = xAcc_with_k0 (X.ofNat 11) 5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments around the chain: an offset before it, a multiplier after it -/

mutual
def xAround_with_k0 (off : Nat) : X → Nat → Nat
  | .stop, _ => off
  | .next l y, m => m * l + yAround_with_k0 off y m
def yAround_with_k0 (off : Nat) : Y → Nat → Nat
  | .stop, _ => off
  | .next l z, m => m * l + zAround_with_k0 off z m
def zAround_with_k0 (off : Nat) : Z → Nat → Nat
  | .stop, _ => off
  | .next l x, m => m * l + xAround_with_k0 off x m
end

def xAround_with_k0_term : Term sigAdd [] (natT ⇒ xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xAround_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xAround_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xAround_with_k0_term 100 (runAdd x7_term) 2 = 150 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xAround_with_k0_term 7 (xOfNat 10) 3 = xAround_with_k0 7 (X.ofNat 10) 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A family of three shapes: constructors, a record, a newtype -/

mutual
def m1Sum_with_k0 : M1 → Nat
  | .done => 0
  | .step r => m2Sum_with_k0 r
def m2Sum_with_k0 : M2 → Nat
  | .mk l n => l + m3Sum_with_k0 n
def m3Sum_with_k0 : M3 → Nat
  | .wrap m => m1Sum_with_k0 m
end

def m1Sum_with_k0_term : Term sigAdd [] (m1T ⇒ natT) := #leanscript_to_term m1Sum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? m1Sum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd m1Sum_with_k0_term (runAdd m1Three_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd m1Sum_with_k0_term (runAdd m1Three_term) = m1Sum_with_k0 m1Three := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A `match` that does not recurse is a `casesOn`

A function that only takes a value apart, several links deep, is no fold: each level is
a `mutualRecursiveFamily_casesOn` (or `…_casesOnWithDefault` for a `match` with a
wildcard) of the member at that level. -/

/-- The label of the third link, if there is one. -/
def xThird : X → Nat
  | .next _ (.next _ (.next l _)) => l
  | _ => 0

def xThird_term : Term sigAdd [] (xT ⇒ natT) := #leanscript_to_term xThird

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xThird_term = none := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xThird_term (runAdd x7_term) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xThird_term (xOfNat 2) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xThird_term (xOfNat 8) = xThird (X.ofNat 8) := by kernel_rfl

/-- The label of the `M2` record under an `M1` step. -/
def m1Label : M1 → Nat
  | .done => 0
  | .step (.mk l _) => l

def m1Label_term : Term sigAdd [] (m1T ⇒ natT) := #leanscript_to_term m1Label

-- [SKIPPED BY PROFILE_LAKE] example : runAdd m1Label_term (runAdd m1Three_term) = 4 := by kernel_rfl

end TermTests.MutualFamilyToTerm.ThreeMembers

end
