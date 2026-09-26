module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 0`: programs of two and three arguments

Part of the `mutualRecursiveFamily_rec k` translation tests on the family `A`/`B` of
`TermTests/MutualFamilyToTermTest/Common.lean`, which says what is checked.  At depth `0`
a branch reads only the answer at the link right below it.  The programs here take more
than the chain: an argument before it (a parameter of the fold), arguments after it (in
Lean's motive, so the fold answers a function), and both. -/

namespace TermTests.MutualFamilyToTerm.Args

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## Two arguments, the weight before the chain -/

mutual
def aWeighted_with_k0 (w : Nat) : A → Nat
  | .stop => 0
  | .next l b => w * l + bWeighted_with_k0 w b
def bWeighted_with_k0 (w : Nat) : B → Nat
  | .stop => 0
  | .next l a => w * l + aWeighted_with_k0 w a
end

def aWeighted_with_k0_term : Term sigAdd [] (natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aWeighted_with_k0
def bWeighted_with_k0_term : Term sigAdd [] (natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bWeighted_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aWeighted_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aWeighted_with_k0_term 3 (runAdd a4_term) = 27 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aWeighted_with_k0_term 2 (aOfNat 10) = 90 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bWeighted_with_k0_term 5 (bOfNat 7) = bWeighted_with_k0 5 (B.ofNat 7) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Two arguments, the accumulator after the chain -/

mutual
def aSumAcc_with_k0 : A → Nat → Nat
  | .stop, acc => acc
  | .next l b, acc => bSumAcc_with_k0 b (acc + l)
def bSumAcc_with_k0 : B → Nat → Nat
  | .stop, acc => acc
  | .next l a, acc => aSumAcc_with_k0 a (acc + l)
end

def aSumAcc_with_k0_term : Term sigAdd [] (aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aSumAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aSumAcc_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSumAcc_with_k0_term (runAdd a4_term) 100 = 109 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSumAcc_with_k0_term (aOfNat 12) 1 = aSumAcc_with_k0 (A.ofNat 12) 1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments, both after the chain

The position `i` and the accumulator: the sum of `i · label`, counting from `i`. -/

mutual
def aDot_with_k0 : A → Nat → Nat → Nat
  | .stop, _, acc => acc
  | .next l b, i, acc => bDot_with_k0 b (i + 1) (acc + i * l)
def bDot_with_k0 : B → Nat → Nat → Nat
  | .stop, _, acc => acc
  | .next l a, i, acc => aDot_with_k0 a (i + 1) (acc + i * l)
end

def aDot_with_k0_term : Term sigAdd [] (aT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aDot_with_k0
def bDot_with_k0_term : Term sigAdd [] (bT ⇒ natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bDot_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aDot_with_k0_term = some 0 := by kernel_rfl
-- 1·3 + 2·1 + 3·4 + 4·1
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aDot_with_k0_term (runAdd a4_term) 1 0 = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aDot_with_k0_term (aOfNat 9) 2 7 = aDot_with_k0 (A.ofNat 9) 2 7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bDot_with_k0_term (runAdd b5_term) 1 0 = bDot_with_k0 b5 1 0 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments, both before the chain -/

mutual
def aAffine_with_k0 (m c : Nat) : A → Nat
  | .stop => c
  | .next l b => m * l + bAffine_with_k0 m c b
def bAffine_with_k0 (m c : Nat) : B → Nat
  | .stop => c
  | .next l a => m * l + aAffine_with_k0 m c a
end

def aAffine_with_k0_term : Term sigAdd [] (natT ⇒ natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aAffine_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aAffine_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aAffine_with_k0_term 2 5 (runAdd a4_term) = 23 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aAffine_with_k0_term 3 1 (aOfNat 8) = aAffine_with_k0 3 1 (A.ofNat 8) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Three arguments around the chain: one before it, one after it -/

mutual
def aAround_with_k0 (off : Nat) : A → Nat → Nat
  | .stop, _ => off
  | .next l b, m => m * l + bAround_with_k0 off b m
def bAround_with_k0 (off : Nat) : B → Nat → Nat
  | .stop, _ => off
  | .next l a, m => m * l + aAround_with_k0 off a m
end

def aAround_with_k0_term : Term sigAdd [] (natT ⇒ aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aAround_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aAround_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aAround_with_k0_term 100 (runAdd a4_term) 2 = 118 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aAround_with_k0_term 4 (aOfNat 11) 3 = aAround_with_k0 4 (A.ofNat 11) 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.Args

end
