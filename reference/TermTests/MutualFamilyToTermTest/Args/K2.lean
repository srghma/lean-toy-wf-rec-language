module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 2`: programs of two and three arguments

Part of the `mutualRecursiveFamily_rec k` translation tests on the family `A`/`B` of
`TermTests/MutualFamilyToTermTest/Common.lean`, which says what is checked.
`TermTests/MutualFamilyToTermTest/K2.lean` folds the tribonacci recursion as a function
of the chain alone; here the same recursion takes more arguments:

* `…From` — two arguments, the start value before the chain (a parameter of the fold,
  so the term is `fun s => …_rec 2 …`);
* `…FromStep` — three arguments, a start value and a step, both before the chain;
* `…Scaled` — two arguments, the start value *after* the chain (in Lean's motive, so the
  fold answers a function `Nat → Nat`);
* `…Mixed` — three arguments, one before the chain and one after it. -/

namespace TermTests.MutualFamilyToTerm.Args

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `TribFrom`: the tribonacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def aTribFrom_with_k2 (s : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      bTribFrom_with_k2 s (.next a1 (.next a2 r)) +
      aTribFrom_with_k2 s (.next a2 r) +
      bTribFrom_with_k2 s r
def bTribFrom_with_k2 (s : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      aTribFrom_with_k2 s (.next a1 (.next a2 r)) +
      bTribFrom_with_k2 s (.next a2 r) +
      aTribFrom_with_k2 s r
end

def aTribFrom_with_k2_term : Term sigAdd [] (natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aTribFrom_with_k2
def bTribFrom_with_k2_term : Term sigAdd [] (natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bTribFrom_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTribFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFrom_with_k2_term 5 (aOfNat 2) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFrom_with_k2_term 5 (aOfNat 10) = 405 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFrom_with_k2_term 5 (aOfNat 12) = aTribFrom_with_k2 5 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFrom_with_k2_term 5 (runAdd a4_term) = aTribFrom_with_k2 5 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTribFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFrom_with_k2_term 5 (bOfNat 11) = 745 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFrom_with_k2_term 5 (bOfNat 9) = bTribFrom_with_k2 5 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFrom_with_k2_term 5 (runAdd b5_term) = bTribFrom_with_k2 5 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribFromStep`: the tribonacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def aTribFromStep_with_k2 (s : Nat) (t : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      bTribFromStep_with_k2 s t (.next a1 (.next a2 r)) +
      aTribFromStep_with_k2 s t (.next a2 r) +
      bTribFromStep_with_k2 s t r +
      t
def bTribFromStep_with_k2 (s : Nat) (t : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      aTribFromStep_with_k2 s t (.next a1 (.next a2 r)) +
      bTribFromStep_with_k2 s t (.next a2 r) +
      aTribFromStep_with_k2 s t r +
      t
end

def aTribFromStep_with_k2_term : Term sigAdd [] (natT ⇒ natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aTribFromStep_with_k2
def bTribFromStep_with_k2_term : Term sigAdd [] (natT ⇒ natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bTribFromStep_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTribFromStep_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFromStep_with_k2_term 2 3 (aOfNat 2) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFromStep_with_k2_term 2 3 (aOfNat 10) = 450 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFromStep_with_k2_term 2 3 (aOfNat 12) = aTribFromStep_with_k2 2 3 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribFromStep_with_k2_term 2 3 (runAdd a4_term) = aTribFromStep_with_k2 2 3 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTribFromStep_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFromStep_with_k2_term 2 3 (bOfNat 11) = 829 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFromStep_with_k2_term 2 3 (bOfNat 9) = bTribFromStep_with_k2 2 3 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribFromStep_with_k2_term 2 3 (runAdd b5_term) = bTribFromStep_with_k2 2 3 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribScaled`: the tribonacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def aTribScaled_with_k2 : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), m => m
  | .next _ (.next a1 (.next a2 r)), m =>
      bTribScaled_with_k2 (.next a1 (.next a2 r)) m +
      aTribScaled_with_k2 (.next a2 r) m +
      bTribScaled_with_k2 r m
def bTribScaled_with_k2 : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), m => m
  | .next _ (.next a1 (.next a2 r)), m =>
      aTribScaled_with_k2 (.next a1 (.next a2 r)) m +
      bTribScaled_with_k2 (.next a2 r) m +
      aTribScaled_with_k2 r m
end

def aTribScaled_with_k2_term : Term sigAdd [] (aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aTribScaled_with_k2
def bTribScaled_with_k2_term : Term sigAdd [] (bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bTribScaled_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTribScaled_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribScaled_with_k2_term (aOfNat 2) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribScaled_with_k2_term (aOfNat 7) 4 = 52 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aTribScaled_with_k2 (A.ofNat 7) 4 = 52 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribScaled_with_k2_term (aOfNat 8) 4 = aTribScaled_with_k2 (A.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribScaled_with_k2_term (runAdd a4_term) 4 = aTribScaled_with_k2 a4 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTribScaled_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribScaled_with_k2_term (bOfNat 8) 4 = 96 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bTribScaled_with_k2 (B.ofNat 8) 4 = 96 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribScaled_with_k2_term (bOfNat 7) 4 = bTribScaled_with_k2 (B.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribScaled_with_k2_term (runAdd b5_term) 4 = bTribScaled_with_k2 b5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribMixed`: the tribonacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def aTribMixed_with_k2 (s : Nat) : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => s
  | .next _ (.next a1 (.next a2 r)), t =>
      bTribMixed_with_k2 s (.next a1 (.next a2 r)) t +
      aTribMixed_with_k2 s (.next a2 r) t +
      bTribMixed_with_k2 s r t +
      t
def bTribMixed_with_k2 (s : Nat) : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => s
  | .next _ (.next a1 (.next a2 r)), t =>
      aTribMixed_with_k2 s (.next a1 (.next a2 r)) t +
      bTribMixed_with_k2 s (.next a2 r) t +
      aTribMixed_with_k2 s r t +
      t
end

def aTribMixed_with_k2_term : Term sigAdd [] (natT ⇒ aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aTribMixed_with_k2
def bTribMixed_with_k2_term : Term sigAdd [] (natT ⇒ bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bTribMixed_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTribMixed_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribMixed_with_k2_term 3 (aOfNat 2) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribMixed_with_k2_term 3 (aOfNat 7) 2 = 69 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aTribMixed_with_k2 3 (A.ofNat 7) 2 = 69 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribMixed_with_k2_term 3 (aOfNat 8) 2 = aTribMixed_with_k2 3 (A.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTribMixed_with_k2_term 3 (runAdd a4_term) 2 = aTribMixed_with_k2 3 a4 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTribMixed_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribMixed_with_k2_term 3 (bOfNat 8) 2 = 128 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bTribMixed_with_k2 3 (B.ofNat 8) 2 = 128 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribMixed_with_k2_term 3 (bOfNat 7) 2 = bTribMixed_with_k2 3 (B.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTribMixed_with_k2_term 3 (runAdd b5_term) 2 = bTribMixed_with_k2 3 b5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.Args

end
