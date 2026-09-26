module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 1`: programs of two and three arguments

Part of the `mutualRecursiveFamily_rec k` translation tests on the family `A`/`B` of
`TermTests/MutualFamilyToTermTest/Common.lean`, which says what is checked.
`TermTests/MutualFamilyToTermTest/K1.lean` folds the Fibonacci recursion as a function
of the chain alone; here the same recursion takes more arguments:

* `…From` — two arguments, the start value before the chain (a parameter of the fold,
  so the term is `fun s => …_rec 1 …`);
* `…FromStep` — three arguments, a start value and a step, both before the chain;
* `…Scaled` — two arguments, the start value *after* the chain (in Lean's motive, so the
  fold answers a function `Nat → Nat`);
* `…Mixed` — three arguments, one before the chain and one after it. -/

namespace TermTests.MutualFamilyToTerm.Args

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `FibFrom`: the Fibonacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def aFibFrom_with_k1 (s : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      bFibFrom_with_k1 s (.next a1 r) +
      aFibFrom_with_k1 s r
def bFibFrom_with_k1 (s : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      aFibFrom_with_k1 s (.next a1 r) +
      bFibFrom_with_k1 s r
end

def aFibFrom_with_k1_term : Term sigAdd [] (natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aFibFrom_with_k1
def bFibFrom_with_k1_term : Term sigAdd [] (natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bFibFrom_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aFibFrom_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFrom_with_k1_term 5 (aOfNat 1) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFrom_with_k1_term 5 (aOfNat 10) = 275 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFrom_with_k1_term 5 (aOfNat 12) = aFibFrom_with_k1 5 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFrom_with_k1_term 5 (runAdd a4_term) = aFibFrom_with_k1 5 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bFibFrom_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFrom_with_k1_term 5 (bOfNat 11) = 445 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFrom_with_k1_term 5 (bOfNat 9) = bFibFrom_with_k1 5 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFrom_with_k1_term 5 (runAdd b5_term) = bFibFrom_with_k1 5 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibFromStep`: the Fibonacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def aFibFromStep_with_k1 (s : Nat) (t : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      bFibFromStep_with_k1 s t (.next a1 r) +
      aFibFromStep_with_k1 s t r +
      t
def bFibFromStep_with_k1 (s : Nat) (t : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      aFibFromStep_with_k1 s t (.next a1 r) +
      bFibFromStep_with_k1 s t r +
      t
end

def aFibFromStep_with_k1_term : Term sigAdd [] (natT ⇒ natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aFibFromStep_with_k1
def bFibFromStep_with_k1_term : Term sigAdd [] (natT ⇒ natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bFibFromStep_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aFibFromStep_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFromStep_with_k1_term 2 3 (aOfNat 1) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFromStep_with_k1_term 2 3 (aOfNat 10) = 374 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFromStep_with_k1_term 2 3 (aOfNat 12) = aFibFromStep_with_k1 2 3 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibFromStep_with_k1_term 2 3 (runAdd a4_term) = aFibFromStep_with_k1 2 3 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bFibFromStep_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFromStep_with_k1_term 2 3 (bOfNat 11) = 607 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFromStep_with_k1_term 2 3 (bOfNat 9) = bFibFromStep_with_k1 2 3 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibFromStep_with_k1_term 2 3 (runAdd b5_term) = bFibFromStep_with_k1 2 3 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibScaled`: the Fibonacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def aFibScaled_with_k1 : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, m => m
  | .next _ (.next a1 r), m =>
      bFibScaled_with_k1 (.next a1 r) m +
      aFibScaled_with_k1 r m
def bFibScaled_with_k1 : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, m => m
  | .next _ (.next a1 r), m =>
      aFibScaled_with_k1 (.next a1 r) m +
      bFibScaled_with_k1 r m
end

def aFibScaled_with_k1_term : Term sigAdd [] (aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aFibScaled_with_k1
def bFibScaled_with_k1_term : Term sigAdd [] (bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bFibScaled_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aFibScaled_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibScaled_with_k1_term (aOfNat 1) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibScaled_with_k1_term (aOfNat 7) 4 = 52 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aFibScaled_with_k1 (A.ofNat 7) 4 = 52 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibScaled_with_k1_term (aOfNat 8) 4 = aFibScaled_with_k1 (A.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibScaled_with_k1_term (runAdd a4_term) 4 = aFibScaled_with_k1 a4 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bFibScaled_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibScaled_with_k1_term (bOfNat 8) 4 = 84 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bFibScaled_with_k1 (B.ofNat 8) 4 = 84 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibScaled_with_k1_term (bOfNat 7) 4 = bFibScaled_with_k1 (B.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibScaled_with_k1_term (runAdd b5_term) 4 = bFibScaled_with_k1 b5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibMixed`: the Fibonacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def aFibMixed_with_k1 (s : Nat) : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => s
  | .next _ (.next a1 r), t =>
      bFibMixed_with_k1 s (.next a1 r) t +
      aFibMixed_with_k1 s r t +
      t
def bFibMixed_with_k1 (s : Nat) : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => s
  | .next _ (.next a1 r), t =>
      aFibMixed_with_k1 s (.next a1 r) t +
      bFibMixed_with_k1 s r t +
      t
end

def aFibMixed_with_k1_term : Term sigAdd [] (natT ⇒ aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aFibMixed_with_k1
def bFibMixed_with_k1_term : Term sigAdd [] (natT ⇒ bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bFibMixed_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aFibMixed_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibMixed_with_k1_term 3 (aOfNat 1) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibMixed_with_k1_term 3 (aOfNat 7) 2 = 79 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aFibMixed_with_k1 3 (A.ofNat 7) 2 = 79 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibMixed_with_k1_term 3 (aOfNat 8) 2 = aFibMixed_with_k1 3 (A.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFibMixed_with_k1_term 3 (runAdd a4_term) 2 = aFibMixed_with_k1 3 a4 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bFibMixed_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibMixed_with_k1_term 3 (bOfNat 8) 2 = 129 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bFibMixed_with_k1 3 (B.ofNat 8) 2 = 129 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibMixed_with_k1_term 3 (bOfNat 7) 2 = bFibMixed_with_k1 3 (B.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFibMixed_with_k1_term 3 (runAdd b5_term) 2 = bFibMixed_with_k1 3 b5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.Args

end
