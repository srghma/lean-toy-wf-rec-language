module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 3`: programs of two and three arguments

Part of the `mutualRecursiveFamily_rec k` translation tests on the family `A`/`B` of
`TermTests/MutualFamilyToTermTest/Common.lean`, which says what is checked.
`TermTests/MutualFamilyToTermTest/K3.lean` folds the tetranacci recursion as a function
of the chain alone; here the same recursion takes more arguments:

* `…From` — two arguments, the start value before the chain (a parameter of the fold,
  so the term is `fun s => …_rec 3 …`);
* `…FromStep` — three arguments, a start value and a step, both before the chain;
* `…Scaled` — two arguments, the start value *after* the chain (in Lean's motive, so the
  fold answers a function `Nat → Nat`);
* `…Mixed` — three arguments, one before the chain and one after it. -/

namespace TermTests.MutualFamilyToTerm.Args

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `TetraFrom`: the tetranacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def aTetraFrom_with_k3 (s : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      bTetraFrom_with_k3 s (.next a1 (.next a2 (.next a3 r))) +
      aTetraFrom_with_k3 s (.next a2 (.next a3 r)) +
      bTetraFrom_with_k3 s (.next a3 r) +
      aTetraFrom_with_k3 s r
def bTetraFrom_with_k3 (s : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      aTetraFrom_with_k3 s (.next a1 (.next a2 (.next a3 r))) +
      bTetraFrom_with_k3 s (.next a2 (.next a3 r)) +
      aTetraFrom_with_k3 s (.next a3 r) +
      bTetraFrom_with_k3 s r
end

def aTetraFrom_with_k3_term : Term sigAdd [] (natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aTetraFrom_with_k3
def bTetraFrom_with_k3_term : Term sigAdd [] (natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bTetraFrom_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTetraFrom_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFrom_with_k3_term 5 (aOfNat 3) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFrom_with_k3_term 5 (aOfNat 10) = 280 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFrom_with_k3_term 5 (aOfNat 12) = aTetraFrom_with_k3 5 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFrom_with_k3_term 5 (runAdd a4_term) = aTetraFrom_with_k3 5 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTetraFrom_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFrom_with_k3_term 5 (bOfNat 11) = 540 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFrom_with_k3_term 5 (bOfNat 9) = bTetraFrom_with_k3 5 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFrom_with_k3_term 5 (runAdd b5_term) = bTetraFrom_with_k3 5 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraFromStep`: the tetranacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def aTetraFromStep_with_k3 (s : Nat) (t : Nat) : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      bTetraFromStep_with_k3 s t (.next a1 (.next a2 (.next a3 r))) +
      aTetraFromStep_with_k3 s t (.next a2 (.next a3 r)) +
      bTetraFromStep_with_k3 s t (.next a3 r) +
      aTetraFromStep_with_k3 s t r +
      t
def bTetraFromStep_with_k3 (s : Nat) (t : Nat) : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      aTetraFromStep_with_k3 s t (.next a1 (.next a2 (.next a3 r))) +
      bTetraFromStep_with_k3 s t (.next a2 (.next a3 r)) +
      aTetraFromStep_with_k3 s t (.next a3 r) +
      bTetraFromStep_with_k3 s t r +
      t
end

def aTetraFromStep_with_k3_term : Term sigAdd [] (natT ⇒ natT ⇒ aT ⇒ natT) :=
  #leanscript_to_term aTetraFromStep_with_k3
def bTetraFromStep_with_k3_term : Term sigAdd [] (natT ⇒ natT ⇒ bT ⇒ natT) :=
  #leanscript_to_term bTetraFromStep_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTetraFromStep_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFromStep_with_k3_term 2 3 (aOfNat 3) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFromStep_with_k3_term 2 3 (aOfNat 10) = 292 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFromStep_with_k3_term 2 3 (aOfNat 12) = aTetraFromStep_with_k3 2 3 (A.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraFromStep_with_k3_term 2 3 (runAdd a4_term) = aTetraFromStep_with_k3 2 3 a4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTetraFromStep_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFromStep_with_k3_term 2 3 (bOfNat 11) = 564 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFromStep_with_k3_term 2 3 (bOfNat 9) = bTetraFromStep_with_k3 2 3 (B.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraFromStep_with_k3_term 2 3 (runAdd b5_term) = bTetraFromStep_with_k3 2 3 b5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraScaled`: the tetranacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def aTetraScaled_with_k3 : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), m => m
  | .next _ (.next a1 (.next a2 (.next a3 r))), m =>
      bTetraScaled_with_k3 (.next a1 (.next a2 (.next a3 r))) m +
      aTetraScaled_with_k3 (.next a2 (.next a3 r)) m +
      bTetraScaled_with_k3 (.next a3 r) m +
      aTetraScaled_with_k3 r m
def bTetraScaled_with_k3 : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), m => m
  | .next _ (.next a1 (.next a2 (.next a3 r))), m =>
      aTetraScaled_with_k3 (.next a1 (.next a2 (.next a3 r))) m +
      bTetraScaled_with_k3 (.next a2 (.next a3 r)) m +
      aTetraScaled_with_k3 (.next a3 r) m +
      bTetraScaled_with_k3 r m
end

def aTetraScaled_with_k3_term : Term sigAdd [] (aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aTetraScaled_with_k3
def bTetraScaled_with_k3_term : Term sigAdd [] (bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bTetraScaled_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTetraScaled_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraScaled_with_k3_term (aOfNat 3) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraScaled_with_k3_term (aOfNat 7) 4 = 32 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aTetraScaled_with_k3 (A.ofNat 7) 4 = 32 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraScaled_with_k3_term (aOfNat 8) 4 = aTetraScaled_with_k3 (A.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraScaled_with_k3_term (runAdd a4_term) 4 = aTetraScaled_with_k3 a4 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTetraScaled_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraScaled_with_k3_term (bOfNat 8) 4 = 60 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bTetraScaled_with_k3 (B.ofNat 8) 4 = 60 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraScaled_with_k3_term (bOfNat 7) 4 = bTetraScaled_with_k3 (B.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraScaled_with_k3_term (runAdd b5_term) 4 = bTetraScaled_with_k3 b5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraMixed`: the tetranacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def aTetraMixed_with_k3 (s : Nat) : A → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), _ => s
  | .next _ (.next a1 (.next a2 (.next a3 r))), t =>
      bTetraMixed_with_k3 s (.next a1 (.next a2 (.next a3 r))) t +
      aTetraMixed_with_k3 s (.next a2 (.next a3 r)) t +
      bTetraMixed_with_k3 s (.next a3 r) t +
      aTetraMixed_with_k3 s r t +
      t
def bTetraMixed_with_k3 (s : Nat) : B → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), _ => s
  | .next _ (.next a1 (.next a2 (.next a3 r))), t =>
      aTetraMixed_with_k3 s (.next a1 (.next a2 (.next a3 r))) t +
      bTetraMixed_with_k3 s (.next a2 (.next a3 r)) t +
      aTetraMixed_with_k3 s (.next a3 r) t +
      bTetraMixed_with_k3 s r t +
      t
end

def aTetraMixed_with_k3_term : Term sigAdd [] (natT ⇒ aT ⇒ natT ⇒ natT) :=
  #leanscript_to_term aTetraMixed_with_k3
def bTetraMixed_with_k3_term : Term sigAdd [] (natT ⇒ bT ⇒ natT ⇒ natT) :=
  #leanscript_to_term bTetraMixed_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTetraMixed_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraMixed_with_k3_term 3 (aOfNat 3) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraMixed_with_k3_term 3 (aOfNat 7) 2 = 40 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : aTetraMixed_with_k3 3 (A.ofNat 7) 2 = 40 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraMixed_with_k3_term 3 (aOfNat 8) 2 = aTetraMixed_with_k3 3 (A.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetraMixed_with_k3_term 3 (runAdd a4_term) 2 = aTetraMixed_with_k3 3 a4 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTetraMixed_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraMixed_with_k3_term 3 (bOfNat 8) 2 = 77 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : bTetraMixed_with_k3 3 (B.ofNat 8) 2 = 77 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraMixed_with_k3_term 3 (bOfNat 7) 2 = bTetraMixed_with_k3 3 (B.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetraMixed_with_k3_term 3 (runAdd b5_term) 2 = bTetraMixed_with_k3 3 b5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.Args

end
