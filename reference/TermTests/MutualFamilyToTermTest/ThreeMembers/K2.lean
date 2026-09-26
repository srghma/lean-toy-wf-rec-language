module

public import TermTests.MutualFamilyToTermTest.ThreeMembers.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 2` on three members: programs that read 3 links down

Part of the three-member family tests; see
`TermTests/MutualFamilyToTermTest/ThreeMembers/Common.lean` for the family and for what is
checked.  The programs are the tribonacci recursion of `TermTests/NatRecDepthTest/` on
the number of links, written as three mutual functions: the branch of a link reads the
answers at the next 3 links, which go round the members `X → Y → Z → X`, so it looks
2 times, each time into a subvalue of the next member.  Each program comes in five
forms: with one argument (the chain), and with two and three arguments before and after
the chain. -/

namespace TermTests.MutualFamilyToTerm.ThreeMembers

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `Trib`: the tribonacci recursion on the number of links -/

mutual
def xTrib_with_k2 : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 1
  | .next _ (.next a1 (.next a2 r)) =>
      yTrib_with_k2 (.next a1 (.next a2 r)) +
      zTrib_with_k2 (.next a2 r) +
      xTrib_with_k2 r
def yTrib_with_k2 : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 1
  | .next _ (.next a1 (.next a2 r)) =>
      zTrib_with_k2 (.next a1 (.next a2 r)) +
      xTrib_with_k2 (.next a2 r) +
      yTrib_with_k2 r
def zTrib_with_k2 : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 1
  | .next _ (.next a1 (.next a2 r)) =>
      xTrib_with_k2 (.next a1 (.next a2 r)) +
      yTrib_with_k2 (.next a2 r) +
      zTrib_with_k2 r
end

def xTrib_with_k2_term : Term sigAdd [] (xT ⇒ natT) :=
  #leanscript_to_term xTrib_with_k2
def yTrib_with_k2_term : Term sigAdd [] (yT ⇒ natT) :=
  #leanscript_to_term yTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTrib_with_k2_term (xOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTrib_with_k2_term (xOfNat 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTrib_with_k2_term (xOfNat 12) = xTrib_with_k2 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTrib_with_k2_term (runAdd x7_term) = xTrib_with_k2 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTrib_with_k2_term (yOfNat 11) = 149 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTrib_with_k2_term (yOfNat 9) = yTrib_with_k2 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTrib_with_k2_term (runAdd y5_term) = yTrib_with_k2 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribFrom`: the tribonacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def xTribFrom_with_k2 (s : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      yTribFrom_with_k2 s (.next a1 (.next a2 r)) +
      zTribFrom_with_k2 s (.next a2 r) +
      xTribFrom_with_k2 s r
def yTribFrom_with_k2 (s : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      zTribFrom_with_k2 s (.next a1 (.next a2 r)) +
      xTribFrom_with_k2 s (.next a2 r) +
      yTribFrom_with_k2 s r
def zTribFrom_with_k2 (s : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      xTribFrom_with_k2 s (.next a1 (.next a2 r)) +
      yTribFrom_with_k2 s (.next a2 r) +
      zTribFrom_with_k2 s r
end

def xTribFrom_with_k2_term : Term sigAdd [] (natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xTribFrom_with_k2
def yTribFrom_with_k2_term : Term sigAdd [] (natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yTribFrom_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTribFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFrom_with_k2_term 5 (xOfNat 2) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFrom_with_k2_term 5 (xOfNat 10) = 405 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFrom_with_k2_term 5 (xOfNat 12) = xTribFrom_with_k2 5 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFrom_with_k2_term 5 (runAdd x7_term) = xTribFrom_with_k2 5 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTribFrom_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFrom_with_k2_term 5 (yOfNat 11) = 745 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFrom_with_k2_term 5 (yOfNat 9) = yTribFrom_with_k2 5 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFrom_with_k2_term 5 (runAdd y5_term) = yTribFrom_with_k2 5 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribFromStep`: the tribonacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def xTribFromStep_with_k2 (s : Nat) (t : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      yTribFromStep_with_k2 s t (.next a1 (.next a2 r)) +
      zTribFromStep_with_k2 s t (.next a2 r) +
      xTribFromStep_with_k2 s t r +
      t
def yTribFromStep_with_k2 (s : Nat) (t : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      zTribFromStep_with_k2 s t (.next a1 (.next a2 r)) +
      xTribFromStep_with_k2 s t (.next a2 r) +
      yTribFromStep_with_k2 s t r +
      t
def zTribFromStep_with_k2 (s : Nat) (t : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => s
  | .next _ (.next a1 (.next a2 r)) =>
      xTribFromStep_with_k2 s t (.next a1 (.next a2 r)) +
      yTribFromStep_with_k2 s t (.next a2 r) +
      zTribFromStep_with_k2 s t r +
      t
end

def xTribFromStep_with_k2_term : Term sigAdd [] (natT ⇒ natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xTribFromStep_with_k2
def yTribFromStep_with_k2_term : Term sigAdd [] (natT ⇒ natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yTribFromStep_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTribFromStep_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFromStep_with_k2_term 2 3 (xOfNat 2) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFromStep_with_k2_term 2 3 (xOfNat 10) = 450 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFromStep_with_k2_term 2 3 (xOfNat 12) = xTribFromStep_with_k2 2 3 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribFromStep_with_k2_term 2 3 (runAdd x7_term) = xTribFromStep_with_k2 2 3 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTribFromStep_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFromStep_with_k2_term 2 3 (yOfNat 11) = 829 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFromStep_with_k2_term 2 3 (yOfNat 9) = yTribFromStep_with_k2 2 3 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribFromStep_with_k2_term 2 3 (runAdd y5_term) = yTribFromStep_with_k2 2 3 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribScaled`: the tribonacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def xTribScaled_with_k2 : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), m => m
  | .next _ (.next a1 (.next a2 r)), m =>
      yTribScaled_with_k2 (.next a1 (.next a2 r)) m +
      zTribScaled_with_k2 (.next a2 r) m +
      xTribScaled_with_k2 r m
def yTribScaled_with_k2 : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), m => m
  | .next _ (.next a1 (.next a2 r)), m =>
      zTribScaled_with_k2 (.next a1 (.next a2 r)) m +
      xTribScaled_with_k2 (.next a2 r) m +
      yTribScaled_with_k2 r m
def zTribScaled_with_k2 : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), m => m
  | .next _ (.next a1 (.next a2 r)), m =>
      xTribScaled_with_k2 (.next a1 (.next a2 r)) m +
      yTribScaled_with_k2 (.next a2 r) m +
      zTribScaled_with_k2 r m
end

def xTribScaled_with_k2_term : Term sigAdd [] (xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xTribScaled_with_k2
def yTribScaled_with_k2_term : Term sigAdd [] (yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yTribScaled_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTribScaled_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribScaled_with_k2_term (xOfNat 2) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribScaled_with_k2_term (xOfNat 7) 4 = 52 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xTribScaled_with_k2 (X.ofNat 7) 4 = 52 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribScaled_with_k2_term (xOfNat 8) 4 = xTribScaled_with_k2 (X.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribScaled_with_k2_term (runAdd x7_term) 4 = xTribScaled_with_k2 x7 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTribScaled_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribScaled_with_k2_term (yOfNat 8) 4 = 96 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yTribScaled_with_k2 (Y.ofNat 8) 4 = 96 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribScaled_with_k2_term (yOfNat 7) 4 = yTribScaled_with_k2 (Y.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribScaled_with_k2_term (runAdd y5_term) 4 = yTribScaled_with_k2 y5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TribMixed`: the tribonacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def xTribMixed_with_k2 (s : Nat) : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => s
  | .next _ (.next a1 (.next a2 r)), t =>
      yTribMixed_with_k2 s (.next a1 (.next a2 r)) t +
      zTribMixed_with_k2 s (.next a2 r) t +
      xTribMixed_with_k2 s r t +
      t
def yTribMixed_with_k2 (s : Nat) : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => s
  | .next _ (.next a1 (.next a2 r)), t =>
      zTribMixed_with_k2 s (.next a1 (.next a2 r)) t +
      xTribMixed_with_k2 s (.next a2 r) t +
      yTribMixed_with_k2 s r t +
      t
def zTribMixed_with_k2 (s : Nat) : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => s
  | .next _ (.next a1 (.next a2 r)), t =>
      xTribMixed_with_k2 s (.next a1 (.next a2 r)) t +
      yTribMixed_with_k2 s (.next a2 r) t +
      zTribMixed_with_k2 s r t +
      t
end

def xTribMixed_with_k2_term : Term sigAdd [] (natT ⇒ xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xTribMixed_with_k2
def yTribMixed_with_k2_term : Term sigAdd [] (natT ⇒ yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yTribMixed_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTribMixed_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribMixed_with_k2_term 3 (xOfNat 2) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribMixed_with_k2_term 3 (xOfNat 7) 2 = 69 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xTribMixed_with_k2 3 (X.ofNat 7) 2 = 69 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribMixed_with_k2_term 3 (xOfNat 8) 2 = xTribMixed_with_k2 3 (X.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTribMixed_with_k2_term 3 (runAdd x7_term) 2 = xTribMixed_with_k2 3 x7 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTribMixed_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribMixed_with_k2_term 3 (yOfNat 8) 2 = 128 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yTribMixed_with_k2 3 (Y.ofNat 8) 2 = 128 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribMixed_with_k2_term 3 (yOfNat 7) 2 = yTribMixed_with_k2 3 (Y.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTribMixed_with_k2_term 3 (runAdd y5_term) 2 = yTribMixed_with_k2 3 y5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A single function that goes *through* the other two members

`xLen_with_k2` is one function on `X` that steps three links at a time, so Lean compiles it
with the motives of `Y` and `Z` set to `PUnit`; their branches answer `default`, which no
branch of `X` reads. -/

def xLen_with_k2 : X → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next _ .stop) => 2
  | .next _ (.next _ (.next _ x)) => xLen_with_k2 x + 3

def xLen_with_k2_term : Term sigAdd [] (xT ⇒ natT) := #leanscript_to_term xLen_with_k2

-- it looks through the `Y` and the `Z` link below to the `X` link under them
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xLen_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xLen_with_k2_term (xOfNat 11) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xLen_with_k2_term (runAdd x7_term) = xLen_with_k2 x7 := by kernel_rfl

/-! ## A single function through a record member and a newtype member

`m1Steps_with_k2` is one function on `M1` with an argument before the value and one
after it; its branch for an `M1` step looks through the `M2` record and the `M3` newtype
below it to the `M1` under them. -/

/-- The number of steps, with a start value before the value and a step after it. -/
def m1Steps_with_k2 (start : Nat) : M1 → Nat → Nat
  | .done, _ => start
  | .step (.mk _ (.wrap m)), inc => m1Steps_with_k2 start m inc + inc

def m1Steps_with_k2_term : Term sigAdd [] (natT ⇒ m1T ⇒ natT ⇒ natT) :=
  #leanscript_to_term m1Steps_with_k2

-- the branch of an `M1` step looks through the record and the newtype below it
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? m1Steps_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd m1Steps_with_k2_term 10 (runAdd m1Three_term) 5 = 25 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd m1Steps_with_k2_term 1 (runAdd m1Three_term) 2 =
-- [SKIPPED BY PROFILE_LAKE]     m1Steps_with_k2 1 m1Three 2 := by kernel_rfl

end TermTests.MutualFamilyToTerm.ThreeMembers

end
