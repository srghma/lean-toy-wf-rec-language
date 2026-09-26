module

public import TermTests.MutualFamilyToTermTest.ThreeMembers.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 1` on three members: programs that read 2 links down

Part of the three-member family tests; see
`TermTests/MutualFamilyToTermTest/ThreeMembers/Common.lean` for the family and for what is
checked.  The programs are the Fibonacci recursion of `TermTests/NatRecDepthTest/` on
the number of links, written as three mutual functions: the branch of a link reads the
answers at the next 2 links, which go round the members `X → Y → Z → X`, so it looks
once into a subvalue of the next member.  Each program comes in five
forms: with one argument (the chain), and with two and three arguments before and after
the chain. -/

namespace TermTests.MutualFamilyToTerm.ThreeMembers

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `Fib`: the Fibonacci recursion on the number of links -/

mutual
def xFib_with_k1 : X → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next a1 r) =>
      yFib_with_k1 (.next a1 r) +
      zFib_with_k1 r
def yFib_with_k1 : Y → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next a1 r) =>
      zFib_with_k1 (.next a1 r) +
      xFib_with_k1 r
def zFib_with_k1 : Z → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next a1 r) =>
      xFib_with_k1 (.next a1 r) +
      yFib_with_k1 r
end

def xFib_with_k1_term : Term sigAdd [] (xT ⇒ natT) :=
  #leanscript_to_term xFib_with_k1
def yFib_with_k1_term : Term sigAdd [] (yT ⇒ natT) :=
  #leanscript_to_term yFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFib_with_k1_term (xOfNat 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFib_with_k1_term (xOfNat 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFib_with_k1_term (xOfNat 12) = xFib_with_k1 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFib_with_k1_term (runAdd x7_term) = xFib_with_k1 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFib_with_k1_term (yOfNat 11) = 89 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFib_with_k1_term (yOfNat 9) = yFib_with_k1 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFib_with_k1_term (runAdd y5_term) = yFib_with_k1 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibFrom`: the Fibonacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def xFibFrom_with_k1 (s : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      yFibFrom_with_k1 s (.next a1 r) +
      zFibFrom_with_k1 s r
def yFibFrom_with_k1 (s : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      zFibFrom_with_k1 s (.next a1 r) +
      xFibFrom_with_k1 s r
def zFibFrom_with_k1 (s : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      xFibFrom_with_k1 s (.next a1 r) +
      yFibFrom_with_k1 s r
end

def xFibFrom_with_k1_term : Term sigAdd [] (natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xFibFrom_with_k1
def yFibFrom_with_k1_term : Term sigAdd [] (natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yFibFrom_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xFibFrom_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFrom_with_k1_term 5 (xOfNat 1) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFrom_with_k1_term 5 (xOfNat 10) = 275 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFrom_with_k1_term 5 (xOfNat 12) = xFibFrom_with_k1 5 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFrom_with_k1_term 5 (runAdd x7_term) = xFibFrom_with_k1 5 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yFibFrom_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFrom_with_k1_term 5 (yOfNat 11) = 445 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFrom_with_k1_term 5 (yOfNat 9) = yFibFrom_with_k1 5 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFrom_with_k1_term 5 (runAdd y5_term) = yFibFrom_with_k1 5 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibFromStep`: the Fibonacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def xFibFromStep_with_k1 (s : Nat) (t : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      yFibFromStep_with_k1 s t (.next a1 r) +
      zFibFromStep_with_k1 s t r +
      t
def yFibFromStep_with_k1 (s : Nat) (t : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      zFibFromStep_with_k1 s t (.next a1 r) +
      xFibFromStep_with_k1 s t r +
      t
def zFibFromStep_with_k1 (s : Nat) (t : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => s
  | .next _ (.next a1 r) =>
      xFibFromStep_with_k1 s t (.next a1 r) +
      yFibFromStep_with_k1 s t r +
      t
end

def xFibFromStep_with_k1_term : Term sigAdd [] (natT ⇒ natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xFibFromStep_with_k1
def yFibFromStep_with_k1_term : Term sigAdd [] (natT ⇒ natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yFibFromStep_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xFibFromStep_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFromStep_with_k1_term 2 3 (xOfNat 1) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFromStep_with_k1_term 2 3 (xOfNat 10) = 374 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFromStep_with_k1_term 2 3 (xOfNat 12) = xFibFromStep_with_k1 2 3 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibFromStep_with_k1_term 2 3 (runAdd x7_term) = xFibFromStep_with_k1 2 3 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yFibFromStep_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFromStep_with_k1_term 2 3 (yOfNat 11) = 607 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFromStep_with_k1_term 2 3 (yOfNat 9) = yFibFromStep_with_k1 2 3 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibFromStep_with_k1_term 2 3 (runAdd y5_term) = yFibFromStep_with_k1 2 3 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibScaled`: the Fibonacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def xFibScaled_with_k1 : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, m => m
  | .next _ (.next a1 r), m =>
      yFibScaled_with_k1 (.next a1 r) m +
      zFibScaled_with_k1 r m
def yFibScaled_with_k1 : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, m => m
  | .next _ (.next a1 r), m =>
      zFibScaled_with_k1 (.next a1 r) m +
      xFibScaled_with_k1 r m
def zFibScaled_with_k1 : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, m => m
  | .next _ (.next a1 r), m =>
      xFibScaled_with_k1 (.next a1 r) m +
      yFibScaled_with_k1 r m
end

def xFibScaled_with_k1_term : Term sigAdd [] (xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xFibScaled_with_k1
def yFibScaled_with_k1_term : Term sigAdd [] (yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yFibScaled_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xFibScaled_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibScaled_with_k1_term (xOfNat 1) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibScaled_with_k1_term (xOfNat 7) 4 = 52 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xFibScaled_with_k1 (X.ofNat 7) 4 = 52 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibScaled_with_k1_term (xOfNat 8) 4 = xFibScaled_with_k1 (X.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibScaled_with_k1_term (runAdd x7_term) 4 = xFibScaled_with_k1 x7 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yFibScaled_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibScaled_with_k1_term (yOfNat 8) 4 = 84 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yFibScaled_with_k1 (Y.ofNat 8) 4 = 84 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibScaled_with_k1_term (yOfNat 7) 4 = yFibScaled_with_k1 (Y.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibScaled_with_k1_term (runAdd y5_term) 4 = yFibScaled_with_k1 y5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `FibMixed`: the Fibonacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def xFibMixed_with_k1 (s : Nat) : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => s
  | .next _ (.next a1 r), t =>
      yFibMixed_with_k1 s (.next a1 r) t +
      zFibMixed_with_k1 s r t +
      t
def yFibMixed_with_k1 (s : Nat) : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => s
  | .next _ (.next a1 r), t =>
      zFibMixed_with_k1 s (.next a1 r) t +
      xFibMixed_with_k1 s r t +
      t
def zFibMixed_with_k1 (s : Nat) : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => s
  | .next _ (.next a1 r), t =>
      xFibMixed_with_k1 s (.next a1 r) t +
      yFibMixed_with_k1 s r t +
      t
end

def xFibMixed_with_k1_term : Term sigAdd [] (natT ⇒ xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xFibMixed_with_k1
def yFibMixed_with_k1_term : Term sigAdd [] (natT ⇒ yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yFibMixed_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xFibMixed_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibMixed_with_k1_term 3 (xOfNat 1) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibMixed_with_k1_term 3 (xOfNat 7) 2 = 79 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xFibMixed_with_k1 3 (X.ofNat 7) 2 = 79 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibMixed_with_k1_term 3 (xOfNat 8) 2 = xFibMixed_with_k1 3 (X.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xFibMixed_with_k1_term 3 (runAdd x7_term) 2 = xFibMixed_with_k1 3 x7 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yFibMixed_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibMixed_with_k1_term 3 (yOfNat 8) 2 = 129 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yFibMixed_with_k1 3 (Y.ofNat 8) 2 = 129 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibMixed_with_k1_term 3 (yOfNat 7) 2 = yFibMixed_with_k1 3 (Y.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yFibMixed_with_k1_term 3 (runAdd y5_term) 2 = yFibMixed_with_k1 3 y5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.ThreeMembers

end
