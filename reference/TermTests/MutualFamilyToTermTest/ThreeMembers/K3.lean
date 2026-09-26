module

public import TermTests.MutualFamilyToTermTest.ThreeMembers.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 3` on three members: programs that read 4 links down

Part of the three-member family tests; see
`TermTests/MutualFamilyToTermTest/ThreeMembers/Common.lean` for the family and for what is
checked.  The programs are the tetranacci recursion of `TermTests/NatRecDepthTest/` on
the number of links, written as three mutual functions: the branch of a link reads the
answers at the next 4 links, which go round the members `X → Y → Z → X`, so it looks
3 times, each time into a subvalue of the next member.  Each program comes in five
forms: with one argument (the chain), and with two and three arguments before and after
the chain. -/

namespace TermTests.MutualFamilyToTerm.ThreeMembers

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

/-! ## `Tetra`: the tetranacci recursion on the number of links -/

mutual
def xTetra_with_k3 : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 1
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      yTetra_with_k3 (.next a1 (.next a2 (.next a3 r))) +
      zTetra_with_k3 (.next a2 (.next a3 r)) +
      xTetra_with_k3 (.next a3 r) +
      yTetra_with_k3 r
def yTetra_with_k3 : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 1
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      zTetra_with_k3 (.next a1 (.next a2 (.next a3 r))) +
      xTetra_with_k3 (.next a2 (.next a3 r)) +
      yTetra_with_k3 (.next a3 r) +
      zTetra_with_k3 r
def zTetra_with_k3 : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 1
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      xTetra_with_k3 (.next a1 (.next a2 (.next a3 r))) +
      yTetra_with_k3 (.next a2 (.next a3 r)) +
      zTetra_with_k3 (.next a3 r) +
      xTetra_with_k3 r
end

def xTetra_with_k3_term : Term sigAdd [] (xT ⇒ natT) :=
  #leanscript_to_term xTetra_with_k3
def yTetra_with_k3_term : Term sigAdd [] (yT ⇒ natT) :=
  #leanscript_to_term yTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetra_with_k3_term (xOfNat 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetra_with_k3_term (xOfNat 10) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetra_with_k3_term (xOfNat 12) = xTetra_with_k3 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetra_with_k3_term (runAdd x7_term) = xTetra_with_k3 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetra_with_k3_term (yOfNat 11) = 108 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetra_with_k3_term (yOfNat 9) = yTetra_with_k3 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetra_with_k3_term (runAdd y5_term) = yTetra_with_k3 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraFrom`: the tetranacci recursion on the number of links

Two arguments: the start value `s` comes first, so Lean keeps it as a parameter of the
fold and the term is `fun s => fold`. -/

mutual
def xTetraFrom_with_k3 (s : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      yTetraFrom_with_k3 s (.next a1 (.next a2 (.next a3 r))) +
      zTetraFrom_with_k3 s (.next a2 (.next a3 r)) +
      xTetraFrom_with_k3 s (.next a3 r) +
      yTetraFrom_with_k3 s r
def yTetraFrom_with_k3 (s : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      zTetraFrom_with_k3 s (.next a1 (.next a2 (.next a3 r))) +
      xTetraFrom_with_k3 s (.next a2 (.next a3 r)) +
      yTetraFrom_with_k3 s (.next a3 r) +
      zTetraFrom_with_k3 s r
def zTetraFrom_with_k3 (s : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      xTetraFrom_with_k3 s (.next a1 (.next a2 (.next a3 r))) +
      yTetraFrom_with_k3 s (.next a2 (.next a3 r)) +
      zTetraFrom_with_k3 s (.next a3 r) +
      xTetraFrom_with_k3 s r
end

def xTetraFrom_with_k3_term : Term sigAdd [] (natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xTetraFrom_with_k3
def yTetraFrom_with_k3_term : Term sigAdd [] (natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yTetraFrom_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTetraFrom_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFrom_with_k3_term 5 (xOfNat 3) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFrom_with_k3_term 5 (xOfNat 10) = 280 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFrom_with_k3_term 5 (xOfNat 12) = xTetraFrom_with_k3 5 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFrom_with_k3_term 5 (runAdd x7_term) = xTetraFrom_with_k3 5 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTetraFrom_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFrom_with_k3_term 5 (yOfNat 11) = 540 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFrom_with_k3_term 5 (yOfNat 9) = yTetraFrom_with_k3 5 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFrom_with_k3_term 5 (runAdd y5_term) = yTetraFrom_with_k3 5 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraFromStep`: the tetranacci recursion on the number of links

Three arguments: the start value `s` and a step `t` added at every link, both before the
chain. -/

mutual
def xTetraFromStep_with_k3 (s : Nat) (t : Nat) : X → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      yTetraFromStep_with_k3 s t (.next a1 (.next a2 (.next a3 r))) +
      zTetraFromStep_with_k3 s t (.next a2 (.next a3 r)) +
      xTetraFromStep_with_k3 s t (.next a3 r) +
      yTetraFromStep_with_k3 s t r +
      t
def yTetraFromStep_with_k3 (s : Nat) (t : Nat) : Y → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      zTetraFromStep_with_k3 s t (.next a1 (.next a2 (.next a3 r))) +
      xTetraFromStep_with_k3 s t (.next a2 (.next a3 r)) +
      yTetraFromStep_with_k3 s t (.next a3 r) +
      zTetraFromStep_with_k3 s t r +
      t
def zTetraFromStep_with_k3 (s : Nat) (t : Nat) : Z → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => s
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      xTetraFromStep_with_k3 s t (.next a1 (.next a2 (.next a3 r))) +
      yTetraFromStep_with_k3 s t (.next a2 (.next a3 r)) +
      zTetraFromStep_with_k3 s t (.next a3 r) +
      xTetraFromStep_with_k3 s t r +
      t
end

def xTetraFromStep_with_k3_term : Term sigAdd [] (natT ⇒ natT ⇒ xT ⇒ natT) :=
  #leanscript_to_term xTetraFromStep_with_k3
def yTetraFromStep_with_k3_term : Term sigAdd [] (natT ⇒ natT ⇒ yT ⇒ natT) :=
  #leanscript_to_term yTetraFromStep_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTetraFromStep_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFromStep_with_k3_term 2 3 (xOfNat 3) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFromStep_with_k3_term 2 3 (xOfNat 10) = 292 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFromStep_with_k3_term 2 3 (xOfNat 12) = xTetraFromStep_with_k3 2 3 (X.ofNat 12) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraFromStep_with_k3_term 2 3 (runAdd x7_term) = xTetraFromStep_with_k3 2 3 x7 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTetraFromStep_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFromStep_with_k3_term 2 3 (yOfNat 11) = 564 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFromStep_with_k3_term 2 3 (yOfNat 9) = yTetraFromStep_with_k3 2 3 (Y.ofNat 9) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraFromStep_with_k3_term 2 3 (runAdd y5_term) = yTetraFromStep_with_k3 2 3 y5 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraScaled`: the tetranacci recursion on the number of links

Two arguments: the start value `m` comes *after* the chain, so it is in Lean's motive
and the fold answers a function `Nat → Nat`. -/

mutual
def xTetraScaled_with_k3 : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), m => m
  | .next _ (.next a1 (.next a2 (.next a3 r))), m =>
      yTetraScaled_with_k3 (.next a1 (.next a2 (.next a3 r))) m +
      zTetraScaled_with_k3 (.next a2 (.next a3 r)) m +
      xTetraScaled_with_k3 (.next a3 r) m +
      yTetraScaled_with_k3 r m
def yTetraScaled_with_k3 : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), m => m
  | .next _ (.next a1 (.next a2 (.next a3 r))), m =>
      zTetraScaled_with_k3 (.next a1 (.next a2 (.next a3 r))) m +
      xTetraScaled_with_k3 (.next a2 (.next a3 r)) m +
      yTetraScaled_with_k3 (.next a3 r) m +
      zTetraScaled_with_k3 r m
def zTetraScaled_with_k3 : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), m => m
  | .next _ (.next a1 (.next a2 (.next a3 r))), m =>
      xTetraScaled_with_k3 (.next a1 (.next a2 (.next a3 r))) m +
      yTetraScaled_with_k3 (.next a2 (.next a3 r)) m +
      zTetraScaled_with_k3 (.next a3 r) m +
      xTetraScaled_with_k3 r m
end

def xTetraScaled_with_k3_term : Term sigAdd [] (xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xTetraScaled_with_k3
def yTetraScaled_with_k3_term : Term sigAdd [] (yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yTetraScaled_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTetraScaled_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraScaled_with_k3_term (xOfNat 3) 4 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraScaled_with_k3_term (xOfNat 7) 4 = 32 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xTetraScaled_with_k3 (X.ofNat 7) 4 = 32 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraScaled_with_k3_term (xOfNat 8) 4 = xTetraScaled_with_k3 (X.ofNat 8) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraScaled_with_k3_term (runAdd x7_term) 4 = xTetraScaled_with_k3 x7 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTetraScaled_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraScaled_with_k3_term (yOfNat 8) 4 = 60 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yTetraScaled_with_k3 (Y.ofNat 8) 4 = 60 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraScaled_with_k3_term (yOfNat 7) 4 = yTetraScaled_with_k3 (Y.ofNat 7) 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraScaled_with_k3_term (runAdd y5_term) 4 = yTetraScaled_with_k3 y5 4 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `TetraMixed`: the tetranacci recursion on the number of links

Three arguments: the start value `s` before the chain and the step `t` after it, so the
fold is under a `fun` and answers a function. -/

mutual
def xTetraMixed_with_k3 (s : Nat) : X → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), _ => s
  | .next _ (.next a1 (.next a2 (.next a3 r))), t =>
      yTetraMixed_with_k3 s (.next a1 (.next a2 (.next a3 r))) t +
      zTetraMixed_with_k3 s (.next a2 (.next a3 r)) t +
      xTetraMixed_with_k3 s (.next a3 r) t +
      yTetraMixed_with_k3 s r t +
      t
def yTetraMixed_with_k3 (s : Nat) : Y → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), _ => s
  | .next _ (.next a1 (.next a2 (.next a3 r))), t =>
      zTetraMixed_with_k3 s (.next a1 (.next a2 (.next a3 r))) t +
      xTetraMixed_with_k3 s (.next a2 (.next a3 r)) t +
      yTetraMixed_with_k3 s (.next a3 r) t +
      zTetraMixed_with_k3 s r t +
      t
def zTetraMixed_with_k3 (s : Nat) : Z → Nat → Nat
  | .stop, _ => 0
  | .next _ .stop, _ => 0
  | .next _ (.next _ .stop), _ => 0
  | .next _ (.next _ (.next _ .stop)), _ => s
  | .next _ (.next a1 (.next a2 (.next a3 r))), t =>
      xTetraMixed_with_k3 s (.next a1 (.next a2 (.next a3 r))) t +
      yTetraMixed_with_k3 s (.next a2 (.next a3 r)) t +
      zTetraMixed_with_k3 s (.next a3 r) t +
      xTetraMixed_with_k3 s r t +
      t
end

def xTetraMixed_with_k3_term : Term sigAdd [] (natT ⇒ xT ⇒ natT ⇒ natT) :=
  #leanscript_to_term xTetraMixed_with_k3
def yTetraMixed_with_k3_term : Term sigAdd [] (natT ⇒ yT ⇒ natT ⇒ natT) :=
  #leanscript_to_term yTetraMixed_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? xTetraMixed_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraMixed_with_k3_term 3 (xOfNat 3) 2 = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraMixed_with_k3_term 3 (xOfNat 7) 2 = 40 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : xTetraMixed_with_k3 3 (X.ofNat 7) 2 = 40 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraMixed_with_k3_term 3 (xOfNat 8) 2 = xTetraMixed_with_k3 3 (X.ofNat 8) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xTetraMixed_with_k3_term 3 (runAdd x7_term) 2 = xTetraMixed_with_k3 3 x7 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? yTetraMixed_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraMixed_with_k3_term 3 (yOfNat 8) 2 = 77 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : yTetraMixed_with_k3 3 (Y.ofNat 8) 2 = 77 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraMixed_with_k3_term 3 (yOfNat 7) 2 = yTetraMixed_with_k3 3 (Y.ofNat 7) 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd yTetraMixed_with_k3_term 3 (runAdd y5_term) 2 = yTetraMixed_with_k3 3 y5 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.MutualFamilyToTerm.ThreeMembers

end
