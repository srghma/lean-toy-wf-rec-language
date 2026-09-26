module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 0`: programs that read the answers one constructor down

Part of the `mutualRecursiveFamily_rec k` translation tests; see
`TermTests/MutualFamilyToTermTest/Common.lean` for what is checked.  At depth `0` a branch
of each member is given the constructor's fields and the answers at its occurrences of
members, and nothing below them. -/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

/-! ## The sum of the labels of an alternating chain -/

mutual
def aSum_with_k0 : A → Nat
  | .stop => 0
  | .next l b => l + bSum_with_k0 b
def bSum_with_k0 : B → Nat
  | .stop => 0
  | .next l a => l + aSum_with_k0 a
end

def aSum_with_k0_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aSum_with_k0
def bSum_with_k0_term : Term sigAdd [] (bT ⇒ natT) := #leanscript_to_term bSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSum_with_k0_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSum_with_k0_term (aOfNat 5) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bSum_with_k0_term (bOfNat 6) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSum_with_k0_term (runAdd a4_term) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bSum_with_k0_term (runAdd b5_term) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSum_with_k0_term (aOfNat 11) = aSum_with_k0 (A.ofNat 11) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bSum_with_k0_term (runAdd b5_term) = bSum_with_k0 b5 := by kernel_rfl

/-! ## The same sum with an accumulator: the fold returns a function -/

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
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSumAcc_with_k0_term (aOfNat 0) 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSumAcc_with_k0_term (runAdd a4_term) 10 = 19 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aSumAcc_with_k0_term (aOfNat 9) 3 = aSumAcc_with_k0 (A.ofNat 9) 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A family with a newtype member: even and odd numbers

`Od` has one constructor of one field, so in the family it is an `alias` member, and its
branch binds its body — an `Ev` — and the answer there. -/

mutual
def evToNat_with_k0 : Ev → Nat
  | .zero => 0
  | .succ o => odToNat_with_k0 o + 1
def odToNat_with_k0 : Od → Nat
  | .succ e => evToNat_with_k0 e + 1
end

/-- `2 * n`, as an even number. -/
def Ev.double : Nat → Ev
  | 0 => .zero
  | n + 1 => .succ (.succ (Ev.double n))

/-- `Ev.double`, as a term: a `nat_rec` building a newtype member inside a `ctors` one. -/
def evDouble_term : Term sigAdd [] (natT ⇒ tyWfOf Ev) := #leanscript_to_term Ev.double

def evToNat_with_k0_term : Term sigAdd [] (tyWfOf Ev ⇒ natT) :=
  #leanscript_to_term evToNat_with_k0
def odToNat_with_k0_term : Term sigAdd [] (tyWfOf Od ⇒ natT) :=
  #leanscript_to_term odToNat_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? evToNat_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? odToNat_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evToNat_with_k0_term (runAdd evDouble_term 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evToNat_with_k0_term (runAdd evDouble_term 6) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evToNat_with_k0_term (runAdd evDouble_term 9) =
-- [SKIPPED BY PROFILE_LAKE]     evToNat_with_k0 (Ev.double 9) := by kernel_rfl

/-- Three, as an odd number, written out. -/
def od3 : Od := .succ (.succ (.succ .zero))

def od3_term : Term sigAdd [] (tyWfOf Od) := #leanscript_to_term od3

-- [SKIPPED BY PROFILE_LAKE] example : runAdd odToNat_with_k0_term (runAdd od3_term) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd odToNat_with_k0_term (runAdd od3_term) = odToNat_with_k0 od3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A family with a record member: terms and pairs of terms

`Pr` has one constructor of two fields, so in the family it is a `record` member, with two
occurrences of `Tm`: its branch binds both and the answers at both. -/

mutual
def tmSum_with_k0 : Tm → Nat
  | .lit n => n
  | .pair p => prSum_with_k0 p
def prSum_with_k0 : Pr → Nat
  | .mk l r => tmSum_with_k0 l + tmSum_with_k0 r
end

/-- A term written out: `((1, 2), (3, (4, 5)))`. -/
def tm5 : Tm :=
  .pair (.mk (.pair (.mk (.lit 1) (.lit 2)))
    (.pair (.mk (.lit 3) (.pair (.mk (.lit 4) (.lit 5))))))

def tm5_term : Term sigAdd [] (tyWfOf Tm) := #leanscript_to_term tm5

def tmSum_with_k0_term : Term sigAdd [] (tyWfOf Tm ⇒ natT) :=
  #leanscript_to_term tmSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? tmSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tmSum_with_k0_term (runAdd tm5_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tmSum_with_k0_term (runAdd tm5_term) = tmSum_with_k0 tm5 := by kernel_rfl

end TermTests.MutualFamilyToTerm

end
