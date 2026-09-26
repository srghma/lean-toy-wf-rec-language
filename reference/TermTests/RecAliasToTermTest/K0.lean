module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec 0`: programs that read the answer one link down

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.  The window of
`recAlias_rec 0` holds the answer at the rest of the chain and nothing below it. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

/-! ### The sum of the labels -/

def chainSum_with_k0 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step l r) => l + chainSum_with_k0 r

def chainSum_with_k0_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainSum_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainSum_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (chainOfNat 5) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (runAdd chain3_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (chainOf [3, 1, 4, 1, 5]) = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (chainOfNat 9) =
-- [SKIPPED BY PROFILE_LAKE]     chainSum_with_k0 (Chain.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSum_with_k0_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     chainSum_with_k0 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

/-! ### The number of links -/

def chainLen_with_k0 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ r) => chainLen_with_k0 r + 1

def chainLen_with_k0_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainLen_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainLen_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainLen_with_k0_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainLen_with_k0_term (chainOfNat 7) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainLen_with_k0_term (runAdd chain3_term) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainLen_with_k0_term (chainOf [3, 1, 4, 1, 5]) =
-- [SKIPPED BY PROFILE_LAKE]     chainLen_with_k0 (Chain.ofList [3, 1, 4, 1, 5]) := by kernel_rfl

/-! ### The sum of the labels with an accumulator: the fold returns a function -/

def chainSumAcc_with_k0 : Chain → Nat → Nat
  | .mk .stop, acc => acc
  | .mk (.step l r), acc => chainSumAcc_with_k0 r (acc + l)

def chainSumAcc_with_k0_term : Term sigAdd [] (chainT ⇒ natT ⇒ natT) :=
  #leanscript_to_term chainSumAcc_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainSumAcc_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSumAcc_with_k0_term (chainOfNat 0) 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSumAcc_with_k0_term (chainOf [3, 1, 4]) 10 = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainSumAcc_with_k0_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6]) 7 =
-- [SKIPPED BY PROFILE_LAKE]     chainSumAcc_with_k0 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6]) 7 := by kernel_rfl

/-! ### A newtype whose body is `Option` of itself: Peano numbers

`Nest` is `μX. Option X`, a newtype over the library's own `Option`. -/

/-- Peano numbers, as the recursive newtype `μX. Option X`. -/
inductive Nest where
  /-- The one constructor, of one field. -/
  | mk (pred : Option Nest)
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Nest = .recAlias (.taggedUnion (.skip (.here ⟨.self, []⟩ []))) := rfl

/-- The Peano number `n`. -/
def Nest.ofNat : Nat → Nest
  | 0 => .mk none
  | n + 1 => .mk (some (Nest.ofNat n))

def nestOfNat_term : Term sigAdd [] (natT ⇒ tyWfOf Nest) := #leanscript_to_term Nest.ofNat

def nestToNat_with_k0 : Nest → Nat
  | .mk none => 0
  | .mk (some p) => nestToNat_with_k0 p + 1

def nestToNat_with_k0_term : Term sigAdd [] (tyWfOf Nest ⇒ natT) :=
  #leanscript_to_term nestToNat_with_k0

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? nestToNat_with_k0_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestToNat_with_k0_term (runAdd nestOfNat_term 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestToNat_with_k0_term (runAdd nestOfNat_term 9) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd nestToNat_with_k0_term (runAdd nestOfNat_term 13) =
-- [SKIPPED BY PROFILE_LAKE]     nestToNat_with_k0 (Nest.ofNat 13) := by kernel_rfl

end TermTests.RecAliasToTerm

end
