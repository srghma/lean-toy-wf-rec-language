module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 2`: programs that read 3 links down

Part of the `mutualRecursiveFamily_rec k` translation tests; see
`TermTests/MutualFamilyToTermTest/Common.lean` for what is checked.  `aTrib_with_k2` and
`bTrib_with_k2` are the `tribonacci` recursion of `TermTests/NatRecDepthTest/` on the
number of links, written as a pair of mutual functions: the branch of an `A` link reads
the answers at the next 3 links, which alternate between `B` and `A`, so it looks 2 times
into a subvalue of the other member or of its own. -/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

mutual
def aTrib_with_k2 : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 1
  | .next _ (.next a1 (.next a2 r)) =>
      bTrib_with_k2 r +
        aTrib_with_k2 (.next a2 r) +
        bTrib_with_k2 (.next a1 (.next a2 r))
def bTrib_with_k2 : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 1
  | .next _ (.next a1 (.next a2 r)) =>
      aTrib_with_k2 r +
        bTrib_with_k2 (.next a2 r) +
        aTrib_with_k2 (.next a1 (.next a2 r))
end

def aTrib_with_k2_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aTrib_with_k2
def bTrib_with_k2_term : Term sigAdd [] (bT ⇒ natT) := #leanscript_to_term bTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTrib_with_k2_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTrib_with_k2_term (aOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTrib_with_k2_term (aOfNat 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTrib_with_k2_term (bOfNat 11) = 149 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTrib_with_k2_term (aOfNat 12) = aTrib_with_k2 (A.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTrib_with_k2_term (bOfNat 9) = bTrib_with_k2 (B.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTrib_with_k2_term (runAdd a4_term) = aTrib_with_k2 a4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTrib_with_k2_term (runAdd b5_term) = bTrib_with_k2 b5 := by kernel_rfl

end TermTests.MutualFamilyToTerm

end
