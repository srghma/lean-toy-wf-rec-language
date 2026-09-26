module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 4`: programs that read 5 links down

Part of the `mutualRecursiveFamily_rec k` translation tests; see
`TermTests/MutualFamilyToTermTest/Common.lean` for what is checked.  `aPenta_with_k4` and
`bPenta_with_k4` are the `pentanacci` recursion of `TermTests/NatRecDepthTest/` on the
number of links, written as a pair of mutual functions: the branch of an `A` link reads
the answers at the next 5 links, which alternate between `B` and `A`, so it looks 4 times
into a subvalue of the other member or of its own. -/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

mutual
def aPenta_with_k4 : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 0
  | .next _ (.next _ (.next _ (.next _ .stop))) => 1
  | .next _ (.next a1 (.next a2 (.next a3 (.next a4 r)))) =>
      bPenta_with_k4 r +
        aPenta_with_k4 (.next a4 r) +
        bPenta_with_k4 (.next a3 (.next a4 r)) +
        aPenta_with_k4 (.next a2 (.next a3 (.next a4 r))) +
        bPenta_with_k4 (.next a1 (.next a2 (.next a3 (.next a4 r))))
def bPenta_with_k4 : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 0
  | .next _ (.next _ (.next _ (.next _ .stop))) => 1
  | .next _ (.next a1 (.next a2 (.next a3 (.next a4 r)))) =>
      aPenta_with_k4 r +
        bPenta_with_k4 (.next a4 r) +
        aPenta_with_k4 (.next a3 (.next a4 r)) +
        bPenta_with_k4 (.next a2 (.next a3 (.next a4 r))) +
        aPenta_with_k4 (.next a1 (.next a2 (.next a3 (.next a4 r))))
end

def aPenta_with_k4_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aPenta_with_k4
def bPenta_with_k4_term : Term sigAdd [] (bT ⇒ natT) := #leanscript_to_term bPenta_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aPenta_with_k4_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aPenta_with_k4_term (aOfNat 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aPenta_with_k4_term (aOfNat 10) = 31 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bPenta_with_k4_term (bOfNat 11) = 61 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aPenta_with_k4_term (aOfNat 12) = aPenta_with_k4 (A.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bPenta_with_k4_term (bOfNat 9) = bPenta_with_k4 (B.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aPenta_with_k4_term (runAdd a4_term) = aPenta_with_k4 a4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bPenta_with_k4_term (runAdd b5_term) = bPenta_with_k4 b5 := by kernel_rfl

end TermTests.MutualFamilyToTerm

end
