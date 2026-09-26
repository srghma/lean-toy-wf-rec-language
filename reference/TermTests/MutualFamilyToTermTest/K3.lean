module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 3`: programs that read 4 links down

Part of the `mutualRecursiveFamily_rec k` translation tests; see
`TermTests/MutualFamilyToTermTest/Common.lean` for what is checked.  `aTetra_with_k3` and
`bTetra_with_k3` are the `tetranacci` recursion of `TermTests/NatRecDepthTest/` on the
number of links, written as a pair of mutual functions: the branch of an `A` link reads
the answers at the next 4 links, which alternate between `B` and `A`, so it looks 3 times
into a subvalue of the other member or of its own. -/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

mutual
def aTetra_with_k3 : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 1
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      aTetra_with_k3 r +
        bTetra_with_k3 (.next a3 r) +
        aTetra_with_k3 (.next a2 (.next a3 r)) +
        bTetra_with_k3 (.next a1 (.next a2 (.next a3 r)))
def bTetra_with_k3 : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next _ (.next _ .stop) => 0
  | .next _ (.next _ (.next _ .stop)) => 1
  | .next _ (.next a1 (.next a2 (.next a3 r))) =>
      bTetra_with_k3 r +
        aTetra_with_k3 (.next a3 r) +
        bTetra_with_k3 (.next a2 (.next a3 r)) +
        aTetra_with_k3 (.next a1 (.next a2 (.next a3 r)))
end

def aTetra_with_k3_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aTetra_with_k3
def bTetra_with_k3_term : Term sigAdd [] (bT ⇒ natT) := #leanscript_to_term bTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetra_with_k3_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetra_with_k3_term (aOfNat 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetra_with_k3_term (aOfNat 10) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetra_with_k3_term (bOfNat 11) = 108 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetra_with_k3_term (aOfNat 12) = aTetra_with_k3 (A.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetra_with_k3_term (bOfNat 9) = bTetra_with_k3 (B.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTetra_with_k3_term (runAdd a4_term) = aTetra_with_k3 a4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bTetra_with_k3_term (runAdd b5_term) = bTetra_with_k3 b5 := by kernel_rfl

end TermTests.MutualFamilyToTerm

end
