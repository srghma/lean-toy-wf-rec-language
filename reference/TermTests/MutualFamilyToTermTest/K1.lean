module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `mutualRecursiveFamily_rec 1`: programs that read 2 links down

Part of the `mutualRecursiveFamily_rec k` translation tests; see
`TermTests/MutualFamilyToTermTest/Common.lean` for what is checked.  `aFib_with_k1` and
`bFib_with_k1` are the `fib` recursion of `TermTests/NatRecDepthTest/` on the number of
links, written as a pair of mutual functions: the branch of an `A` link reads the answers
at the next 2 links, which alternate between `B` and `A`, so it looks 1 times into a
subvalue of the other member or of its own. -/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

mutual
def aFib_with_k1 : A → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next a1 r) =>
      aFib_with_k1 r +
        bFib_with_k1 (.next a1 r)
def bFib_with_k1 : B → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next a1 r) =>
      bFib_with_k1 r +
        aFib_with_k1 (.next a1 r)
end

def aFib_with_k1_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aFib_with_k1
def bFib_with_k1_term : Term sigAdd [] (bT ⇒ natT) := #leanscript_to_term bFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? bFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFib_with_k1_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFib_with_k1_term (aOfNat 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFib_with_k1_term (aOfNat 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFib_with_k1_term (bOfNat 11) = 89 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFib_with_k1_term (aOfNat 12) = aFib_with_k1 (A.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFib_with_k1_term (bOfNat 9) = bFib_with_k1 (B.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aFib_with_k1_term (runAdd a4_term) = aFib_with_k1 a4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bFib_with_k1_term (runAdd b5_term) = bFib_with_k1 b5 := by kernel_rfl

/-! ## A single function that goes *through* the other member

`aLen_with_k1` is one function on `A`, not a pair: Lean compiles it with the motive of `B`
set to `PUnit`, and the fold still needs branches for `B`, which answer `default` — an
answer no branch of `A` reads, since the branch of an `A` link looks through the `B` link
below it to the `A` link below that. -/

def aLen_with_k1 : A → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next _ a) => aLen_with_k1 a + 2

def aLen_with_k1_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term aLen_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aLen_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aLen_with_k1_term (aOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aLen_with_k1_term (aOfNat 7) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aLen_with_k1_term (aOfNat 10) = aLen_with_k1 (A.ofNat 10) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aLen_with_k1_term (runAdd a4_term) = aLen_with_k1 a4 := by kernel_rfl

/-! ## The sum of the products of neighbouring labels

The branch reads the label of the link below, which it sees only by looking into it. -/

mutual
def aNeighbourProducts_with_k1 : A → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next a (.next b r) => a * b + bNeighbourProducts_with_k1 (.next b r)
def bNeighbourProducts_with_k1 : B → Nat
  | .stop => 0
  | .next _ .stop => 0
  | .next a (.next b r) => a * b + aNeighbourProducts_with_k1 (.next b r)
end

def aNeighbourProducts_with_k1_term : Term sigAdd [] (aT ⇒ natT) :=
  #leanscript_to_term aNeighbourProducts_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : familyRecDepth? aNeighbourProducts_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aNeighbourProducts_with_k1_term (runAdd a4_term) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aNeighbourProducts_with_k1_term (aOfNat 6) =
-- [SKIPPED BY PROFILE_LAKE]     aNeighbourProducts_with_k1 (A.ofNat 6) := by kernel_rfl

end TermTests.MutualFamilyToTerm

end
