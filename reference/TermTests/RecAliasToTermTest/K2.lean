module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec 2`: programs that read 3 links down

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.  The window of
`recAlias_rec 2` holds the answers at every link at most 3 levels down, along the chain.

`chainTrib_with_k2` is the `tribonacci` recursion of `TermTests/NatRecDepthTest/`, on the number of
links: `trib 0 = 0`, `trib 1 = 0`, `trib 2 = 1`, `trib (n + 3) = trib n + trib (n + 1) +
trib (n + 2)`. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

def chainTrib_with_k2 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ (.mk .stop)) => 0
  | .mk (.step _ (.mk (.step _ (.mk .stop)))) => 1
  | .mk (.step _ (.mk (.step a1 (.mk (.step a2 r))))) =>
      chainTrib_with_k2 r +
        chainTrib_with_k2 (.mk (.step a2 r)) +
        chainTrib_with_k2 (.mk (.step a1 (.mk (.step a2 r))))

def chainTrib_with_k2_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainTrib_with_k2

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainTrib_with_k2_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOfNat 10) = 81 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOfNat 12) = 274 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOfNat 8) =
-- [SKIPPED BY PROFILE_LAKE]     chainTrib_with_k2 (Chain.ofNat 8) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTrib_with_k2_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6, 5]) =
-- [SKIPPED BY PROFILE_LAKE]     chainTrib_with_k2 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6, 5]) := by kernel_rfl

end TermTests.RecAliasToTerm

end
