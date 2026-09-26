module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec 4`: programs that read 5 links down

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.  The window of
`recAlias_rec 4` holds the answers at every link at most 5 levels down, along the chain.

`chainPenta_with_k4` is the `pentanacci` recursion of `TermTests/NatRecDepthTest/`, on the number of
links: `penta 0 = … = penta 3 = 0`, `penta 4 = 1`, and `penta (n + 5)` is the sum of the
five before it. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

def chainPenta_with_k4 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ (.mk .stop)) => 0
  | .mk (.step _ (.mk (.step _ (.mk .stop)))) => 0
  | .mk (.step _ (.mk (.step _ (.mk (.step _ (.mk .stop)))))) => 0
  | .mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk .stop)))))))) => 1
  | .mk (.step _ (.mk (.step a1 (.mk (.step a2 (.mk (.step a3 (.mk (.step a4 r))))))))) =>
      chainPenta_with_k4 r +
        chainPenta_with_k4 (.mk (.step a4 r)) +
        chainPenta_with_k4 (.mk (.step a3 (.mk (.step a4 r)))) +
        chainPenta_with_k4 (.mk (.step a2 (.mk (.step a3 (.mk (.step a4 r)))))) +
        chainPenta_with_k4 (.mk (.step a1 (.mk (.step a2 (.mk (.step a3 (.mk (.step a4 r))))))))

def chainPenta_with_k4_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainPenta_with_k4

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainPenta_with_k4_term = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOfNat 4) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOfNat 10) = 31 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOfNat 12) = 120 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOfNat 10) =
-- [SKIPPED BY PROFILE_LAKE]     chainPenta_with_k4 (Chain.ofNat 10) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainPenta_with_k4_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6, 5]) =
-- [SKIPPED BY PROFILE_LAKE]     chainPenta_with_k4 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6, 5]) := by kernel_rfl

end TermTests.RecAliasToTerm

end
