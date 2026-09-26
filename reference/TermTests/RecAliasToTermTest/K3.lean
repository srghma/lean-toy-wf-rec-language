module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec 3`: programs that read 4 links down

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.  The window of
`recAlias_rec 3` holds the answers at every link at most 4 levels down, along the chain.

`chainTetra_with_k3` is the `tetranacci` recursion of `TermTests/NatRecDepthTest/`, on the number of
links: `tetra 0 = tetra 1 = tetra 2 = 0`, `tetra 3 = 1`, and `tetra (n + 4)` is the sum of
the four before it. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

def chainTetra_with_k3 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ (.mk .stop)) => 0
  | .mk (.step _ (.mk (.step _ (.mk .stop)))) => 0
  | .mk (.step _ (.mk (.step _ (.mk (.step _ (.mk .stop)))))) => 1
  | .mk (.step _ (.mk (.step a1 (.mk (.step a2 (.mk (.step a3 r))))))) =>
      chainTetra_with_k3 r +
        chainTetra_with_k3 (.mk (.step a3 r)) +
        chainTetra_with_k3 (.mk (.step a2 (.mk (.step a3 r)))) +
        chainTetra_with_k3 (.mk (.step a1 (.mk (.step a2 (.mk (.step a3 r))))))

def chainTetra_with_k3_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainTetra_with_k3

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainTetra_with_k3_term = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOfNat 3) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOfNat 10) = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOfNat 12) = 208 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOfNat 9) =
-- [SKIPPED BY PROFILE_LAKE]     chainTetra_with_k3 (Chain.ofNat 9) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTetra_with_k3_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6, 5]) =
-- [SKIPPED BY PROFILE_LAKE]     chainTetra_with_k3 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6, 5]) := by kernel_rfl

end TermTests.RecAliasToTerm

end
