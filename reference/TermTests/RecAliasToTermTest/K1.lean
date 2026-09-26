module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec 1`: programs that read two links down

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.  The window of
`recAlias_rec 1` holds, for the link below, the answer there *and* that link's own body:
its label and the answer at the link below it. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

/-! ### `fib` of the length: `fib (n + 2) = fib n + fib (n + 1)` -/

def chainFib_with_k1 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ (.mk .stop)) => 1
  | .mk (.step _ (.mk (.step l r))) => chainFib_with_k1 r + chainFib_with_k1 (.mk (.step l r))

def chainFib_with_k1_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainFib_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainFib_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOfNat 0) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOfNat 1) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOfNat 2) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOfNat 10) = 55 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (runAdd chain3_term) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOfNat 12) =
-- [SKIPPED BY PROFILE_LAKE]     chainFib_with_k1 (Chain.ofNat 12) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainFib_with_k1_term (chainOf [3, 1, 4, 1, 5, 9]) =
-- [SKIPPED BY PROFILE_LAKE]     chainFib_with_k1 (Chain.ofList [3, 1, 4, 1, 5, 9]) := by kernel_rfl

/-! ### The sum of the products of neighbouring labels

The branch reads the label of the link below, which is in the window only at depth `1`. -/

def chainNeighbourProducts_with_k1 : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ (.mk .stop)) => 0
  | .mk (.step a (.mk (.step b r))) => a * b + chainNeighbourProducts_with_k1 (.mk (.step b r))

def chainNeighbourProducts_with_k1_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainNeighbourProducts_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainNeighbourProducts_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainNeighbourProducts_with_k1_term (chainOf [7]) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainNeighbourProducts_with_k1_term (runAdd chain3_term) = 8 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainNeighbourProducts_with_k1_term (chainOf [1, 2, 3, 4]) = 20 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainNeighbourProducts_with_k1_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     chainNeighbourProducts_with_k1 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

/-! ### The continuant of the labels: reads the labels two links down too

`K [] = 1`, `K [a] = a` and `K (a :: b :: l) = a * K (b :: l) + K l`. -/

def chainCont_with_k1 : Chain → Nat
  | .mk .stop => 1
  | .mk (.step a (.mk .stop)) => a
  | .mk (.step a (.mk (.step b r))) => a * chainCont_with_k1 (.mk (.step b r)) + chainCont_with_k1 r

def chainCont_with_k1_term : Term sigAdd [] (chainT ⇒ natT) :=
  #leanscript_to_term chainCont_with_k1

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? chainCont_with_k1_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainCont_with_k1_term (chainOf []) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainCont_with_k1_term (chainOf [7]) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainCont_with_k1_term (chainOf [2, 3]) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainCont_with_k1_term (chainOf [1, 2, 3, 4]) = 43 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainCont_with_k1_term (chainOf [3, 1, 4, 1, 5, 9, 2, 6]) =
-- [SKIPPED BY PROFILE_LAKE]     chainCont_with_k1 (Chain.ofList [3, 1, 4, 1, 5, 9, 2, 6]) := by kernel_rfl

end TermTests.RecAliasToTerm

end
