module

public import TermTests.NatRecDepthTest.Common
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

/-! Part of the `nat_rec k` translation tests; see `TermTests/NatRecDepthTest/Common.lean`
for what is checked. -/

namespace TermTests.NatRecDepth

open LeanScript

def hexanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 0
  | 5     => 1
  | n + 6 => hexanacci n + hexanacci (n + 1) + hexanacci (n + 2)
           + hexanacci (n + 3) + hexanacci (n + 4) + hexanacci (n + 5)

def hexanacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term hexanacci

-- [SKIPPED BY PROFILE_LAKE] example : runAdd hexanacci_term 5 = 1 := by kernel_rfl

-- The six-deep window makes this the largest of the checks, and the elaborator's own
-- `isDefEq` check of it is slow, so the equation is left to the kernel alone
-- (`kernel_rfl`, see `LeanScript/KernelRfl.lean`); no raised heartbeat budget is needed.
-- [SKIPPED BY PROFILE_LAKE] example : runAdd hexanacci_term 8 = hexanacci 8 := by kernel_rfl

end TermTests.NatRecDepth

end
