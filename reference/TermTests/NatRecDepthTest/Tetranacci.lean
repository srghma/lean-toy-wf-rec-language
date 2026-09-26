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

def tetranacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 1
  | n + 4 => tetranacci n + tetranacci (n + 1) + tetranacci (n + 2) + tetranacci (n + 3)

def tetranacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tetranacci

-- [SKIPPED BY PROFILE_LAKE] example : runAdd tetranacci_term 3 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tetranacci_term 8 = tetranacci 8 := by kernel_rfl

end TermTests.NatRecDepth

end
