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

def pentanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 1
  | n + 5 => pentanacci n + pentanacci (n + 1) + pentanacci (n + 2)
           + pentanacci (n + 3) + pentanacci (n + 4)

def pentanacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term pentanacci

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pentanacci_term 4 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pentanacci_term 8 = pentanacci 8 := by kernel_rfl

end TermTests.NatRecDepth

end
