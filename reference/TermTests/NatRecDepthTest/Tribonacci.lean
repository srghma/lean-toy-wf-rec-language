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

/-! ### Three steps and more

The depth is not fixed by the grammar, so the whole family translates: the tribonacci
numbers descend three steps, the tetranacci four, the pentanacci five and the hexanacci
six. -/

def tribonacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

def tribonacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tribonacci

-- [SKIPPED BY PROFILE_LAKE] example : runAdd tribonacci_term 2 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tribonacci_term 10 = tribonacci 10 := by kernel_rfl

end TermTests.NatRecDepth

end
