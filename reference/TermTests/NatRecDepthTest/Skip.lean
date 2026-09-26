module

public import TermTests.NatRecDepthTest.Common
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

/-! Part of the `nat_rec k` translation tests; see `TermTests/NatRecDepthTest/Common.lean`
for what is checked.

## Skipping levels

A natural number has one subvalue at each step, its predecessor, so there is no "both
subtrees" for a fold of a `Nat` to reach: the window of `nat_rec k` already holds the
answers at **all** of the `k + 1` predecessors, so a recursion that reads only some of
them — the answer two or three steps down, and not the ones in between — is a `nat_rec k`
of the depth of the furthest one it reads. -/

namespace TermTests.NatRecDepth

open LeanScript

mutual
/-- The depth of the `nat_rec` a translated function `fun n => nat_rec k …` is, or
    `none` if the translation is not of that shape. -/
def natRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sigAdd Γ τ J → Option Nat
  | .nat_rec k _ _ _ _ => some k
  | .letE c body => (natRecDepth?.comp c).orElse fun _ => natRecDepth? body
  | .letJ jp body => (natRecDepth? body).orElse fun _ => natRecDepth? jp
  | _ => none

/-- `natRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def natRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sigAdd Γ τ → Option Nat
  | .lam b => natRecDepth? b
  | _ => none
end

/-! ### Two steps down: the sum of the numbers of the same parity -/

def paritySum : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => n + 2 + paritySum n

def paritySum_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term paritySum

-- [SKIPPED BY PROFILE_LAKE] example : natRecDepth? paritySum_term = some 1 := by kernel_rfl
-- `10 + 8 + 6 + 4 + 2`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd paritySum_term 10 = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd paritySum_term 15 = paritySum 15 := by kernel_rfl

/-! ### Three steps down, twice -/

def skip3 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => skip3 n + skip3 n + n

def skip3_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term skip3

-- [SKIPPED BY PROFILE_LAKE] example : natRecDepth? skip3_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd skip3_term 9 = skip3 9 := by kernel_rfl

/-! ### One and three steps down, not two -/

def oneAndThree : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | n + 3 => oneAndThree (n + 2) + oneAndThree n

def oneAndThree_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term oneAndThree

-- [SKIPPED BY PROFILE_LAKE] example : natRecDepth? oneAndThree_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd oneAndThree_term 12 = oneAndThree 12 := by kernel_rfl

end TermTests.NatRecDepth

end
