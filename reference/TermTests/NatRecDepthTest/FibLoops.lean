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

/-! ### `fibLoopTR` and `fibTR`: the accumulator-passing loop

The recursion descends one step, but its accumulators change on the way down, so the
value of the fold is the **function** of the two accumulators.  The node folds at any
type, function types included, so this is the depth-zero instance. -/

@[inline] def fibLoopTR : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fibLoopTR n b (a + b)

def fibLoopTR_term :
    Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibLoopTR

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoopTR_term 0 0 1 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoopTR_term 1 0 1 = 1 := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `fibTR n = fibLoopTR n 0 1`, which is the loop applied to the two starting
-- [SKIPPED BY PROFILE_LAKE]     accumulators.  The value of this fold is a *function*, so the kernel has a closure to
-- [SKIPPED BY PROFILE_LAKE]     reduce at every step and the checks are kept small. -/
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoopTR_term 3 0 1 = 2 := by kernel_rfl

/-- And the wrapper itself: `fibLoopTR` is marked `@[inline]`, so the call is built in
    place and `fibTR` translates as it is written. -/
def fibTR (n : Nat) : Nat := fibLoopTR n 0 1

def fibTR_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibTR

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTR_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTR_term 1 = 1 := by kernel_rfl

/-! ### `fibPair` and `fib2`: the fold at a pair

A `Nat × Nat` is a record of two fields here, so the fold runs at that record and the
answer is its first field. -/

def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibPair n
    (b, a + b)

def fibPair_term : Term sigAdd [] (TyWf.prim .nat ⇒ tyWfOf (Nat × Nat)) :=
  #leanscript_to_term fibPair

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibPair_term 0 = ((0, 1, PUnit.unit) : Nat × Nat × PUnit) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibPair_term 6 = ((8, 13, PUnit.unit) : Nat × Nat × PUnit) := by kernel_rfl

/-! ### `fibLoop`: the `for` loop

`do` in the identity monad is not an effect, and a `for` over `[:n]` is the fold of `n`
whose value is the state of the loop — the depth-zero node again, at the record of the
two mutable variables. -/

def fibLoop (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let next := a + b
    a := b
    b := next
  return a

def fibLoop_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibLoop

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoop_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoop_term 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibLoop_term 4 = 3 := by kernel_rfl

end TermTests.NatRecDepth

end
