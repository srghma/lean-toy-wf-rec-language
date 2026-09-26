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

/-! ## The same definitions, translated

`#leanscript_to_term` reads the depth off the compiled recursion: it is the smallest
number of steps at which the history the `brecOn` hands the branch is fully read. -/

/-- `fib` as the request writes it. -/
def fibDef : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibDef n + fibDef (n + 1)

def fibDef_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibDef

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibDef_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibDef_term 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibDef_term 12 = fibDef 12 := by kernel_rfl

/-! ## What is still refused

`fibFast` calls itself at `n / 2`.  That is not a descent by a fixed number of steps, so
no depth makes it a fold of this kind; Lean compiles it by well-founded recursion, which
the translation refuses. -/

def fibFastAux (n : Nat) : Nat × Nat :=
  if h : n = 0 then
    (0, 1)
  else
    have : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let (a, b) := fibFastAux (n / 2)
    let c := a * (2 * b - a)
    let d := a * a + b * b
    if n % 2 == 0 then
      (c, d)
    else
      (d, c + d)
termination_by n

/-- error: `#leanscript_to_term`: well-founded recursion (WellFounded.Nat.fix) is not supported — the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive -/
#guard_msgs (error) in
example : Term sigAdd [] (TyWf.prim .nat ⇒ tyWfOf (Nat × Nat)) :=
  #leanscript_to_term fibFastAux

end TermTests.NatRecDepth

end
