module

public import TermTests.NatRecDepthTest.Common
public import LeanScript.NatRecFacts
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! Part of the `nat_rec k` tests (see `TermTests/NatRecDepthTest/Common.lean`): `fib`
as a term at depth two — translated by `#leanscript_to_term`, with the term it is
written out beside it — and proved correct at every argument. -/

namespace TermTests.NatRecDepth

open LeanScript

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ (TyWf.prim .nat)) : Term sigAdd Γ (TyWf.prim .nat) :=
  .ap (.ap (.global .here) a) b

/-- The definition every term below computes. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-! ## `fib` at depth two

The base values are `(fib 1, fib 0) = (1, 0)`, nearest first, and the branch at `n + 2`
binds `n` at index `0`, `fib (n + 1)` at index `1` and `fib n` at index `2`. -/

/-- `fib`, as a term of the grammar: the depth-two fold. -/
def fibTerm : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term fib

-- [SKIPPED BY PROFILE_LAKE] /-- The term, written out. -/
-- [SKIPPED BY PROFILE_LAKE] example : fibTerm =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.nat_rec' 1 (.var (v♯0))
-- [SKIPPED BY PROFILE_LAKE]       (.cons (.nat_mk 1) (.cons (.nat_mk 0) .nil))
-- [SKIPPED BY PROFILE_LAKE]       (addT (.var (v♯2)) (.var (v♯1)))) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTerm 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTerm 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTerm 10 = 55 := by kernel_rfl

/-- The fold the term evaluates to, named so that the two equations can be read off it:
    its base window is `(1, 0)` and its branch adds the two answers the window holds. -/
def fibFold : Nat → Nat :=
  natFoldK (τ := TyWf.prim .nat) (k := 1) (1, 0, PUnit.unit) (fun _ w => w.2.1 + w.1)

/-- The term's value **is** that fold, at every argument. -/
theorem fibTerm_eq_fibFold (n : Nat) : runAdd fibTerm n = fibFold n := rfl

/-- The base equation, read off `natFoldK_base`: below the depth the answer is the base
    value written for the argument. -/
theorem fibFold_zero : fibFold 0 = 0 :=
  natFoldK_base (τ := TyWf.prim .nat) (k := 1) _ _ 0 (by omega)

theorem fibFold_one : fibFold 1 = 1 :=
  natFoldK_base (τ := TyWf.prim .nat) (k := 1) _ _ 1 (by omega)

/-- The step equation, read off `natFoldK_step`: at `n + 2` the branch is given the
    answers at `n` and at `n + 1`. -/
theorem fibFold_step (n : Nat) : fibFold (n + 2) = fibFold n + fibFold (n + 1) :=
  natFoldK_step (τ := TyWf.prim .nat) (k := 1) _ _ n

/-- **The term computes `fib`, at every argument** — not only at the ones checked by
    `rfl` above. -/
theorem fibTerm_eval (n : Nat) : runAdd fibTerm n = fib n := by
  rw [fibTerm_eq_fibFold]
  induction n using fib.induct with
  | case1 => exact fibFold_zero
  | case2 => exact fibFold_one
  | case3 n ih0 ih1 =>
      rw [show n.succ.succ = n + 2 from rfl, fibFold_step, ih0, ih1]
      rfl

end TermTests.NatRecDepth

end
