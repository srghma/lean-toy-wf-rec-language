module

public import LeanScript.NatRecFacts
public import TermTests.FibWindowTest
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# One fold for every depth: the node, at depth one, two and three

`proposals/FibProposals.md` asked whether **one** constructor can serve `nat_rec`, `nat_rec2`,
`nat_rec3`, … at once, or whether a fixed, finite family is the better answer.  The
answer taken is the first one, and `LeanScript.Term.nat_rec` is now that constructor:

```lean
| nat_rec : ∀ {Γ τ} (k : Nat := 0), Term Sg Γ (.prim .nat) →
    Spine Sg Γ (natRecCtx τ (k + 1) []) →
    Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ →
    Term Sg Γ τ
```

Its meaning (`LeanScript.natFoldK`) and the two equations it promises are proved in
`LeanScript.NatRecFacts`, in full generality and at every depth.  What this file checks
is that the generality costs nothing at a *use site*:

1. **Every depth is the one fold.**  The depth-one instance is the old one-step fold
   `LeanScript.natFold` (`natFoldK_eq_natFold`), the depth-two instance is the two-step
   fold of `TermTests/FibWindowTest.lean` (`natFoldK_eq_natFold2`) and computes `fib`, and
   a genuine depth-three recursion — the tribonacci numbers — runs on it.

2. **The types reduce to what one would have written by hand.**  The branch's context at
   a literal depth is the readable `τ :: τ :: Γ` / `τ :: τ :: τ :: Γ` (`natRecCtx_two`,
   `natRecCtx_three`), depth one is the old `nat_rec`'s own type definitionally, the base
   values are an ordinary `Spine`, and the window the evaluator carries **is** the
   environment of that block of the context.
-/

namespace TermTests.NatRecK

open LeanScript

/-- The type the folds below run at: its values are Lean's `Nat`. -/
abbrev natT : TyWf := TyWf.prim .nat

-- [SKIPPED BY PROFILE_LAKE] example : TyWf.Den natT = Nat := by kernel_rfl

/-! ## Every depth at once: the fold at `k = 0`, `k = 1`, `k = 2` -/

/-- Depth one **is** `natFold`: the old one-step fold is the `k = 0` instance. -/
theorem natFoldK_eq_natFold (z : Nat) (s : Nat → Nat → Nat) (n : Nat) :
    natFoldK (τ := natT) (k := 0) (z, PUnit.unit) (fun n w => s n w.1) n = natFold z s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show s n (natFoldK (τ := natT) (k := 0) (z, PUnit.unit) (fun n w => s n w.1) n) =
        s n (natFold z s n)
      rw [ih]

/-- Depth two **is** the two-step fold: the window is nearest first, so the base tuple is
    `(f 1, f 0)` and the branch reads the value at `n + 1` as `w.1` and the value at `n`
    as `w.2.1`. -/
theorem natFoldK_eq_natFold2 (z0 z1 : Nat) (s : Nat → Nat → Nat → Nat) (n : Nat) :
    natFoldK (τ := natT) (k := 1) (z1, z0, PUnit.unit) (fun n w => s n w.2.1 w.1) n =
      TermTests.FibWindow.natFold2 z0 z1 s n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      match n with
      | 0 => rfl
      | 1 => rfl
      | n + 2 =>
          rw [TermTests.FibWindow.natFold2_succ_succ, ← ih n (by omega), ← ih (n + 1) (by omega)]
          exact natFoldK_step (τ := natT) (k := 1) _ _ n

/-- Depth two computes `fib`, at every argument. -/
theorem natFoldK_fib (n : Nat) :
    natFoldK (τ := natT) (k := 1) (1, 0, PUnit.unit) (fun _ w => w.1 + w.2.1) n =
      TermTests.FibWindow.fib n := by
  rw [show (fun (_ : Nat) (w : NatWin natT 2) => w.1 + w.2.1) =
      (fun (n : Nat) (w : NatWin natT 2) =>
        (fun (_ : Nat) (a b : Nat) => a + b) n w.2.1 w.1) from
      funext fun _ => funext fun w => Nat.add_comm _ _,
    natFoldK_eq_natFold2, TermTests.FibWindow.natFold2_fib]

/-- A depth-**three** recursion, to show the generality is real: the tribonacci
    numbers. -/
def trib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => trib n + trib (n + 1) + trib (n + 2)

/-- The depth-three fold for `trib`: its base tuple is `(trib 2, trib 1, trib 0)` and its
    branch adds the three values the window holds. -/
def tribFold (n : Nat) : Nat :=
  natFoldK (τ := natT) (k := 2) (1, 1, 0, PUnit.unit) (fun _ w => w.2.2.1 + w.2.1 + w.1) n

-- [SKIPPED BY PROFILE_LAKE] example : tribFold 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tribFold 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tribFold 2 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tribFold 12 = 504 := by kernel_rfl

/-- The step equation of the depth-three fold, read off `natFoldK_step`: the branch is
    given the three previous answers. -/
theorem tribFold_step (n : Nat) :
    tribFold (n + 3) = tribFold n + tribFold (n + 1) + tribFold (n + 2) :=
  natFoldK_step (τ := natT) (k := 2) (1, 1, 0, PUnit.unit)
    (fun _ w => w.2.2.1 + w.2.1 + w.1) n

/-- And it is `trib`, at every argument — by the two equations, at `k = 2`. -/
theorem tribFold_eq (n : Nat) : tribFold n = trib n := by
  induction n using trib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 n ih0 ih1 ih2 =>
      rw [show n.succ.succ.succ = n + 3 from rfl, tribFold_step, ih0, ih1, ih2]
      rfl

/-! ## The types the node asks for

The worry about a depth-indexed node was that its base values and its branch are typed by
*computed* descriptions, so a written-out term would be full of casts and length proofs.
It is not so, and the checks below are the reason. -/

section Types

variable {Sg : Sig} {Γ : Ctx} {τ : TyWf}

-- [SKIPPED BY PROFILE_LAKE] /-- Depth one: the context of the branch is exactly the one-step fold's, so the node
-- [SKIPPED BY PROFILE_LAKE]     subsumes it **definitionally** — no term had to be rewritten for the depth. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term Sg (TyWf.prim .nat :: natRecCtx τ 1 Γ) τ =
-- [SKIPPED BY PROFILE_LAKE]     Term Sg (TyWf.prim .nat :: τ :: Γ) τ := by kernel_rfl

/-- Depth two: the context a hand-written two-step fold would be written in. -/
theorem natRecCtx_two : natRecCtx τ 2 Γ = τ :: τ :: Γ := rfl

/-- Depth three, and so on: the de Bruijn indices of the branch stay readable. -/
theorem natRecCtx_three : natRecCtx τ 3 Γ = τ :: τ :: τ :: Γ := rfl

/-- The base values are a `Spine` written out as usual — nothing to prove at its type. -/
def baseSpine_two (a b : Term Sg Γ τ) : Spine Sg Γ (natRecCtx τ 2 []) :=
  .cons a (.cons b .nil)

/-- The window the evaluator carries **is** the environment of that block of the
    context. -/
theorem win_eq_denList : NatWin τ 3 = TyWf.DenList (natRecCtx τ 3 []) := rfl

/-- And the environment of the branch is the window in front of the environment of the
    ambient context, with no cast and no length proof. -/
example (w : NatWin τ 2) (env : Env Γ) : Env (natRecCtx τ 2 Γ) := Env.ofWin w env

end Types

end TermTests.NatRecK

end
