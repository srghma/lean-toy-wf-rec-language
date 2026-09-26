module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# What `Term.nat_rec k` means

`LeanScript.Term.nat_rec k` is the fold of a natural number that descends `k + 1` steps:
its base values are the answers at `k, …, 1, 0` — nearest first — and its branch, at
`n + k + 1`, is given `n` and the answers at `n + k, …, n + 1, n`.  `LeanScript.Eval`
evaluates it with `LeanScript.natFoldK`, which carries those `k + 1` answers as a
**window** and shifts a new one in at each step.

This file says what that fold computes, in full generality and at every depth:

* `natFoldK_base` — below the depth, the answer at `j` is the base value written for `j`;
* `natFoldK_step` — at and above it, the answer at `n + k + 1` is the branch applied to
  the window of the previous `k + 1` answers;
* `natFoldKAux_eq_ofFun` — the invariant that makes the second statement say what it
  should: the window the fold carries **is** the tuple of the previous answers, which is
  why the fold is linear and no answer is ever recomputed;
* `Term.eval_nat_rec`, `Term.eval_nat_rec_base` and `Term.eval_nat_rec_step` — the same
  three facts for the grammar's node, stated of `Term.eval`.
-/

variable {τ : TyWf}

/-! ## Reading a window -/

/-- The `i`-th answer a window holds, `0` being the newest. -/
def NatWin.get : {k : Nat} → NatWin τ k → (i : Nat) → i < k → TyWf.Den τ
  | _ + 1, w, 0, _ => w.1
  | _ + 1, w, i + 1, h => NatWin.get w.2 i (by omega)

/-- The window of a *function*: the answers at `n + k - 1, …, n`, nearest first. -/
def NatWin.ofFun (f : Nat → TyWf.Den τ) : (k : Nat) → Nat → NatWin τ k
  | 0, _ => PUnit.unit
  | k + 1, n => (f (n + k), NatWin.ofFun f k n)

/-- Two windows holding the same answers are the same window. -/
theorem NatWin.ext : {k : Nat} → {w w' : NatWin τ k} →
    (∀ i (hi : i < k), NatWin.get w i hi = NatWin.get w' i hi) → w = w'
  | 0, w, w', _ => by
      cases w; cases w'; rfl
  | k + 1, w, w', h => by
      have h0 : w.1 = w'.1 := h 0 (by omega)
      have hr : w.2 = w'.2 := NatWin.ext (fun i hi => h (i + 1) (by omega))
      show ((w.1, w.2) : TyWf.Den τ × NatWin τ k) = ((w'.1, w'.2) : TyWf.Den τ × NatWin τ k)
      rw [h0, hr]

/-- The oldest answer of a window is its last entry. -/
theorem NatWin.last_eq_get : {k : Nat} → (w : NatWin τ (k + 1)) →
    NatWin.last w = NatWin.get w k (by omega)
  | 0, _ => rfl
  | k + 1, w => NatWin.last_eq_get (k := k) w.2

@[simp] theorem NatWin.get_push_zero {k : Nat} (a : TyWf.Den τ) (w : NatWin τ (k + 1))
    (h : 0 < k + 1) : NatWin.get (NatWin.push a w) 0 h = a := by
  cases k <;> rfl

@[simp] theorem NatWin.get_push_succ : {k : Nat} → (a : TyWf.Den τ) → (w : NatWin τ (k + 1)) →
    (i : Nat) → (h : i + 1 < k + 1) → (hi : i < k + 1) →
    NatWin.get (NatWin.push a w) (i + 1) h = NatWin.get w i hi
  | 0, _, _, _, h, _ => absurd h (by omega)
  | k + 1, _, w, i, h, hi => by
      show NatWin.get (NatWin.push w.1 w.2) i (by omega) = NatWin.get w i hi
      match i with
      | 0 => exact NatWin.get_push_zero w.1 w.2 (by omega)
      | i + 1 => exact NatWin.get_push_succ (k := k) w.1 w.2 i (by omega) (by omega)

@[simp] theorem NatWin.get_ofFun (f : Nat → TyWf.Den τ) :
    {k : Nat} → (n i : Nat) → (h : i < k) →
    NatWin.get (NatWin.ofFun f k n) i h = f (n + (k - 1 - i))
  | _ + 1, _, 0, _ => rfl
  | k + 1, n, i + 1, h => by
      show NatWin.get (NatWin.ofFun f k n) i (by omega) = _
      rw [NatWin.get_ofFun f n i (by omega)]
      congr 1
      omega

/-! ## The two equations of the fold -/

/-- Reading the window at `n` is reading an answer: entry `i` is the answer at
    `n + (k - i)`. -/
theorem NatWin.get_natFoldKAux {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) :
    (j : Nat) → (n i : Nat) → (h : i < k + 1) → i + j = k →
      NatWin.get (natFoldKAux z s n) i h = natFoldK z s (n + j)
  | 0, n, i, h, hij => by
      have hik : i = k := by omega
      subst hik
      exact (NatWin.last_eq_get (natFoldKAux z s n)).symm
  | j + 1, n, i, h, hij => by
      have hstep : NatWin.get (natFoldKAux z s (n + 1)) (i + 1) (by omega) =
          NatWin.get (natFoldKAux z s n) i h := by
        show NatWin.get
          (NatWin.push (s n (natFoldKAux z s n)) (natFoldKAux z s n)) (i + 1) (by omega) = _
        rw [NatWin.get_push_succ]
      rw [← hstep, NatWin.get_natFoldKAux z s j (n + 1) (i + 1) (by omega) (by omega)]
      congr 1
      omega

/-- **The window is the history.**  At every argument, the window the fold carries is the
    tuple of the previous `k + 1` answers, nearest first — which is what makes the fold
    linear rather than exponential. -/
theorem natFoldKAux_eq_ofFun {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) (n : Nat) :
    natFoldKAux z s n = NatWin.ofFun (natFoldK z s) (k + 1) n := by
  refine NatWin.ext (fun i hi => ?_)
  rw [NatWin.get_natFoldKAux z s (k - i) n i hi (by omega), NatWin.get_ofFun]
  congr 1

/-- **The step equation.**  At `n + k + 1` — the first argument at which all `k + 1`
    predecessors exist — the answer is the branch applied to `n` and to the window of the
    previous `k + 1` answers. -/
theorem natFoldK_step {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) (n : Nat) :
    natFoldK z s (n + k + 1) = s n (NatWin.ofFun (natFoldK z s) (k + 1) n) := by
  have h0 : NatWin.get (natFoldKAux z s (n + 1)) 0 (by omega) = natFoldK z s (n + 1 + k) :=
    NatWin.get_natFoldKAux z s k (n + 1) 0 (by omega) (by omega)
  have h1 : NatWin.get (natFoldKAux z s (n + 1)) 0 (by omega) =
      s n (natFoldKAux z s n) := by
    show NatWin.get
      (NatWin.push (s n (natFoldKAux z s n)) (natFoldKAux z s n)) 0 (by omega) = _
    rw [NatWin.get_push_zero]
  rw [← natFoldKAux_eq_ofFun, show n + k + 1 = n + 1 + k from by omega, ← h0, h1]

/-- **The base equation.**  Below the depth, the answer at `j` is the base value written
    for `j`: the base values are held nearest first, so the answer at `j` is entry
    `k - j`. -/
theorem natFoldK_base {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) (j : Nat) (hj : j ≤ k) :
    natFoldK z s j = NatWin.get z (k - j) (by omega) := by
  have h := NatWin.get_natFoldKAux z s j 0 (k - j) (by omega) (by omega)
  rw [Nat.zero_add] at h
  rw [← h]
  rfl

/-! ## The node, evaluated -/

variable {Sg : Sig} {Γ : Ctx} {k : Nat} (G : GlobalEnv Sg.decls)
    (nT : Atom Γ (.prim .nat)) (base : Args Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ)
    (env : Env Γ)

/-- The value of the node — here answering with the term's own value, `Dest.ret` — **is**
    the fold: its base values are the atoms `base`, and its step runs the branch with the
    window in front of the environment. -/
theorem Term.eval_nat_rec :
    Term.eval G (Term.nat_rec k nT base branch .ret) env =
      natFoldK (Args.eval G base env)
        (fun m w => Term.eval G branch (m, Env.ofWin w env))
        (show Nat from Atom.eval nT env) :=
  rfl

/-- Below the depth, the node answers with the base value written for the argument. -/
theorem Term.eval_nat_rec_base (j : Nat) (hj : j ≤ k)
    (hn : (show Nat from Atom.eval nT env) = j) :
    Term.eval G (Term.nat_rec k nT base branch .ret) env =
      NatWin.get (Args.eval G base env) (k - j) (by omega) := by
  rw [Term.eval_nat_rec, hn, natFoldK_base _ _ j hj]

/-- At and above the depth, the node answers with its branch, given the predecessor and
    the window of the previous `k + 1` answers. -/
theorem Term.eval_nat_rec_step (n : Nat)
    (hn : (show Nat from Atom.eval nT env) = n + k + 1) :
    Term.eval G (Term.nat_rec k nT base branch .ret) env =
      Term.eval G branch
        (n, Env.ofWin
          (NatWin.ofFun
            (natFoldK (Args.eval G base env)
              (fun m w => Term.eval G branch (m, Env.ofWin w env))) (k + 1) n)
          env) := by
  rw [Term.eval_nat_rec, hn, natFoldK_step]

end LeanScript

end
