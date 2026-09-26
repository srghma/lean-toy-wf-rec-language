module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `fib` in the grammar as it stands: the sliding-window fold

`proposals/FibProposals.md` proposes five ways to give the language a recursion that descends more
than one step at a time.  This file *runs* the first of them, the one that needs no new
constructor (the grammar has since gained the depth-indexed node as well): a recursion that reads its own value at `n` and at `n + 1` is a fold whose
value is the **window** of the last two answers, a record of two `nat`s, and the answer
is the first field of that window.

Everything here is a term of the grammar exactly as it is today — `Term.nat_rec`,
`Term.record_mk`, `Term.record_casesOn` — produced by `#leanscript_to_term` from the Lean
program that computes the window, with the terms written out beside them in `example`s;
and `fib_term_eval` proves that the term's
value **is** `fib n`, at every `n`, rather than only at the arguments a test would try.
-/

namespace TermTests.FibWindow

open LeanScript

/-- The definition to be expressed: it reads its own value at `n` and at `n + 1`.  Since
    this file was written the grammar has gained the depth-indexed fold
    `Term.nat_rec k`, so `#leanscript_to_term` translates it directly
    (`TermTests/NatRecDepthTest/`); what is written here is the *other* way of saying
    it, as a one-step fold whose value is a window, and it still typechecks and still
    computes `fib`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`: the language's arithmetic
    is external, so the step of the fold calls it. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- The window: the pair `(fib n, fib (n + 1))`. -/
abbrev winSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/-- The type of the window. -/
abbrev Win : TyWf := TyWf.record winSchema

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ (TyWf.prim .nat)) : Term sigAdd Γ (TyWf.prim .nat) :=
  .ap (.ap (.global .here) a) b

/-- The window as a Lean program: `(fib n, fib (n + 1))`, one step at a time
    (`@[inline]`, so that `fibFromWin` below translates to the fold itself). -/
@[inline] def fibWin : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibWin n
    (b, a + b)

/-- `fib`, read off the window. -/
def fibFromWin (n : Nat) : Nat := (fibWin n).1

-- kept in direct style (not normalized, `LeanScript.ToTerm.Normalize`), so that
-- `#leanscript_fold_bases` reads its base values as terms (a `Spine`)
set_option leanscript.toTerm.normalize false in
/-- The fold itself: the window at the argument,
    `.lam (.nat_rec' 0 (.var (v♯0)) (.cons seed .nil) step)`. -/
def window : Term sigAdd [] (TyWf.prim .nat ⇒ Win) := #leanscript_to_term fibWin

/-- The context the fold is written in: the argument. -/
abbrev WinCtx : Ctx := [TyWf.prim .nat]

/-- The window at `0`: `(fib 0, fib 1) = (0, 1)`.  These are the base branches of the
    Lean definition, which read nothing of the recursion. -/
def seed : Term sigAdd WinCtx Win :=
  match (#leanscript_fold_bases window : Spine sigAdd WinCtx (natRecCtx Win 1 [])) with
  | .cons z .nil => z

-- [SKIPPED BY PROFILE_LAKE] example : seed = .record_mk winSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil)) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The step of the fold: it binds the predecessor `k` (index `0`) and the window at `k`
    (index `1`), takes the window apart — so inside, index `0` is `fib k` and index `1`
    is `fib (k + 1)` — and answers with the window at `k + 1`,
    `(fib (k + 1), fib k + fib (k + 1))`.

    The recursion that the branch of the Lean definition writes at `n` and at `n + 1` is
    read off the window: nothing is called, so the term is still terminating by
    construction. -/
def step : Term sigAdd (TyWf.prim .nat :: Win :: WinCtx) Win :=
  #leanscript_fold_branch window

-- [SKIPPED BY PROFILE_LAKE] example : step =
-- [SKIPPED BY PROFILE_LAKE]     .record_casesOn' (.var (v♯1))
-- [SKIPPED BY PROFILE_LAKE]       (.record_mk winSchema
-- [SKIPPED BY PROFILE_LAKE]         (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil))) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : window = .lam (.nat_rec' 0 (.var (v♯0)) (.cons seed .nil) step) := by kernel_rfl

/-- `fib`, as a term of the language: the first field of the window.  The translation
    inlines the fold, so the term takes apart the fold itself rather than applying
    `window`. -/
def fib_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibFromWin

-- [SKIPPED BY PROFILE_LAKE] example : fib_term =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.record_casesOn' (fs := winSchema) (.nat_rec' 0 (.var (v♯0)) (.cons seed .nil) step)
-- [SKIPPED BY PROFILE_LAKE]       (.var (v♯0))) := by kernel_rfl

/-! ## What it computes

First a few values, checked by the kernel, and then the general statement. -/

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 1 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 2 = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 10 = 55 := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 12 = fib 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fib_term 15 = 610 := by kernel_rfl

/-- The window term's value at `n` is the pair `(fib n, fib (n + 1))` — at **every**
    argument, not only at the ones checked above. -/
theorem window_eval (n : Nat) :
    runAdd window n = (fib n, fib (n + 1), PUnit.unit) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : runAdd window (n + 1) =
          ((runAdd window n).2.1,
            (runAdd window n).1 + (runAdd window n).2.1, PUnit.unit) := by
        -- `kernel_rfl`, not `rfl`: the elaborator's own check of this equation is slow
        -- (the extern call goes through the case splits of `Extern.eval`);
        -- the kernel checks it quickly (see `LeanScript/KernelRfl.lean`)
        kernel_rfl
      rw [hstep, ih]
      show ((fib (n + 1), fib n + fib (n + 1), PUnit.unit) : Nat × Nat × PUnit) =
        (fib (n + 1), fib (n + 2), PUnit.unit)
      rw [show fib (n + 2) = fib n + fib (n + 1) from rfl]

/-- `fib_term` computes `fib`, at every argument. -/
theorem fib_term_eval (n : Nat) : runAdd fib_term n = fib n := by
  have h : runAdd fib_term n = (runAdd window n).1 := rfl
  rw [h, window_eval]

/-! ## The semantics a two-step fold would have

`proposals/FibProposals.md`'s second proposal adds a constructor `Term.nat_rec2` whose branch is
given the value of the recursion at the **two** predecessors.  Its clause in the
evaluator would be the fold below, and the point of writing it here is that it is
*linear*: the fold carries the window internally, so a branch that reads both
predecessors still costs one step per number, which a naive double recursion would not.

`natFold2_succ_succ` is the equation such a constructor promises, and it is proved, so
the design is checked rather than asserted. -/

/-- The window of a two-step fold: `(f n, f (n + 1))`. -/
def natFold2Aux {α : Type} (z0 z1 : α) (s : Nat → α → α → α) : Nat → α × α
  | 0 => (z0, z1)
  | n + 1 => let w := natFold2Aux z0 z1 s n; (w.2, s n w.1 w.2)

/-- `Nat.rec` that descends two steps: the value at `n + 2` is the branch applied to the
    values at `n` and at `n + 1`. -/
def natFold2 {α : Type} (z0 z1 : α) (s : Nat → α → α → α) (n : Nat) : α :=
  (natFold2Aux z0 z1 s n).1

@[simp] theorem natFold2_zero {α : Type} (z0 z1 : α) (s : Nat → α → α → α) :
    natFold2 z0 z1 s 0 = z0 := rfl

@[simp] theorem natFold2_one {α : Type} (z0 z1 : α) (s : Nat → α → α → α) :
    natFold2 z0 z1 s 1 = z1 := rfl

/-- The equation the proposed constructor promises: the branch at `n + 2` is given the
    value at `n` and the value at `n + 1`. -/
theorem natFold2_succ_succ {α : Type} (z0 z1 : α) (s : Nat → α → α → α) (n : Nat) :
    natFold2 z0 z1 s (n + 2) = s n (natFold2 z0 z1 s n) (natFold2 z0 z1 s (n + 1)) := rfl

/-- And it does compute `fib`. -/
theorem natFold2_fib (n : Nat) : natFold2 0 1 (fun _ a b => a + b) n = fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
      rw [natFold2_succ_succ, ih1, ih2]
      rfl

end TermTests.FibWindow
