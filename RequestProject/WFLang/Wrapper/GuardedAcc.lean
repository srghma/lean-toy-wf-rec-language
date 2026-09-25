import RequestProject.WFLang.Wrapper.Guarded

/-!
# Proposal 3 — `GuardedAcc`: guarded semantics + recursion on a `Prop`-valued `Acc`

Same certificate as proposal 1 (`Guarded.Dec`, a `Prop`), but the evaluator is
written directly with the recursor of the ordinary `Prop`-valued accessibility
predicate `Acc` (no `AccT`!).  The `Acc` proof is obtained from `WellFounded`
and is erased by code generation (Lean compiles `Acc.rec` via `Acc.recC`, whose
accessibility argument is irrelevant), so it cannot act as fuel at runtime.
-/

namespace WFLang.GuardedAcc

open Guarded

/-- Programs are the same as in proposal 1. -/
def Term (s : Sig) : Type := Guarded.Term s

/-- Evaluation by `Acc.rec` on the (erased) proof `h : Acc R x`. -/
def Term.runAcc {s : Sig} (t : Term s) (x : Env s.args) (h : Acc t.R x) : s.ret.denote :=
  Acc.rec (motive := fun _ _ => s.ret.denote)
    (fun x _ ih => (sem t.R x ih x t.body).2 (t.dec x ih)) h

/-- The evaluator. -/
def Term.run {s : Sig} (t : Term s) (x : Env s.args) : s.ret.denote :=
  t.runAcc x (t.wf.apply x)

/-- Curried evaluator. -/
def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv t.run

theorem Term.runAcc_eq {s : Sig} (t : Term s) (x : Env s.args) (h : Acc t.R x) :
    t.runAcc x h = (sem t.R x (fun y hy => t.runAcc y (h.inv hy)) x t.body).2 (t.dec x _) := by
  cases h
  rfl

theorem Term.run_unfold {s : Sig} (t : Term s) (x : Env s.args) :
    t.run x = (sem t.R x (fun y _ => t.run y) x t.body).2 (t.dec x _) := by
  unfold Term.run
  rw [Term.runAcc_eq]

/-- **Soundness (1):** the evaluator satisfies the defining equation. -/
theorem Term.run_isFix {s : Sig} (t : Term s) : IsFix t.body t.run := by
  intro x
  rw [Term.run_unfold]
  exact sem_eq t.R x _ t.run (fun _ _ => rfl) x t.body _

/-- **Soundness (2):** uniqueness of solutions of the defining equation. -/
theorem Term.isFix_unique {s : Sig} (t : Term s) (f : Env s.args → s.ret.denote)
    (hf : IsFix t.body f) : ∀ x, t.run x = f x := by
  intro x
  induction x using t.wf.induction with
  | _ x IH =>
    rw [Term.run_unfold, hf x,
      ← sem_eq t.R x (fun y _ => t.run y) f (fun y h => IH y h) x t.body (t.dec x _)]

/-- Agreement with any Lean function satisfying the same recursive equation. -/
theorem Term.eval_eq {s : Sig} (t : Term s) (f : FnType s.args s.ret)
    (hf : IsFix t.body (uncurryEnv f)) : t.eval = f :=
  curryEnv_eq_of_isFix_unique t.isFix_unique f hf

end WFLang.GuardedAcc
