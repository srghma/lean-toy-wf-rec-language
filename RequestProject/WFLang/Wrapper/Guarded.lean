import RequestProject.WFLang.Wrapper.Expr
import RequestProject.WFLang.Common.WFBox

/-!
# Proposal 1 — `Guarded`: proof-carrying ("delayed") evaluation

The well-foundedness certificate is an ordinary `Prop`:

* a relation `R` on argument tuples with `WellFounded R`, and
* `Dec R body : Prop`, which says that *every recursive call that is actually
  reached* goes to an `R`-smaller argument tuple.

"Actually reached" is made precise by the dependent semantics `sem`: for every
expression it returns a pair `⟨G, v⟩` where `G : Prop` is the *guard* (the
condition under which the expression may be evaluated with the partial
recursion hypothesis `ih : ∀ y, R y x → β`) and `v : G → τ` is the delayed value.
Because `G` is a `Prop`, code generation erases it and `v` becomes a closure
— the evaluator is a staged ("delayed") interpreter, with no fuel.

The top-level evaluator `Term.run` is defined by `termination_by` on the
user-supplied well-founded relation.
-/

namespace WFLang.Guarded

variable {s : Sig} (R : Env s.args → Env s.args → Prop) (x : Env s.args)
  (ih : (y : Env s.args) → R y x → s.ret.denote)

mutual
/-- Guard/value semantics of an expression under the partial recursion
hypothesis `ih` (recursive calls must be `R`-below `x`). -/
def sem {Γ : List Ty} (env : Env Γ) : {t : Ty} → Expr s Γ t → (G : Prop) ×' (G → t.denote)
  | _, .var v => ⟨True, fun _ => v.get env⟩
  | _, .lit _ v => ⟨True, fun _ => v⟩
  | _, .bin op a b =>
      let A := sem env a
      let B := sem env b
      ⟨A.1 ∧ B.1, fun h => op.eval (A.2 h.1) (B.2 h.2)⟩
  | _, .not a =>
      let A := sem env a
      ⟨A.1, fun h => !(A.2 h)⟩
  | _, .ite c a b =>
      let C := sem env c
      let A := sem env a
      let B := sem env b
      ⟨C.1 ∧ ∀ hc : C.1, (C.2 hc = true → A.1) ∧ (C.2 hc = false → B.1),
       fun h =>
        match hb : C.2 h.1 with
        | true => A.2 ((h.2 h.1).1 hb)
        | false => B.2 ((h.2 h.1).2 hb)⟩
  | _, .call args =>
      let As := sems env args
      ⟨As.1 ∧ ∀ h : As.1, R (As.2 h) x, fun h => ih (As.2 h.1) (h.2 h.1)⟩
/-- Guard/value semantics of argument lists. -/
def sems {Γ : List Ty} (env : Env Γ) : {ts : List Ty} → Exprs s Γ ts → (G : Prop) ×' (G → Env ts)
  | _, .nil => ⟨True, fun _ => ()⟩
  | _, .cons a as =>
      let A := sem env a
      let As := sems env as
      ⟨A.1 ∧ As.1, fun h => (A.2 h.1, As.2 h.2)⟩
end

/-- The well-foundedness certificate (a `Prop`): for every argument tuple `x`
and every partial recursion hypothesis below `x`, the guard of the body holds. -/
def Dec (body : Body s) : Prop :=
  ∀ x (ih : (y : Env s.args) → R y x → s.ret.denote), (sem R x ih x body).1

end WFLang.Guarded

namespace WFLang.Guarded

/-- A closed, well-founded program of signature `s`: body + `Prop`-level
termination certificate. -/
structure Term (s : Sig) where
  body : Body s
  R : Env s.args → Env s.args → Prop
  wf : WellFounded R
  dec : Dec R body

/-- The evaluator: no fuel, no measure; recursion justified by `t.wf`. -/
def Term.run {s : Sig} (t : Term s) (x : Env s.args) : s.ret.denote :=
  (sem t.R x (fun y _ => t.run y) x t.body).2 (t.dec x _)
termination_by (WFBox.mk x : WFBox t.R t.wf)
decreasing_by all_goals exact ‹_›

/-- Curried evaluator: `Term.eval gcd_term m n`. -/
def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv t.run

/-! ## Soundness -/

section sound
variable {s : Sig} (R : Env s.args → Env s.args → Prop) (x : Env s.args)
  (ih : (y : Env s.args) → R y x → s.ret.denote) (o : Env s.args → s.ret.denote)

mutual
/-- The delayed value agrees with the reference semantics whenever the
partial hypothesis agrees with the oracle. -/
theorem sem_eq (hio : ∀ y h, ih y h = o y) {Γ : List Ty} (env : Env Γ) : ∀ {t : Ty} (e : Expr s Γ t) (g : (sem R x ih env e).1),
    (sem R x ih env e).2 g = e.evalWith o env
  | _, .var _, _ => rfl
  | _, .lit _ _, _ => rfl
  | _, .bin op a b, g => by
      simp only [sem, Expr.evalWith]
      rw [sem_eq hio env a, sem_eq hio env b]
  | _, .not a, g => by
      simp only [sem, Expr.evalWith]
      rw [sem_eq hio env a]
  | _, .ite c a b, g => by
      simp only [sem, Expr.evalWith]
      split
      · rename_i hb
        rw [sem_eq hio env a, ← sem_eq hio env c g.1, hb]; rfl
      · rename_i hb
        rw [sem_eq hio env b, ← sem_eq hio env c g.1, hb]; rfl
  | _, .call args, g => by
      simp only [sem, Expr.evalWith]
      rw [hio, sems_eq hio env args]
theorem sems_eq (hio : ∀ y h, ih y h = o y) {Γ : List Ty} (env : Env Γ) : ∀ {ts : List Ty} (e : Exprs s Γ ts) (g : (sems R x ih env e).1),
    (sems R x ih env e).2 g = e.evalWith o env
  | _, .nil, _ => rfl
  | _, .cons a as, g => by
      simp only [sems, Exprs.evalWith]
      rw [sem_eq hio env a, sems_eq hio env as]
end

end sound

/-- **Soundness (1):** the evaluator satisfies the defining equation. -/
theorem Term.run_isFix {s : Sig} (t : Term s) : IsFix t.body t.run := by
  intro x
  unfold Term.run
  exact sem_eq t.R x _ t.run (fun _ _ => rfl) x t.body _

/-- **Soundness (2):** the defining equation has at most one solution, so the
evaluator computes *the* function described by the program. -/
theorem Term.isFix_unique {s : Sig} (t : Term s) (f : Env s.args → s.ret.denote)
    (hf : IsFix t.body f) : ∀ x, t.run x = f x := by
  intro x
  induction x using t.wf.induction with
  | _ x IH =>
    rw [t.run_isFix x, hf x,
      ← sem_eq t.R x (fun y _ => t.run y) t.run (fun _ _ => rfl) x t.body (t.dec x _),
      ← sem_eq t.R x (fun y _ => t.run y) f (fun y h => IH y h) x t.body (t.dec x _)]

/-- Agreement with any Lean function satisfying the same recursive equation. -/
theorem Term.eval_eq {s : Sig} (t : Term s) (f : FnType s.args s.ret)
    (hf : IsFix t.body (uncurryEnv f)) : t.eval = f :=
  curryEnv_eq_of_isFix_unique t.isFix_unique f hf

end WFLang.Guarded
