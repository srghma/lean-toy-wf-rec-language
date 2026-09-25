import RequestProject.WFLang.Wrapper.FreeCall
import RequestProject.WFLang.Wrapper.Guarded

/-!
# Proposal 4 — `Checked`: extensional certificate + runtime-decided relation

The certificate is the extensional ("contraction") property, an ordinary
`Prop`: the body at `x` only depends on the recursive calls at `R`-smaller
arguments.  Since that certificate says nothing about *which* calls are made,
the evaluator has to **decide `R y x` at runtime** before every recursive call
(falling back to a default value otherwise).  This needs `DecidableRel R`, and
the generated code evaluates the relation (typically: computes and compares the
measure) at every call — a fuel-like runtime artefact, included for contrast.
-/

namespace WFLang.Checked

/-- Extensional well-foundedness certificate. -/
def Contracting {s : Sig} (R : Env s.args → Env s.args → Prop) (body : Body s) : Prop :=
  ∀ x (o₁ o₂ : Env s.args → s.ret.denote), (∀ y, R y x → o₁ y = o₂ y) →
    body.evalWith o₁ x = body.evalWith o₂ x

/-- A closed program with a decidable well-founded relation. -/
structure Term (s : Sig) where
  body : Body s
  R : Env s.args → Env s.args → Prop
  wf : WellFounded R
  decR : ∀ a b, Decidable (R a b)
  contr : Contracting R body

/-- The evaluator: every recursive call first *checks* `R y x` at runtime. -/
def Term.run {s : Sig} (t : Term s) (x : Env s.args) : s.ret.denote :=
  t.body.evalWith
    (fun y => match t.decR y x with
      | .isTrue _ => t.run y
      | .isFalse _ => s.ret.default) x
termination_by (WFBox.mk x : WFBox t.R t.wf)
decreasing_by all_goals exact ‹_›

/-- Curried evaluator. -/
def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv t.run

/-- **Soundness (1):** the evaluator satisfies the defining equation. -/
theorem Term.run_isFix {s : Sig} (t : Term s) : IsFix t.body t.run := by
  intro x
  rw [Term.run]
  apply t.contr
  intro y hy
  split
  · rfl
  · contradiction

/-- **Soundness (2):** uniqueness of solutions of the defining equation. -/
theorem Term.isFix_unique {s : Sig} (t : Term s) (f : Env s.args → s.ret.denote)
    (hf : IsFix t.body f) : ∀ x, t.run x = f x := by
  intro x
  induction x using t.wf.induction with
  | _ x IH =>
    rw [t.run_isFix x, hf x]
    exact t.contr x _ _ IH

/-- Agreement with any Lean function satisfying the same recursive equation. -/
theorem Term.eval_eq {s : Sig} (t : Term s) (f : FnType s.args s.ret)
    (hf : IsFix t.body (uncurryEnv f)) : t.eval = f :=
  curryEnv_eq_of_isFix_unique t.isFix_unique f hf

/-! The call-tree certificate of proposal 2 implies the extensional one. -/

theorem runWith_congr {A B τ : Type} (P : A → Prop) (o₁ o₂ : A → B)
    (h : ∀ a, P a → o₁ a = o₂ a) (c : FreeCall.Comp A B τ) (hc : c.AllCalls P) :
    c.runWith o₁ = c.runWith o₂ := by
  induction c with
  | pure v => rfl
  | call a k IH =>
    simp only [FreeCall.Comp.runWith]
    rw [h a hc.1]
    exact IH _ (hc.2 _)

theorem contracting_of_allCalls {s : Sig} {R : Env s.args → Env s.args → Prop} {body : Body s}
    (h : FreeCall.Dec R body) : Contracting R body := by
  intro x o₁ o₂ ho
  rw [← FreeCall.evalC_runWith, ← FreeCall.evalC_runWith]
  exact runWith_congr _ _ _ ho _ (h x)

end WFLang.Checked
