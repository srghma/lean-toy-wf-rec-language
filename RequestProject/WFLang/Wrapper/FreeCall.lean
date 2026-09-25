import RequestProject.WFLang.Wrapper.Expr

/-!
# Proposal 2 — `FreeCall`: call trees (a free monad) + `WellFounded.fix`

The body is first interpreted, *without* performing any recursive call, into a
call tree `Comp` (the free monad of the "recursive call" effect):

* `Comp.pure v`   — finished with value `v`;
* `Comp.call y k` — "please call the function on `y`, and continue with `k`".

The certificate is an ordinary `Prop`: every `call y` node that can occur in the
tree for input `x` satisfies `R y x` (`Comp.AllCalls`), with `WellFounded R`.

The driver interprets the tree, answering `call y k` by a recursive call which
is justified by the (erased) proof `R y x`.  Recursion is `WellFounded.fix`,
which Lean compiles to a native recursive function (`WellFounded.fixC`).
-/

namespace WFLang.FreeCall

/-- Call trees: the free monad over the "recursive call" effect, with request
type `A` and answer type `B`. -/
inductive Comp (A B : Type) (τ : Type) : Type where
  | pure : τ → Comp A B τ
  | call : A → (B → Comp A B τ) → Comp A B τ

namespace Comp
variable {A B : Type}

/-- Monadic bind of call trees. -/
def bind {σ τ : Type} : Comp A B σ → (σ → Comp A B τ) → Comp A B τ
  | .pure v, f => f v
  | .call a k, f => .call a (fun b => (k b).bind f)

/-- Every request in the tree satisfies `P`.  (A `Prop`, defined by recursion.) -/
def AllCalls {τ : Type} (P : A → Prop) : Comp A B τ → Prop
  | .pure _ => True
  | .call a k => P a ∧ ∀ b, (k b).AllCalls P

/-- Run a call tree against a total oracle (reference semantics). -/
def runWith {τ : Type} (o : A → B) : Comp A B τ → τ
  | .pure v => v
  | .call a k => (k (o a)).runWith o

theorem runWith_bind {σ τ : Type} (o : A → B) (c : Comp A B σ) (f : σ → Comp A B τ) :
    (c.bind f).runWith o = (f (c.runWith o)).runWith o := by
  induction c with
  | pure v => rfl
  | call a k ih => exact ih (o a)

theorem allCalls_bind {σ τ : Type} (P : A → Prop) (c : Comp A B σ) (f : σ → Comp A B τ)
    (hc : c.AllCalls P) (hf : ∀ v, (f v).AllCalls P) : (c.bind f).AllCalls P := by
  induction c with
  | pure v => exact hf v
  | call a k ih => exact ⟨hc.1, fun b => ih b (hc.2 b)⟩

/-- Interpret a call tree using a *partial* oracle defined only on `P`-requests;
the proof of `AllCalls` is erased at runtime. -/
def interp {τ : Type} (P : A → Prop) (ih : (a : A) → P a → B) :
    (c : Comp A B τ) → c.AllCalls P → τ
  | .pure v, _ => v
  | .call a k, h => interp P ih (k (ih a h.1)) (h.2 _)

theorem interp_eq {τ : Type} (P : A → Prop) (ih : (a : A) → P a → B) (o : A → B)
    (hio : ∀ a h, ih a h = o a) (c : Comp A B τ) (h : c.AllCalls P) :
    interp P ih c h = c.runWith o := by
  induction c with
  | pure v => rfl
  | call a k IH =>
    simp only [interp, runWith]
    rw [IH, hio]

end Comp

section
variable {s : Sig}

/-- Shorthand for call trees of signature `s`. -/
abbrev C (s : Sig) (τ : Type) := Comp (Env s.args) s.ret.denote τ

mutual
/-- Interpret an expression into a call tree (no recursion performed). -/
def evalC {Γ : List Ty} (env : Env Γ) : {t : Ty} → Expr s Γ t → C s t.denote
  | _, .var v => .pure (v.get env)
  | _, .lit _ v => .pure v
  | _, .bin op a b =>
      (evalC env a).bind fun va => (evalC env b).bind fun vb => .pure (op.eval va vb)
  | _, .not a => (evalC env a).bind fun va => .pure (!va)
  | _, .ite c a b =>
      (evalC env c).bind fun vc => if vc then evalC env a else evalC env b
  | _, .call args => (evalsC env args).bind fun vs => .call vs .pure
/-- Interpret an argument list into a call tree. -/
def evalsC {Γ : List Ty} (env : Env Γ) : {ts : List Ty} → Exprs s Γ ts → C s (Env ts)
  | _, .nil => .pure ()
  | _, .cons a as =>
      (evalC env a).bind fun va => (evalsC env as).bind fun vs => .pure (va, vs)
end

mutual
theorem evalC_runWith (o : Env s.args → s.ret.denote) {Γ : List Ty} (env : Env Γ) :
    ∀ {t : Ty} (e : Expr s Γ t), (evalC env e).runWith o = e.evalWith o env
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, .bin op a b => by
      simp only [evalC, Comp.runWith_bind, Expr.evalWith, evalC_runWith o env a,
        evalC_runWith o env b]
      rfl
  | _, .not a => by
      simp only [evalC, Comp.runWith_bind, Expr.evalWith, evalC_runWith o env a]
      rfl
  | _, .ite c a b => by
      simp only [evalC, Comp.runWith_bind, Expr.evalWith, evalC_runWith o env c]
      split <;> simp only [evalC_runWith o env a, evalC_runWith o env b]
  | _, .call args => by
      simp only [evalC, Comp.runWith_bind, Expr.evalWith, evalsC_runWith o env args]
      rfl
theorem evalsC_runWith (o : Env s.args → s.ret.denote) {Γ : List Ty} (env : Env Γ) :
    ∀ {ts : List Ty} (e : Exprs s Γ ts), (evalsC env e).runWith o = e.evalWith o env
  | _, .nil => rfl
  | _, .cons a as => by
      simp only [evalsC, Comp.runWith_bind, Exprs.evalWith, evalC_runWith o env a,
        evalsC_runWith o env as]
      rfl
end

/-- The well-foundedness certificate (a `Prop`): every request in the call tree
of the body at `x` is `R`-below `x`. -/
def Dec (R : Env s.args → Env s.args → Prop) (body : Body s) : Prop :=
  ∀ x, (evalC x body).AllCalls (R · x)

end

/-- A closed, well-founded program. -/
structure Term (s : Sig) where
  body : Body s
  R : Env s.args → Env s.args → Prop
  wf : WellFounded R
  dec : Dec R body

/-- The evaluator: `WellFounded.fix` over the call-tree interpreter. -/
def Term.run {s : Sig} (t : Term s) : Env s.args → s.ret.denote :=
  t.wf.fix fun x ih => Comp.interp (t.R · x) ih (evalC x t.body) (t.dec x)

/-- Curried evaluator. -/
def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv t.run

/-- **Soundness (1):** the evaluator satisfies the defining equation. -/
theorem Term.run_isFix {s : Sig} (t : Term s) : IsFix t.body t.run := by
  intro x
  rw [Term.run, WellFounded.fix_eq, Comp.interp_eq _ _ (t.wf.fix _) (fun _ _ => rfl),
    evalC_runWith]

/-- **Soundness (2):** uniqueness of solutions of the defining equation. -/
theorem Term.isFix_unique {s : Sig} (t : Term s) (f : Env s.args → s.ret.denote)
    (hf : IsFix t.body f) : ∀ x, t.run x = f x := by
  intro x
  induction x using t.wf.induction with
  | _ x IH =>
    rw [hf x, ← evalC_runWith, ← Comp.interp_eq _ _ f (fun y h => IH y h) _ (t.dec x)]
    rw [Term.run, WellFounded.fix_eq]

/-- Agreement with any Lean function satisfying the same recursive equation. -/
theorem Term.eval_eq {s : Sig} (t : Term s) (f : FnType s.args s.ret)
    (hf : IsFix t.body (uncurryEnv f)) : t.eval = f :=
  curryEnv_eq_of_isFix_unique t.isFix_unique f hf

end WFLang.FreeCall
