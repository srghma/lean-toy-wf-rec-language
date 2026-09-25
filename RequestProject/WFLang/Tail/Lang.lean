import RequestProject.WFLang.Common.PExpr
import RequestProject.WFLang.Common.WFBox

/-!
# Language `Tail`: well-founded *loops* as a construct of the grammar

This language only has **tail** recursion, and makes it a construct of the grammar:

```
Expr  ::= ret p | ite p Expr Expr | loop ps r R wf Body args Expr   -- let v := loop … in k
Body  ::= done p | next args dec | ite p Body Body                   -- one loop iteration
```

* `loop` carries the relation `R` on the loop state and `wf : WellFounded R` (a `Prop`).
* A loop body is a tree of tests ending either in `done p` (leave the loop with value `p`)
  or in `next args dec` (continue with the new state `args`), where `dec` proves that the new
  state is `R`-smaller whenever this leaf is reached (the index `G` is the path condition).
* The call-free expressions are `PExpr` (`Common/PExpr.lean`).

The evaluator runs a loop with a self tail call (`Loop.run`), which Lean's code generator
turns into a C `goto` loop: the stack does not grow with the number of iterations.
-/

namespace WFLang.Tail

/-- One iteration of a loop over the state `ps`, with result type `r`, reached under the
path condition `G`. -/
inductive Body (ps : List Ty) (r : Ty) (R : Env ps → Env ps → Prop) : (Env ps → Prop) → Type where
  | done {G : Env ps → Prop} (p : PExpr ps r) : Body ps r R G
  | next {G : Env ps → Prop} (args : PExprs ps ps) (dec : ∀ e, G e → R (args.eval e) e) :
      Body ps r R G
  | ite {G : Env ps → Prop} (c : PExpr ps .bool)
      (a : Body ps r R (fun e => G e ∧ c.eval e = true))
      (b : Body ps r R (fun e => G e ∧ c.eval e = false)) : Body ps r R G

/-- Expressions: `loop` is one of them. -/
inductive Expr : List Ty → Ty → Type where
  | ret {Γ : List Ty} {t : Ty} (p : PExpr Γ t) : Expr Γ t
  | ite {Γ : List Ty} {t : Ty} (c : PExpr Γ .bool) (a b : Expr Γ t) : Expr Γ t
  /-- `let v := (loop state := args; body) in k` -/
  | loop {Γ : List Ty} {t : Ty} (ps : List Ty) (r : Ty) (R : Env ps → Env ps → Prop) (wf : WellFounded R)
      (body : Body ps r R (fun _ => True)) (args : PExprs Γ ps) (k : Expr (r :: Γ) t) : Expr Γ t

section Body
variable {ps : List Ty} {r : Ty} {R : Env ps → Env ps → Prop}

/-- One iteration: either the result, or the next (smaller) state. -/
def Body.step : {G : Env ps → Prop} → Body ps r R G → (x : Env ps) → G x →
    r.denote ⊕ { y : Env ps // R y x }
  | _, .done p, x, _ => .inl (p.eval x)
  | _, .next args dec, x, g => .inr ⟨args.eval x, dec x g⟩
  | _, .ite c a b, x, g =>
      if hc : c.eval x = true then a.step x ⟨g, hc⟩
      else b.step x ⟨g, Bool.eq_false_iff.mpr hc⟩

/-- Reference one-step semantics, with the next iteration answered by an oracle `o`. -/
def Body.evalWith (o : Env ps → r.denote) : {G : Env ps → Prop} → Body ps r R G → Env ps → r.denote
  | _, .done p, x => p.eval x
  | _, .next args _, x => o (args.eval x)
  | _, .ite c a b, x => if c.eval x = true then a.evalWith o x else b.evalWith o x

theorem Body.step_evalWith (o : Env ps → r.denote) :
    ∀ {G : Env ps → Prop} (b : Body ps r R G) (x : Env ps) (g : G x),
      (match b.step x g with | .inl v => v | .inr y => o y.1) = b.evalWith o x
  | _, .done _, _, _ => rfl
  | _, .next _ _, _, _ => rfl
  | _, .ite c a b, x, g => by
      simp only [Body.step, Body.evalWith]
      by_cases hc : c.eval x = true
      · rw [dif_pos hc, if_pos hc]; exact a.step_evalWith o x _
      · rw [dif_neg hc, if_neg hc]; exact b.step_evalWith o x _

/-- Run a loop: a self tail call, compiled to a `goto` loop. -/
def Loop.run (wf : WellFounded R) (body : Body ps r R (fun _ => True)) (x : Env ps) : r.denote :=
  match body.step x trivial with
  | .inl v => v
  | .inr ⟨y, _⟩ => Loop.run wf body y
termination_by (WFBox.mk x : WFBox R wf)
decreasing_by all_goals exact ‹_›

/-- **Soundness (1):** a loop satisfies its one-step equation. -/
theorem Loop.run_eq (wf : WellFounded R) (body : Body ps r R (fun _ => True)) (x : Env ps) :
    Loop.run wf body x = body.evalWith (Loop.run wf body) x := by
  rw [← body.step_evalWith (Loop.run wf body) x trivial]
  conv => lhs; rw [Loop.run]
  generalize body.step x trivial = st
  rcases st with v | ⟨y, hy⟩ <;> rfl

/-- **Soundness (2):** it is the only solution of that equation. -/
theorem Loop.run_unique (wf : WellFounded R) (body : Body ps r R (fun _ => True))
    (f : Env ps → r.denote) (hf : ∀ x, f x = body.evalWith f x) : ∀ x, Loop.run wf body x = f x := by
  intro x
  induction x using wf.induction with
  | _ x IH =>
    rw [Loop.run_eq, hf x, ← body.step_evalWith _ x trivial, ← body.step_evalWith _ x trivial]
    generalize body.step x trivial = st
    rcases st with v | ⟨y, hy⟩
    · rfl
    · exact IH y hy

end Body

/-- The evaluator of expressions (structural recursion). -/
def Expr.eval {Γ : List Ty} : {t : Ty} → Expr Γ t → Env Γ → t.denote
  | _, .ret p, e => p.eval e
  | _, .ite c a b, e => if c.eval e = true then a.eval e else b.eval e
  | _, .loop _ _ _ wf body args k, e => k.eval (Loop.run wf body (args.eval e), e)

/-- Closed programs of signature `s`. -/
abbrev Term (s : Sig) := Expr s.args s.ret

def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv (Expr.eval t)

/-- Agreement for a program of the shape produced by the capture macro,
`let v := (loop state := xs; body) in v`. -/
theorem Term.eval_loop_eq {s : Sig} (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Body s.args s.ret R (fun _ => True)) (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x = body.evalWith (uncurryEnv f) x) :
    Term.eval (Expr.loop s.args s.ret R wf body (PExprs.ids s.args) (.ret (.var .here)) :
      Term s) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  show (Loop.run wf body ((PExprs.ids s.args).eval x), x).1 = _
  rw [PExprs.ids_eval]
  exact Loop.run_unique wf body _ hf x

end WFLang.Tail
