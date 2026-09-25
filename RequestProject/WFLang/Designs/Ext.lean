import RequestProject.WFLang.Common.PExpr

/-!
# Design `PCL-Ext`: no termination information in the syntax; the measure is chosen outside

The body of a recursive function is plain syntax: `ret`, `ite`, and `let v := self args in k`.
There is **no** relation, measure or proof in the program.  The termination argument is
supplied *from outside*, by whoever runs the program, as a measure
`μ : Env ps → ℕ × ℕ` (compared lexicographically; a single `ℕ` measure is `fun x => (f x, 0)`).
The measure is an ordinary Lean function, not an object-language expression.

There are two evaluators, and they answer the question *"what happens if the measure is
wrong?"* differently:

* `Program.eval p μ hμ` — **certified**.  It needs a proof `hμ : p.Decreases μ` that every
  recursive call decreases `μ` (a verification condition computed from the syntax by
  `Body.VC`).  It performs no runtime check.  With a wrong measure the proof does not exist, so
  the program cannot be run: "the measure is exhausted" is ruled out statically.
* `Program.runChecked p μ` — **checked**, no proof needed.  It compares the measures at every
  call and, if a call does not decrease, stops with `Except.error (.notDecreasing callee caller)`.
  It never returns a made-up default value.

The two agree whenever the certificate exists (`runChecked_eq_ok`), so an `error` is a proof
that the measure is wrong (`not_decreases_of_error`).  Finally, the result does not depend on
*which* correct measure is chosen (`eval_measure_irrelevant`): the measure only justifies
termination, it never changes the value.

Restriction of this design: one recursive function per program (no nested `fix`).
-/

namespace WFLang.Ext

/-- Measures: lexicographic pairs of naturals. -/
abbrev Measure (ps : List Ty) := Env ps → Nat × Nat

/-- The (strict) lexicographic order on measures. -/
def LexLt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Nat × Nat) : Decidable (LexLt a b) := by unfold LexLt; infer_instance

theorem lexLt_wf : WellFounded LexLt := by
  have : LexLt = Prod.Lex (· < ·) (· < ·) := by
    funext a b; exact propext Prod.lex_def.symm
  rw [this]
  exact (WellFoundedRelation.wf (α := Nat × Nat))

/-- "`y` has a smaller measure than `x`" is well-founded. -/
theorem measure_wf {ps : List Ty} (μ : Measure ps) :
    WellFounded (fun y x : Env ps => LexLt (μ y) (μ x)) :=
  InvImage.wf μ lexLt_wf

/-- Body of a recursive function with parameters `ps` and result `r`.  `Γ` is the current
context (local results of earlier calls, then the parameters) and `cur` reads the current
parameters from it.  No proofs, no measure. -/
inductive Body (ps : List Ty) (r : Ty) : (Γ : List Ty) → (Env Γ → Env ps) → Type where
  | ret {Γ : List Ty} {cur : Env Γ → Env ps} (p : PExpr Γ r) : Body ps r Γ cur
  | ite {Γ : List Ty} {cur : Env Γ → Env ps} (c : PExpr Γ .bool) (a b : Body ps r Γ cur) :
      Body ps r Γ cur
  /-- `let v := self args in k`. -/
  | call {Γ : List Ty} {cur : Env Γ → Env ps} (args : PExprs Γ ps)
      (k : Body ps r (r :: Γ) (fun e => cur e.2)) : Body ps r Γ cur

/-- A program: one recursive function of signature `s`. -/
structure Program (s : Sig) where
  body : Body s.args s.ret s.args id

variable {ps : List Ty} {r : Ty}

/-! ## Checked evaluation: errors, never default values -/

/-- Why a checked run failed. -/
inductive Error where
  /-- A recursive call whose measure `callee` is not below the measure `caller` of the
  current call. -/
  | notDecreasing (callee caller : Nat × Nat)
  /-- The fuel given to `Program.runFuel` ran out. -/
  | outOfFuel
  deriving Repr, DecidableEq

/-- Evaluate a body, given a (checked) way of answering recursive calls. -/
def Body.evalE : {Γ : List Ty} → {cur : Env Γ → Env ps} → Body ps r Γ cur → Env Γ →
    (Env ps → Except Error r.denote) → Except Error r.denote
  | _, _, .ret p, e, _ => .ok (p.eval e)
  | _, _, .ite c a b, e, h => if c.eval e then a.evalE e h else b.evalE e h
  | _, _, .call args k, e, h =>
      match h (args.eval e) with
      | .ok v => k.evalE (v, e) h
      | .error err => .error err

/-- Recursion with a runtime measure check.  Terminates for every `μ`. -/
def checkedFix (μ : Measure ps) (F : Env ps → (Env ps → Except Error r.denote) → Except Error r.denote)
    (x : Env ps) : Except Error r.denote :=
  F x fun y => if LexLt (μ y) (μ x) then checkedFix μ F y
    else .error (.notDecreasing (μ y) (μ x))
termination_by μ x
decreasing_by exact Prod.lex_def.mpr ‹LexLt (μ y) (μ x)›

theorem checkedFix_eq (μ : Measure ps)
    (F : Env ps → (Env ps → Except Error r.denote) → Except Error r.denote) (x : Env ps) :
    checkedFix μ F x = F x fun y => if LexLt (μ y) (μ x) then checkedFix μ F y
      else .error (.notDecreasing (μ y) (μ x)) := by
  rw [checkedFix]

/-- Checked run of a program with a measure chosen by the caller. -/
def Program.runChecked {s : Sig} (p : Program s) (μ : Measure s.args) (x : Env s.args) :
    Except Error s.ret.denote :=
  checkedFix μ (fun x h => p.body.evalE x h) x

/-! ## Certified evaluation: the measure comes with a proof -/

/-- Verification condition: every reached call decreases `μ`. -/
def Body.VC (μ : Measure ps) : {Γ : List Ty} → {cur : Env Γ → Env ps} → Body ps r Γ cur →
    Env Γ → Prop
  | _, _, .ret _, _ => True
  | _, _, .ite c a b, e => (c.eval e = true → a.VC μ e) ∧ (c.eval e = false → b.VC μ e)
  | _, cur, .call args k, e => LexLt (μ (args.eval e)) (μ (cur e)) ∧ ∀ v, k.VC μ (v, e)

/-- `μ` is a correct termination measure for `p`. -/
def Program.Decreases {s : Sig} (p : Program s) (μ : Measure s.args) : Prop :=
  ∀ x, p.body.VC μ x

/-- Evaluate a body, given a handler defined only below the current measure. -/
def Body.eval (μ : Measure ps) : {Γ : List Ty} → {cur : Env Γ → Env ps} →
    (b : Body ps r Γ cur) → (e : Env Γ) → b.VC μ e →
    ((y : Env ps) → LexLt (μ y) (μ (cur e)) → r.denote) → r.denote
  | _, _, .ret p, e, _, _ => p.eval e
  | _, _, .ite c a b, e, hv, h =>
      if hc : c.eval e = true then a.eval μ e (hv.1 hc) h
      else b.eval μ e (hv.2 (Bool.eq_false_iff.mpr hc)) h
  | _, _, .call args k, e, hv, h => k.eval μ (h (args.eval e) hv.1, e) (hv.2 _) h

/-- The function computed by a program with a certified measure (uncurried). -/
def Program.fn {s : Sig} (p : Program s) (μ : Measure s.args) (hμ : p.Decreases μ) :
    Env s.args → s.ret.denote :=
  (measure_wf μ).fix fun x ih => p.body.eval μ x (hμ x) ih

/-- Certified, curried evaluator: `Program.eval p μ hμ m n`. -/
def Program.eval {s : Sig} (p : Program s) (μ : Measure s.args) (hμ : p.Decreases μ) :
    FnType s.args s.ret :=
  curryEnv (p.fn μ hμ)

/-! ## A reference semantics without any termination argument -/

/-- Evaluate a body against an arbitrary total function for the recursive calls.  This is the
"recursive equation" of the program; it mentions no measure. -/
def Body.evalT : {Γ : List Ty} → {cur : Env Γ → Env ps} → Body ps r Γ cur → Env Γ →
    (Env ps → r.denote) → r.denote
  | _, _, .ret p, e, _ => p.eval e
  | _, _, .ite c a b, e, f => if c.eval e then a.evalT e f else b.evalT e f
  | _, _, .call args k, e, f => k.evalT (f (args.eval e), e) f

theorem Body.eval_total (μ : Measure ps) : ∀ {Γ : List Ty} {cur : Env Γ → Env ps}
    (b : Body ps r Γ cur) (e : Env Γ) (hv : b.VC μ e) (f : Env ps → r.denote),
    b.eval μ e hv (fun y _ => f y) = b.evalT e f
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .ite c a b, e, hv, f => by
      simp only [Body.eval, Body.evalT]
      by_cases hc : c.eval e = true
      · rw [dif_pos hc, if_pos hc]; exact a.eval_total μ e _ f
      · rw [dif_neg hc, if_neg hc]; exact b.eval_total μ e _ f
  | _, _, .call args k, e, hv, f => k.eval_total μ _ _ f

/-! ## Soundness -/

/-- **Soundness (1):** the certified evaluator satisfies the recursive equation of the program
(which does not mention the measure). -/
theorem Program.fn_eq {s : Sig} (p : Program s) (μ : Measure s.args) (hμ : p.Decreases μ)
    (x : Env s.args) : p.fn μ hμ x = p.body.evalT x (p.fn μ hμ) := by
  rw [Program.fn, WellFounded.fix_eq]
  exact p.body.eval_total μ x (hμ x) _

/-- **Soundness (2):** it is the only solution of that equation. -/
theorem Program.fn_unique {s : Sig} (p : Program s) (μ : Measure s.args) (hμ : p.Decreases μ)
    (f : Env s.args → s.ret.denote) (hf : ∀ x, f x = p.body.evalT x f) :
    ∀ x, p.fn μ hμ x = f x := by
  intro x
  induction x using (measure_wf μ).induction with
  | _ x IH =>
    rw [Program.fn, WellFounded.fix_eq, hf x, ← p.body.eval_total μ x (hμ x) f]
    congr 1
    funext y hy
    exact IH y hy

/-- The value does not depend on which correct measure was chosen. -/
theorem Program.eval_measure_irrelevant {s : Sig} (p : Program s) (μ₁ μ₂ : Measure s.args)
    (h₁ : p.Decreases μ₁) (h₂ : p.Decreases μ₂) : p.eval μ₁ h₁ = p.eval μ₂ h₂ := by
  refine curryEnv_congr _ _ fun x => ?_
  exact p.fn_unique μ₁ h₁ _ (p.fn_eq μ₂ h₂) x

/-- Agreement with a Lean function satisfying the program's recursive equation. -/
theorem Program.eval_eq_of_eqn {s : Sig} (p : Program s) (μ : Measure s.args)
    (hμ : p.Decreases μ) (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x = p.body.evalT x (uncurryEnv f)) : p.eval μ hμ = f :=
  curryEnv_eq _ _ (p.fn_unique μ hμ _ hf)

/-! ## Checked vs. certified -/

theorem Body.evalE_ok (μ : Measure ps) : ∀ {Γ : List Ty} {cur : Env Γ → Env ps}
    (b : Body ps r Γ cur) (e : Env Γ) (hv : b.VC μ e)
    (h : (y : Env ps) → LexLt (μ y) (μ (cur e)) → r.denote)
    (hc : Env ps → Except Error r.denote), (∀ y hy, hc y = .ok (h y hy)) →
    b.evalE e hc = .ok (b.eval μ e hv h)
  | _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, .ite c a b, e, hv, h, hc, hh => by
      simp only [Body.evalE, Body.eval]
      by_cases hcnd : c.eval e = true
      · rw [dif_pos hcnd, if_pos hcnd]; exact a.evalE_ok μ e _ h hc hh
      · rw [dif_neg hcnd, if_neg hcnd]; exact b.evalE_ok μ e _ h hc hh
  | _, _, .call args k, e, hv, h, hc, hh => by
      simp only [Body.evalE, Body.eval, hh _ hv.1]
      exact k.evalE_ok μ (h (args.eval e) hv.1, e) (hv.2 _) h hc hh

/-- With a certified measure, the checked run never fails and gives the certified value. -/
theorem Program.runChecked_eq_ok {s : Sig} (p : Program s) (μ : Measure s.args)
    (hμ : p.Decreases μ) (x : Env s.args) : p.runChecked μ x = .ok (p.fn μ hμ x) := by
  induction x using (measure_wf μ).induction with
  | _ x IH =>
    rw [Program.runChecked, checkedFix_eq, Program.fn, WellFounded.fix_eq]
    refine p.body.evalE_ok μ x (hμ x) _ _ fun y hy => ?_
    rw [if_pos (show LexLt (μ y) (μ x) from hy)]
    exact IH y hy

/-- So a checked run that reports an error proves that the measure is not a correct one. -/
theorem Program.not_decreases_of_error {s : Sig} (p : Program s) (μ : Measure s.args)
    (x : Env s.args) (err : Error) (h : p.runChecked μ x = .error err) : ¬ p.Decreases μ := by
  intro hμ
  rw [p.runChecked_eq_ok μ hμ x] at h
  cases h

/-! ## Fuel computed from a certified measure

A third evaluator: plain structural recursion on a fuel counter, with no measure check at all.
It stops with `.error .outOfFuel` when the fuel runs out.  Because it is structural, it reduces in
the kernel (`decide`/`rfl` work on concrete inputs).  The fuel is not part of the program: it is
computed from a certified `ℕ`-valued measure `f`, and then it provably never runs out. -/

/-- Run with `n` units of fuel (one unit per nested recursive call). -/
def Program.runFuel {s : Sig} (p : Program s) : Nat → Env s.args → Except Error s.ret.denote
  | 0, _ => .error .outOfFuel
  | n + 1, x => p.body.evalE x (p.runFuel n)

/-- With a certified `ℕ`-valued measure `f`, any fuel above `f x` is enough, and the result is
the certified value. -/
theorem Program.runFuel_eq_ok {s : Sig} (p : Program s) (f : Env s.args → Nat)
    (hμ : p.Decreases (fun x => (f x, 0))) :
    ∀ n x, f x < n → p.runFuel n x = .ok (p.fn _ hμ x)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, h => by
    rw [Program.runFuel, Program.fn, WellFounded.fix_eq]
    refine p.body.evalE_ok _ x (hμ x) _ _ fun y hy => ?_
    have hy' : f y < f x := by
      rcases hy with hy | ⟨_, hy⟩
      · exact hy
      · exact absurd hy (Nat.not_lt_zero _)
    exact p.runFuel_eq_ok f hμ n y (by omega)

/-- In particular fuel `f x + 1` suffices. -/
theorem Program.runFuel_measure {s : Sig} (p : Program s) (f : Env s.args → Nat)
    (hμ : p.Decreases (fun x => (f x, 0))) (x : Env s.args) :
    p.runFuel (f x + 1) x = .ok (p.fn _ hμ x) :=
  p.runFuel_eq_ok f hμ _ x (Nat.lt_succ_self _)

end WFLang.Ext
