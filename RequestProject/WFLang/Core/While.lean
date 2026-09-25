module

/-!
# Well-founded `while` loops in Lean

Lean's own `while` (in `do` notation) is built on `Loop.forIn`, a `partial def`: it comes with
no termination proof and cannot be unfolded in proofs, so a function using it can neither be
captured nor proved equal to anything.  This file provides the well-founded replacement that
`#lean_wf_func_to_term` captures as the `PCL` statement `Expr.whileLoop`:

* `whileWF R wf inv c body step b hb` runs `while c b do b := body b` from `b`: each iteration
  that runs (`c b = true`) keeps the invariant `inv` and goes down along the well-founded relation
  `R` (`step`);
* `whileMeasure μ c body dec b` is the common special case of a `Nat`-valued measure `μ` that
  decreases at each iteration (`dec`), with no invariant;
* the notation `wf_while b := init while c do body termination_by μ` (see below) writes
  `whileMeasure (fun b => μ) (fun b => c) (fun b => body) (by …) init`, proving the decrease
  with `omega` / `decreasing_tactic` (or `decreasing_by tac`).

`whileWF_eq` is the loop equation, `whileWF_unique` says it has only one solution, `whileWF_spec`
that the result satisfies the invariant and the exit condition, and `whileWF_congr` that the
value does not depend on the termination argument (relation, invariant, proofs).
-/

@[expose] public section

namespace WFLang

/-- The well-founded loop `while c b do b := body b`, started from `b`.  Every iteration that runs
keeps the invariant `inv` and goes down along the well-founded relation `R` (`step`). -/
def whileWF {β : Type} (R : β → β → Prop) (wf : WellFounded R) (inv : β → Prop)
    (c : β → Bool) (body : β → β)
    (step : ∀ b, inv b → c b = true → inv (body b) ∧ R (body b) b) (b : β) (hb : inv b) : β :=
  wf.fix (C := fun b => inv b → β)
    (fun b ih hb => if h : c b = true then ih (body b) (step b hb h).2 (step b hb h).1 else b) b hb

section
variable {β : Type} (R : β → β → Prop) (wf : WellFounded R) (inv : β → Prop)
    (c : β → Bool) (body : β → β)
    (step : ∀ b, inv b → c b = true → inv (body b) ∧ R (body b) b)

/-- **The loop equation.** -/
theorem whileWF_eq (b : β) (hb : inv b) :
    whileWF R wf inv c body step b hb =
      if h : c b = true then whileWF R wf inv c body step (body b) (step b hb h).1 else b := by
  unfold whileWF
  rw [WellFounded.fix_eq]

theorem whileWF_of_true (b : β) (hb : inv b) (h : c b = true) :
    whileWF R wf inv c body step b hb = whileWF R wf inv c body step (body b) (step b hb h).1 := by
  rw [whileWF_eq, dif_pos h]

theorem whileWF_of_false (b : β) (hb : inv b) (h : c b = false) :
    whileWF R wf inv c body step b hb = b := by
  rw [whileWF_eq, dif_neg (by simp [h])]

/-- **The loop equation has only one solution** (on the states satisfying the invariant). -/
theorem whileWF_unique (W : (b : β) → inv b → β)
    (hW : ∀ b hb, W b hb = if h : c b = true then W (body b) (step b hb h).1 else b) :
    ∀ b hb, whileWF R wf inv c body step b hb = W b hb := by
  intro b
  induction b using wf.induction with
  | _ b IH =>
    intro hb
    rw [whileWF_eq, hW]
    by_cases h : c b = true
    · rw [dif_pos h, dif_pos h]; exact IH _ (step b hb h).2 _
    · rw [dif_neg h, dif_neg h]

/-- **Partial correctness for free:** the result satisfies the invariant and the exit
condition. -/
theorem whileWF_spec (b : β) (hb : inv b) :
    inv (whileWF R wf inv c body step b hb) ∧ c (whileWF R wf inv c body step b hb) = false := by
  induction b using wf.induction with
  | _ b IH =>
    by_cases h : c b = true
    · rw [whileWF_of_true R wf inv c body step b hb h]
      exact IH _ (step b hb h).2 _
    · rw [whileWF_of_false R wf inv c body step b hb (by simpa using h)]
      exact ⟨hb, by simpa using h⟩

/-- Hoare-style reasoning: a property `P` that holds initially and is preserved by every
iteration that runs holds at the end (where the test is false). -/
theorem whileWF_induction (P : β → Prop) (b : β) (hb : inv b) (h0 : P b)
    (hstep : ∀ x, inv x → c x = true → P x → P (body x)) :
    P (whileWF R wf inv c body step b hb) := by
  induction b using wf.induction with
  | _ b IH =>
    by_cases h : c b = true
    · rw [whileWF_of_true R wf inv c body step b hb h]
      exact IH _ (step b hb h).2 _ (hstep b hb h h0)
    · rw [whileWF_of_false R wf inv c body step b hb (by simpa using h)]
      exact h0

end

/-- **The value of a loop does not depend on its termination argument**: two loops with the
same test and body (on the states satisfying the first invariant) compute the same value,
whatever their relations, invariants and proofs. -/
theorem whileWF_congr {β : Type} {R R' : β → β → Prop} {wf : WellFounded R}
    {wf' : WellFounded R'} {inv inv' : β → Prop} {c c' : β → Bool} {body body' : β → β}
    {step : ∀ b, inv b → c b = true → inv (body b) ∧ R (body b) b}
    {step' : ∀ b, inv' b → c' b = true → inv' (body' b) ∧ R' (body' b) b}
    (hc : ∀ x, inv x → c x = c' x) (hbody : ∀ x, inv x → c x = true → body x = body' x)
    (b : β) (hb : inv b) (hb' : inv' b) :
    whileWF R wf inv c body step b hb = whileWF R' wf' inv' c' body' step' b hb' := by
  induction b using wf.induction with
  | _ b IH =>
    by_cases h : c b = true
    · have h' : c' b = true := by rw [← hc b hb]; exact h
      rw [whileWF_of_true R wf inv c body step b hb h,
        whileWF_of_true R' wf' inv' c' body' step' b hb' h']
      have hi' : inv' (body b) := by rw [hbody b hb h]; exact (step' b hb' h').1
      have := IH _ (step b hb h).2 (step b hb h).1 hi'
      rw [this]
      congr 1
      exact hbody b hb h
    · have h' : c' b = false := by rw [← hc b hb]; simpa using h
      rw [whileWF_of_false R wf inv c body step b hb (by simpa using h),
        whileWF_of_false R' wf' inv' c' body' step' b hb' h']

/-- A `while` loop whose `Nat`-valued measure `μ` goes down at every iteration. -/
@[reducible] def whileMeasure {β : Type} (μ : β → Nat) (c : β → Bool) (body : β → β)
    (dec : ∀ b, c b = true → μ (body b) < μ b) (b : β) : β :=
  whileWF (InvImage (· < ·) μ) (InvImage.wf μ Nat.lt_wfRel.wf) (fun _ => True) c body
    (fun b _ h => ⟨trivial, dec b h⟩) b trivial

theorem whileMeasure_eq {β : Type} (μ : β → Nat) (c : β → Bool) (body : β → β)
    (dec : ∀ b, c b = true → μ (body b) < μ b) (b : β) :
    whileMeasure μ c body dec b = if c b then whileMeasure μ c body dec (body b) else b := by
  unfold whileMeasure
  rw [whileWF_eq]
  by_cases h : c b = true <;> simp [h]

/-- `wf_while b := init while c do body termination_by μ`: the loop `while c do b := body` started
from `b := init`, whose measure `μ : Nat` goes down at every iteration.  The decrease is proved
by `omega` (after simplifying the test) or `decreasing_tactic`, or by the tactic given with
`decreasing_by`.  The state `b` may be a tuple: `wf_while (x, y) := … while … do … termination_by …`. -/
syntax "wf_while " term:max " := " term " while " Lean.Parser.Term.termBeforeDo " do " term
  " termination_by " term (" decreasing_by " tacticSeq)? : term

macro_rules
  | `(wf_while $b := $init while $c do $body termination_by $μ decreasing_by $tac) =>
    `(WFLang.whileMeasure (fun $b => $μ) (fun $b => $c) (fun $b => $body) (by $tac) $init)
  | `(wf_while $b := $init while $c do $body termination_by $μ) =>
    `(WFLang.whileMeasure (fun $b => $μ) (fun $b => $c) (fun $b => $body)
        (by
          intro b h
          first
            | (simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
                beq_iff_eq, ne_eq] at h
               first | omega | (simp_all; omega) | (split at * <;> simp_all <;> omega))
            | (simp_all; done)
            | (simp_all <;> omega)
            | decreasing_tactic)
        $init)

end WFLang

end
