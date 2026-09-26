import RequestProject.WFLang.Tests.While
import RequestProject.WFLang.Tests.LeanWhile

/-!
# The evaluator on `diagonalWhile`: theorems instead of sampled checks

`Tests/While.lean` checks `PCL.Term.eval WhilePCL.diagonalWhile_term m n == Tco.diagonalWhile m n`
on sample inputs with `#eval`.  This file states and proves it as theorems:

* `diagonalWhile_term_eq`: the captured `wf_while` program computes the uploaded `while`
  function `Tco.diagonalWhile` **for all** `m n` (from the agreement theorem of the capture, the
  loop invariant of `WhileEx.diagonalWhile`, and `LeanWhileProofs.diagonalWhile_eq`);
* `diagonalWhile_check`: the sampled check itself (every `n < 60`, `m < 8`), as a corollary;
* runs of the compiled evaluator (the jump machine, `PCL/Lang/Machine.lean`) on inputs with
  hundreds of thousands of loop iterations or nested tail calls, checked by `native_decide`.
  Before the jump machine, these runs aborted with a `deep recursion` error
  (`STACK_OVERFLOW.md`).  `native_decide` runs the compiled code, in which `Expr.eval` and
  `fixFn` are replaced by the machine through the `@[csimp]` lemmas `Expr.eval_eq_evalImpl` and
  `fixFn_eq_fixFnImpl`.
-/

open WFLang PCL

namespace WhileProofs

/-- The test of the loop of `WhileEx.diagonalWhile` (state `(m, n, acc)`). -/
def diagC : Nat × Nat × Nat → Bool := fun (m, n, _) => m != 0 || n != 0

/-- The body of the loop of `WhileEx.diagonalWhile`. -/
def diagBody : Nat × Nat × Nat → Nat × Nat × Nat := fun (m, n, acc) =>
  if m > 0 then (m - 1, n + 1, acc + 1) else (n - 1, 0, acc + 1)

/-- The loop invariant: `acc + diagonal m n` is preserved, and at the exit `m = n = 0`.  (Stated
for any loop whose test and body are pointwise `diagC` and `diagBody`.) -/
theorem diag_loop {R : Nat × Nat × Nat → Nat × Nat × Nat → Prop} {wf : WellFounded R}
    {inv : Nat × Nat × Nat → Prop} {c : Nat × Nat × Nat → Bool}
    {body : Nat × Nat × Nat → Nat × Nat × Nat}
    {step : ∀ b, inv b → c b = true → inv (body b) ∧ R (body b) b}
    {b : Nat × Nat × Nat} {hb : inv b}
    (hc : ∀ x, c x = diagC x) (hbody : ∀ x, body x = diagBody x) :
    (whileWF R wf inv c body step b hb).2.2 = b.2.2 + Tco.diagonal b.1 b.2.1 := by
  obtain rfl : c = diagC := funext hc
  obtain rfl : body = diagBody := funext hbody
  have hP := whileWF_induction R wf inv diagC diagBody step
    (fun x => x.2.2 + Tco.diagonal x.1 x.2.1 = b.2.2 + Tco.diagonal b.1 b.2.1) b hb rfl
    (by
      rintro ⟨m, n, acc⟩ - hc hx
      simp only [diagC, bne_iff_ne, ne_eq, Bool.or_eq_true] at hc
      simp only [diagBody] at hx ⊢
      rw [← hx]
      split
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        show acc + 1 + Tco.diagonal (k + 1 - 1) (n + 1) = acc + Tco.diagonal (k + 1) n
        rw [Tco.diagonal.eq_3, Nat.add_sub_cancel]
        omega
      · obtain rfl : m = 0 := by omega
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        show acc + 1 + Tco.diagonal (k + 1 - 1) 0 = acc + Tco.diagonal 0 (k + 1)
        rw [Tco.diagonal.eq_2, Nat.add_sub_cancel]
        omega)
  have hs := (whileWF_spec R wf inv diagC diagBody step b hb).2
  generalize whileWF R wf inv diagC diagBody step b hb = r at hP hs
  obtain ⟨m, n, acc⟩ := r
  obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by simpa [diagC] using hs
  simpa [Tco.diagonal.eq_1] using hP

/-- The `wf_while` version `WhileEx.diagonalWhile` computes `diagonal`. -/
theorem diagonalWhile_eq_diagonal (m n : Nat) : WhileEx.diagonalWhile m n = Tco.diagonal m n := by
  unfold WhileEx.diagonalWhile whileMeasure
  rw [diag_loop]
  · simp
  all_goals rintro ⟨_, _, _⟩; rfl

end WhileProofs

namespace WhilePCL

/-- **The check of `Tests/While.lean`, for all inputs:** the program captured from the
`wf_while` loop computes the uploaded `while` function `Tco.diagonalWhile`. -/
theorem diagonalWhile_term_eq (m n : Nat) :
    Term.eval diagonalWhile_term m n = Tco.diagonalWhile m n := by
  rw [diagonalWhile_agree, WhileProofs.diagonalWhile_eq_diagonal,
    LeanWhileProofs.diagonalWhile_eq]

/-- The sampled check of `Tests/While.lean` (every `n < 60`, `m < 8`, with no restriction to
`n < 40`), proved from `diagonalWhile_term_eq`, not by running it. -/
theorem diagonalWhile_check :
    ((List.range 60).all fun n => (List.range 8).all fun m =>
      Term.eval diagonalWhile_term m n == Tco.diagonalWhile m n) = true := by
  simp [diagonalWhile_term_eq]

/-! ## Runs of the compiled evaluator (checked by running it) -/

/-- `diagonalWhile 0 1000`: 500 500 loop iterations. -/
theorem diagonalWhile_term_0_1000 : Term.eval diagonalWhile_term 0 1000 = 500500 := by
  native_decide

/-- The same run agrees with the uploaded `while` function, run natively. -/
theorem diagonalWhile_term_0_1000_eq :
    (Term.eval diagonalWhile_term 0 1000 == Tco.diagonalWhile 0 1000) = true := by
  native_decide

end WhilePCL

namespace ExPCL

/-- `sumTo 100000 0`: 100 000 nested tail calls of a global function. -/
theorem sumTo_term_100000 : Term.eval sumTo_term 100000 0 = 5000050000 := by
  native_decide

/-- `diagonal_tr 1000 0 0`: 501 500 nested tail calls. -/
theorem diagonal_tr_run_1000 : diagonal_tr_run 1000 0 0 = 501500 := by
  native_decide

end ExPCL
