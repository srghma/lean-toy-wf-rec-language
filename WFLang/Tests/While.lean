import RequestProject.WFLang.Tests.MoreChecks
import RequestProject.WFLang.Tests.WhileFunctions

/-!
# `while` loops

The `PCL` statement `Expr.whileLoop` (`let v := while c do x := body from init in k`, see
`PCL/Lang.lean`) is a well-founded loop: it carries a relation on the loop states, its
well-foundedness proof, an invariant, and the body proves that each iteration keeps the
invariant and goes down.  It is a derived form: a join point `K` (the rest of the statement)
and a recursive join point `L` (the loop) whose body is `if c then jump L body else jump K x`.
Its evaluation (`WellFounded.fix` on the loop states) is total, and `eval_whileLoop` shows that
it computes the Lean loop `whileWF`.

* A **hand-written** program with a `while` loop, and what the typing of the loop gives for
  free: the result satisfies the invariant and not the test (`divOut_not_dvd`).
* **Captures**: every Lean function of `Tests/WhileFunctions.lean` (written with `wf_while` or
  `whileWF`) is captured by `#lean_wf_func_to_term`, each loop as one `while` statement (a join
  point for the exit and a recursive join point for the loop; the number of loops is pinned), with its agreement theorem proved by `wf_agree`.  This
  includes loops with tuple states, loops whose body contains an `if`, a loop with an
  invariant, two loops in a row, a loop after a recursive call inside a recursive function, a
  loop in a global function and a loop whose initial state calls a global function.
* **Runtime checks** against the uploaded (partial) `while` functions.
* **Rejections**: a call inside the body of a loop, and Lean's own `while` without a measure
  (captured with one in `Tests/LeanWhile.lean`).
-/

open WFLang PCL

/-! ## A hand-written program -/

namespace WhileHand

/-- `divOut n d`: divide `n` by `d` as long as it is divisible:

```
let x := while (1 < d && x % d == 0 && 0 < x) do x := x / d  from x := n  in x
```

The loop state is `x`, the relation is `<` on `Nat`, and the invariant is `0 < n → 0 < x`.  The
program's type carries its specification (a postcondition): for `d > 1` and `n > 0`, the result
is positive and no longer divisible by `d`.  The final `ret` proves it from what the loop
guarantees on exit (the invariant, and that the test is false). -/
def divOut_term : Term ⟨[.nat, .nat], .nat⟩
    (fun e r => 1 < e.2.1 → 0 < e.1 → 0 < r ∧ r % e.2.1 ≠ 0) :=
  ⟨.nil, .whileLoop .nat (.var .here) rfl
    (.bin .and
      (.bin .and (.bin .lt (.lit .nat 1) (.var (.there (.there .here))))
        (.bin (.beq .nat) (.bin .mod (.var .here) (.var (.there (.there .here)))) (.lit .nat 0)))
      (.bin .lt (.lit .nat 0) (.var .here)))
    (by decide)
    (fun _ a b => a < b) (fun _ => Nat.lt_wfRel.wf)
    (fun e x => 0 < e.1 → 0 < x) (fun _ _ h => h)
    (.bin .div (.var .here) (.var (.there (.there .here)))) (by decide)
    (fun e g => by
        obtain ⟨x, n, d, ⟨⟩⟩ := e
        simp only [PExpr.eval, Var.get, BinOp.eval, Ty.beq, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at g ⊢
        obtain ⟨-, -, ⟨⟨hd, hmod⟩, hx⟩⟩ := g
        have hle : d ≤ x := Nat.le_of_dvd hx (Nat.dvd_of_mod_eq_zero hmod)
        exact ⟨fun _ => Nat.div_pos hle (by omega), Nat.div_lt_self hx hd⟩)
    (.ret (.var .here) rfl (fun e g => by
        obtain ⟨x, n, d, ⟨⟩⟩ := e
        simp only [PExpr.eval, Var.get, BinOp.eval, Ty.beq] at g ⊢
        obtain ⟨-, hinv, hc⟩ := g
        intro hd hn
        have hx := hinv hn
        exact ⟨hx, fun hm => by simp [hd, hm, hx] at hc⟩))⟩

/-- info: [12, 3, 5, 1, 7, 0] -/
#guard_msgs in
#eval [Term.eval divOut_term 96 8, Term.eval divOut_term 96 2, Term.eval divOut_term 5 3,
  Term.eval divOut_term 1024 2, Term.eval divOut_term 7 1, Term.eval divOut_term 0 2]

/-- **Partial correctness for free**: for `d > 1` and `n > 0` the result of `divOut` is positive
and not divisible by `d`.  This is the postcondition in the type of the program
(`PTerm.run_post`), established from what the `while` node guarantees on exit. -/
theorem divOut_spec (n d : Nat) (hd : 1 < d) (hn : 0 < n) :
    0 < Term.eval divOut_term n d ∧ Term.eval divOut_term n d % d ≠ 0 :=
  PTerm.run_post divOut_term (n, d, ()) trivial hd hn

end WhileHand

/-! ## Captures of Lean functions with `while` loops -/

namespace WhilePCL

def isqrt_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.isqrt
theorem isqrt_agree : ∀ n, Term.eval isqrt_term n = WhileEx.isqrt n := by wf_agree

def isqrtNewton_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.isqrtNewton
theorem isqrtNewton_agree : ∀ n, Term.eval isqrtNewton_term n = WhileEx.isqrtNewton n := by
  wf_agree

def gcdLoop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term WhileEx.gcdLoop
theorem gcdLoop_agree : ∀ m n, Term.eval gcdLoop_term m n = WhileEx.gcdLoop m n := by wf_agree

def sumDown_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.sumDown
theorem sumDown_agree : ∀ n, Term.eval sumDown_term n = WhileEx.sumDown n := by wf_agree

def mc91While_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.mc91While
theorem mc91While_agree : ∀ n, Term.eval mc91While_term n = WhileEx.mc91While n := by wf_agree

def diagonalWhile_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term WhileEx.diagonalWhile
theorem diagonalWhile_agree :
    ∀ m n, Term.eval diagonalWhile_term m n = WhileEx.diagonalWhile m n := by wf_agree

def collatzSteps_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.collatzSteps
theorem collatzSteps_agree : ∀ n, Term.eval collatzSteps_term n = WhileEx.collatzSteps n := by
  wf_agree

def roundSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.roundSum
theorem roundSum_agree : ∀ n, Term.eval roundSum_term n = WhileEx.roundSum n := by wf_agree

def evenDown_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.evenDown
theorem evenDown_agree : ∀ n, Term.eval evenDown_term n = WhileEx.evenDown n := by wf_agree

def twoLoops_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.twoLoops
theorem twoLoops_agree : ∀ n, Term.eval twoLoops_term n = WhileEx.twoLoops n := by wf_agree

end WhilePCL

/-! ## Loops and global functions -/

namespace WhilePCL

/-- `isqrt` (containing a loop) is a global function, called twice. -/
def isqrtSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.isqrtSum
theorem isqrtSum_agree : ∀ n, Term.eval isqrtSum_term n = WhileEx.isqrtSum n := by wf_agree

/-- The initial state of the loop is the result of a call of the global function `isqrt`. -/
def evenSqrt_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term WhileEx.evenSqrt
theorem evenSqrt_agree : ∀ n, Term.eval evenSqrt_term n = WhileEx.evenSqrt n := by wf_agree

end WhilePCL

/-! ## Shapes: each loop is one recursive join point (`loops`)

The second component is the number of global functions (`nglobals`): the recursive `roundSum`
itself, and `isqrt` for `isqrtSum` and `evenSqrt`.  No loop needs a global function. -/

/-- info: [(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 1), (1, 0), (2, 0), (1, 1), (2, 1)] -/
#guard_msgs in
#eval open WhilePCL in
  [isqrt_term.loops, isqrtNewton_term.loops, gcdLoop_term.loops, sumDown_term.loops,
    mc91While_term.loops, diagonalWhile_term.loops, collatzSteps_term.loops,
    roundSum_term.loops, evenDown_term.loops, twoLoops_term.loops, isqrtSum_term.loops,
    evenSqrt_term.loops].zip
  [isqrt_term.nglobals, isqrtNewton_term.nglobals, gcdLoop_term.nglobals, sumDown_term.nglobals,
    mc91While_term.nglobals, diagonalWhile_term.nglobals, collatzSteps_term.nglobals,
    roundSum_term.nglobals, evenDown_term.nglobals, twoLoops_term.nglobals,
    isqrtSum_term.nglobals, evenSqrt_term.nglobals]

/-! ## Runtime checks -/

/-- info: [0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4] -/
#guard_msgs in
#eval (List.range 20).map (PCL.Term.eval WhilePCL.isqrt_term)

-- The loops agree with the uploaded (partial) `while` functions they transcribe: Newton's
-- `isqrt`, `diagonalWhile` and `mc91While` (sample inputs).
/-- info: true -/
#guard_msgs in
#eval (List.range 60).all fun n =>
  PCL.Term.eval WhilePCL.isqrtNewton_term n == Tco.AckWithoutStackButUsingCantorPairing.isqrt n &&
  PCL.Term.eval WhilePCL.isqrt_term n == Tco.AckWithoutStackButUsingCantorPairing.isqrt n &&
  PCL.Term.eval WhilePCL.mc91While_term (3 * n) == Tco.mc91While (3 * n) &&
  (List.range 8).all fun m =>
    PCL.Term.eval WhilePCL.diagonalWhile_term m n == Tco.diagonalWhile m n

-- `diagonalWhile 0 n` runs `n (n + 1) / 2` loop iterations (here 80 200).  Loops run in constant
-- stack (`PCL/Lang/Machine.lean`, see `STACK_OVERFLOW.md`).
/-- info: true -/
#guard_msgs in
#eval PCL.Term.eval WhilePCL.diagonalWhile_term 0 400 == Tco.diagonalWhile 0 400

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun m => (List.range 30).all fun n =>
  PCL.Term.eval WhilePCL.gcdLoop_term m n == Nat.gcd m n

/-- info: [0, 0, 1, 7, 2, 5, 8, 16, 3, 19, 6, 14, 9, 9, 17, 17, 4, 12, 20, 20] -/
#guard_msgs in
#eval (List.range 20).map (PCL.Term.eval WhilePCL.collatzSteps_term)

/-- info: [0, 1, 9, 17, 25, 33, 41, 49] -/
#guard_msgs in
#eval (List.range 8).map (PCL.Term.eval WhilePCL.roundSum_term)

/-! ## Rejections -/

/-- info: rejected: #lean_wf_func_to_term: a call (or a loop) inside the test or the body of a `while` loop is not supported -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term WhileEx.callInBody : PCL.Term ⟨[.nat], .nat⟩)

-- Lean's own `while` (in `do` notation) is captured through its well-founded version, if the
-- termination of the loop can be proved (`Tests/LeanWhile.lean`): here Lean finds no measure.
/-- info: rejected: lean_while_to_wf: cannot prove that loop 1 of Tco.mc91While terminates: give its measure, `lean_while_to_wf Tco.mc91While termination_by …` (and `decreasing_by …`) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.mc91While : PCL.Term ⟨[.nat], .nat⟩)
