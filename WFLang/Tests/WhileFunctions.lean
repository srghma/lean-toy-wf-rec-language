import RequestProject.WFLang.Core.While
import Mathlib.Tactic.Linarith

/-!
# Lean functions written with well-founded `while` loops

Lean's `while` (in `do` notation) carries no termination measure: the uploaded `while` functions
(`Tco.diagonalWhile`, `Tco.mc91While`, `Tco.AckWithoutStackButUsingCantorPairing.isqrt`, …) state
no measure.  These are the same loops written with the well-founded loop of `Core/While.lean` (the notation `wf_while`, or `WFLang.whileWF` with an
invariant): each one states its termination measure, and is captured by
`#lean_wf_func_to_term` as a `PCL` `while` statement (`Tests/While.lean`).

The uploaded `while` functions themselves are captured too, through `lean_while_to_wf` and the
unfolding law of Lean's `while`, `WFLang.loopLaw` (`Tests/LeanWhile.lean`).
-/

open WFLang

namespace WhileEx

/-- Integer square root by linear search: the largest `r` with `r * r ≤ n`. -/
def isqrt (n : Nat) : Nat :=
  wf_while r := 0 while (r + 1) * (r + 1) ≤ n do r + 1 termination_by n - r
    decreasing_by intro r h; simp at h; have := Nat.le_mul_self (r + 1); omega

/-- Newton iteration for the integer square root: the loop of the uploaded
`Tco.AckWithoutStackButUsingCantorPairing.isqrt`, with the measure `x`. -/
def isqrtNewton (n : Nat) : Nat :=
  (wf_while (x, y) := (n, (n + 1) / 2) while y < x do (y, (y + n / y) / 2)
    termination_by x).1

/-- Euclid's algorithm as a loop on the pair `(a, b)`. -/
def gcdLoop (m n : Nat) : Nat :=
  (wf_while (a, b) := (m, n) while b != 0 do (b, a % b) termination_by b
    decreasing_by
      intro p h
      obtain ⟨a, b⟩ := p
      simp at h ⊢
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)).1

/-- `n + (n - 1) + … + 1`, counting down. -/
def sumDown (n : Nat) : Nat :=
  (wf_while p := (n, 0) while p.1 != 0 do (p.1 - 1, p.2 + p.1) termination_by p.1).2

/-- The loop of the uploaded `Tco.mc91While`, with the measure of `Tco.mc91Loop`. -/
def mc91While (n : Nat) : Nat :=
  (wf_while (c, cur) := (1, n) while c != 0 do
      (if cur > 100 then (c - 1, cur - 10) else (c + 1, cur + 11))
    termination_by 2 * (111 - cur) + 21 * c).2

/-- The loop of the uploaded `Tco.diagonalWhile` (state `(m, n, acc)`), with the measure
`(m + n)² + m`. -/
def diagonalWhile (m n : Nat) : Nat :=
  (wf_while (m, n, acc) := (m, n, 0) while m != 0 || n != 0 do
      (if m > 0 then (m - 1, n + 1, acc + 1) else (n - 1, 0, acc + 1))
    termination_by (m + n) * (m + n) + m
    decreasing_by
      intro p h
      obtain ⟨m, n, acc⟩ := p
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true] at h
      split
      · have e : m - 1 + (n + 1) = m + n := by omega
        dsimp only
        rw [e]
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have hm : m = 0 := by omega
        subst hm
        dsimp only
        simp only [Nat.add_sub_cancel, Nat.zero_add, Nat.add_zero]
        nlinarith).2.2

/-- The number of Collatz steps from `x` to `1`, giving up after 1000 steps. -/
def collatzSteps (x : Nat) : Nat :=
  (wf_while (x, k) := (x, 0) while 1 < x && k < 1000 do
    (if x % 2 == 0 then x / 2 else 3 * x + 1, k + 1) termination_by 1000 - k).2

/-- A loop in a recursive function, after a recursive call: round the previous value up to a
multiple of 7, then add `n`. -/
def roundSum (n : Nat) : Nat :=
  if n = 0 then 0 else
  let a := roundSum (n - 1)
  let b := wf_while i := a while i % 7 != 0 do i + 1 termination_by (7 - i % 7) % 7
  b + n

/-- The general form `whileWF`, with an invariant: `x` stays even, so `x - 2` never jumps over
`0`.  (The loop computes `0`, in `n` iterations.) -/
def evenDown (n : Nat) : Nat :=
  whileWF (InvImage (· < ·) id) (InvImage.wf _ Nat.lt_wfRel.wf) (fun x => x % 2 = 0)
    (fun x => x != 0) (fun x => x - 2)
    (fun x hx hc => by simp only [bne_iff_ne, ne_eq, InvImage, id] at *; omega) (2 * n)
    (by omega)

/-- Two loops in a row, the second starting from the result of the first: round `n` up to a
multiple of 3, then count its base-3 digits. -/
def twoLoops (n : Nat) : Nat :=
  let a := wf_while x := n while x % 3 != 0 do x + 1 termination_by (3 - x % 3) % 3
  (wf_while (x, k) := (a, 0) while x != 0 do (x / 3, k + 1) termination_by x
    decreasing_by intro p h; obtain ⟨x, k⟩ := p; simp at h ⊢; omega).2

/-- Calls `isqrt` (a function containing a loop, which becomes a global function of the
captured program) twice. -/
def isqrtSum (n : Nat) : Nat := isqrt n + isqrt (n + 1)

/-- A loop whose initial state is computed by a call (of the global function `isqrt`). -/
def evenSqrt (n : Nat) : Nat :=
  wf_while x := isqrt n while x % 2 != 0 do x + 1 termination_by (2 - x % 2) % 2

/-- A loop whose body calls a function: not supported by the capture (rejected). -/
def callInBody (n : Nat) : Nat :=
  wf_while x := n while x != 0 do min (x - 1) (sumDown x) termination_by x
    decreasing_by intro x h; simp at h; have := Nat.min_le_left (x - 1) (sumDown x); omega

end WhileEx
