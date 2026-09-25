import RequestProject.WFLang.Tests.Sources
import RequestProject.WFLang.Tests.While

/-!
# Lean's own `while` loops

Functions written with Lean's `while` in `do` notation (`Lean.Loop.forIn`, a `partial def`) are
captured through their well-founded version (`Capture/LeanWhile.lean`):

* `lean_while_to_wf f termination_by …` generates `f.loop_i` (each loop as a tail-recursive
  well-founded function on its mutable variables), `f.wf` and
  `f.eq_wf : LoopLaw → ∀ xs, f xs = f.wf xs`;
* `#lean_wf_func_to_term f` captures `f.wf` (running `lean_while_to_wf f` first, with Lean's
  guessed measure, if it was not run);
* `wf_agree` proves `∀ xs, Term.eval f_term xs = f xs` from a hypothesis `h : LoopLaw`, the
  unfolding law of `while` (`Core/LeanWhile.lean`): nothing can be proved about Lean's `while`
  without it, since `Lean.Loop.forIn` is opaque to the logic.

Below: the uploaded `while` functions (`Tco.…`, `Tests/Functions.lean`), other loops (`break`,
two loops in a row, nested loops, `match` in the body, `Int`/`Bool`/list state, a function calling
a function with a loop), the formerly omitted `diagonalWhile_eq`, runtime checks against the
compiled Lean functions, and the loops that are still rejected.
-/

open WFLang

/-! ## The uploaded `while` functions -/

-- Newton's integer square root: Lean guesses the measure (`x`).
open Tco.AckWithoutStackButUsingCantorPairing in
lean_while_to_wf isqrt

-- The measures of the tail-recursive versions `Tco.diagonal_tr` and `Tco.mc91Loop`.
lean_while_to_wf Tco.diagonalWhile
  termination_by (m + n, m)

lean_while_to_wf Tco.mc91While
  termination_by 2 * (111 - cur) + 21 * c

namespace LeanWhilePCL
open PCL Tco.AckWithoutStackButUsingCantorPairing

def isqrt_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term isqrt
theorem isqrt_agree (h : LoopLaw) : ∀ n, Term.eval isqrt_term n = isqrt n := by wf_agree

-- `unpairLeft`/`unpairRight` are not recursive; they call `isqrt`, whose loop is inlined.
def unpairLeft_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term unpairLeft
theorem unpairLeft_agree (h : LoopLaw) :
    ∀ z, Term.eval unpairLeft_term z = unpairLeft z := by wf_agree

def unpairRight_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term unpairRight
theorem unpairRight_agree (h : LoopLaw) :
    ∀ z, Term.eval unpairRight_term z = unpairRight z := by wf_agree

def diagonalWhile_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.diagonalWhile
theorem diagonalWhile_agree (h : LoopLaw) :
    ∀ m n, Term.eval diagonalWhile_term m n = Tco.diagonalWhile m n := by wf_agree

def mc91While_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91While
theorem mc91While_agree (h : LoopLaw) :
    ∀ n, Term.eval mc91While_term n = Tco.mc91While n := by wf_agree

-- Each program has one loop (a recursive join point) and no global function.
/-- info: [(1, 0), (1, 0), (1, 0), (1, 0), (1, 0)] -/
#guard_msgs in
#eval [(isqrt_term.loops, isqrt_term.nglobals), (unpairLeft_term.loops, unpairLeft_term.nglobals),
  (unpairRight_term.loops, unpairRight_term.nglobals),
  (diagonalWhile_term.loops, diagonalWhile_term.nglobals),
  (mc91While_term.loops, mc91While_term.nglobals)]

end LeanWhilePCL

/-! ## Theorems about the uploaded `while` functions

`diagonalWhile_eq` is the theorem of the uploaded `TcoDiagonal.lean` that was left out of
`Tests/SourceProofs.lean`, because nothing could be proved about a `while` loop: under the
unfolding law of `while` it follows from the loop function `Tco.diagonalWhile.loop_1` (state
`(acc, m, n)`) by functional induction. -/

namespace LeanWhileProofs

theorem diagonalWhile_loop (acc m n : Nat) :
    (Tco.diagonalWhile.loop_1 acc m n).1 = acc + Tco.diagonal m n := by
  fun_induction Tco.diagonalWhile.loop_1 acc m n with
  | case1 acc m n _ _ hm _ _ ih =>
    rw [ih]
    show acc + 1 + Tco.diagonal (m - 1) (n + 1) = acc + Tco.diagonal m n
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Tco.diagonal.eq_3]
    simp only [Nat.add_sub_cancel]
    omega
  | case2 acc m n hc _ hm _ _ ih =>
    rw [ih]
    show acc + 1 + Tco.diagonal (n - 1) 0 = acc + Tco.diagonal m n
    have hm0 : m = 0 := by omega
    subst hm0
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp_all; omega⟩
    rw [Tco.diagonal.eq_2]
    simp only [Nat.add_sub_cancel]
    omega
  | case3 acc m n hc =>
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, not_or,
      Classical.not_not] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [Tco.diagonal.eq_1]
    rfl

/-- **`diagonalWhile m n = diagonal m n`** (the theorem of the uploaded file), under the
unfolding law of `while`. -/
theorem diagonalWhile_eq (h : LoopLaw) (m n : Nat) : Tco.diagonalWhile m n = Tco.diagonal m n := by
  rw [Tco.diagonalWhile.eq_wf h, Tco.diagonalWhile.wf, diagonalWhile_loop, Nat.zero_add]

theorem mc91While_loop (c cur : Nat) : (Tco.mc91While.loop_1 c cur).2 = Tco.mc91Loop c cur := by
  fun_induction Tco.mc91While.loop_1 c cur with
  | case1 c cur hc hcur _ _ ih =>
    rw [ih]
    show Tco.mc91Loop (c - 1) (cur - 10) = Tco.mc91Loop c cur
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by simp_all; omega⟩
    rw [Tco.mc91Loop.eq_2, dif_pos hcur, Nat.add_sub_cancel]
  | case2 c cur hc hcur _ _ ih =>
    rw [ih]
    show Tco.mc91Loop (c + 1) (cur + 11) = Tco.mc91Loop c cur
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by simp_all; omega⟩
    conv_rhs => rw [Tco.mc91Loop.eq_2]
    rw [dif_neg hcur]
  | case3 c cur hc =>
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
    subst hc
    rw [Tco.mc91Loop.eq_1]

/-- `mc91While n = mc91TR n`, under the unfolding law of `while`. -/
theorem mc91While_eq (h : LoopLaw) (n : Nat) : Tco.mc91While n = Tco.mc91TR n := by
  rw [Tco.mc91While.eq_wf h, Tco.mc91While.wf, mc91While_loop, Tco.mc91TR]

/-- The `PCL` program captured from the recursive `diagonal` computes `diagonalWhile`. -/
theorem diagonal_term_eq_diagonalWhile (h : LoopLaw) :
    ∀ m n, PCL.Term.eval ExPCL.diagonal_term m n = Tco.diagonalWhile m n := by
  intro m n
  rw [ExPCL.diagonal_agree, diagonalWhile_eq h]

end LeanWhileProofs

/-! ## Other loops -/

namespace LeanWhileEx

/-- Euclid's algorithm. -/
def gcdW (a b : Nat) : Nat := Id.run do
  let mut a := a
  let mut b := b
  while b != 0 do
    let t := b
    b := a % b
    a := t
  return a

lean_while_to_wf gcdW
  termination_by b
  decreasing_by all_goals exact Nat.mod_lt _ (by simp_all; omega)

/-- `break`: the first `i` with `i * i ≥ n` (or `n`). -/
def firstSq (n : Nat) : Nat := Id.run do
  let mut i := 0
  while i < n do
    if i * i ≥ n then break
    i := i + 1
  return i

/-- Two loops in a row: round `n` up to a multiple of 3, then count its base-3 digits. -/
def twoLoops (n : Nat) : Nat := Id.run do
  let mut x := n
  while x % 3 != 0 do
    x := x + 1
  let mut k := 0
  while x != 0 do
    x := x / 3
    k := k + 1
  return k

lean_while_to_wf twoLoops
  termination_by (3 - x % 3) % 3
  termination_by x

/-- Nested loops: `∑_{i < n} ∑_{j < i} j`. -/
def nested (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    let mut j := 0
    while j < i do
      s := s + j
      j := j + 1
    i := i + 1
  return s

/-- A `match` on a list in the body. -/
def sumList (l : List Nat) : Nat := Id.run do
  let mut l := l
  let mut s := 0
  while !l.isEmpty do
    match l with
    | [] => break
    | x :: r =>
      s := s + x
      l := r
  return s

lean_while_to_wf sumList
  termination_by l.length

/-- `Int` and `Bool` mutable variables. -/
def countDown (k : Int) : Nat := Id.run do
  let mut x := k
  let mut steps := 0
  let mut flag := false
  while x > 0 do
    x := x - 2
    steps := steps + 1
    flag := !flag
  return if flag then steps else steps + 100

lean_while_to_wf countDown
  termination_by x.toNat

/-- A function calling a function with a loop (`gcdW`). -/
def lcmW (a b : Nat) : Nat := if a = 0 then 0 else a * b / gcdW a b

/-- A loop reading a parameter of the function (`n`) and a value computed before it (`lim`). -/
def countMultiples (n d : Nat) : Nat := Id.run do
  let lim := n * n
  let mut i := 0
  let mut c := 0
  while i < lim do
    if i % (d + 1) == 0 then c := c + 1
    i := i + 1
  return c

end LeanWhileEx

namespace LeanWhileExPCL
open PCL LeanWhileEx

def gcdW_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdW
theorem gcdW_agree (h : LoopLaw) : ∀ a b, Term.eval gcdW_term a b = gcdW a b := by wf_agree

def firstSq_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term firstSq
theorem firstSq_agree (h : LoopLaw) : ∀ n, Term.eval firstSq_term n = firstSq n := by wf_agree

def twoLoops_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term twoLoops
theorem twoLoops_agree (h : LoopLaw) : ∀ n, Term.eval twoLoops_term n = twoLoops n := by
  wf_agree

def nested_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term nested
theorem nested_agree (h : LoopLaw) : ∀ n, Term.eval nested_term n = nested n := by wf_agree

def sumList_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term sumList
theorem sumList_agree (h : LoopLaw) : ∀ l, Term.eval sumList_term l = sumList l := by wf_agree

def countDown_term : Term ⟨[.int], .nat⟩ := #lean_wf_func_to_term countDown
theorem countDown_agree (h : LoopLaw) : ∀ k, Term.eval countDown_term k = countDown k := by
  wf_agree

def lcmW_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term lcmW
theorem lcmW_agree (h : LoopLaw) : ∀ a b, Term.eval lcmW_term a b = lcmW a b := by wf_agree

def countMultiples_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term countMultiples
theorem countMultiples_agree (h : LoopLaw) :
    ∀ n d, Term.eval countMultiples_term n d = countMultiples n d := by wf_agree

-- The number of loops (recursive join points) of each program: one per `while`.
/-- info: [1, 1, 2, 2, 1, 1, 1, 1] -/
#guard_msgs in
#eval [gcdW_term.loops, firstSq_term.loops, twoLoops_term.loops, nested_term.loops,
  sumList_term.loops, countDown_term.loops, lcmW_term.loops, countMultiples_term.loops]

end LeanWhileExPCL

/-! ## The generated declarations

The loop of `gcdW` as a tail-recursive well-founded function, and the unfolding law of `while`
turned into its equation. -/

/--
info: LeanWhileEx.gcdW.loop_1 (a b : ℕ) : ℕ × ℕ
-/
#guard_msgs in
#check LeanWhileEx.gcdW.loop_1

/--
info: LeanWhileEx.gcdW.eq_wf (h : LoopLaw) (a b : ℕ) : LeanWhileEx.gcdW a b = LeanWhileEx.gcdW.wf a b
-/
#guard_msgs in
#check LeanWhileEx.gcdW.eq_wf

/-! ## Runtime checks against the compiled Lean functions

The compiled code of Lean's `while` is the real loop (not the opaque constant of the logic), so
these compare the captured programs with the uploaded functions as they run. -/

section
open Tco.AckWithoutStackButUsingCantorPairing

/-- info: true -/
#guard_msgs in
#eval (List.range 300).all fun n => PCL.Term.eval LeanWhilePCL.isqrt_term n == isqrt n

/-- info: true -/
#guard_msgs in
#eval (List.range 300).all fun z =>
  PCL.Term.eval LeanWhilePCL.unpairLeft_term z == unpairLeft z &&
  PCL.Term.eval LeanWhilePCL.unpairRight_term z == unpairRight z

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun m => (List.range 12).all fun n =>
  PCL.Term.eval LeanWhilePCL.diagonalWhile_term m n == Tco.diagonalWhile m n

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n => PCL.Term.eval LeanWhilePCL.mc91While_term n == Tco.mc91While n

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun a => (List.range 30).all fun b =>
  PCL.Term.eval LeanWhileExPCL.gcdW_term a b == LeanWhileEx.gcdW a b &&
  PCL.Term.eval LeanWhileExPCL.lcmW_term a b == LeanWhileEx.lcmW a b

/-- info: true -/
#guard_msgs in
#eval (List.range 40).all fun n =>
  PCL.Term.eval LeanWhileExPCL.firstSq_term n == LeanWhileEx.firstSq n &&
  PCL.Term.eval LeanWhileExPCL.twoLoops_term n == LeanWhileEx.twoLoops n &&
  PCL.Term.eval LeanWhileExPCL.nested_term n == LeanWhileEx.nested n &&
  PCL.Term.eval LeanWhileExPCL.countDown_term (n - 20 : Int) == LeanWhileEx.countDown (n - 20) &&
  PCL.Term.eval LeanWhileExPCL.countMultiples_term n 3 == LeanWhileEx.countMultiples n 3

/-- info: true -/
#guard_msgs in
#eval [[], [1], [3, 1, 4, 1, 5], List.range 20].all fun l =>
  PCL.Term.eval LeanWhileExPCL.sumList_term l == LeanWhileEx.sumList l

end

/-! ## Still rejected -/

namespace LeanWhileRejected

/-- `return` inside the loop: the loop state holds an `Option` (not a `PCL` type). -/
def findDiv (n : Nat) : Nat := Id.run do
  let mut d := 2
  while d < n do
    if n % d == 0 then return d
    d := d + 1
  return n

/-- A recursive function containing a loop. -/
def recLoop : Nat → Nat
  | 0 => 0
  | k + 1 => Id.run do
    let mut i := 0
    while i < k do
      i := i + 2
    return i + recLoop k

end LeanWhileRejected

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term LeanWhileRejected.findDiv : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term LeanWhileRejected.recLoop : PCL.Term ⟨[.nat], .nat⟩)
