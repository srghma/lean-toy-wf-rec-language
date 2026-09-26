import RequestProject.WFLang.Tests.Functions
import Mathlib.Logic.Function.Iterate

/-!
# The theorems of the uploaded files

The proofs that accompanied the functions of the uploaded `Tco*.lean` files, about the Lean
functions in namespace `Tco` (`Functions.lean`).  They are kept here because the uploaded files
were removed; `Sources.lean` uses them to transfer the `PCL` agreement theorems to the
functions that `PCL` cannot capture directly (`ack2`, `hyperTCO`, `hyperWhile`).

Changes with respect to the uploaded files:
* `mc91Loop_eq`: the uploaded proof used `grind => instantiate only [mc91Loop, iter]`; it is
  proved here through `Function.iterate` instead (see the last item).
* `diagonalWhile_eq` (`diagonalWhile m n = diagonal m n`) is about a function written with
  Lean's `while`; it is proved in `Tests/LeanWhile.lean` (`LeanWhileProofs.diagonalWhile_eq`),
  through the capture of `diagonalWhile` and the unfolding law of `while` (`WFLang.loopLaw`, a
  theorem in Lean v4.34, where `while` is defined in the logic).
* The two iteration helpers `iter` and `hyperLoop` are identified with Mathlib's
  `Function.iterate` (`f^[n]`, lemmas `iter_eq_iterate`, `hyperLoop_eq_iterate`), and the
  proofs of `hyperLoop_step` and `mc91Loop_eq` use Mathlib's iterate lemmas instead of
  unfolding the helpers.
-/

namespace Tco

/-! ## The iteration helpers are Mathlib's `Function.iterate` -/

theorem iter_eq_iterate (f : Nat → Nat) (c x : Nat) : iter f c x = f^[c] x := by
  induction c generalizing x with
  | zero => rfl
  | succ c ih => rw [iter, ih, Function.iterate_succ_apply]

theorem hyperLoop_eq_iterate (f : Nat → Nat) (b acc : Nat) : hyperLoop f b acc = f^[b] acc := by
  induction b generalizing acc with
  | zero => rfl
  | succ b ih => rw [hyperLoop, ih, Function.iterate_succ_apply]

/-! ## From `TcoAck.lean` -/

-- Equivalence theorem: ack2 m n = ack m n
theorem ack2_eq_ack (m n : Nat) : ack2 m n = ack m n := by
  induction m, n using ack.induct with
  | case1 n =>
    -- ack 0 n = n + 1
    simp [ack2, ack]
  | case2 m ih =>
    -- ack (m + 1) 0 = ack m 1
    -- ack2 (m + 1) 0 = ackInner (ack2 m) 0 = ack2 m 1
    have h : ack2 (m + 1) 0 = ack2 m 1 := by rfl
    rw [h, ih]
    simp [ack]
  | case3 m n ih1 ih2 =>
    -- ack (m + 1) (n + 1) = ack m (ack (m + 1) n)
    -- ack2 (m + 1) (n + 1) = ack2 m (ack2 (m + 1) n)
    have h : ack2 (m + 1) (n + 1) = ack2 m (ack2 (m + 1) n) := by rfl
    grind [= ack, = ack2]

/-! ## From `TcoDiagonal.lean` -/

/-! ### Unfolding lemmas for `diagonal` -/

@[simp] theorem diagonal_zero_zero : diagonal 0 0 = 0 := by rw [diagonal]

@[simp] theorem diagonal_zero_succ (n : Nat) : diagonal 0 (n + 1) = diagonal n 0 + 1 := by
  rw [diagonal]

@[simp] theorem diagonal_succ (m n : Nat) : diagonal (m + 1) n = diagonal m (n + 1) + 1 := by
  rw [diagonal]

-- Lemma: Generalized accumulator invariant
theorem diagonal_tr_eq (m n acc : Nat) :
    diagonal_tr m n acc = diagonal m n + acc := by
  induction m, n using diagonal.induct generalizing acc with
  | case1 =>
    -- Base case: m = 0, n = 0
    unfold diagonal diagonal_tr
    omega
  | case2 n ih =>
    -- Step: m = 0, n + 1
    unfold diagonal diagonal_tr
    rw [ih (acc + 1)]
    omega
  | case3 m n ih =>
    -- Step: m + 1, n
    unfold diagonal diagonal_tr
    rw [ih (acc + 1)]
    omega

-- Main Theorem: diagonal_tr with acc = 0 equals diagonal
theorem diagonal_tr_zero_eq_diagonal (m n : Nat) :
    diagonal_tr m n 0 = diagonal m n := by
  rw [diagonal_tr_eq]
  omega

/-! ## From `TcoHyper.lean` -/

-- Key property of `hyperLoop`: pulling `f` outside the loop
theorem hyperLoop_step (f : Nat → Nat) (b acc : Nat) :
    hyperLoop f (b + 1) acc = f (hyperLoop f b acc) := by
  simp only [hyperLoop_eq_iterate, Function.iterate_succ_apply']

-- Base values match at b = 0
theorem hyperBase_eq (n a : Nat) : hyperBase (n + 1) a = hyper (n + 1) a 0 := by
  cases n with
  | zero => simp [hyperBase, hyper]
  | succ n =>
    cases n with
    | zero => simp [hyperBase, hyper]
    | succ n => simp [hyperBase, hyper]

-- Main equivalence theorem: hyperTCO n a b = hyper n a b
theorem hyperTCO_eq : ∀ n a b, hyperTCO n a b = hyper n a b := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp [hyperTCO, hyper]
  | succ n ih =>
    intro a b
    have hfun : hyperTCO n a = hyper n a := funext fun x => ih a x
    have hbase : hyperBase (n + 1) a = hyper (n + 1) a 0 := hyperBase_eq n a
    have hloop : ∀ b, hyperLoop (hyper n a) b (hyper (n + 1) a 0) = hyper (n + 1) a b := by
      intro b
      induction b with
      | zero => rfl
      | succ b ihb =>
        rw [hyperLoop_step, ihb]
        simp [hyper]
    show hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a) = hyper (n + 1) a b
    rw [hfun, hbase, hloop]

/-! ### Added: `hyperWhile` computes `hyper`

Not in the uploaded file.  Unlike a `while` loop, `for _ in [0:b]` is a fold over a list, so
it can be reasoned about. -/

theorem foldl_range'_eq_hyperLoop (f : Nat → Nat) (s b acc : Nat) :
    List.foldl (fun b _ => f b) acc (List.range' s b) = hyperLoop f b acc := by
  induction b generalizing s acc with
  | zero => rfl
  | succ b ih => simp [List.range'_succ, hyperLoop, ih]

theorem hyperWhile_eq_hyper : ∀ n a b, hyperWhile n a b = hyper n a b := by
  intro n
  induction n with
  | zero => intro a b; simp [hyperWhile, hyper]
  | succ n ih =>
    intro a b
    rw [← hyperTCO_eq]
    have hfun : hyperWhile n a = hyperTCO n a :=
      funext fun x => (ih a x).trans (hyperTCO_eq n a x).symm
    simp [hyperWhile, hyperTCO, hfun, foldl_range'_eq_hyperLoop]

/-! ## From `TcoMc91.lean` -/

-- Closed-form characterization of McCarthy 91
theorem mc91_spec (n : Nat) : mc91 n = if n > 100 then n - 10 else 91 := by
  rfl

-- Step 1: Characterize single step when n > 100
theorem mc91_step_gt {n : Nat} (h : n > 100) : mc91 n = n - 10 := by
  unfold mc91
  split
  · rfl
  · omega

-- Step 2: Characterize nested double-step when n ≤ 100
-- `repeat (first | split | omega)` safely splits ifs and closes arithmetic leaves
theorem mc91_step_le {n : Nat} (h : n ≤ 100) : mc91 (mc91 (n + 11)) = mc91 n := by
  unfold mc91
  repeat (first | split | omega)

-- Step 3: Loop invariant for arbitrary pending call count `c`
theorem mc91Loop_eq (c n : Nat) : mc91Loop c n = iter mc91 c n := by
  rw [iter_eq_iterate]
  induction c, n using mc91Loop.induct with
  | case1 n => simp [mc91Loop]
  | case2 c n hgt ih =>
    rw [mc91Loop, dite_eq_left hgt, ih, Function.iterate_succ_apply, mc91_step_gt hgt]
  | case3 c n hle ih =>
    rw [mc91Loop, dite_eq_right hle, ih, Function.iterate_succ_apply, Function.iterate_succ_apply,
      mc91_step_le (by omega), Function.iterate_succ_apply]

-- Main Theorem: mc91TR n = mc91 n
theorem mc91TR_eq_mc91 (n : Nat) : mc91TR n = mc91 n := by
  unfold mc91TR
  rw [mc91Loop_eq 1 n]
  rfl

/-! ## From `TcoBoom.lean` -/

example : boom 1 (by simp [Safe]) = 0 := by grind only [boom]

end Tco
