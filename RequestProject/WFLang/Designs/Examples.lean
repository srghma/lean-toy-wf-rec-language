import RequestProject.WFLang.Designs.VC
import RequestProject.WFLang.Designs.Ext
import RequestProject.WFLang.Examples.Langs

/-!
# Examples for the alternative designs, and what happens when a measure is wrong

* `PCL-VC`: the captured `gcd` and `ack` (via `Certified.ofPCL`), and a hand-written `gcd`
  with a wrong relation, whose verification condition is provably false.
* `PCL-Ext`: `gcd` and `ack` written by hand, measures chosen from outside.  A wrong measure
  makes the checked evaluator return an **error**, and makes the certified evaluator
  impossible to call.
* `Meas` (the existing design), for comparison: with a wrong measure it silently returns the
  **default value** `0`.
-/

open WFLang

/-! ## `PCL-VC` -/

namespace ExVC
open VC

/-- `gcd`, captured into `PCL` by `#lean_wf_func_to_term`, then with its proofs erased. -/
def gcd_c : Certified ⟨[.nat, .nat], .nat⟩ := Certified.ofPCL ExPCL.gcd_term

theorem gcd_agree : ∀ m n, gcd_c.eval m n = gcd m n := by
  intro m n
  rw [gcd_c, Certified.ofPCL_eval]
  exact ExPCL.gcd_agree m n

def ack_c : Certified ⟨[.nat, .nat], .nat⟩ := Certified.ofPCL ExPCL.ack_term

theorem ack_agree : ∀ m n, ack_c.eval m n = Tco.ack m n := by
  intro m n
  rw [ack_c, Certified.ofPCL_eval]
  exact ExPCL.ack_agree m n

/-- The body of `gcd` in `PCL-VC`, for an arbitrary relation `R` (the syntax does not depend
on whether `R` is a correct termination argument). -/
def gcdBody (R : Env [.nat, .nat] → Env [.nat, .nat] → Prop) :
    Expr [.nat, .nat] (some (PCL.Self.top [.nat, .nat] .nat R)) .nat :=
  .ite (.bin (.beq .nat) (.var (.there .here)) (.lit .nat 0))
    (.ret (.var .here))
    (.call (.cons (.var (.there .here)) (.cons (.bin .mod (.var .here) (.var (.there .here))) .nil))
      (.ret (.var .here)))

/-- A wrong termination argument for `gcd`: "the first argument decreases". -/
def wrongR : Env [.nat, .nat] → Env [.nat, .nat] → Prop := fun y x => y.1 < x.1

/-- The program built with the wrong relation is syntactically fine … -/
def gcdWrong : Term ⟨[.nat, .nat], .nat⟩ :=
  .fix [.nat, .nat] .nat wrongR (InvImage.wf (fun x : Env [.nat, .nat] => x.1) Nat.lt_wfRel.wf)
    (gcdBody wrongR)
    (PExprs.ids _) (.ret (.var .here))

/-- … but its verification condition is false (at `gcd 4 6` the call `gcd 6 4` does not
decrease the first argument), so it can never be turned into a `Certified` program. -/
theorem gcdWrong_not_certified : ¬ ∀ x, gcdWrong.VC x := by
  intro h
  have := (h (4, 6, ())).1 (4, 6, ())
  simp [gcdBody, Expr.VC, wrongR, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq,
    PCL.Self.push, PCL.Self.top] at this

end ExVC

/-! ## `PCL-Ext`: measures chosen from outside -/

namespace ExExt
open Ext

/-- `gcd m n = if n == 0 then m else let v := gcd n (m % n) in v`. -/
def gcdP : Program ⟨[.nat, .nat], .nat⟩ where
  body :=
    .ite (.bin (.beq .nat) (.var (.there .here)) (.lit .nat 0))
      (.ret (.var .here))
      (.call (.cons (.var (.there .here)) (.cons (.bin .mod (.var .here) (.var (.there .here))) .nil))
        (.ret (.var .here)))

/-- The measure written in `termination_by n`. -/
def gcdμ : Measure [.nat, .nat] := fun x => (x.2.1, 0)

theorem gcdμ_ok : gcdP.Decreases gcdμ := by
  rintro ⟨m, n, ⟨⟩⟩
  simp only [gcdP, Body.VC, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, gcdμ, LexLt]
  refine ⟨fun _ => trivial, fun h => ⟨Or.inl ?_, fun _ => trivial⟩⟩
  simp at h
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem gcd_agree : ∀ m n, gcdP.eval gcdμ gcdμ_ok m n = gcd m n := by
  have : gcdP.eval gcdμ gcdμ_ok = gcd := by
    refine gcdP.eval_eq_of_eqn _ _ _ ?_
    rintro ⟨m, n, ⟨⟩⟩
    simp only [gcdP, uncurryEnv, Body.evalT, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq]
    rw [gcd]
    simp
  intro m n; rw [this]

/-- A wrong measure: "the first argument decreases". -/
def gcdWrongμ : Measure [.nat, .nat] := fun x => (x.1, 0)

/-- With the wrong measure, the checked evaluator stops with an error naming the offending
measures (`gcd 4 6` calls `gcd 6 4`, measure `6` is not below `4`). -/
theorem gcd_wrong_error :
    gcdP.runChecked gcdWrongμ (4, 6, ()) = .error (.notDecreasing (6, 0) (4, 0)) := by
  rw [Program.runChecked, checkedFix_eq]
  rfl

/-- Hence the wrong measure has no certificate: the certified evaluator cannot be called. -/
theorem gcd_wrong_not_certified : ¬ gcdP.Decreases gcdWrongμ :=
  gcdP.not_decreases_of_error _ _ _ gcd_wrong_error

/-- On inputs where the wrong measure happens to decrease, the checked run succeeds. -/
theorem gcd_wrong_ok : gcdP.runChecked gcdWrongμ (6, 4, ()) = .ok 2 := by
  have h3 : gcdP.runChecked gcdWrongμ (2, 0, ()) = .ok 2 := by
    rw [Program.runChecked, checkedFix_eq]; rfl
  have h2 : gcdP.runChecked gcdWrongμ (4, 2, ()) = .ok 2 := by
    rw [Program.runChecked, checkedFix_eq]
    rw [Program.runChecked] at h3
    simp [gcdP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq] at h3
    simp [gcdP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, LexLt,
      gcdWrongμ, h3]
  rw [Program.runChecked, checkedFix_eq]
  rw [Program.runChecked] at h2
  simp [gcdP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq] at h2
  simp [gcdP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, LexLt,
    gcdWrongμ, h2]

/-- `ack m n = if m == 0 then n + 1 else if n == 0 then ack (m-1) 1
               else let v := ack m (n-1) in let w := ack (m-1) v in w`. -/
def ackP : Program ⟨[.nat, .nat], .nat⟩ where
  body :=
    .ite (.bin (.beq .nat) (.var .here) (.lit .nat 0))
      (.ret (.bin .add (.var (.there .here)) (.lit .nat 1)))
      (.ite (.bin (.beq .nat) (.var (.there .here)) (.lit .nat 0))
        (.call (.cons (.bin .sub (.var .here) (.lit .nat 1)) (.cons (.lit .nat 1) .nil))
          (.ret (.var .here)))
        (.call (.cons (.var .here) (.cons (.bin .sub (.var (.there .here)) (.lit .nat 1)) .nil))
          (.call (.cons (.bin .sub (.var (.there .here)) (.lit .nat 1)) (.cons (.var .here) .nil))
            (.ret (.var .here)))))

/-- The lexicographic measure of `termination_by m n => (m, n)`. -/
def ackμ : Measure [.nat, .nat] := fun x => (x.1, x.2.1)

theorem ackμ_ok : ackP.Decreases ackμ := by
  rintro ⟨m, n, ⟨⟩⟩
  simp [ackP, Body.VC, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, ackμ, LexLt]
  exact fun hm => ⟨fun _ => by omega, fun hn => ⟨by omega, fun _ => by omega⟩⟩

theorem ack_agree : ∀ m n, ackP.eval ackμ ackμ_ok m n = Tco.ack m n := by
  have : ackP.eval ackμ ackμ_ok = Tco.ack := by
    refine ackP.eval_eq_of_eqn _ _ _ ?_
    rintro ⟨m, n, ⟨⟩⟩
    simp only [ackP, uncurryEnv, Body.evalT, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq]
    rcases m with _ | m <;> rcases n with _ | n <;> simp [Tco.ack]
  intro m n; rw [this]

/-- A measure that is correct for `ack` but different from the one Lean used: the value is
the same (`eval_measure_irrelevant`). -/
def ackμ' : Measure [.nat, .nat] := fun x => (2 * x.1, x.2.1)

theorem ackμ'_ok : ackP.Decreases ackμ' := by
  rintro ⟨m, n, ⟨⟩⟩
  simp [ackP, Body.VC, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, ackμ', LexLt]
  exact fun hm => ⟨fun _ => by omega, fun hn => ⟨by omega, fun _ => by omega⟩⟩

example : ackP.eval ackμ' ackμ'_ok = ackP.eval ackμ ackμ_ok :=
  ackP.eval_measure_irrelevant _ _ _ _

/-- A wrong measure for `ack`: only the second argument. -/
def ackWrongμ : Measure [.nat, .nat] := fun x => (x.2.1, 0)

/-- `ack 1 1` calls `ack 1 0` (fine: `0 < 1`), which calls `ack 0 1`, where the measure goes
up from `0` to `1`: the checked run stops with that error. -/
theorem ack_wrong_error :
    ackP.runChecked ackWrongμ (1, 1, ()) = .error (.notDecreasing (1, 0) (0, 0)) := by
  have h2 : ackP.runChecked ackWrongμ (1, 0, ()) = .error (.notDecreasing (1, 0) (0, 0)) := by
    rw [Program.runChecked, checkedFix_eq]; rfl
  rw [Program.runChecked] at h2
  simp [ackP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq] at h2
  rw [Program.runChecked, checkedFix_eq]
  simp [ackP, Body.evalE, PExpr.eval, PExprs.eval, BinOp.eval, Var.get, Ty.beq, LexLt,
    ackWrongμ, h2]

theorem ack_wrong_not_certified : ¬ ackP.Decreases ackWrongμ :=
  ackP.not_decreases_of_error _ _ _ ack_wrong_error

/-- Fuel computed from the certified measure of `gcd` (its second argument) is always enough;
since `runFuel` is structural, concrete runs are checked by `rfl` (kernel evaluation). -/
theorem gcd_fuel (m n : Nat) : gcdP.runFuel (n + 1) (m, n, ()) = .ok (gcd m n) := by
  have := gcdP.runFuel_measure (fun x => x.2.1) gcdμ_ok (m, n, ())
  rw [this]
  congr 1
  have h := gcd_agree m n
  simp only [Program.eval, curryEnv] at h
  exact h

example : gcdP.runFuel 7 (12, 18, ()) = .ok 6 := rfl

/-- Too little fuel is reported as an error, not as a default value. -/
example : gcdP.runFuel 1 (12, 18, ()) = .error .outOfFuel := rfl

/-! ### Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 40).all fun i => (List.range 40).all fun j =>
  (gcdP.runChecked gcdμ (i, j, ())).toOption == some (gcd i j) &&
  (gcdP.runFuel (j + 1) (i, j, ())).toOption == some (gcd i j) &&
  gcdP.eval gcdμ gcdμ_ok i j == gcd i j

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 5).all fun n =>
  (ackP.runChecked ackμ (m, n, ())).toOption == some (Tco.ack m n) && ackP.eval ackμ ackμ_ok m n == Tco.ack m n

/-- info: Except.error (WFLang.Ext.Error.notDecreasing (6, 0) (4, 0)) -/
#guard_msgs in
#eval gcdP.runChecked gcdWrongμ (4, 6, ())

end ExExt

/-! ## `Meas`: a wrong measure silently gives the default value -/

namespace ExMeasWrong
open Meas

/-- `gcd` in `Meas`, with the wrong measure `(m, 0)`. -/
def gcdWrong : Term ⟨[.nat, .nat], .nat⟩ :=
  .fix [.nat, .nat] .nat (.var .here) (.lit .nat 0)
    (.ite (.bin (.beq .nat) (.var (.there .here)) (.lit .nat 0))
      (.var .here)
      (.call (.cons (.var (.there .here)) (.cons (.bin .mod (.var .here) (.var (.there .here))) .nil))))
    (.cons (.var .here) (.cons (.var (.there .here)) .nil))

/-- The `Meas` evaluator answers `0` for `gcd 4 6` (the correct answer is `2`): the call
`gcd 6 4` fails the measure check and is replaced by the default value of `nat`. -/
theorem gcdWrong_4_6 : Term.eval gcdWrong 4 6 = 0 := by
  simp only [Term.eval, curryEnv, gcdWrong, Expr.eval, Exprs.eval]
  rw [measFix_eq]
  rfl

example : gcd 4 6 = 2 := by
  rw [gcd, gcd, gcd, gcd]; simp

/-- info: 0 -/
#guard_msgs in
#eval Term.eval gcdWrong 4 6

end ExMeasWrong
