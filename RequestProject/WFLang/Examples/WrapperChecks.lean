import RequestProject.WFLang.Examples.Wrapper

/-!
# Runtime checks for the wrapper designs

These run compiled code (the terms and evaluators are imported), so they also exercise the
generated C of the evaluators.
-/

/-! ## Quick runtime checks (all four evaluators agree with Lean's `gcd`). -/

/-- info: [6, 6, 6, 6, 6] -/
#guard_msgs in
#eval [gcd 12 18, ExGuarded.gcd_run 12 18, ExGuardedAcc.gcd_run 12 18,
  ExFreeCall.gcd_run 12 18, ExChecked.gcd_run 12 18]

/-- info: (36, true, false, 55) -/
#guard_msgs in
#eval (WFLang.Guarded.Term.eval ExGuarded.digitSum_term 9999,
  WFLang.Guarded.Term.eval ExGuarded.isPow2_term 1024,
  WFLang.Checked.Term.eval ExChecked.isPow2_term 1000,
  WFLang.FreeCall.Term.eval ExFreeCall.sumTo_term 10 0)

-- Many inputs: all evaluators agree with the native `gcd`.
/-- info: true -/
#guard_msgs in
#eval (List.range 200).all fun i =>
  let m := 1000003 * i + 17
  let n := 7919 * i + 5
  ExGuarded.gcd_run m n == gcd m n && ExGuardedAcc.gcd_run m n == gcd m n &&
  ExFreeCall.gcd_run m n == gcd m n && ExChecked.gcd_run m n == gcd m n

namespace Tco
open WFLang


/-! ## Runtime checks: every evaluator agrees with the Lean function -/

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 4).all fun n =>
  G.ack_run m n == ack m n && GA.ack_run m n == ack m n &&
  FC.ack_run m n == ack m n && CK.ack_run m n == ack m n

/-- info: true -/
#guard_msgs in
#eval (List.range 15).all fun m => (List.range 15).all fun n =>
  G.diagonal_tr_run m n 0 == diagonal_tr m n 0 && GA.diagonal_tr_run m n 0 == diagonal_tr m n 0 &&
  FC.diagonal_tr_run m n 0 == diagonal_tr m n 0 && CK.diagonal_tr_run m n 0 == diagonal_tr m n 0 &&
  Guarded.Term.eval G.diagonal_term m n == diagonal m n

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun n => (List.range 3).all fun a => (List.range 3).all fun b =>
  Guarded.Term.eval G.hyper_term n a b == hyper n a b &&
  FreeCall.Term.eval FC.hyper_term n a b == hyper n a b &&
  Checked.Term.eval CK.hyper_term n a b == hyper n a b

/-- info: true -/
#guard_msgs in
#eval (List.range 200).all fun n =>
  G.mc91Loop_run 1 n == mc91Loop 1 n && GA.mc91Loop_run 1 n == mc91Loop 1 n &&
  FC.mc91Loop_run 1 n == mc91Loop 1 n && CK.mc91Loop_run 1 n == mc91Loop 1 n &&
  Guarded.Term.eval G.mc91_term n == mc91 n

end Tco
