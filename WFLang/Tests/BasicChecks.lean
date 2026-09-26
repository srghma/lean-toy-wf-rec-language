import RequestProject.WFLang.Tests.Basic

/-!
# Runtime checks for `Basic.lean`
-/

open WFLang

/-! ## Every captured program agrees with the Lean function on sample inputs -/

/-- info: true -/
#guard_msgs in
#eval (List.range 60).all fun i => (List.range 60).all fun j => ExPCL.gcd_run i j == gcd i j

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 5).all fun n => ExPCL.ack_run m n == Tco.ack m n

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun m => (List.range 12).all fun n =>
  ExPCL.diagonal_tr_run m n 0 == Tco.diagonal_tr m n 0 &&
  PCL.Term.eval ExPCL.diagonal_term m n == Tco.diagonal m n

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun n => (List.range 3).all fun a => (List.range 3).all fun b =>
  PCL.Term.eval ExPCL.hyper_term n a b == Tco.hyper n a b

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n => ExPCL.mc91Loop_run 1 n == Tco.mc91Loop 1 n

/-- info: true -/
#guard_msgs in
#eval (List.range 300).all fun n =>
  PCL.Term.eval ExPCL.isPow2_term n == isPow2 n &&
  PCL.Term.eval ExPCL.digitSum_term n == digitSum n &&
  PCL.Term.eval ExPCL.sumTo_term n 0 == sumTo n 0

/-- info: [false, true, true, false, true, false, false, false, true] -/
#guard_msgs in
#eval (List.range 9).map (PCL.Term.eval ExPCL.isPow2_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 8).all fun n =>
  PCL.Term.eval ExNonRec.mc91_term (95 + n) == Tco.mc91 (95 + n) &&
  (List.range 5).all fun a =>
    PCL.Term.eval ExNonRec.hyperBase_term n a == Tco.hyperBase n a &&
    PCL.Term.eval ExNonRec.pair_term n a == Tco.AckWithoutStackButUsingCantorPairing.pair n a

/-! ## Deep tail recursion

A tail call `let v := self args in ret v` of a global function is run as a jump
(`PCL/Lang/Fix.lean`, `fixS`), so tail-recursive programs run in constant stack: here
`sumTo 50000` (50 000 nested calls) and `diagonal_tr 300 0 0` (45 450 calls).  Before, the
interpreter aborted with a `deep recursion` error at about 2 500 nested calls
(`STACK_OVERFLOW.md`). -/

/-- info: true -/
#guard_msgs in
#eval PCL.Term.eval ExPCL.sumTo_term 50000 0 == sumTo 50000 0 &&
  ExPCL.diagonal_tr_run 300 0 0 == Tco.diagonal_tr 300 0 0

-- The uploaded functions that are rejected (`boom`, `iter`, `while` loops, higher-order
-- functions) are checked in `Sources.lean`.
