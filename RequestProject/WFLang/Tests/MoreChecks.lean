import RequestProject.WFLang.Tests.More
import RequestProject.WFLang.Tests.BasicChecks

/-!
# Runtime checks for `More.lean`, and functions that are rejected

* Every captured program is run and compared with the Lean function on sample inputs (the
  `#guard_msgs` blocks fail the build if an answer differs).
* `#expect_reject t` elaborates `t` and succeeds only if elaboration *fails*; it prints the first
  line of the error message, which `#guard_msgs` then checks.
-/

open WFLang
open More

/-! ## `#expect_reject` -/

open Lean Elab Command in
/-- `#expect_reject t`: elaborating `t` must fail; the first line of the error is reported. -/
elab "#expect_reject " t:term : command => liftTermElabM do
  let ok ← try
      discard <| Term.withoutErrToSorry <| Term.elabTermAndSynthesize t none
      pure true
    catch ex =>
      let msg ← ex.toMessageData.toString
      logInfo m!"rejected: {(msg.splitOn "\n").headD msg}"
      pure false
  if ok then throwError "#expect_reject: {t} was accepted"

/-! ## Fixed parameters -/

/-- info: true -/
#guard_msgs in
#eval (List.range 8).all fun k => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.addK_term k n == addK k n

/-- info: true -/
#guard_msgs in
#eval (List.range 6).all fun b => (List.range 6).all fun m => (List.range 8).all fun e =>
  PCL.Term.eval MorePCL.powMod_term b m e == powMod b m e

/-- info: [1, 2, 4, 1, 2, 4, 1, 2] -/
#guard_msgs in
#eval (List.range 8).map (PCL.Term.eval MorePCL.powMod_term 2 7)

/-- info: true -/
#guard_msgs in
#eval (List.range 8).all fun k => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.countDown_term k n 0 == countDown k n 0

/-- info: true -/
#guard_msgs in
#eval [true, false].all fun s => (List.range 8).all fun k => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.countAbove_term s k n == countAbove s k n

/-- info: true -/
#guard_msgs in
#eval [true, false].all fun b => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.flipB_term b n == flipB b n

/-! ## Structural recursion -/

/-- info: [1, 1, 2, 6, 24, 120, 720, 5040] -/
#guard_msgs in
#eval (List.range 8).map (PCL.Term.eval MorePCL.fact_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.fact_term n == fact n &&
  PCL.Term.eval MorePCL.evenS_term n == evenS n &&
  PCL.Term.eval MorePCL.fib_term n == fib n

/-- info: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89] -/
#guard_msgs in
#eval (List.range 12).map (PCL.Term.eval MorePCL.fib_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 5).all fun k => (List.range 5).all fun m => (List.range 8).all fun n =>
  PCL.Term.eval MorePCL.addIter_term k m n == addIter k m n

/-! ## Calls to other functions -/

/-- info: true -/
#guard_msgs in
#eval (List.range 20).all fun n =>
  PCL.Term.eval MorePCL.sumDoubles_term n == sumDoubles n &&
  PCL.Term.eval MorePCL.gcdSum_term n == gcdSum n &&
  PCL.Term.eval MorePCL.sumFacts_term n == sumFacts n &&
  PCL.Term.eval MorePCL.chain_term n == chain n &&
  PCL.Term.eval MorePCL.twoLoops_term n == twoLoops n

/-- info: true -/
#guard_msgs in
#eval (List.range 15).all fun a => (List.range 15).all fun b =>
  PCL.Term.eval MorePCL.lcmGcd_term a b == lcmGcd a b &&
  PCL.Term.eval MorePCL.countCoprime_term a b == countCoprime a b &&
  PCL.Term.eval MorePCL.gcdLoop_term a b == gcdLoop a b

/-- info: [0, 12, 12, 12, 12, 60, 12, 84, 24, 36, 60] -/
#guard_msgs in
#eval (List.range 11).map (PCL.Term.eval MorePCL.lcmGcd_term 12)

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n =>
  PCL.Term.eval MorePCL.mc91TR_term n == Tco.mc91TR n

/-- info: true -/
#guard_msgs in
#eval (List.range 102).all fun n => PCL.Term.eval MorePCL.mc91TR_term n == 91

/-! ## Rejections -/

-- Mutual recursion is not supported (neither function is a self-recursive function whose body
-- only calls previously captured functions).
/-- info: rejected: #lean_wf_func_to_term: mutual recursion through More.Mutual.isEven is not supported -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term More.Mutual.isEven : PCL.Term ⟨[.nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_term: mutual recursion through More.Mutual.isOdd is not supported -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term More.Mutual.isOdd : PCL.Term ⟨[.nat], .bool⟩)

-- A wrong signature is reported by the elaborator of the program type.
/-- info: rejected: Application type mismatch: The argument -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term addK : PCL.Term ⟨[.nat], .nat⟩)

-- The rejections of the functions of the uploaded files are checked in `Sources.lean`.
