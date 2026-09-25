import RequestProject.WFLang.Examples.More
import RequestProject.WFLang.Examples.LangChecks

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
  PCL.Term.eval MorePCL.addK_term k n == addK k n &&
  Meas.Term.eval MoreMeas.addK_term k n == addK k n &&
  Guarded.Term.eval MoreWrapper.addK_guarded k n == addK k n &&
  GuardedAcc.Term.eval MoreWrapper.addK_guardedAcc k n == addK k n &&
  FreeCall.Term.eval MoreWrapper.addK_freeCall k n == addK k n &&
  Checked.Term.eval MoreWrapper.addK_checked k n == addK k n

/-- info: true -/
#guard_msgs in
#eval (List.range 6).all fun b => (List.range 6).all fun m => (List.range 8).all fun e =>
  PCL.Term.eval MorePCL.powMod_term b m e == powMod b m e &&
  Meas.Term.eval MoreMeas.powMod_term b m e == powMod b m e &&
  Guarded.Term.eval MoreWrapper.powMod_guarded b m e == powMod b m e

/-- info: [1, 2, 4, 1, 2, 4, 1, 2] -/
#guard_msgs in
#eval (List.range 8).map (PCL.Term.eval MorePCL.powMod_term 2 7)

/-- info: true -/
#guard_msgs in
#eval (List.range 8).all fun k => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.countDown_term k n 0 == countDown k n 0 &&
  Tail.Term.eval MoreTail.countDown_term k n 0 == countDown k n 0 &&
  Meas.Term.eval MoreMeas.countDown_term k n 0 == countDown k n 0 &&
  FreeCall.Term.eval MoreWrapper.countDown_freeCall k n 0 == countDown k n 0

/-- info: true -/
#guard_msgs in
#eval [true, false].all fun s => (List.range 8).all fun k => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.countAbove_term s k n == countAbove s k n &&
  Meas.Term.eval MoreMeas.countAbove_term s k n == countAbove s k n &&
  Checked.Term.eval MoreWrapper.countAbove_checked s k n == countAbove s k n

/-- info: true -/
#guard_msgs in
#eval [true, false].all fun b => (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.flipB_term b n == flipB b n &&
  Tail.Term.eval MoreTail.flipB_term b n == flipB b n &&
  Meas.Term.eval MoreMeas.flipB_term b n == flipB b n

/-! ## Structural recursion -/

/-- info: [1, 1, 2, 6, 24, 120, 720, 5040] -/
#guard_msgs in
#eval (List.range 8).map (PCL.Term.eval MorePCL.fact_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun n =>
  PCL.Term.eval MorePCL.fact_term n == fact n &&
  Meas.Term.eval MoreMeas.fact_term n == fact n &&
  Guarded.Term.eval MoreWrapper.fact_guarded n == fact n &&
  PCL.Term.eval MorePCL.evenS_term n == evenS n &&
  Meas.Term.eval MoreMeas.evenS_term n == evenS n &&
  GuardedAcc.Term.eval MoreWrapper.evenS_guardedAcc n == evenS n &&
  PCL.Term.eval MorePCL.fib_term n == fib n &&
  Meas.Term.eval MoreMeas.fib_term n == fib n &&
  FreeCall.Term.eval MoreWrapper.fib_freeCall n == fib n

/-- info: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89] -/
#guard_msgs in
#eval (List.range 12).map (Meas.Term.eval MoreMeas.fib_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 5).all fun k => (List.range 5).all fun m => (List.range 8).all fun n =>
  PCL.Term.eval MorePCL.addIter_term k m n == addIter k m n &&
  Tail.Term.eval MoreTail.addIter_term k m n == addIter k m n &&
  Meas.Term.eval MoreMeas.addIter_term k m n == addIter k m n &&
  Checked.Term.eval MoreWrapper.addIter_checked k m n == addIter k m n

/-! ## Calls to other functions -/

/-- info: true -/
#guard_msgs in
#eval (List.range 20).all fun n =>
  PCL.Term.eval MorePCL.sumDoubles_term n == sumDoubles n &&
  Meas.Term.eval MoreMeas.sumDoubles_term n == sumDoubles n &&
  Guarded.Term.eval MoreWrapper.sumDoubles_guarded n == sumDoubles n &&
  PCL.Term.eval MorePCL.gcdSum_term n == gcdSum n &&
  Meas.Term.eval MoreMeas.gcdSum_term n == gcdSum n &&
  PCL.Term.eval MorePCL.sumFacts_term n == sumFacts n &&
  Meas.Term.eval MoreMeas.sumFacts_term n == sumFacts n &&
  PCL.Term.eval MorePCL.chain_term n == chain n &&
  Meas.Term.eval MoreMeas.chain_term n == chain n &&
  PCL.Term.eval MorePCL.twoLoops_term n == twoLoops n &&
  Tail.Term.eval MoreTail.twoLoops_term n == twoLoops n &&
  Meas.Term.eval MoreMeas.twoLoops_term n == twoLoops n

/-- info: true -/
#guard_msgs in
#eval (List.range 15).all fun a => (List.range 15).all fun b =>
  PCL.Term.eval MorePCL.lcmGcd_term a b == lcmGcd a b &&
  Tail.Term.eval MoreTail.lcmGcd_term a b == lcmGcd a b &&
  Meas.Term.eval MoreMeas.lcmGcd_term a b == lcmGcd a b &&
  PCL.Term.eval MorePCL.countCoprime_term a b == countCoprime a b &&
  Meas.Term.eval MoreMeas.countCoprime_term a b == countCoprime a b &&
  PCL.Term.eval MorePCL.gcdLoop_term a b == gcdLoop a b &&
  Meas.Term.eval MoreMeas.gcdLoop_term a b == gcdLoop a b

/-- info: [0, 12, 12, 12, 12, 60, 12, 84, 24, 36, 60] -/
#guard_msgs in
#eval (List.range 11).map (PCL.Term.eval MorePCL.lcmGcd_term 12)

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n =>
  PCL.Term.eval MorePCL.mc91TR_term n == Tco.mc91TR n &&
  Tail.Term.eval MoreTail.mc91TR_term n == Tco.mc91TR n &&
  Meas.Term.eval MoreMeas.mc91TR_term n == Tco.mc91TR n

/-- info: true -/
#guard_msgs in
#eval (List.range 102).all fun n => PCL.Term.eval MorePCL.mc91TR_term n == 91

/-! ## Rejections -/

-- Mutual recursion is not supported (neither function is a self-recursive function whose body
-- only calls previously captured functions).
/-- info: rejected: #lean_wf_func_to_pcl: mutual recursion through More.Mutual.isEven is not supported -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term More.Mutual.isEven : PCL.Term ⟨[.nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_meas: mutual recursion through More.Mutual.isOdd is not supported -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term More.Mutual.isOdd : Meas.Term ⟨[.nat], .bool⟩)

-- A `Tail` loop body cannot run another loop.
/-- info: rejected: #lean_wf_func_to_term: unsupported call of gcd (only first-order functions on Nat and Bool, fully applied, can be called) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term gcdLoop : Tail.Term ⟨[.nat, .nat], .nat⟩)

-- The wrapper designs have a single recursive body, so they cannot call another recursive
-- function.
/-- info: rejected: #lean_wf_func_to_term: unsupported call of gcd (only first-order functions on Nat and Bool, fully applied, can be called) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term gcdSum : Guarded.Term ⟨[.nat], .nat⟩)

-- Not tail recursive.
/-- info: rejected: #lean_wf_func_to_tail: More.fact is not tail recursive: a recursive call is not in tail position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term fact : Tail.Term ⟨[.nat], .nat⟩)

-- A wrong signature is reported by the elaborator of the program type.
/-- info: rejected: Application type mismatch: The argument -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term addK : PCL.Term ⟨[.nat], .nat⟩)

/-! ### The remaining functions of the uploaded files -/

namespace TcoRest

-- verbatim from `TcoAck.lean`
def ackWhile (m n : Nat) : Nat := Id.run do
  let mut stack : List Nat := [m]
  let mut curN : Nat := n
  while !stack.isEmpty do
    match stack with
    | [] => break
    | top :: rest =>
      stack := rest
      if top == 0 then
        curN := curN + 1
      else if curN == 0 then
        stack := (top - 1) :: stack
        curN := 1
      else
        stack := (top - 1) :: top :: stack
        curN := curN - 1
  return curN

-- verbatim from `TcoAck.lean`
def isqrt (n : Nat) : Nat := Id.run do
  let mut x := n
  let mut y := (x + 1) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

-- verbatim from `TcoMc91.lean`
def mc91While (n : Nat) : Nat := Id.run do
  let mut c : Nat := 1
  let mut cur : Nat := n

  while c != 0 do
    if cur > 100 then
      cur := cur - 10
      c := c - 1
    else
      cur := cur + 11
      c := c + 1

  return cur

-- verbatim from `TcoHyper.lean`
def hyperWhile : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => Id.run do
    let mut acc := Tco.hyperBase (n + 1) a
    for _ in [0:b] do
      acc := hyperWhile n a acc
    return acc

end TcoRest

-- `while` loops have no termination proof (Lean builds them with `Loop.forIn`), so there is
-- nothing to capture: all are rejected, in every grammar.
/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoRest.ackWhile : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoRest.isqrt : Meas.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoRest.mc91While : Tail.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoRest.mc91While : Guarded.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_pcl: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoRest.hyperWhile : PCL.Term ⟨[.nat, .nat, .nat], .nat⟩)

-- Higher-order functions are outside the first-order languages.
/-- info: rejected: #lean_wf_func_to_term: unsupported type Nat → Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term TcoMore.hyperLoop : Meas.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Nat → Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.iter : Tail.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Tco.Safe n (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.boom : Meas.Term ⟨[.nat], .nat⟩)
