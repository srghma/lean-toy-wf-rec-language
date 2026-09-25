import RequestProject.WFLang.Examples.Langs

/-!
# Runtime checks for the three languages, and the functions they reject
-/

open WFLang

/-! ## Every evaluator agrees with the Lean function on sample inputs -/

/-- info: true -/
#guard_msgs in
#eval (List.range 60).all fun i => (List.range 60).all fun j =>
  ExPCL.gcd_run i j == gcd i j && ExTail.gcd_run i j == gcd i j && ExMeas.gcd_run i j == gcd i j

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 5).all fun n =>
  ExPCL.ack_run m n == Tco.ack m n && ExMeas.ack_run m n == Tco.ack m n

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun m => (List.range 12).all fun n =>
  ExPCL.diagonal_tr_run m n 0 == Tco.diagonal_tr m n 0 &&
  ExTail.diagonal_tr_run m n 0 == Tco.diagonal_tr m n 0 &&
  ExMeas.diagonal_tr_run m n 0 == Tco.diagonal_tr m n 0 &&
  PCL.Term.eval ExPCL.diagonal_term m n == Tco.diagonal m n &&
  Meas.Term.eval ExMeas.diagonal_term m n == Tco.diagonal m n

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun n => (List.range 3).all fun a => (List.range 3).all fun b =>
  PCL.Term.eval ExPCL.hyper_term n a b == Tco.hyper n a b &&
  Meas.Term.eval ExMeas.hyper_term n a b == Tco.hyper n a b

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n =>
  ExPCL.mc91Loop_run 1 n == Tco.mc91Loop 1 n && ExTail.mc91Loop_run 1 n == Tco.mc91Loop 1 n &&
  ExMeas.mc91Loop_run 1 n == Tco.mc91Loop 1 n

/-- info: true -/
#guard_msgs in
#eval (List.range 300).all fun n =>
  PCL.Term.eval ExPCL.isPow2_term n == isPow2 n && Tail.Term.eval ExTail.isPow2_term n == isPow2 n &&
  Meas.Term.eval ExMeas.isPow2_term n == isPow2 n &&
  PCL.Term.eval ExPCL.digitSum_term n == digitSum n &&
  Meas.Term.eval ExMeas.digitSum_term n == digitSum n &&
  PCL.Term.eval ExPCL.sumTo_term n 0 == sumTo n 0 && Tail.Term.eval ExTail.sumTo_term n 0 == sumTo n 0 &&
  Meas.Term.eval ExMeas.sumTo_term n 0 == sumTo n 0

/-- info: [false, true, true, false, true, false, false, false, true] -/
#guard_msgs in
#eval (List.range 9).map (PCL.Term.eval ExPCL.isPow2_term)

/-- info: true -/
#guard_msgs in
#eval (List.range 8).all fun n =>
  PCL.Term.eval ExNonRec.mc91_pcl (95 + n) == Tco.mc91 (95 + n) &&
  Tail.Term.eval ExNonRec.mc91_tail (95 + n) == Tco.mc91 (95 + n) &&
  Meas.Term.eval ExNonRec.mc91_meas (95 + n) == Tco.mc91 (95 + n) &&
  (List.range 5).all fun a =>
    PCL.Term.eval ExNonRec.hyperBase_pcl n a == Tco.hyperBase n a &&
    Tail.Term.eval ExNonRec.hyperBase_tail n a == Tco.hyperBase n a &&
    Meas.Term.eval ExNonRec.hyperBase_meas n a == Tco.hyperBase n a &&
    PCL.Term.eval ExNonRec.pair_pcl n a == Tco.pair n a &&
    Tail.Term.eval ExNonRec.pair_tail n a == Tco.pair n a &&
    Meas.Term.eval ExNonRec.pair_meas n a == Tco.pair n a

/-! ## Functions that are rejected -/

-- `boom` takes a proof argument: its body alone diverges for `n ≠ 1`, so it is not a total
-- function on `Nat` and cannot be a program of any of the languages.
/-- error: #lean_wf_func_to_term: unsupported type Tco.Safe n (only Nat and Bool) -/
#guard_msgs in
example : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.boom

-- `mc91TR` calls another function (`mc91Loop`); it used to be rejected, and is now captured
-- with a nested local recursive function: see `More.lean` and `MoreChecks.lean`.

-- `iter` has a function argument; the languages are first order.
/-- error: #lean_wf_func_to_term: unsupported type Nat → Nat (only Nat and Bool) -/
#guard_msgs in
example : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.iter

-- `ack` is not tail recursive, so it is not a `Tail` loop.
/--
error: #lean_wf_func_to_tail: Tco.ack is not tail recursive: a recursive call is not in tail position
  Tco.ack (x✝¹ - 1) (Tco.ack (x✝¹ - 1 + 1) (x✝ - 1))
-/
#guard_msgs in
example : Tail.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.ack

/-! ### Further functions of the uploaded files -/

-- `while` loops (`Id.run do … while …`) are not well-founded recursion: Lean compiles them to
-- `forIn Lean.Loop.mk`, which has no termination proof, so there is nothing to capture.
-- Higher-order functions (`ack2`, `hyperLoop`, `hyperTCO`) are outside the first-order languages.

namespace TcoMore
def diagonalWhile (m n : Nat) : Nat := Id.run do
  let mut m := m
  let mut n := n
  let mut acc := 0
  while m != 0 || n != 0 do
    acc := acc + 1
    if m > 0 then
      m := m - 1
      n := n + 1
    else
      m := n - 1
      n := 0
  return acc
def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)
def ack2 : Nat → (Nat → Nat)
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack2 m)
def hyperLoop (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | b + 1, acc => hyperLoop f b (f acc)
def hyperTCO : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => hyperLoop (hyperTCO n a) b (Tco.hyperBase (n + 1) a)
end TcoMore

/--
error: #lean_wf_func_to_term: unsupported expression
  (have m := m;
    have n := n;
    have acc := 0;
    do
    let r ←
      forIn Lean.Loop.mk ⟨acc, m, n⟩ fun x r =>
          have acc := r.fst;
          have x := r.snd;
          have m := x.fst;
          have n := x.snd;
          if (m != 0 || n != 0) = true then
            have acc := acc + 1;
            if m > 0 then
              have m := m - 1;
              have n := n + 1;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨acc, m, n⟩)
            else
              have m := n - 1;
              have n := 0;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨acc, m, n⟩)
          else pure (ForInStep.done ⟨acc, m, n⟩)
    match r with
      | ⟨acc, m, n⟩ => pure acc).run
-/
#guard_msgs in
example : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term TcoMore.diagonalWhile

/--
error: #lean_wf_func_to_term: unsupported expression
  fun n => n + 1
-/
#guard_msgs in
example : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term TcoMore.ack2

/--
error: #lean_wf_func_to_term: unsupported call of TcoMore.hyperLoop (only first-order functions on Nat and Bool, fully applied, can be called)
  TcoMore.hyperLoop r x✝
    (match x✝² - 1 + 1, x✝¹ with
    | 0, x => 1
    | 1, a => a
    | 2, x => 0
    | n.succ.succ.succ, x => 1)
-/
#guard_msgs in
example : PCL.Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term TcoMore.hyperTCO

/--
error: #lean_wf_func_to_term: unsupported call of TcoMore.hyperLoop (only first-order functions on Nat and Bool, fully applied, can be called)
  TcoMore.hyperLoop (TcoMore.hyperTCO (x✝² - 1) x✝¹) x✝
    (match x✝² - 1 + 1, x✝¹ with
    | 0, x => 1
    | 1, a => a
    | 2, x => 0
    | n.succ.succ.succ, x => 1)
-/
#guard_msgs in
example : Meas.Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term TcoMore.hyperTCO
