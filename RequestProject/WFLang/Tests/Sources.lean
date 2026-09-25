import RequestProject.WFLang.Tests.MoreChecks
import RequestProject.WFLang.Tests.SourceProofs

/-!
# Every function of the uploaded `Tco*.lean` files: captured by `PCL`, or rejected

The uploaded files `TcoAck.lean`, `TcoDiagonal.lean`, `TcoHyper.lean`, `TcoMc91.lean` and
`TcoBoom.lean` imported an external `LeanScript` package and did not build in this project.
Their functions were moved, verbatim (except for the corrected `ackWhile`), into namespace `Tco`
of `Functions.lean`, and their
theorems into `SourceProofs.lean`.  This file accounts for **each** of those functions:

| function (namespace `Tco`)   | file      | `#lean_wf_func_to_term`             | agreement            |
|------------------------------|-----------|-------------------------------------|----------------------|
| `ack`                        | Ack       | captured (global function)          | `ExPCL.ack_agree`    |
| `ack999`                     | Ack       | captured (0 arguments)              | `ack999_agree` below |
| `ack2`                       | Ack       | captured (recursion through `ackInner`'s function argument) | `ack2_term_agree` below; also `ack2_agree` (via `ack`) |
| `ackWhile`                   | Ack       | rejected: `while` loop with no simple measure | runtime check below  |
| `…Cantor….pair`              | Ack       | captured (no recursion)             | `ExNonRec.pair_agree` |
| `…Cantor….isqrt`             | Ack       | captured (`while` loop, `Tests/LeanWhile.lean`) | `LeanWhilePCL.isqrt_agree` (under `LoopLaw`) |
| `…Cantor….unpairLeft/Right`  | Ack       | captured (calls `isqrt`, `Tests/LeanWhile.lean`) | `LeanWhilePCL.unpairLeft_agree`, `…unpairRight_agree` (under `LoopLaw`) |
| `…Cantor….ackNoDataStructure`| Ack       | rejected: `while` loop with no simple measure | runtime check below  |
| `diagonal`                   | Diagonal  | captured                            | `ExPCL.diagonal_agree` |
| `diagonal_tr`                | Diagonal  | captured                            | `ExPCL.diagonal_tr_agree` |
| `diagonalWhile`              | Diagonal  | captured (`while` loop, measure given in `Tests/LeanWhile.lean`) | `LeanWhilePCL.diagonalWhile_agree`; `LeanWhileProofs.diagonalWhile_eq` (under `LoopLaw`) |
| `hyper`                      | Hyper     | captured (global function)          | `ExPCL.hyper_agree`  |
| `hyperBase`                  | Hyper     | captured (no recursion)             | `ExNonRec.hyperBase_agree` |
| `hyperLoop`                  | Hyper     | captured when specialised, e.g. `(hyperLoop (hyperBase 2))` | `hyperLoop_agree` below |
| `hyperTCO`                   | Hyper     | captured (recursion through `hyperLoop`'s function argument) | `hyperTCO_term_agree` below; also `hyperTCO_agree` (via `hyper`) |
| `hyperWhile`                 | Hyper     | captured (recursion through a `for` loop body) | `hyperWhile_term_agree` below; also `hyperWhile_agree` (via `hyper`) |
| `mc91`                       | Mc91      | captured (no recursion)             | `ExNonRec.mc91_agree` |
| `mc91Loop`                   | Mc91      | captured                            | `ExPCL.mc91Loop_agree` |
| `mc91TR`                     | Mc91      | captured (calls `mc91Loop`)         | `MorePCL.mc91TR_agree` |
| `mc91While`                  | Mc91      | captured (`while` loop, measure given in `Tests/LeanWhile.lean`) | `LeanWhilePCL.mc91While_agree`; `LeanWhileProofs.mc91While_eq` (under `LoopLaw`) |
| `iter`                       | Mc91      | captured when specialised: `(iter mc91)` | `iter_mc91_agree'` below; also `iter_mc91_agree` (via `mc91Loop`) |
| `Safe`                       | Boom      | rejected: a proposition             | —                    |
| `boom`                       | Boom      | captured (precondition `Safe n`)    | `boom_agree` below   |

("Ack", … stand for the uploaded files `TcoAck.lean`, …; `…Cantor…` is the namespace
`AckWithoutStackButUsingCantorPairing`.)

"via `f`" means: the function itself cannot be captured, but a theorem of the uploaded file
(`SourceProofs.lean`) says it equals a captured function `f`, so the `PCL` program of `f`
computes it; the agreement theorem is proved here.  Lean's `while` loop (`Lean.Loop.forIn`) is a
`partial def`, opaque to the logic: the agreement theorems of the `while`-loop functions
(`Tests/LeanWhile.lean`) assume its unfolding law `WFLang.LoopLaw` as a hypothesis.  The two
loops without a simple measure (`ackWhile`, `ackNoDataStructure`) are only compared with the
`PCL` programs on sample inputs, as are the other loops (below).
-/

open WFLang

namespace SourcesPCL
open PCL

/-! ## Captured here: `ack999`

`ack999` has no argument: its program has the signature `⟨[], .nat⟩`.  The agreement theorem
is proved without evaluating `ack 999 1` (which is far too large to compute). -/

def ack999_term : Term ⟨[], .nat⟩ := #lean_wf_func_to_term Tco.ack999
theorem ack999_agree : Term.eval ack999_term = Tco.ack999 := by wf_agree

/-! ## Captured here: `boom`, a function with a precondition

`boom (n : Nat) (h : Safe n)` takes a proof argument.  It is captured as a program with the
*precondition* `Safe n`: the program can only be run on arguments satisfying it
(`PTerm.run boom_term (n, ()) h`), and its recursive call proves `Safe (3 * n)` and the decrease
`3 * n < n` from the path condition `Safe n ∧ n ≠ 1`, exactly as `boom`'s own proofs do (both are
vacuous: `Safe n` means `n = 1`). -/

def boom_term : PTerm ⟨[.nat], .nat⟩ (fun e => Tco.Safe e.1) (fun _ _ => True) :=
  #lean_wf_func_to_term Tco.boom
theorem boom_agree : ∀ n (h : Tco.Safe n), PTerm.run boom_term (n, ()) h = Tco.boom n h := by
  wf_agree

/-- info: 0 -/
#guard_msgs in
#eval PTerm.run boom_term (1, ()) (rfl : Tco.Safe 1)

/-! ## Captured here: `iter` and `hyperLoop`, specialised to a function argument

A function with a function parameter is not a first-order program, but its copy *specialised*
to a known (closed) function argument is: `#lean_wf_func_to_term (Tco.iter Tco.mc91)` captures
`fun c n => Tco.iter Tco.mc91 c n`.  (A call of such a function inside another captured
function is specialised in the same way, with the free variables of the function argument as
extra parameters.) -/

def iter_mc91_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term (Tco.iter Tco.mc91)
theorem iter_mc91_agree' : ∀ c n, Term.eval iter_mc91_term c n = Tco.iter Tco.mc91 c n := by
  wf_agree

def hyperLoop_term : Term ⟨[.nat, .nat], .nat⟩ :=
  #lean_wf_func_to_term (Tco.hyperLoop (Tco.hyperBase 2))
theorem hyperLoop_agree : ∀ b acc,
    Term.eval hyperLoop_term b acc = Tco.hyperLoop (Tco.hyperBase 2) b acc := by
  wf_agree

/-- info: true -/
#guard_msgs in
#eval (List.range 120).all fun n => (List.range 4).all fun c =>
  Term.eval iter_mc91_term c n == Tco.iter Tco.mc91 c n &&
  Term.eval hyperLoop_term c n == Tco.hyperLoop (Tco.hyperBase 2) c n

/-! ## Captured here: `ack2`, `hyperTCO`, `hyperWhile`: recursion through a function argument

`ack2 (m + 1) = ackInner (ack2 m)`, `hyperTCO (n + 1) a b = hyperLoop (hyperTCO n a) b …` and
`hyperWhile`'s `for` loop (whose body calls `hyperWhile n a`) call themselves inside a function
argument.  Each is captured together with the copy of `ackInner`, `hyperLoop` or the loop
specialised to that argument, as one global function with a tag parameter (relation
`WFLang.hoRel`, see `Gaps.lean`).  (`ack2` returns a function; its program takes both
arguments.) -/

def ack2_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.ack2
theorem ack2_term_agree : ∀ m n, Term.eval ack2_term m n = Tco.ack2 m n := by wf_agree

def hyperTCO_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperTCO
theorem hyperTCO_term_agree : ∀ n a b, Term.eval hyperTCO_term n a b = Tco.hyperTCO n a b := by
  wf_agree

def hyperWhile_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperWhile
theorem hyperWhile_term_agree :
    ∀ n a b, Term.eval hyperWhile_term n a b = Tco.hyperWhile n a b := by
  wf_agree

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 5).all fun n =>
  Term.eval ack2_term m n == Tco.ack2 m n &&
  Term.eval hyperTCO_term m 2 n == Tco.hyperTCO m 2 n &&
  Term.eval hyperWhile_term m 2 n == Tco.hyperWhile m 2 n

/-! ## Not capturable, but equal to a captured function (proved) -/

/-- `ack2` returns a function (`Nat → (Nat → Nat)`), so it is rejected, but it equals `ack`
(`Tco.ack2_eq_ack`), which is captured. -/
theorem ack2_agree : ∀ m n, Term.eval ExPCL.ack_term m n = Tco.ack2 m n := by
  intro m n; rw [ExPCL.ack_agree, Tco.ack2_eq_ack]

/-- `hyperTCO` calls the higher-order `hyperLoop`, but equals `hyper` (`Tco.hyperTCO_eq`). -/
theorem hyperTCO_agree : ∀ n a b, Term.eval ExPCL.hyper_term n a b = Tco.hyperTCO n a b := by
  intro n a b; rw [ExPCL.hyper_agree, Tco.hyperTCO_eq]

/-- `hyperWhile` recurses inside a `for` loop, but equals `hyper` (`Tco.hyperWhile_eq_hyper`). -/
theorem hyperWhile_agree : ∀ n a b, Term.eval ExPCL.hyper_term n a b = Tco.hyperWhile n a b := by
  intro n a b; rw [ExPCL.hyper_agree, Tco.hyperWhile_eq_hyper]

/-- `iter` takes a function argument, but its instance `iter mc91` is `mc91Loop`
(`Tco.mc91Loop_eq`). -/
theorem iter_mc91_agree : ∀ c n, Term.eval ExPCL.mc91Loop_term c n = Tco.iter Tco.mc91 c n := by
  intro c n; rw [ExPCL.mc91Loop_agree, Tco.mc91Loop_eq]

/-- The program of the non-recursive `mc91` computes the recursive `mc91TR`
(`Tco.mc91TR_eq_mc91`). -/
theorem mc91_mc91TR_agree : ∀ n, Term.eval ExNonRec.mc91_term n = Tco.mc91TR n := by
  intro n; rw [ExNonRec.mc91_agree, Tco.mc91TR_eq_mc91]

/-- The program of `diagonal_tr`, started with `acc = 0`, computes `diagonal`
(`Tco.diagonal_tr_zero_eq_diagonal`). -/
theorem diagonal_tr_diagonal_agree :
    ∀ m n, Term.eval ExPCL.diagonal_tr_term m n 0 = Tco.diagonal m n := by
  intro m n; rw [ExPCL.diagonal_tr_agree, Tco.diagonal_tr_zero_eq_diagonal]

end SourcesPCL

/-! ## Rejections

`#expect_reject` (from `MoreChecks.lean`) succeeds only if the capture fails, and reports the
first line of the error message. -/

-- Lean's `while` loops are captured through their well-founded version (`Tests/LeanWhile.lean`,
-- which captures `isqrt`, `unpairLeft`, `unpairRight`, `diagonalWhile` and `mc91While`), but
-- only if the loop's termination can be proved: Lean does not guess a measure for these loops,
-- which must be given with `lean_while_to_wf f termination_by …`.  `ackWhile` and
-- `ackNoDataStructure` (an explicit stack) have no simple measure.
/-- info: rejected: lean_while_to_wf: cannot prove that loop 1 of Tco.ackWhile terminates: give its measure, `lean_while_to_wf Tco.ackWhile termination_by …` (and `decreasing_by …`) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.ackWhile : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: lean_while_to_wf: cannot prove that loop 1 of Tco.AckWithoutStackButUsingCantorPairing.ackNoDataStructure terminates: give its measure, `lean_while_to_wf Tco.AckWithoutStackButUsingCantorPairing.ackNoDataStructure termination_by …` (and `decreasing_by …`) -/
#guard_msgs in
#expect_reject
  (#lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.ackNoDataStructure :
    PCL.Term ⟨[.nat, .nat], .nat⟩)

-- Without their measures (given in `Tests/LeanWhile.lean`):
/-- info: rejected: lean_while_to_wf: cannot prove that loop 1 of Tco.diagonalWhile terminates: give its measure, `lean_while_to_wf Tco.diagonalWhile termination_by …` (and `decreasing_by …`) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.diagonalWhile : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: lean_while_to_wf: cannot prove that loop 1 of Tco.mc91While terminates: give its measure, `lean_while_to_wf Tco.mc91While termination_by …` (and `decreasing_by …`) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.mc91While : PCL.Term ⟨[.nat], .nat⟩)

-- Higher-order functions: `PCL` is first order.  `iter` and `hyperLoop` are captured once
-- specialised to a function argument (above); unspecialised, their function parameter is
-- rejected.  (`ack2`, `hyperTCO`, `hyperWhile` are captured above.)

/-- info: rejected: #lean_wf_func_to_term: Tco.hyperLoop has a function (or type) parameter; capture a copy specialised to a closed function instead: `#lean_wf_func_to_term (Tco.hyperLoop f)` -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.hyperLoop : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: Tco.iter has a function (or type) parameter; capture a copy specialised to a closed function instead: `#lean_wf_func_to_term (Tco.iter f)` -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.iter : PCL.Term ⟨[.nat, .nat], .nat⟩)

-- `Safe` is a proposition (`n = 1`), not a `Bool`-valued function.
/-- info: rejected: #lean_wf_func_to_term: unsupported type Prop (only Nat, Bool, Int, pairs, lists and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.Safe : PCL.Term ⟨[.nat], .bool⟩)

-- `boom` takes a proof argument `h : Safe n`: it is captured as a program with the
-- precondition `Safe n` (see `boom_term` above), not as a total program on `Nat`.
/-- info: rejected: Type mismatch -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.boom : PCL.Term ⟨[.nat], .nat⟩)

/-! ## `while` loops, compared with the `PCL` programs at runtime -/

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun m => (List.range 12).all fun n =>
  Tco.diagonalWhile m n == PCL.Term.eval ExPCL.diagonal_term m n

/-- info: true -/
#guard_msgs in
#eval (List.range 150).all fun n => Tco.mc91While n == PCL.Term.eval MorePCL.mc91TR_term n

-- `ackNoDataStructure` encodes its stack with nested Cantor pairs, whose size grows doubly
-- exponentially with the stack depth, so only small inputs are feasible.
open Tco.AckWithoutStackButUsingCantorPairing in
/-- info: true -/
#guard_msgs in
#eval (List.range 3).all fun m => (List.range 4).all fun n =>
  ackNoDataStructure m n == ExPCL.ack_run m n

-- `isqrt` is the integer square root; `unpairLeft`/`unpairRight` invert the captured `pair`.
open Tco.AckWithoutStackButUsingCantorPairing in
/-- info: true -/
#guard_msgs in
#eval (List.range 300).all fun n =>
  isqrt n * isqrt n ≤ n && n < (isqrt n + 1) * (isqrt n + 1)

open Tco.AckWithoutStackButUsingCantorPairing in
/-- info: true -/
#guard_msgs in
#eval (List.range 20).all fun x => (List.range 20).all fun y =>
  unpairLeft (PCL.Term.eval ExNonRec.pair_term x y) == x &&
  unpairRight (PCL.Term.eval ExNonRec.pair_term x y) == y

/-! ## `ackWhile` agrees with the `PCL` program of `ack` on sample inputs -/

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun m => (List.range 5).all fun n =>
  Tco.ackWhile m n == ExPCL.ack_run m n
