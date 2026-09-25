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
| `ack`                        | Ack       | captured (nested `fix`)             | `ExPCL.ack_agree`    |
| `ack999`                     | Ack       | captured (0 arguments)              | `ack999_agree` below |
| `ack2`                       | Ack       | rejected: returns a function        | `ack2_agree` below (via `ack`) |
| `ackWhile`                   | Ack       | rejected: `while` loop              | runtime check below  |
| `…Cantor….pair`              | Ack       | captured (no recursion)             | `ExNonRec.pair_agree` |
| `…Cantor….isqrt`             | Ack       | rejected: `while` loop              | runtime check below  |
| `…Cantor….unpairLeft/Right`  | Ack       | rejected: inlined `isqrt` is a loop | runtime check below  |
| `…Cantor….ackNoDataStructure`| Ack       | rejected: `while` loop              | runtime check below  |
| `diagonal`                   | Diagonal  | captured                            | `ExPCL.diagonal_agree` |
| `diagonal_tr`                | Diagonal  | captured                            | `ExPCL.diagonal_tr_agree` |
| `diagonalWhile`              | Diagonal  | rejected: `while` loop              | runtime check below  |
| `hyper`                      | Hyper     | captured (nested `fix`)             | `ExPCL.hyper_agree`  |
| `hyperBase`                  | Hyper     | captured (no recursion)             | `ExNonRec.hyperBase_agree` |
| `hyperLoop`                  | Hyper     | rejected: function argument         | —                    |
| `hyperTCO`                   | Hyper     | rejected: calls `hyperLoop`         | `hyperTCO_agree` below (via `hyper`) |
| `hyperWhile`                 | Hyper     | rejected: call inside a `for` loop  | `hyperWhile_agree` below (via `hyper`) |
| `mc91`                       | Mc91      | captured (no recursion)             | `ExNonRec.mc91_agree` |
| `mc91Loop`                   | Mc91      | captured                            | `ExPCL.mc91Loop_agree` |
| `mc91TR`                     | Mc91      | captured (calls `mc91Loop`)         | `MorePCL.mc91TR_agree` |
| `mc91While`                  | Mc91      | rejected: `while` loop              | runtime check below  |
| `iter`                       | Mc91      | rejected: function argument         | `iter_mc91_agree` below (via `mc91Loop`) |
| `Safe`                       | Boom      | rejected: a proposition             | —                    |
| `boom`                       | Boom      | rejected: proof argument            | —                    |

("Ack", … stand for the uploaded files `TcoAck.lean`, …; `…Cantor…` is the namespace
`AckWithoutStackButUsingCantorPairing`.)

"via `f`" means: the function itself cannot be captured, but a theorem of the uploaded file
(`SourceProofs.lean`) says it equals a captured function `f`, so the `PCL` program of `f`
computes it; the agreement theorem is proved here.  The `while`-loop functions cannot be
reasoned about in this Lean version (see `SourceProofs.lean`), so they are only compared with
the `PCL` programs on sample inputs.
-/

open WFLang

namespace SourcesPCL
open PCL

/-! ## Captured here: `ack999`

`ack999` has no argument: its program has the signature `⟨[], .nat⟩`.  The agreement theorem
is proved without evaluating `ack 999 1` (which is far too large to compute). -/

def ack999_term : Term ⟨[], .nat⟩ := #lean_wf_func_to_term Tco.ack999
theorem ack999_agree : Term.eval ack999_term = Tco.ack999 := by wf_agree

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

-- `while` loops: Lean builds them with `Lean.Loop.forIn`, which has no termination proof.
/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.ackWhile : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.isqrt :
  PCL.Term ⟨[.nat], .nat⟩)

-- `unpairLeft`/`unpairRight` are not recursive, but the `isqrt` they call (inlined) is a loop.
/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.unpairLeft :
  PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.unpairRight :
  PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject
  (#lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.ackNoDataStructure :
    PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.diagonalWhile : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.mc91While : PCL.Term ⟨[.nat], .nat⟩)

-- A recursive call inside a `for` loop.
/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.hyperWhile : PCL.Term ⟨[.nat, .nat, .nat], .nat⟩)

-- Higher-order functions: `PCL` is first order.
/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.ack2 : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Nat → Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.hyperLoop : PCL.Term ⟨[.nat, .nat], .nat⟩)

/--
info: rejected: #lean_wf_func_to_term: unsupported call of Tco.hyperLoop (only first-order functions on Nat and Bool, fully applied, can be called)
-/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.hyperTCO : PCL.Term ⟨[.nat, .nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Nat → Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.iter : PCL.Term ⟨[.nat, .nat], .nat⟩)

-- `Safe` is a proposition (`n = 1`), not a `Bool`-valued function.
/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.Safe : PCL.Term ⟨[.nat], .bool⟩)

-- `boom` takes a proof argument: its body alone diverges for `n ≠ 1`, so it is not a total
-- function on `Nat` and cannot be a `PCL` program.
/-- info: rejected: #lean_wf_func_to_term: unsupported type Tco.Safe n (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Tco.boom : PCL.Term ⟨[.nat], .nat⟩)

/-! ## Rejected `while` loops, compared with the `PCL` programs at runtime -/

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
