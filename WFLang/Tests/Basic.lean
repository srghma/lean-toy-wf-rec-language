import RequestProject.WFLang.Capture.Elab
import RequestProject.WFLang.Tests.Functions

/-!
# Basic tests: captures of the user's `gcd` and of the uploaded `Tco` functions

Each program is produced by `#lean_wf_func_to_term`, and each agreement theorem is proved by
`wf_agree`.

| function      | recursion                      |
|---------------|--------------------------------|
| `gcd`         | tail                           |
| `isPow2`      | tail (under `&&`)              |
| `digitSum`    | non-tail                       |
| `sumTo`       | tail                           |
| `ack`         | nested, `match`                |
| `diagonal`    | non-tail, `match`              |
| `diagonal_tr` | tail, `match`                  |
| `hyper`       | nested, `match` on 0,1,2,3+    |
| `mc91Loop`    | tail, measure `2*(111-n)+21*c` |
| `mc91`, `hyperBase`, `pair` | none (no `fix` node is produced) |
-/

open WFLang

namespace ExPCL
open PCL

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def isPow2_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term isPow2
theorem isPow2_agree : ∀ n, Term.eval isPow2_term n = isPow2 n := by wf_agree

def digitSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term digitSum
theorem digitSum_agree : ∀ n, Term.eval digitSum_term n = digitSum n := by wf_agree

def sumTo_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term sumTo
theorem sumTo_agree : ∀ i acc, Term.eval sumTo_term i acc = sumTo i acc := by wf_agree

def ack_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.ack
theorem ack_agree : ∀ m n, Term.eval ack_term m n = Tco.ack m n := by wf_agree

def diagonal_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.diagonal
theorem diagonal_agree : ∀ m n, Term.eval diagonal_term m n = Tco.diagonal m n := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc,
    Term.eval diagonal_tr_term m n acc = Tco.diagonal_tr m n acc := by wf_agree

def hyper_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyper
theorem hyper_agree : ∀ n a b, Term.eval hyper_term n a b = Tco.hyper n a b := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = Tco.mc91Loop c n := by wf_agree

/-- Entry points used by the runtime checks and the benchmark (`Bench.lean`). -/
def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n
def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end ExPCL

/-! ## Non-recursive functions (no `fix` node is produced) -/

namespace ExNonRec
open PCL

def mc91_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91
theorem mc91_agree : ∀ n, Term.eval mc91_term n = Tco.mc91 n := by wf_agree

def hyperBase_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperBase
theorem hyperBase_agree : ∀ n a, Term.eval hyperBase_term n a = Tco.hyperBase n a := by
  wf_agree

def pair_term : Term ⟨[.nat, .nat], .nat⟩ :=
  #lean_wf_func_to_term Tco.AckWithoutStackButUsingCantorPairing.pair
theorem pair_agree : ∀ x y, Term.eval pair_term x y =
    Tco.AckWithoutStackButUsingCantorPairing.pair x y := by wf_agree

end ExNonRec
