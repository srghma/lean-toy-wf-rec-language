import RequestProject.WFLang.Capture
import RequestProject.WFLang.Examples.Functions

/-!
# Examples for the three languages with well-founded recursion in the grammar

For each language (`PCL`, `Tail`, `Meas`), the user's `gcd` is captured with
`#lean_wf_func_to_term` and `gcd_agree` is proved with `wf_agree`; then the functions of the
`Tco*.lean` files are captured where the language can express them.

| function      | recursion                  | `PCL` | `Tail` | `Meas` |
|---------------|----------------------------|-------|--------|--------|
| `gcd`         | tail                       | ✓     | ✓      | ✓      |
| `isPow2`      | tail (under `&&`)          | ✓     | ✓      | ✓      |
| `digitSum`    | non-tail                   | ✓     | –      | ✓      |
| `sumTo`       | tail                       | ✓     | ✓      | ✓      |
| `ack`         | nested, `match`            | ✓     | –      | ✓      |
| `diagonal`    | non-tail, `match`          | ✓     | –      | ✓      |
| `diagonal_tr` | tail, `match`              | ✓     | ✓      | ✓      |
| `hyper`       | nested, `match` on 0,1,2,3+| ✓     | –      | ✓      |
| `mc91`        | none                       | ✓     | ✓      | ✓      |
| `mc91Loop`    | tail, measure `2*(111-n)+21*c` | ✓ | ✓      | ✓      |

`Tail` only accepts tail recursion (the capture reports the offending call otherwise).
-/

open WFLang

/-! ## `PCL`: proof-carrying calls -/

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

/-- Entry points used for the C-code inspection and the benchmark. -/
def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n
def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end ExPCL

/-! ## `Tail`: well-founded loops -/

namespace ExTail
open Tail

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def isPow2_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term isPow2
theorem isPow2_agree : ∀ n, Term.eval isPow2_term n = isPow2 n := by wf_agree

def sumTo_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term sumTo
theorem sumTo_agree : ∀ i acc, Term.eval sumTo_term i acc = sumTo i acc := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc,
    Term.eval diagonal_tr_term m n acc = Tco.diagonal_tr m n acc := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = Tco.mc91Loop c n := by wf_agree

def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end ExTail

/-! ## `Meas`: in-language measure, checked at runtime -/

namespace ExMeas
open Meas

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

def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n
def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end ExMeas

/-! ## Non-recursive functions (no `fix`/`loop` node is produced) -/

namespace ExNonRec

def mc91_pcl : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91
theorem mc91_pcl_agree : ∀ n, PCL.Term.eval mc91_pcl n = Tco.mc91 n := by wf_agree

def mc91_tail : Tail.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91
theorem mc91_tail_agree : ∀ n, Tail.Term.eval mc91_tail n = Tco.mc91 n := by wf_agree

def mc91_meas : Meas.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91
theorem mc91_meas_agree : ∀ n, Meas.Term.eval mc91_meas n = Tco.mc91 n := by wf_agree

def hyperBase_pcl : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperBase
theorem hyperBase_pcl_agree : ∀ n a, PCL.Term.eval hyperBase_pcl n a = Tco.hyperBase n a := by
  wf_agree

def pair_meas : Meas.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.pair
theorem pair_meas_agree : ∀ x y, Meas.Term.eval pair_meas x y = Tco.pair x y := by wf_agree

def hyperBase_tail : Tail.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperBase
theorem hyperBase_tail_agree : ∀ n a, Tail.Term.eval hyperBase_tail n a = Tco.hyperBase n a := by
  wf_agree

def hyperBase_meas : Meas.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.hyperBase
theorem hyperBase_meas_agree : ∀ n a, Meas.Term.eval hyperBase_meas n a = Tco.hyperBase n a := by
  wf_agree

def pair_pcl : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.pair
theorem pair_pcl_agree : ∀ x y, PCL.Term.eval pair_pcl x y = Tco.pair x y := by wf_agree

def pair_tail : Tail.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term Tco.pair
theorem pair_tail_agree : ∀ x y, Tail.Term.eval pair_tail x y = Tco.pair x y := by wf_agree

end ExNonRec
