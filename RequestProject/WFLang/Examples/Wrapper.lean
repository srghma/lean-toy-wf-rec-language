import RequestProject.WFLang.Capture
import RequestProject.WFLang.Examples.Functions

/-!
# Examples for the wrapper designs (`Guarded`, `GuardedAcc`, `FreeCall`, `Checked`)

The user's `gcd`, captured once per design, together with the agreement theorem
`gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n`; then `digitSum`, `isPow2`, `sumTo` and
the first-order functions of the `Tco*.lean` files.  Definitions by pattern matching on `Nat`
(`ack`, `diagonal`, `diagonal_tr`, `hyper`, `mc91Loop`, `hyperBase`) are handled by unfolding
the `match` into `if t == 0 then … else …` with `t - 1` for the predecessor.
-/

namespace ExGuarded
open WFLang Guarded

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd

theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def digitSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term digitSum
theorem digitSum_agree : ∀ n, Term.eval digitSum_term n = digitSum n := by wf_agree

def isPow2_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term isPow2
theorem isPow2_agree : ∀ n, Term.eval isPow2_term n = isPow2 n := by wf_agree

def sumTo_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term sumTo
theorem sumTo_agree : ∀ i acc, Term.eval sumTo_term i acc = sumTo i acc := by wf_agree

/-- Entry point used for the C-code inspection. -/
def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n

end ExGuarded

namespace ExGuardedAcc
open WFLang GuardedAcc

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd

theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def isPow2_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term isPow2
theorem isPow2_agree : ∀ n, Term.eval isPow2_term n = isPow2 n := by wf_agree

def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n

end ExGuardedAcc

namespace ExFreeCall
open WFLang FreeCall

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd

theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def digitSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term digitSum
theorem digitSum_agree : ∀ n, Term.eval digitSum_term n = digitSum n := by wf_agree

def sumTo_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term sumTo
theorem sumTo_agree : ∀ i acc, Term.eval sumTo_term i acc = sumTo i acc := by wf_agree

def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n

end ExFreeCall

namespace ExChecked
open WFLang Checked

def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd

theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree

def isPow2_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term isPow2
theorem isPow2_agree : ∀ n, Term.eval isPow2_term n = isPow2 n := by wf_agree

def gcd_run (m n : Nat) : Nat := Term.eval gcd_term m n

end ExChecked

namespace Tco

open WFLang

/-! ## Design 1: `Guarded` -/

namespace G
open Guarded

def ack_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term ack
theorem ack_agree : ∀ m n, Term.eval ack_term m n = ack m n := by wf_agree

def diagonal_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal
theorem diagonal_agree : ∀ m n, Term.eval diagonal_term m n = diagonal m n := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc, Term.eval diagonal_tr_term m n acc = diagonal_tr m n acc := by
  wf_agree

def hyper_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term hyper
theorem hyper_agree : ∀ n a b, Term.eval hyper_term n a b = hyper n a b := by wf_agree

def hyperBase_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term hyperBase
theorem hyperBase_agree : ∀ n a, Term.eval hyperBase_term n a = hyperBase n a := by wf_agree

def mc91_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mc91
theorem mc91_agree : ∀ n, Term.eval mc91_term n = mc91 n := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = mc91Loop c n := by wf_agree

def pair_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term pair
theorem pair_agree : ∀ x y, Term.eval pair_term x y = pair x y := by wf_agree

/-- Entry points used for the C-code inspection. -/
def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end G

/-! ## Design 3: `GuardedAcc` -/

namespace GA
open GuardedAcc

def ack_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term ack
theorem ack_agree : ∀ m n, Term.eval ack_term m n = ack m n := by wf_agree

def diagonal_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal
theorem diagonal_agree : ∀ m n, Term.eval diagonal_term m n = diagonal m n := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc, Term.eval diagonal_tr_term m n acc = diagonal_tr m n acc := by
  wf_agree

def hyper_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term hyper
theorem hyper_agree : ∀ n a b, Term.eval hyper_term n a b = hyper n a b := by wf_agree

def mc91_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mc91
theorem mc91_agree : ∀ n, Term.eval mc91_term n = mc91 n := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = mc91Loop c n := by wf_agree

def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end GA

/-! ## Design 2: `FreeCall` -/

namespace FC
open FreeCall

def ack_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term ack
theorem ack_agree : ∀ m n, Term.eval ack_term m n = ack m n := by wf_agree

def diagonal_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal
theorem diagonal_agree : ∀ m n, Term.eval diagonal_term m n = diagonal m n := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc, Term.eval diagonal_tr_term m n acc = diagonal_tr m n acc := by
  wf_agree

def hyper_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term hyper
theorem hyper_agree : ∀ n a b, Term.eval hyper_term n a b = hyper n a b := by wf_agree

def mc91_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mc91
theorem mc91_agree : ∀ n, Term.eval mc91_term n = mc91 n := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = mc91Loop c n := by wf_agree

def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end FC

/-! ## Design 4: `Checked` -/

namespace CK
open Checked

def ack_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term ack
theorem ack_agree : ∀ m n, Term.eval ack_term m n = ack m n := by wf_agree

def diagonal_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal
theorem diagonal_agree : ∀ m n, Term.eval diagonal_term m n = diagonal m n := by wf_agree

def diagonal_tr_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term diagonal_tr
theorem diagonal_tr_agree : ∀ m n acc, Term.eval diagonal_tr_term m n acc = diagonal_tr m n acc := by
  wf_agree

def hyper_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term hyper
theorem hyper_agree : ∀ n a b, Term.eval hyper_term n a b = hyper n a b := by wf_agree

def mc91_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mc91
theorem mc91_agree : ∀ n, Term.eval mc91_term n = mc91 n := by wf_agree

def mc91Loop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term mc91Loop
theorem mc91Loop_agree : ∀ c n, Term.eval mc91Loop_term c n = mc91Loop c n := by wf_agree

def ack_run (m n : Nat) : Nat := Term.eval ack_term m n
def diagonal_tr_run (m n acc : Nat) : Nat := Term.eval diagonal_tr_term m n acc
def mc91Loop_run (c n : Nat) : Nat := Term.eval mc91Loop_term c n

end CK

end Tco

