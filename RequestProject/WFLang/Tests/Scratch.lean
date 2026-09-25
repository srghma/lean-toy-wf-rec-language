import RequestProject.WFLang.Capture.Elab

namespace Scr
open WFLang PCL

def gcd' (m n : Nat) : Nat :=
  if n = 0 then m else gcd' n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

def gcd'_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd'
theorem gcd'_agree : ∀ m n, Term.eval gcd'_term m n = gcd' m n := by wf_agree

@[inlinable] def sumAcc (n acc : Nat) : Nat := if n = 0 then acc else sumAcc (n - 1) (acc + n)
termination_by n

def useLoop (a b : Nat) : Nat := sumAcc a 0 + b * sumAcc b a

def useLoop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useLoop
#eval useLoop_term.loops
#eval useLoop_term.nglobals
#eval (Term.eval useLoop_term 5 6, useLoop 5 6)
theorem useLoop_agree : ∀ a b, Term.eval useLoop_term a b = useLoop a b := by wf_agree

end Scr
