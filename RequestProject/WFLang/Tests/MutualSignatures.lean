import RequestProject.WFLang

/-!
# Mutual recursion with different signatures, and a decrease re-proved after translation

Before, a group of mutually recursive functions was captured only if its members had the same
parameter and result types (see `UNSUPPORTED.md`).  Now the global function capturing the group
takes a tag, then the parameters of all the members one after the other (each member reads its
own, the others are padded with default values); if the result types differ, it returns the
tuple of the results (each member fills its own component).  Structural recursion (on `Nat` or
on lists) and well-founded recursion (`termination_by`) are both covered, and so are calls of a
member from another function.
-/

open WFLang PCL

namespace MutualSig

mutual
def mA : Nat → Nat
  | 0 => 0
  | n + 1 => mB n true
def mB : Nat → Bool → Nat
  | 0, _ => 1
  | n + 1, b => if b then mA n else mA n + 1
end

mutual
def rA : Nat → Nat
  | 0 => 0
  | n + 1 => if rB n then 1 else 2
def rB : Nat → Bool
  | 0 => true
  | n + 1 => rA n == 0
end

mutual
def wEven (n : Nat) : Bool := if n = 0 then true else wOdd (n - 1) 0
termination_by n
decreasing_by omega
def wOdd (n k : Nat) : Bool := if n = 0 then false else wEven (n - 1 - k)
termination_by n
decreasing_by omega
end

mutual
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lcount xs 1
def lcount : List Nat → Nat → Nat
  | [], k => k
  | _ :: xs, k => lsum xs + k
end

/-- A call of members of a group from another function. -/
def callOdd (n : Nat) : Bool := wOdd n 1 && wEven (n + 2)

/-- Lean proves the decrease with `omega` on `min n _ ≤ n`; the capture re-proves it on the
translated goal (where `min` is an `if`) by splitting the `if`. -/
def nestMin : Nat → Nat
  | 0 => 0
  | n + 1 => nestMin (min n (nestMin n)) + 1
termination_by n => n
decreasing_by all_goals omega

end MutualSig

def mA_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term MutualSig.mA
theorem mA_agree : ∀ n, Term.eval mA_term n = MutualSig.mA n := by wf_agree
def mB_term : Term ⟨[.nat, .bool], .nat⟩ := #lean_wf_func_to_term MutualSig.mB
theorem mB_agree : ∀ n b, Term.eval mB_term n b = MutualSig.mB n b := by wf_agree
def rA_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term MutualSig.rA
theorem rA_agree : ∀ n, Term.eval rA_term n = MutualSig.rA n := by wf_agree
def rB_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term MutualSig.rB
theorem rB_agree : ∀ n, Term.eval rB_term n = MutualSig.rB n := by wf_agree
def wEven_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term MutualSig.wEven
theorem wEven_agree : ∀ n, Term.eval wEven_term n = MutualSig.wEven n := by wf_agree
def wOdd_term : Term ⟨[.nat, .nat], .bool⟩ := #lean_wf_func_to_term MutualSig.wOdd
theorem wOdd_agree : ∀ n k, Term.eval wOdd_term n k = MutualSig.wOdd n k := by wf_agree
def lsum_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term MutualSig.lsum
theorem lsum_agree : ∀ l, Term.eval lsum_term l = MutualSig.lsum l := by wf_agree
def lcount_term : Term ⟨[.list .nat, .nat], .nat⟩ := #lean_wf_func_to_term MutualSig.lcount
theorem lcount_agree : ∀ l k, Term.eval lcount_term l k = MutualSig.lcount l k := by wf_agree
def callOdd_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term MutualSig.callOdd
theorem callOdd_agree : ∀ n, Term.eval callOdd_term n = MutualSig.callOdd n := by wf_agree
def nestMin_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term MutualSig.nestMin
theorem nestMin_agree : ∀ n, Term.eval nestMin_term n = MutualSig.nestMin n := by wf_agree

#guard (List.range 12).all fun n =>
  Term.eval mA_term n == MutualSig.mA n &&
  Term.eval mB_term n true == MutualSig.mB n true &&
  Term.eval mB_term n false == MutualSig.mB n false &&
  Term.eval rA_term n == MutualSig.rA n &&
  Term.eval rB_term n == MutualSig.rB n &&
  Term.eval wEven_term n == MutualSig.wEven n &&
  Term.eval wOdd_term n 1 == MutualSig.wOdd n 1 &&
  Term.eval callOdd_term n == MutualSig.callOdd n &&
  Term.eval nestMin_term n == MutualSig.nestMin n
#guard [[], [1], [1, 2, 3, 4], [5, 0, 7]].all fun l =>
  Term.eval lsum_term l == MutualSig.lsum l && Term.eval lcount_term l 2 == MutualSig.lcount l 2
