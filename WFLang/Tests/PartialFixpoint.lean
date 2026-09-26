import RequestProject.WFLang

/-!
# Functions defined by `partial_fixpoint`

Lean accepts a `partial_fixpoint` definition without a termination proof, so there is no
termination argument to reuse.  `#lean_wf_func_to_term` supplies one: it tries, in turn, the
value of each `Nat` parameter, the length of each `List` parameter, and the difference `a - b` of
two `Nat` parameters as the measure (`Capture/Meta/Fix.lean`, `pfixCandidates`), and keeps the
first one for which every recursive call of the program is proved to decrease (as usual, from the
path condition).  `set_option wfLang.pfixMeasure k` picks the `k`-th candidate directly.

The agreement theorem, proved by `wf_agree` from the equation `f.eq_def` that Lean generates for
the definition, therefore also shows that the function is total: it is equal, on every input, to
a program whose evaluator terminates.  A `partial_fixpoint` function that does not terminate on
some input (`Unsupported.loopUp` in `Tests/Unsupported.lean`) is rejected.
-/

open WFLang PCL

namespace PFix

def pfix (n : Nat) : Nat := if n = 0 then 0 else pfix (n - 1)
partial_fixpoint

/-- The measure is the second parameter. -/
def sumDown (acc n : Nat) : Nat := if n = 0 then acc else sumDown (acc + n) (n - 1)
partial_fixpoint

/-- The measure is the length of the list. -/
def lenP (acc : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => acc
  | _ :: xs => lenP (acc + 1) xs
partial_fixpoint

/-- The measure is the difference `n - d`: a counter going up. -/
def firstDiv (n d : Nat) : Option Nat :=
  if n ≤ d then none else if n % d = 0 then some d else firstDiv n (d + 1)
partial_fixpoint

/-- Euclid's algorithm, the measure is the second parameter. -/
def gcdP (m n : Nat) : Nat := if n = 0 then m else gcdP n (m % n)
partial_fixpoint

end PFix

def pfix_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term PFix.pfix
theorem pfix_agree : ∀ n, Term.eval pfix_term n = PFix.pfix n := by wf_agree
def sumDown_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term PFix.sumDown
theorem sumDown_agree : ∀ a n, Term.eval sumDown_term a n = PFix.sumDown a n := by wf_agree
def lenP_term : Term ⟨[.nat, .list .nat], .nat⟩ := #lean_wf_func_to_term PFix.lenP
theorem lenP_agree : ∀ a l, Term.eval lenP_term a l = PFix.lenP a l := by wf_agree
def firstDiv_term : Term ⟨[.nat, .nat], .option .nat⟩ := #lean_wf_func_to_term PFix.firstDiv
theorem firstDiv_agree : ∀ n d, Term.eval firstDiv_term n d = PFix.firstDiv n d := by wf_agree
def gcdP_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term PFix.gcdP
theorem gcdP_agree : ∀ m n, Term.eval gcdP_term m n = PFix.gcdP m n := by wf_agree

-- The measure can also be chosen by hand.
set_option wfLang.pfixMeasure 1 in
def sumDown_term' : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term PFix.sumDown
theorem sumDown_agree' : ∀ a n, Term.eval sumDown_term' a n = PFix.sumDown a n := by wf_agree

#guard Term.eval sumDown_term 0 100 == 5050
#guard (List.range 20).all fun n =>
  Term.eval pfix_term n == PFix.pfix n &&
  Term.eval sumDown_term 3 n == PFix.sumDown 3 n &&
  Term.eval firstDiv_term n 2 == PFix.firstDiv n 2 &&
  Term.eval gcdP_term 48 n == PFix.gcdP 48 n
#guard [[], [1], [1, 2, 3]].all fun l => Term.eval lenP_term 5 l == PFix.lenP 5 l
