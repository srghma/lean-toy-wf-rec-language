import RequestProject.WFLang.Capture.Elab
import RequestProject.WFLang.Tests.MoreFunctions

/-!
# Captures of the functions of `MoreFunctions.lean`, with agreement theorems

Each program is produced by `#lean_wf_func_to_term`, and each agreement theorem is proved by
`wf_agree`.

| function       | feature                                   |
|----------------|-------------------------------------------|
| `addK`         | fixed parameter                           |
| `powMod`       | two fixed parameters                      |
| `countDown`    | fixed parameter in the measure `n - k`    |
| `countAbove`   | fixed `Bool` and `Nat` parameters         |
| `flipB`        | changing `Bool` parameter                 |
| `fact`         | structural recursion                      |
| `evenS`        | structural recursion, `Bool` result       |
| `addIter`      | structural, fixed parameter               |
| `fib`          | structural, two calls, pattern `n + 2`    |
| `sumDoubles`   | calls a non-recursive function (inlined)  |
| `gcdSum`       | calls `gcd` (nested `fix`)                |
| `lcmGcd`       | non-recursive, calls `gcd`                |
| `countCoprime` | call of `gcd` in a test                   |
| `sumFacts`     | calls the structural `fact`               |
| `chain`        | nested calls of four recursive functions  |
| `twoLoops`     | two loops and calls in a test             |
| `gcdLoop`      | call of `gcd` inside a recursive body     |
| `Tco.mc91TR`   | the uploaded function (calls `mc91Loop`)  |

The rejections are checked in `MoreChecks.lean` (mutual recursion) and `Sources.lean` (the
uploaded functions with `while` loops, function arguments or proof arguments).
-/

open WFLang
open More

namespace MorePCL
open PCL

def addK_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term addK
theorem addK_agree : ∀ k n, Term.eval addK_term k n = addK k n := by wf_agree

def powMod_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term powMod
theorem powMod_agree : ∀ b m e, Term.eval powMod_term b m e = powMod b m e := by wf_agree

def countDown_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term countDown
theorem countDown_agree : ∀ k n a, Term.eval countDown_term k n a = countDown k n a := by
  wf_agree

def countAbove_term : Term ⟨[.bool, .nat, .nat], .nat⟩ := #lean_wf_func_to_term countAbove
theorem countAbove_agree : ∀ s k n, Term.eval countAbove_term s k n = countAbove s k n := by
  wf_agree

def flipB_term : Term ⟨[.bool, .nat], .bool⟩ := #lean_wf_func_to_term flipB
theorem flipB_agree : ∀ b n, Term.eval flipB_term b n = flipB b n := by wf_agree

def fact_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term fact
theorem fact_agree : ∀ n, Term.eval fact_term n = fact n := by wf_agree

def evenS_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term evenS
theorem evenS_agree : ∀ n, Term.eval evenS_term n = evenS n := by wf_agree

def addIter_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term addIter
theorem addIter_agree : ∀ k m n, Term.eval addIter_term k m n = addIter k m n := by wf_agree

def fib_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term fib
theorem fib_agree : ∀ n, Term.eval fib_term n = fib n := by wf_agree

def sumDoubles_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumDoubles
theorem sumDoubles_agree : ∀ n, Term.eval sumDoubles_term n = sumDoubles n := by wf_agree

def gcdSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term gcdSum
theorem gcdSum_agree : ∀ n, Term.eval gcdSum_term n = gcdSum n := by wf_agree

def lcmGcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term lcmGcd
theorem lcmGcd_agree : ∀ a b, Term.eval lcmGcd_term a b = lcmGcd a b := by wf_agree

def countCoprime_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term countCoprime
theorem countCoprime_agree : ∀ n i, Term.eval countCoprime_term n i = countCoprime n i := by
  wf_agree

def sumFacts_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumFacts
theorem sumFacts_agree : ∀ n, Term.eval sumFacts_term n = sumFacts n := by wf_agree

def chain_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term chain
theorem chain_agree : ∀ n, Term.eval chain_term n = chain n := by wf_agree

def twoLoops_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term twoLoops
theorem twoLoops_agree : ∀ n, Term.eval twoLoops_term n = twoLoops n := by wf_agree

def gcdLoop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdLoop
theorem gcdLoop_agree : ∀ n a, Term.eval gcdLoop_term n a = gcdLoop n a := by wf_agree

def mc91TR_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91TR
theorem mc91TR_agree : ∀ n, Term.eval mc91TR_term n = Tco.mc91TR n := by wf_agree

/-! ### Mutual recursion

A group of mutually recursive functions is captured as **one** local recursive function whose
first parameter is a tag selecting the member; a call of the `i`-th member is a recursive call
with tag `i`.  The relation is the one Lean built for the group, pulled back along
`(i, xs) ↦ PSum.inl/inr xs`. -/

def isEven_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term Mutual.isEven
theorem isEven_agree : ∀ n, Term.eval isEven_term n = Mutual.isEven n := by wf_agree

def isOdd_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term Mutual.isOdd
theorem isOdd_agree : ∀ n, Term.eval isOdd_term n = Mutual.isOdd n := by wf_agree

def downA_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Mutual.downA
theorem downA_agree : ∀ n, Term.eval downA_term n = Mutual.downA n := by wf_agree

def downB_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Mutual.downB
theorem downB_agree : ∀ n, Term.eval downB_term n = Mutual.downB n := by wf_agree

def mod3b_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Mutual.mod3b
theorem mod3b_agree : ∀ n, Term.eval mod3b_term n = Mutual.mod3b n := by wf_agree

end MorePCL
