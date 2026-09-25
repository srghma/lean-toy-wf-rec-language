import RequestProject.WFLang.Capture
import RequestProject.WFLang.Examples.MoreFunctions

/-!
# Captures of the functions of `MoreFunctions.lean`, with agreement theorems

Each program is produced by `#lean_wf_func_to_term`, and each agreement theorem is proved by
`wf_agree`.

| function       | feature                                   | `PCL` | `Tail` | `Meas` | wrapper designs |
|----------------|-------------------------------------------|:-----:|:------:|:------:|:---------------:|
| `addK`         | fixed parameter                           | ✓     | –      | ✓      | all four        |
| `powMod`       | two fixed parameters                      | ✓     | –      | ✓      | `Guarded`       |
| `countDown`    | fixed parameter in the measure `n - k`    | ✓     | ✓      | ✓      | `FreeCall`      |
| `countAbove`   | fixed `Bool` and `Nat` parameters         | ✓     | –      | ✓      | `Checked`       |
| `flipB`        | changing `Bool` parameter                 | ✓     | ✓      | ✓      | –               |
| `fact`         | structural recursion                      | ✓     | –      | ✓      | `Guarded`       |
| `evenS`        | structural recursion, `Bool` result       | ✓     | –      | ✓      | `GuardedAcc`    |
| `addIter`      | structural, fixed parameter               | ✓     | ✓      | ✓      | `Checked`       |
| `fib`          | structural, two calls, pattern `n + 2`    | ✓     | –      | ✓      | `FreeCall`      |
| `sumDoubles`   | calls a non-recursive function (inlined)  | ✓     | –      | ✓      | `Guarded`       |
| `gcdSum`       | calls `gcd` (nested `fix`)                | ✓     | –      | ✓      | –               |
| `lcmGcd`       | non-recursive, calls `gcd`                | ✓     | ✓      | ✓      | –               |
| `countCoprime` | call of `gcd` in a test                   | ✓     | –      | ✓      | –               |
| `sumFacts`     | calls the structural `fact`               | ✓     | –      | ✓      | –               |
| `chain`        | nested calls of four recursive functions  | ✓     | –      | ✓      | –               |
| `twoLoops`     | two loops and calls in a test             | ✓     | ✓      | ✓      | –               |
| `gcdLoop`      | call of `gcd` in a loop body              | ✓     | –      | ✓      | –               |
| `Tco.mc91TR`   | the uploaded function (calls `mc91Loop`)  | ✓     | ✓      | ✓      | –               |

A `–` in the `Tail` column means the function is not tail recursive, or (for `gcdLoop`) calls
another loop from its loop body; a `–` in the last column means the wrapper grammar (a single
self-recursive body) has no local recursive functions.  The rejections are checked in
`MoreChecks.lean`.
-/

open WFLang
open More

/-! ## `PCL` -/

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

end MorePCL

/-! ## `Tail` -/

namespace MoreTail
open Tail

def countDown_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term countDown
theorem countDown_agree : ∀ k n a, Term.eval countDown_term k n a = countDown k n a := by
  wf_agree

def flipB_term : Term ⟨[.bool, .nat], .bool⟩ := #lean_wf_func_to_term flipB
theorem flipB_agree : ∀ b n, Term.eval flipB_term b n = flipB b n := by wf_agree

def addIter_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term addIter
theorem addIter_agree : ∀ k m n, Term.eval addIter_term k m n = addIter k m n := by wf_agree

def lcmGcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term lcmGcd
theorem lcmGcd_agree : ∀ a b, Term.eval lcmGcd_term a b = lcmGcd a b := by wf_agree

def twoLoops_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term twoLoops
theorem twoLoops_agree : ∀ n, Term.eval twoLoops_term n = twoLoops n := by wf_agree

def mc91TR_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Tco.mc91TR
theorem mc91TR_agree : ∀ n, Term.eval mc91TR_term n = Tco.mc91TR n := by wf_agree

end MoreTail

/-! ## `Meas` -/

namespace MoreMeas
open Meas

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

end MoreMeas

/-! ## The wrapper designs -/

namespace MoreWrapper

def addK_guarded : Guarded.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term addK
theorem addK_guarded_agree : ∀ k n, Guarded.Term.eval addK_guarded k n = addK k n := by
  wf_agree

def addK_guardedAcc : GuardedAcc.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term addK
theorem addK_guardedAcc_agree : ∀ k n, GuardedAcc.Term.eval addK_guardedAcc k n = addK k n := by
  wf_agree

def addK_freeCall : FreeCall.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term addK
theorem addK_freeCall_agree : ∀ k n, FreeCall.Term.eval addK_freeCall k n = addK k n := by
  wf_agree

def addK_checked : Checked.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term addK
theorem addK_checked_agree : ∀ k n, Checked.Term.eval addK_checked k n = addK k n := by
  wf_agree

def powMod_guarded : Guarded.Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term powMod
theorem powMod_guarded_agree : ∀ b m e,
    Guarded.Term.eval powMod_guarded b m e = powMod b m e := by wf_agree

def countDown_freeCall : FreeCall.Term ⟨[.nat, .nat, .nat], .nat⟩ :=
  #lean_wf_func_to_term countDown
theorem countDown_freeCall_agree : ∀ k n a,
    FreeCall.Term.eval countDown_freeCall k n a = countDown k n a := by wf_agree

def countAbove_checked : Checked.Term ⟨[.bool, .nat, .nat], .nat⟩ :=
  #lean_wf_func_to_term countAbove
theorem countAbove_checked_agree : ∀ s k n,
    Checked.Term.eval countAbove_checked s k n = countAbove s k n := by wf_agree

def fact_guarded : Guarded.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term fact
theorem fact_guarded_agree : ∀ n, Guarded.Term.eval fact_guarded n = fact n := by wf_agree

def evenS_guardedAcc : GuardedAcc.Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term evenS
theorem evenS_guardedAcc_agree : ∀ n, GuardedAcc.Term.eval evenS_guardedAcc n = evenS n := by
  wf_agree

def addIter_checked : Checked.Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term addIter
theorem addIter_checked_agree : ∀ k m n,
    Checked.Term.eval addIter_checked k m n = addIter k m n := by wf_agree

def fib_freeCall : FreeCall.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term fib
theorem fib_freeCall_agree : ∀ n, FreeCall.Term.eval fib_freeCall n = fib n := by wf_agree

def sumDoubles_guarded : Guarded.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumDoubles
theorem sumDoubles_guarded_agree : ∀ n,
    Guarded.Term.eval sumDoubles_guarded n = sumDoubles n := by wf_agree

end MoreWrapper
