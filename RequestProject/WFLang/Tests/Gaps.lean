import RequestProject.WFLang.Tests.MoreChecks
import RequestProject.WFLang.Tests.GapFunctions

/-!
# The coverage study (`GAPS.md`): captures, agreement theorems, runtime checks

Each function of `GapFunctions.lean` exercises one feature that the capture did not handle at
first: control flow (`if`/`match` with calls in non-tail position, `match` on `Bool`, literal
patterns, `match h : …`), operators, `Int`/pairs/lists, subtype results (postconditions),
bounded loops and `Nat.fold`, specialised higher-order functions, and recursion through a
function argument.  Each is captured by `#lean_wf_func_to_term`, its agreement theorem is proved
by `wf_agree`, and it is checked at runtime (`#guard_msgs`).  `underLambda` is still rejected;
its error message is pinned by `#expect_reject` (from `MoreChecks.lean`).  `GAPS.md` at the
project root describes each construct and what is left.
-/


namespace GapsPCL

open WFLang Gaps

def diteHyp_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term diteHyp
theorem diteHyp_agree : ∀ n, PCL.Term.eval diteHyp_term n = diteHyp n := by wf_agree

def fixedMid_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term fixedMid
theorem fixedMid_agree : ∀ n k, PCL.Term.eval fixedMid_term n k = fixedMid n k := by wf_agree

def fixedMid3_term : PCL.Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term fixedMid3
theorem fixedMid3_agree : ∀ n k acc,
    PCL.Term.eval fixedMid3_term n k acc = fixedMid3 n k acc := by wf_agree

def whereHelper_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term whereHelper
theorem whereHelper_agree : ∀ n, PCL.Term.eval whereHelper_term n = whereHelper n := by
  wf_agree

def ackLike_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term ackLike
theorem ackLike_agree : ∀ n m, PCL.Term.eval ackLike_term n m = ackLike n m := by wf_agree

def ifArg_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ifArg
theorem ifArg_agree : ∀ n, PCL.Term.eval ifArg_term n = ifArg n := by wf_agree


def haveProof_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term haveProof
theorem haveProof_agree : ∀ n, PCL.Term.eval haveProof_term n = haveProof n := by wf_agree

/-! ### Closed gaps: control flow and operators -/

def callInInnerIf_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term callInInnerIf
theorem callInInnerIf_agree : ∀ n, PCL.Term.eval callInInnerIf_term n = callInInnerIf n := by wf_agree
def boolMatch_term : PCL.Term ⟨[.bool, .nat], .nat⟩ := #lean_wf_func_to_term boolMatch
theorem boolMatch_agree : ∀ b n, PCL.Term.eval boolMatch_term b n = boolMatch b n := by wf_agree
def litPatterns_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term litPatterns
theorem litPatterns_agree : ∀ n, PCL.Term.eval litPatterns_term n = litPatterns n := by wf_agree
def callInAnd_term : PCL.Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term callInAnd
theorem callInAnd_agree : ∀ n, PCL.Term.eval callInAnd_term n = callInAnd n := by wf_agree
def matchEq_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term matchEq
theorem matchEq_agree : ∀ n, PCL.Term.eval matchEq_term n = matchEq n := by wf_agree
def usesPow_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesPow
theorem usesPow_agree : ∀ n, PCL.Term.eval usesPow_term n = usesPow n := by wf_agree
def usesMin_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term usesMin
theorem usesMin_agree : ∀ a b, PCL.Term.eval usesMin_term a b = usesMin a b := by wf_agree
def usesBne_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesBne
theorem usesBne_agree : ∀ n, PCL.Term.eval usesBne_term n = usesBne n := by wf_agree
def usesShift_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesShift
theorem usesShift_agree : ∀ n, PCL.Term.eval usesShift_term n = usesShift n := by wf_agree
def usesLibFns_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesLibFns
theorem usesLibFns_agree : ∀ n, PCL.Term.eval usesLibFns_term n = usesLibFns n := by wf_agree
def usesDvd_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesDvd
theorem usesDvd_agree : ∀ n, PCL.Term.eval usesDvd_term n = usesDvd n := by wf_agree
def usesXor_term : PCL.Term ⟨[.bool, .nat], .bool⟩ := #lean_wf_func_to_term usesXor
theorem usesXor_agree : ∀ b n, PCL.Term.eval usesXor_term b n = usesXor b n := by wf_agree

/-! ### Closed gaps: types other than `Nat` and `Bool`, postconditions -/

def fibPair_term : PCL.Term ⟨[.nat], .prod .nat .nat⟩ := #lean_wf_func_to_term fibPair
theorem fibPair_agree : ∀ n, PCL.Term.eval fibPair_term n = fibPair n := by wf_agree

def intDown_term : PCL.Term ⟨[.int], .int⟩ := #lean_wf_func_to_term intDown
theorem intDown_agree : ∀ n, PCL.Term.eval intDown_term n = intDown n := by wf_agree

def listSum_term : PCL.Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term listSum
theorem listSum_agree : ∀ l, PCL.Term.eval listSum_term l = listSum l := by wf_agree

/-- A subtype result `{r // r ≤ n}` becomes the postcondition `fun e v => v ≤ e.1` of the
program: it is part of the program's type, so every run satisfies it
(`PCL.PTerm.run_post`). -/
def boundedRes_term : PCL.Term ⟨[.nat], .nat⟩ (fun e v => v ≤ e.1) :=
  #lean_wf_func_to_term boundedRes
theorem boundedRes_agree : ∀ n, PCL.Term.eval boundedRes_term n = (boundedRes n).val := by
  wf_agree

/-- The decrease proof of the second recursive call uses the postcondition of the first
one. -/
def nestedBound_term : PCL.Term ⟨[.nat], .nat⟩ (fun e v => v ≤ e.1) :=
  #lean_wf_func_to_term nestedBound
theorem nestedBound_agree : ∀ n, PCL.Term.eval nestedBound_term n = (nestedBound n).val := by
  wf_agree

/-- The postcondition, for free. -/
theorem nestedBound_term_le (n : Nat) : PCL.Term.eval nestedBound_term n ≤ n :=
  PCL.PTerm.run_post nestedBound_term (n, ()) trivial

def swapSteps_term : PCL.Term ⟨[.nat, .prod .nat .nat], .prod .nat .nat⟩ :=
  #lean_wf_func_to_term swapSteps
theorem swapSteps_agree : ∀ k p, PCL.Term.eval swapSteps_term k p = swapSteps k p := by
  wf_agree

def intSteps_term : PCL.Term ⟨[.int, .int], .int⟩ := #lean_wf_func_to_term intSteps
theorem intSteps_agree : ∀ n a, PCL.Term.eval intSteps_term n a = intSteps n a := by wf_agree

def listRev_term : PCL.Term ⟨[.list .nat, .list .nat], .list .nat⟩ :=
  #lean_wf_func_to_term listRev
theorem listRev_agree : ∀ l a, PCL.Term.eval listRev_term l a = listRev l a := by wf_agree

def listPairs_term : PCL.Term ⟨[.list .nat], .list (.prod .nat .nat)⟩ :=
  #lean_wf_func_to_term listPairs
theorem listPairs_agree : ∀ l, PCL.Term.eval listPairs_term l = listPairs l := by wf_agree

def listHalve_term : PCL.Term ⟨[.list .nat], .list .nat⟩ := #lean_wf_func_to_term listHalve
theorem listHalve_agree : ∀ l, PCL.Term.eval listHalve_term l = listHalve l := by wf_agree

/-! ### Closed gaps: bounded loops

A `for i in [a:b]` loop (in `Id`) and `Nat.fold` are rewritten into `WFLang.rangeLoop`, a
first-order well-founded function with a function parameter (the loop body), which is then
specialised to the known loop body: a nested `fix` whose measure is `stop - i`. -/

def forRange_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term forRange
theorem forRange_agree : ∀ n, PCL.Term.eval forRange_term n = forRange n := by wf_agree

def usesFold_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term usesFold
theorem usesFold_agree : ∀ n, PCL.Term.eval usesFold_term n = usesFold n := by wf_agree

/-- A specialised call: the free variable `k` of the function argument becomes an extra
parameter of the nested `fix` capturing `Tco.iter (fun x => x + k)`. -/
def useIter_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useIter
theorem useIter_agree : ∀ k n, PCL.Term.eval useIter_term k n = useIter k n := by wf_agree

/-! ### Closed gaps: recursion through a function argument

`f` calls a recursive function `g` with a function argument that calls `f` again (a `for` loop
or `Nat.fold` whose body calls `f`, or a user-defined higher-order function).  `f` and the copy
of `g` specialised to that argument are captured as **one** local recursive function, with a
tag parameter selecting `f` (tag `0`) or `g` (tag `1`).  Its relation is `WFLang.hoRel`: calls
of `f` go down along `f`'s own relation, calls of `g` along `g`'s, entering `g` from `f x` is a
decrease if every call of `f` that the function argument can make is below `x`, and the
function argument calling `f` is a decrease.  The body stays in strict A-normal form. -/

def loopRec_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term loopRec
theorem loopRec_agree : ∀ n, PCL.Term.eval loopRec_term n = loopRec n := by wf_agree

def foldRec_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term foldRec
theorem foldRec_agree : ∀ n, PCL.Term.eval foldRec_term n = foldRec n := by wf_agree

def viaApplyN_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term viaApplyN
theorem viaApplyN_agree : ∀ n, PCL.Term.eval viaApplyN_term n = viaApplyN n := by wf_agree

def useHyperWhile_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term useHyperWhile
theorem useHyperWhile_agree : ∀ n, PCL.Term.eval useHyperWhile_term n = useHyperWhile n := by
  wf_agree

def sumHyperTCO_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumHyperTCO
theorem sumHyperTCO_agree : ∀ n, PCL.Term.eval sumHyperTCO_term n = sumHyperTCO n := by
  wf_agree

end GapsPCL

open WFLang Gaps GapsPCL

/-! ## Runtime checks of the accepted functions -/

/-- info: true -/
#guard_msgs in
#eval (List.range 10).all fun n => (List.range 10).all fun k => (List.range 5).all fun a =>
  PCL.Term.eval fixedMid_term n k == fixedMid n k &&
  PCL.Term.eval fixedMid3_term n k a == fixedMid3 n k a

/-- info: true -/
#guard_msgs in
#eval (List.range 50).all fun n =>
  PCL.Term.eval diteHyp_term n == diteHyp n && PCL.Term.eval whereHelper_term n == whereHelper n &&
  PCL.Term.eval ifArg_term n == ifArg n && PCL.Term.eval haveProof_term n == haveProof n

/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun n => (List.range 5).all fun m =>
  PCL.Term.eval ackLike_term n m == ackLike n m

/-- info: true -/
#guard_msgs in
#eval (List.range 40).all fun n =>
  PCL.Term.eval callInInnerIf_term n == callInInnerIf n &&
  PCL.Term.eval boolMatch_term true n == boolMatch true n &&
  PCL.Term.eval boolMatch_term false n == boolMatch false n &&
  PCL.Term.eval litPatterns_term n == litPatterns n &&
  PCL.Term.eval callInAnd_term n == callInAnd n &&
  PCL.Term.eval matchEq_term n == matchEq n &&
  PCL.Term.eval usesPow_term n == usesPow n &&
  PCL.Term.eval usesBne_term n == usesBne n &&
  PCL.Term.eval usesShift_term n == usesShift n &&
  PCL.Term.eval usesLibFns_term n == usesLibFns n &&
  PCL.Term.eval usesDvd_term n == usesDvd n &&
  PCL.Term.eval usesXor_term true n == usesXor true n &&
  PCL.Term.eval usesXor_term false n == usesXor false n &&
  (List.range 12).all fun a => PCL.Term.eval usesMin_term a n == usesMin a n

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun n =>
  PCL.Term.eval fibPair_term n == fibPair n &&
  PCL.Term.eval boundedRes_term n == (boundedRes n).val &&
  PCL.Term.eval swapSteps_term n (n, 1) == swapSteps n (n, 1) &&
  PCL.Term.eval listSum_term (List.range n) == listSum (List.range n) &&
  PCL.Term.eval listRev_term (List.range n) [n] == listRev (List.range n) [n] &&
  PCL.Term.eval listPairs_term (List.range n) == listPairs (List.range n) &&
  PCL.Term.eval listHalve_term (List.range n) == listHalve (List.range n) &&
  [-3, 0, 7].all fun (a : Int) =>
    PCL.Term.eval intDown_term (n - 10 : Int) == intDown (n - 10 : Int) &&
    PCL.Term.eval intSteps_term (n - 5 : Int) a == intSteps (n - 5 : Int) a

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun n =>
  PCL.Term.eval forRange_term n == forRange n && PCL.Term.eval usesFold_term n == usesFold n &&
  PCL.Term.eval useIter_term 3 n == useIter 3 n

/-- info: true -/
#guard_msgs in
#eval (List.range 10).all fun n =>
  PCL.Term.eval loopRec_term n == loopRec n && PCL.Term.eval foldRec_term n == foldRec n &&
  PCL.Term.eval viaApplyN_term n == viaApplyN n &&
  PCL.Term.eval sumHyperTCO_term n == sumHyperTCO n

-- `useHyperWhile n` computes the `n`-th hyperoperation (`useHyperWhile 5` is `2 ↑↑↑ 3 + 1`).
/-- info: true -/
#guard_msgs in
#eval (List.range 5).all fun n => PCL.Term.eval useHyperWhile_term n == useHyperWhile n

-- `nestedBound` makes `2 ^ n` calls, so it is only checked on small inputs.
/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun n => PCL.Term.eval nestedBound_term n == (nestedBound n).val

/-! ## Rejections -/

-- A recursive call under `fun` in `List.map` over `List.attach`: `List.map` is a library
-- function (not specialised), and the elements of `attach` are subtypes whose property the
-- termination proof needs.
/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term underLambda : PCL.Term ⟨[.nat], .nat⟩)

