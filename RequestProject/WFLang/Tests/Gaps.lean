import RequestProject.WFLang.Tests.MoreChecks

/-!
# Coverage gaps: well-founded functions the capture does not (yet) handle

Each function below is a well-founded (or structurally recursive, or plain) Lean function.
The `#guard_msgs` blocks record what `#lean_wf_func_to_term` currently does with it, so the
build fails as soon as that changes.  `GAPS.md` at the project root classifies these gaps
by how much work each would take to support.

* **Accepted**: captured, agreement theorem proved by `wf_agree`, and checked at runtime.
  `fixedMid`/`fixedMid3` (a fixed parameter that is not the first one), `whereHelper` (a
  non-recursive function with a recursive `where` helper) and `haveProof` (a `have` using the
  hypothesis of `if h : …`) were rejected or failed before, and were fixed together with this
  file.
* **Rejected**: `#expect_reject` (from `MoreChecks.lean`) succeeds only if the capture fails,
  and prints the first line of the error.
-/

namespace Gaps

/-! ## Accepted -/

/-- `if h : …` whose hypothesis is only used by the termination proof. -/
def diteHyp (n : Nat) : Nat := if _h : n = 0 then 0 else diteHyp (n - 1) + 1
termination_by n

/-- A fixed parameter `k` that is *not* the first parameter (Lean moves it in front of the
`WellFounded.fix`). -/
def fixedMid (n k : Nat) : Nat := if n = 0 then k else fixedMid (n - 1) k + 1
termination_by n

/-- Fixed parameter between two changing ones. -/
def fixedMid3 (n k acc : Nat) : Nat := if n = 0 then acc + k else fixedMid3 (n - 1) k (acc + n)
termination_by n

/-- A non-recursive function with a recursive `where` helper. -/
def whereHelper (n : Nat) : Nat := go n 0
where go (i acc : Nat) : Nat := if i = 0 then acc else go (i - 1) (acc + i)
termination_by i

/-- Two-scrutinee `match` with a nested call (Ackermann-like). -/
def ackLike : Nat → Nat → Nat
  | 0, m => m + 1
  | n + 1, 0 => ackLike n 1
  | n + 1, m + 1 => ackLike n (ackLike (n + 1) m)
termination_by n m => (n, m)

/-- An `if` in the argument of a recursive call. -/
def ifArg (n : Nat) : Nat := if n = 0 then 0 else ifArg (if n % 2 = 0 then n / 2 else n - 1) + 1
termination_by n
decreasing_by split <;> omega

/-- The decrease is proved by a `have` that uses the hypothesis of the `if h : …`. -/
def haveProof (n : Nat) : Nat := if h : n = 0 then 0 else
  have : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
  haveProof (n / 2) + 1

/-! ## Rejected: control flow the capture does not translate (grammar already sufficient) -/

/-- A recursive call inside a branch of an `if` that is not in tail position. -/
def callInInnerIf (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + (if n % 2 = 0 then callInInnerIf (n / 2) else callInInnerIf (n - 1))
termination_by n
decreasing_by all_goals omega

/-- `match` on a `Bool`. -/
def boolMatch (b : Bool) (n : Nat) : Nat := match b with
  | true => if n = 0 then 1 else boolMatch false (n - 1)
  | false => if n = 0 then 0 else boolMatch true (n - 1)
termination_by n

/-- `match` with literal patterns other than `0` / `n + 1`. -/
def litPatterns : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 5 => 50
  | n + 2 => litPatterns n + 1

/-- A recursive call on the right of `&&` in non-tail position. -/
def callInAnd (n : Nat) : Bool := if n = 0 then true else !(n % 3 == 0 && callInAnd (n - 1))
termination_by n


/-- `match h : e with`, which names the equation. -/
def matchEq (n : Nat) : Nat := match _h : n % 3 with
  | 0 => if n = 0 then 0 else matchEq (n - 1)
  | _ => if n = 0 then 1 else matchEq (n - 1)
termination_by n

/-! ## Rejected: operators missing from the grammar -/

def usesPow (n : Nat) : Nat := if n = 0 then 1 else 2 ^ n + usesPow (n - 1)
termination_by n

def usesMin (a b : Nat) : Nat := if b = 0 then a else usesMin (min a b) (b - 1)
termination_by b

def usesBne (n : Nat) : Nat := if n != 0 then usesBne (n - 1) + 1 else 0
termination_by n
decreasing_by simp_all; omega

def usesShift (n : Nat) : Nat := if n = 0 then 0 else 1 + usesShift (n >>> 1)
termination_by n
decreasing_by simp only [Nat.shiftRight_eq_div_pow]; omega

def usesLibFns (n : Nat) : Nat := if n = 0 then 0 else Nat.gcd n 6 + usesLibFns (Nat.pred n)
termination_by n
decreasing_by simp_wf; omega

def usesDvd (n : Nat) : Nat := if n = 0 then 0 else (if 3 ∣ n then 1 else 0) + usesDvd (n - 1)
termination_by n

def usesXor (b : Bool) (n : Nat) : Bool := if n = 0 then b else usesXor (xor b true) (n - 1)
termination_by n

/-! ## Rejected: types other than `Nat` and `Bool` -/

def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let p := fibPair n; (p.2, p.1 + p.2)

def intDown (n : Int) : Int := if n ≤ 0 then 0 else intDown (n - 1) + 2
termination_by n.toNat

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Result in a subtype, so that the result's bound is available to termination proofs. -/
def boundedRes (n : Nat) : {r : Nat // r ≤ n} := if h : n = 0 then ⟨0, by omega⟩ else
  let r := boundedRes (n - 1); ⟨r.1, by have := r.2; omega⟩
termination_by n

/-! ## Rejected: higher-order code -/

/-- A recursive call under a `fun` (via `List.attach`). -/
def underLambda (n : Nat) : Nat :=
  if n = 0 then 1 else ((List.range n).attach.map fun ⟨i, _⟩ => underLambda i).sum
termination_by n
decreasing_by rename_i h; simp at h; omega

/-- A bounded `for` loop (terminating, unlike `while`). -/
def forRange (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do s := s + i
  return s

/-- A library iterator with a function argument. -/
def usesFold (n : Nat) : Nat := Nat.fold n (fun i _ acc => acc + i) 0

end Gaps

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

/-! ## Rejections -/

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term callInInnerIf : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term boolMatch : PCL.Term ⟨[.bool, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term litPatterns : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term callInAnd : PCL.Term ⟨[.nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term matchEq : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesPow : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesMin : PCL.Term ⟨[.nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesBne : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesShift : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesLibFns : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported condition -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesDvd : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesXor : PCL.Term ⟨[.bool, .nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Nat × Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term fibPair : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Int (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term intDown : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type List Nat (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term listSum : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type { r // r ≤ n } (only Nat and Bool) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term boundedRes : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call in an unsupported position -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term underLambda : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term forRange : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term usesFold : PCL.Term ⟨[.nat], .nat⟩)
