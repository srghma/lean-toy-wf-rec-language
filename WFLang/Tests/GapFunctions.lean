import RequestProject.WFLang.Tests.Functions

/-!
# The functions of the coverage study (`GAPS.md`)

Well-founded, structural and plain Lean functions, each exercising one feature that the capture
did not handle at first.  Their captures, agreement theorems and runtime checks (or the
checked rejection messages) are in `Gaps.lean`.
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

/-! ## Grammar extensions: types, postconditions -/

/-- The termination proof of the second call uses the *postcondition* of the first call
(`r.1 ≤ n - 1`), which is available because the result is a subtype. -/
def nestedBound (n : Nat) : {r : Nat // r ≤ n} :=
  if h : n = 0 then ⟨0, by omega⟩ else
    have r := nestedBound (n - 1)
    have s := nestedBound r.1
    ⟨s.1 + 1, by have := r.2; have := s.2; omega⟩
termination_by n
decreasing_by
  · omega
  · exact Nat.lt_of_le_of_lt r.2 (by omega)

/-- `match` on a pair and a pair result. -/
def swapSteps : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | k + 1, (a, b) => swapSteps k (b, a + b)

/-- `Int` arithmetic, comparisons and conversions. -/
def intSteps (n : Int) (acc : Int) : Int :=
  if n ≤ 0 then acc - n else intSteps (n - 2) (acc + n * 3 % 5 - (n.toNat : Int))
termination_by n.toNat

/-- Structural recursion on a list, with a list result. -/
def listRev : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc => listRev xs (x :: acc)

/-- Nested list patterns; the recursive call is on the tail of the tail. -/
def listPairs : List Nat → List (Nat × Nat)
  | x :: y :: rest => (x, y) :: listPairs rest
  | _ => []

/-- Well-founded recursion on a list (by its length), with `++` and `length`. -/
def listHalve (l : List Nat) : List Nat :=
  if _h : l.length < 2 then l else listHalve (l.tail.tail) ++ [l.length]
termination_by l.length
decreasing_by simp; omega

/-! ## Higher-order code -/

/-- A call of a function with a function argument; the argument mentions the parameter `k`. -/
def useIter (k n : Nat) : Nat := Tco.iter (fun x => x + k) n 0

/-! ## Recursion through a function argument -/

/-- Well-founded recursion through the body of a `for` loop; the decrease proof uses the
hypothesis `h` of the enclosing `if`. -/
def loopRec (n : Nat) : Nat :=
  if h : n = 0 then 1 else Id.run do
    let mut s := 0
    for i in [0:3] do
      s := s + loopRec (n / 2) + i
    return s
termination_by n
decreasing_by omega

/-- Structural recursion through the function argument of `Nat.fold`. -/
def foldRec (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => Nat.fold 3 (fun i _ acc => acc + foldRec k + i) 1

/-- A user-defined higher-order function. -/
def applyN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => applyN f k (f x)

/-- Well-founded recursion through a user-defined higher-order function. -/
def viaApplyN (n : Nat) : Nat :=
  if n = 0 then 1 else applyN (fun x => viaApplyN (n - 1) + x) 2 n
termination_by n

/-- A non-recursive function calling one that recurses through a loop body. -/
def useHyperWhile (n : Nat) : Nat := Tco.hyperWhile n 2 3 + 1

/-- A recursive function calling one that recurses through a function argument. -/
def sumHyperTCO (n : Nat) : Nat := if n = 0 then 0 else sumHyperTCO (n - 1) + Tco.hyperTCO 2 n 2
termination_by n

end Gaps
