import RequestProject.WFLang.Tests.Functions

/-!
# Further Lean functions, exercising the features added to the capture

* **fixed parameters** (parameters passed unchanged to every recursive call, which Lean keeps
  outside of the `WellFounded.fix`): `addK`, `powMod`, `countDown`, `countAbove`;
* **structural recursion** (no `termination_by`; Lean uses the recursor instead of
  `WellFounded.fix`): `fact`, `evenS`, `addIter`, `fib`;
* **calls to other functions**: non-recursive ones are inlined (`double` in `sumDoubles`),
  recursive ones become nested `fix` nodes (`gcd` in `gcdSum`, `lcmGcd`,
  `countCoprime`; `fact` in `sumFacts`; several of them in `chain`; two loops in `twoLoops`;
  `Tco.mc91Loop` in the uploaded `Tco.mc91TR`);
* a call of a recursive function inside the body of a recursive function (`gcdLoop`);
* a pair of functions that must be **rejected** (`Mutual.isEven`/`isOdd`: mutual recursion).

The captures and agreement theorems are in `More.lean`, the runtime checks and rejections in
`MoreChecks.lean`.
-/

namespace More

/-! ## Fixed parameters -/

/-- `k` is fixed. -/
def addK (k : Nat) (n : Nat) : Nat := if n = 0 then k else addK k (n - 1) + 1
termination_by n

/-- `b` and `m` are fixed. -/
def powMod (b m e : Nat) : Nat := if e = 0 then 1 % m else (b * powMod b m (e - 1)) % m
termination_by e

/-- `k` is fixed, and the measure `n - k` mentions it. -/
def countDown (k n acc : Nat) : Nat := if n ≤ k then acc else countDown k (n - 1) (acc + 1)
termination_by n - k

/-- A fixed `Bool` parameter and a fixed `Nat` parameter. -/
def countAbove (strict : Bool) (k n : Nat) : Nat :=
  if n = 0 then 0
  else (if (strict && k < n) || (!strict && k ≤ n) then 1 else 0) + countAbove strict k (n - 1)
termination_by n

/-- A `Bool` parameter that changes at every call (not fixed). -/
def flipB (b : Bool) (n : Nat) : Bool := if n = 0 then b else flipB (!b) (n - 1)
termination_by n

/-! ## Structural recursion -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def evenS : Nat → Bool
  | 0 => true
  | n + 1 => !evenS n

/-- Structural on the third parameter, `k` fixed, `m` changing. -/
def addIter (k : Nat) (m : Nat) : Nat → Nat
  | 0 => m + k
  | n + 1 => addIter k (m + 1) n

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-! ## Calls to other functions -/

/-- Non-recursive helper (inlined by the capture). -/
def double (n : Nat) : Nat := n + n

def sumDoubles (n : Nat) : Nat := if n = 0 then 0 else double n + sumDoubles (n - 1)
termination_by n

/-- Calls the user's `gcd` in a recursive function. -/
def gcdSum (n : Nat) : Nat := if n = 0 then 0 else gcd n 12 + gcdSum (n - 1)
termination_by n

/-- Non-recursive, calls `gcd`. -/
def lcmGcd (a b : Nat) : Nat := if a = 0 then 0 else a * b / gcd a b

/-- A call of `gcd` inside the test of an `if` that is not in tail position. -/
def countCoprime (n i : Nat) : Nat :=
  if i = 0 then 0 else (if gcd n i == 1 then 1 else 0) + countCoprime n (i - 1)
termination_by i

/-- A recursive function calling a structurally recursive one. -/
def sumFacts (n : Nat) : Nat := if n = 0 then 1 else fact n + sumFacts (n - 1)
termination_by n

/-- Nested calls of several recursive functions (and, through `gcdSum`, of `gcd`). -/
def chain (n : Nat) : Nat := gcdSum (fact (n % 5)) + addK n (digitSum n)

/-- Two tail-recursive functions called from a non-recursive one (and a call in a test). -/
def twoLoops (n : Nat) : Nat :=
  if gcd n 6 = 1 then sumTo n 0 else Tco.mc91Loop 1 (gcd n 10)

/-- A call of `gcd` in the body of a tail-recursive function. -/
def gcdLoop (n acc : Nat) : Nat := if n = 0 then acc else gcdLoop (n - 1) (acc + gcd n 6)
termination_by n

end More

namespace More.Mutual

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

end More.Mutual
