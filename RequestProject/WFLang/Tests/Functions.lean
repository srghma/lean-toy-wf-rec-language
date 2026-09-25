/-!
# The Lean functions captured by the examples

* The user's `gcd` (verbatim) and a few further well-founded functions exercising the language
  features: `digitSum` (non-tail recursion), `isPow2` (`Bool` result, `&&`, `==`), `sumTo`
  (accumulator loop).
* Namespace `Tco`: **every** function of the uploaded files `TcoAck.lean`, `TcoDiagonal.lean`,
  `TcoHyper.lean`, `TcoMc91.lean` and `TcoBoom.lean`, copied verbatim except for `ackWhile`,
  whose push order was corrected so that it computes Ackermann, and `ack999`, which is marked
  `noncomputable` (a compiled argument-free `def` is evaluated when the module is initialised,
  so every executable importing this file computed `ack 999 1` at startup and crashed with a
  stack overflow before `main` ran; see `STACK_OVERFLOW.md`) (those files imported an
  external `LeanScript` package and did not build here, so they were removed after the move).
  This includes the functions `PCL` cannot capture (`while` loops, higher-order functions,
  proof arguments): `Sources.lean` checks, function by function, that each one is either
  captured with an agreement theorem or rejected by `#lean_wf_func_to_term`.
* The theorems of the uploaded files about these functions are in `SourceProofs.lean`.

The captures and agreement theorems are in `Basic.lean`, the runtime checks in
`BasicChecks.lean`, the per-function coverage of the uploaded files in `Sources.lean`.

## Recursion kind of each function

Every definition below carries a `-- Recursion:` comment saying how Lean compiled it:
* **well-founded (WF)**: compiled via `WellFounded.fix`; the comment gives the measure
  (`termination_by`) and which / how many arguments it depends on;
* **structural**: compiled via `Nat.brecOn`; Lean's structural recursion always recurses on
  exactly one argument, which the comment names (other arguments are fixed or vary freely);
* **non-recursive**: no self-call; loops (`while`, `for`) go through the `Lean.Loop` /
  `Std.Range` `ForIn` combinators, i.e. the loop itself is `partial`, not WF or structural.

These classifications were read off Lean's own elaboration data (the WF / structural
equation info recorded for each constant), not guessed from the syntax. Only comments were
added to the uploaded functions.
-/

-- Recursion: WF, measure `n` (1 of 2 args; `m` is unconstrained), `decreasing_by` via
-- `Nat.mod_lt`. Tail recursive.
/-- The user's function (verbatim). -/
def gcd (m n : Nat) : Nat :=
  if n = 0 then m else gcd n (m % n)
termination_by n
decreasing_by
  -- uses the theorem: m % n < n when n ≠ 0
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

-- Recursion: WF, measure `n` (its only arg), inferred by Lean (no `termination_by`);
-- decreases by `n / 10 < n`. Not tail recursive (`n % 10 + …`).
/-- Sum of decimal digits (single argument; default `decreasing_by`). -/
def digitSum (n : Nat) : Nat :=
  if n < 10 then n else n % 10 + digitSum (n / 10)

-- Recursion: WF, measure `n` (its only arg), `decreasing_by omega` (`n / 2 < n`).
-- Recursive call under `&&`.
/-- Is `n` a power of two?  (Boolean result, `&&`, `==`.) -/
def isPow2 (n : Nat) : Bool :=
  if n ≤ 1 then n == 1 else n % 2 == 0 && isPow2 (n / 2)
termination_by n
decreasing_by omega

-- Recursion: WF, measure `i` (1 of 2 args; accumulator `acc` grows), default
-- `decreasing_by`. Tail recursive.
/-- Accumulator loop: `sumTo i acc = acc + i + (i-1) + … + 1`. -/
def sumTo (i acc : Nat) : Nat :=
  if i = 0 then acc else sumTo (i - 1) (acc + i)
termination_by i

namespace Tco

/-! ## From `TcoAck.lean` -/

-- Recursion: WF, lexicographic measure `(m, n)` (both args). Nested call
-- `ack m (ack (m + 1) n)`.
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

-- Recursion: non-recursive (a constant calling the WF function `ack`).
noncomputable def ack999 := ack 999 1 -- XXX: DONT TRY TO EVALUATE!!! only build Term

-- Inner recursion: structurally recursive on `n`
-- Recursion: structural on 1 arg, the `Nat` argument (2nd; `f` is a fixed parameter).
private def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)
-- Outer recursion: structurally recursive on `m`
-- Recursion: structural on 1 arg, `m` (1st); higher-order: returns `Nat → Nat`, the inner
-- recursion is delegated to `ackInner`.
def ack2 : Nat → (Nat → Nat)
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack2 m)

-- Recursion: non-recursive; a `while` loop (`Lean.Loop`, partial) over an explicit
-- `List Nat` stack.
def ackWhile (m n : Nat) : Nat := Id.run do
  let mut stack : List Nat := [m]
  let mut curN : Nat := n
  while !stack.isEmpty do
    match stack with
    | [] => break
    | top :: rest =>
      stack := rest
      if top == 0 then
        -- A(0, n) = n + 1
        curN := curN + 1
      else if curN == 0 then
        -- A(m, 0) = A(m - 1, 1)
        stack := (top - 1) :: stack
        curN := 1
      else
        -- A(m, n) = A(m - 1, A(m, n - 1))
        stack := top :: (top - 1) :: stack
        curN := curN - 1
  return curN

namespace AckWithoutStackButUsingCantorPairing

-- Cantor pairing function: encodes two Nats into one Nat
-- Recursion: non-recursive.
def pair (x y : Nat) : Nat :=
  ((x + y) * (x + y + 1)) / 2 + y

-- Integer square root helper to invert Cantor pairing
-- Recursion: non-recursive; a `while` loop (`Lean.Loop`, partial) — Newton iteration.
def isqrt (n : Nat) : Nat := Id.run do
  let mut x := n
  let mut y := (x + 1) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

-- Decode the first element from a Cantor pair
-- Recursion: non-recursive (calls `isqrt`).
def unpairLeft (z : Nat) : Nat :=
  let w := (isqrt (8 * z + 1) - 1) / 2
  let t := (w * (w + 1)) / 2
  let y := z - t
  w - y

-- Decode the second element from a Cantor pair
-- Recursion: non-recursive (calls `isqrt`).
def unpairRight (z : Nat) : Nat :=
  let w := (isqrt (8 * z + 1) - 1) / 2
  let t := (w * (w + 1)) / 2
  z - t

-- Ackermann using ONLY a while loop and Nat variables:
-- Recursion: non-recursive; a `while` loop (`Lean.Loop`, partial) with the stack encoded
-- as a Cantor-paired `Nat`.
def ackNoDataStructure (m n : Nat) : Nat := Id.run do
  -- 0 represents the empty stack.
  -- A non-empty stack is represented as pair(top, rest) + 1
  let mut s : Nat := pair m 0 + 1
  let mut curN : Nat := n

  while s != 0 do
    let code := s - 1
    let top := unpairLeft code
    s := unpairRight code

    if top == 0 then
      curN := curN + 1
    else if curN == 0 then
      -- Push top - 1
      s := pair (top - 1) s + 1
      curN := 1
    else
      -- Push top - 1, then push top
      s := pair (top - 1) s + 1
      s := pair top s + 1
      curN := curN - 1

  return curN

end AckWithoutStackButUsingCantorPairing

/-! ## From `TcoDiagonal.lean` -/

-- Recursion: WF, lexicographic measure `(m + n, m)` (both args), `decreasing_by omega`.
-- Not tail recursive (`… + 1`).
def diagonal : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     n + 1 => diagonal n 0 + 1
  | m + 1, n     => diagonal m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals omega

-- Recursion: WF, lexicographic measure `(m + n, m)` (2 of 3 args; accumulator `acc` grows),
-- `decreasing_by omega`. Tail recursive.
def diagonal_tr (m n acc : Nat) : Nat :=
  match m, n with
  | 0,     0     => acc
  | 0,     n + 1 => diagonal_tr n 0 (acc + 1)
  | m + 1, n     => diagonal_tr m (n + 1) (acc + 1)
  termination_by (m + n, m)
  decreasing_by all_goals omega

-- Recursion: non-recursive; a `while` loop (`Lean.Loop`, partial).
def diagonalWhile (m n : Nat) : Nat := Id.run do
  let mut m := m
  let mut n := n
  let mut acc := 0

  while m != 0 || n != 0 do
    acc := acc + 1
    if m > 0 then
      m := m - 1
      n := n + 1
    else
      -- Here m == 0 and n > 0
      m := n - 1
      n := 0

  return acc

/-! ## From `TcoHyper.lean` -/

-- 1. Original recursive definition
-- Recursion: WF, lexicographic measure `(n, b)` (2 of 3 args; `a` is unchanged),
-- `decreasing_by omega`. Nested call `hyper n a (hyper (n + 1) a b)`.
def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

-- Base value for each operation level at b = 0
-- Recursion: non-recursive (pattern match only).
def hyperBase : Nat → Nat → Nat
  | 0,     _ => 1
  | 1,     a => a
  | 2,     _ => 0
  | _ + 3, _ => 1

-- 2. Tail-recursive loop helper: applies `f` to `acc`, `b` times.
-- Automatically verified terminating structurally on `b`.
-- Recursion: structural on 1 arg, `b` (2nd; `f` is a fixed parameter, `acc` varies).
-- Tail recursive, higher-order (takes `f : Nat → Nat`).
def hyperLoop (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | b + 1, acc => hyperLoop f b (f acc)

-- 2. Staged TCO evaluator: structurally recursive on `n`.
-- Recursion: structural on 1 arg, `n` (1st); the recursive call `hyperTCO n a` is passed
-- partially applied to `hyperLoop`.
def hyperTCO : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a)

-- 3. Imperative evaluator using a stateful loop over level n
-- Recursion: structural on 1 arg, `n` (1st); the recursive call sits inside a
-- `for _ in [0:b]` loop body (`Std.Range` `ForIn`).
def hyperWhile : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => Id.run do
    let mut acc := hyperBase (n + 1) a
    for _ in [0:b] do
      acc := hyperWhile n a acc
    return acc

/-! ## From `TcoMc91.lean` -/

-- Recursion: non-recursive (closed form of McCarthy 91).
def mc91 (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    91

-- Tail-recursive loop helper:
-- `c` is the number of pending calls to evaluate.
-- When c = 0, all calls have completed.
-- Recursion: WF, measure `2 * (111 - n) + 21 * c` (both args), `decreasing_by omega`.
-- Tail recursive.
def mc91Loop : Nat → Nat → Nat
  | 0,     n => n
  | c + 1, n =>
    if h : n > 100 then
      mc91Loop c (n - 10)
    else
      mc91Loop (c + 1 + 1) (n + 11)
termination_by c n => 2 * (111 - n) + 21 * c
decreasing_by
  all_goals omega

-- Tail-recursive entry point (starts with 1 pending call)
-- Recursion: non-recursive (calls the WF function `mc91Loop`).
def mc91TR (n : Nat) : Nat :=
  mc91Loop 1 n

-- Recursion: non-recursive; a `while` loop (`Lean.Loop`, partial).
def mc91While (n : Nat) : Nat := Id.run do
  let mut c : Nat := 1
  let mut cur : Nat := n

  while c != 0 do
    if cur > 100 then
      cur := cur - 10
      c := c - 1
    else
      cur := cur + 11
      c := c + 1

  return cur

-- Simple function iteration helper without Mathlib
-- Recursion: structural on 1 arg, the counter `c` (2nd; `f` is a fixed parameter, `x`
-- varies). Tail recursive, higher-order.
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | c + 1, x => iter f c (f x)

/-! ## From `TcoBoom.lean` -/

-- Recursion: non-recursive (a `Prop`).
/-- Only n = 1 is a safe starting point; every other value diverges. -/
def Safe (n : Nat) : Prop := n = 1

-- Recursion: WF, measure `n` (1 of 2 args; the other is the proof `h : Safe n`). The
-- `decreasing_by` goal `3 * n < n` is discharged only because `h` makes it vacuous.
/-- Triples its argument at every step — obviously diverges for n ≠ 1.
    The proof `h : Safe n` rules out all other inputs:
    the else-branch is unreachable, proven by contradiction. -/
def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then
    0                              -- the one terminating case
  else
    boom (3 * n)                   -- blatant divergence: 1 → 3 → 9 → 27 → …
      (by simp [Safe] at h; omega) -- h : n = 1, hn : n ≠ 1 ⊢ False → anything
termination_by n
decreasing_by
  simp [Safe] at h  -- h : n = 1
  omega             -- n = 1 ∧ n ≠ 1 ⊢ False ⊢ 3 * n < n

end Tco
