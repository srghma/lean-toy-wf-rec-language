/-!
# The Lean functions captured by the examples

* The user's `gcd` (verbatim) and a few further well-founded functions exercising the language
  features: `digitSum` (non-tail recursion), `isPow2` (`Bool` result, `&&`, `==`), `sumTo`
  (accumulator loop).
* Namespace `Tco`: the functions of the uploaded files `TcoAck.lean`, `TcoDiagonal.lean`,
  `TcoHyper.lean`, `TcoMc91.lean`, `TcoBoom.lean`, copied verbatim (those files import a module
  `LeanScript` that is not part of the project).

The captures and agreement theorems are in `Wrapper.lean` (the four wrapper designs) and
`Langs.lean` (the grammars `PCL`, `Tail`, `Meas`).
-/

/-- The user's function (verbatim). -/
def gcd (m n : Nat) : Nat :=
  if n = 0 then m else gcd n (m % n)
termination_by n
decreasing_by
  -- uses the theorem: m % n < n when n ≠ 0
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Sum of decimal digits (single argument; default `decreasing_by`). -/
def digitSum (n : Nat) : Nat :=
  if n < 10 then n else n % 10 + digitSum (n / 10)

/-- Is `n` a power of two?  (Boolean result, `&&`, `==`.) -/
def isPow2 (n : Nat) : Bool :=
  if n ≤ 1 then n == 1 else n % 2 == 0 && isPow2 (n / 2)
termination_by n
decreasing_by omega

/-- Accumulator loop: `sumTo i acc = acc + i + (i-1) + … + 1`. -/
def sumTo (i acc : Nat) : Nat :=
  if i = 0 then acc else sumTo (i - 1) (acc + i)
termination_by i

namespace Tco

/-! ## The functions (verbatim) -/

def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def diagonal : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     n + 1 => diagonal n 0 + 1
  | m + 1, n     => diagonal m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals omega

def diagonal_tr (m n acc : Nat) : Nat :=
  match m, n with
  | 0,     0     => acc
  | 0,     n + 1 => diagonal_tr n 0 (acc + 1)
  | m + 1, n     => diagonal_tr m (n + 1) (acc + 1)
  termination_by (m + n, m)
  decreasing_by all_goals omega

def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

def hyperBase : Nat → Nat → Nat
  | 0,     _ => 1
  | 1,     a => a
  | 2,     _ => 0
  | _ + 3, _ => 1

def mc91 (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    91

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

def pair (x y : Nat) : Nat :=
  ((x + y) * (x + y + 1)) / 2 + y

def Safe (n : Nat) : Prop := n = 1

def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then
    0
  else
    boom (3 * n)
      (by simp [Safe] at h; omega)
termination_by n
decreasing_by
  simp [Safe] at h
  omega

def mc91TR (n : Nat) : Nat :=
  mc91Loop 1 n

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | c + 1, x => iter f c (f x)

end Tco
