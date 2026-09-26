import RequestProject.WFLang.Tests.MoreChecks

/-!
# Global functions and `@[inlinable]`

`#lean_wf_func_to_term f` treats a call of another user-defined function `g` according to
`g`'s attribute:

* `g` marked **`@[inlinable]`**: the call is inlined.  A non-recursive `g` is replaced by its
  body; a tail-recursive `g` becomes a loop (a recursive join point) at the call site, which
  reads the caller's variables and jumps to the rest of the caller's computation when it is
  done (see `Tests/Loops.lean`).  A recursive `g` with non-tail self calls (`sumToI` below)
  cannot be a loop: it becomes a global function, like a function without the attribute.
* `g` **not** marked `@[inlinable]`: `g` is a **global function** of the program.  It is
  captured once, as an entry of the global context (`PTerm.globals`, a `Globals` list whose
  entries may call the entries before them), and each call is `Expr.gCall i args` where `i`
  is `g`'s index in the global context.

Functions with function parameters are specialised to the function passed at each call (one
global function per specialisation); a group of mutually recursive functions is one global
function (with a tag selecting the member).  The captured function itself, when it is
recursive, is also a global function, and the main statement calls it.

A call of a global function only knows the postcondition of the callee (its subtype
property, if any), not its definition.  When a termination proof of the caller needs the
value computed by a non-recursive helper (e.g. `half n < n`), the helper must be
`@[inlinable]` (`logHalf` below).

The measures `PTerm.nglobals` (entries of the global context), `PTerm.gcalls` (calls of global
functions), `PTerm.loops` (recursive join points) and `PTerm.size` (statement nodes, global
bodies included) are pinned below.
-/

namespace GlobalsEx

/-- A non-recursive helper: a global function. -/
def triple (n : Nat) : Nat := 3 * n

/-- The same helper, inlined. -/
@[inlinable] def tripleI (n : Nat) : Nat := 3 * n

/-- A recursive function: a global function. -/
def sumTo (n : Nat) : Nat := if n = 0 then 0 else n + sumTo (n - 1)
termination_by n

/-- The same function, marked `@[inlinable]`: its self call is not a tail call, so it is still
a global function. -/
@[inlinable] def sumToI (n : Nat) : Nat := if n = 0 then 0 else n + sumToI (n - 1)
termination_by n

/-- Three calls of the global `sumTo` and two of the global `triple`: two global functions,
five calls. -/
def useGlobals (a b : Nat) : Nat := sumTo a + sumTo b + sumTo (triple a) + triple b

/-- The same with the inlinable functions: `tripleI` disappears, and `sumToI` (not
tail-recursive) is a global function called three times. -/
def useInlined (a b : Nat) : Nat := sumToI a + sumToI b + sumToI (tripleI a) + tripleI b

/-- A global function calling another global function: the global context is ordered, callees
first (`triple` before `sumTriple`). -/
def sumTriple (n : Nat) : Nat := if n = 0 then 0 else triple n + sumTriple (n - 1)
termination_by n

def useChain (n : Nat) : Nat := sumTriple n + triple n

/-- A recursive function calling a global function in its body. -/
def countTriples (n acc : Nat) : Nat :=
  if n = 0 then acc else countTriples (n - 1) (acc + triple n)
termination_by n

/-- A helper whose value the termination proof of `logHalf` needs: it must be inlined. -/
@[inlinable] def half (n : Nat) : Nat := n / 2

def logHalf (n : Nat) : Nat := if n = 0 then 0 else 1 + logHalf (half n)
termination_by n
decreasing_by simp only [half]; omega

/-- `half`, not inlinable. -/
def halfG (n : Nat) : Nat := n / 2

def logHalfG (n : Nat) : Nat := if n = 0 then 0 else 1 + logHalfG (halfG n)
termination_by n
decreasing_by simp only [halfG]; omega

/-- A global function with a subtype result: callers know its postcondition. -/
def pred' (n : Nat) : {m : Nat // m ≤ n} := ⟨n - 1, Nat.sub_le n 1⟩

/-- The recursive call on the result of the global `pred'` terminates thanks to its
postcondition. -/
def downBy (n : Nat) : Nat :=
  if h : n = 0 then 0 else
    have hlt : (pred' (n - 1)).1 < n := Nat.lt_of_le_of_lt (pred' (n - 1)).2 (by omega)
    1 + downBy (pred' (n - 1)).1
termination_by n

end GlobalsEx

namespace ExGlobals
open WFLang PCL GlobalsEx

def useGlobals_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useGlobals
theorem useGlobals_agree : ∀ a b, Term.eval useGlobals_term a b = useGlobals a b := by wf_agree

def useInlined_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useInlined
theorem useInlined_agree : ∀ a b, Term.eval useInlined_term a b = useInlined a b := by wf_agree

def useChain_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term useChain
theorem useChain_agree : ∀ n, Term.eval useChain_term n = useChain n := by wf_agree

def countTriples_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term countTriples
theorem countTriples_agree : ∀ n acc, Term.eval countTriples_term n acc = countTriples n acc := by
  wf_agree

def logHalf_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term logHalf
theorem logHalf_agree : ∀ n, Term.eval logHalf_term n = logHalf n := by wf_agree

def downBy_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term downBy
theorem downBy_agree : ∀ n, Term.eval downBy_term n = downBy n := by wf_agree

/-- The uploaded `gcd` called from a function of the test suite: a global function. -/
def gcdTwice (m n : Nat) : Nat := gcd m n + gcd n m

def gcdTwice_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdTwice
theorem gcdTwice_agree : ∀ m n, Term.eval gcdTwice_term m n = gcdTwice m n := by wf_agree

/-! ## A helper needed by a termination proof must be inlined

`logHalfG` is `logHalf` with a helper `halfG` that is not `@[inlinable]`: the recursive call
`logHalfG v` receives the result `v` of the global call `halfG n`, and the decrease proof
`v < n` cannot be found (the program only knows the postcondition of `halfG`, which is
`True`), so `#lean_wf_func_to_term GlobalsEx.logHalfG` reports a termination error. -/

/-! ## The shape of the programs -/

-- Entries of the global context: `useGlobals` has `sumTo` and `triple`, `useInlined` `sumToI`,
-- `useChain` has `triple` and `sumTriple`, `countTriples` has `triple` and itself, `logHalf`
-- itself (`half` is inlined), `downBy` `pred'` and itself, `gcdTwice` `gcd`.
/-- info: [2, 1, 2, 2, 1, 2, 1] -/
#guard_msgs in
#eval [useGlobals_term.nglobals, useInlined_term.nglobals, useChain_term.nglobals,
  countTriples_term.nglobals, logHalf_term.nglobals, downBy_term.nglobals,
  gcdTwice_term.nglobals]

-- Calls of global functions (`sumTriple`'s body calls `triple` once; the recursive programs
-- `countTriples`, `logHalf` and `downBy` call themselves once from the main statement, and their
-- recursive calls are self calls, not global calls).
/-- info: [5, 3, 3, 2, 1, 2, 2] -/
#guard_msgs in
#eval [useGlobals_term.gcalls, useInlined_term.gcalls, useChain_term.gcalls,
  countTriples_term.gcalls, logHalf_term.gcalls, downBy_term.gcalls, gcdTwice_term.gcalls]

-- Loops: none of these programs calls a tail-recursive `@[inlinable]` function.
/-- info: [0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval [useGlobals_term.loops, useInlined_term.loops, useChain_term.loops,
  countTriples_term.loops, logHalf_term.loops, downBy_term.loops, gcdTwice_term.loops]

-- Statement nodes (global bodies included): both programs share their recursive function in
-- the global context; `useInlined` has one global function less (`tripleI` is inlined).
/-- info: [11, 8] -/
#guard_msgs in
#eval [useGlobals_term.size, useInlined_term.size]

/-! ## Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 20).all fun a => (List.range 20).all fun b =>
  Term.eval useGlobals_term a b == useGlobals a b &&
  Term.eval useInlined_term a b == useInlined a b &&
  Term.eval countTriples_term a b == countTriples a b &&
  Term.eval gcdTwice_term a b == gcdTwice a b

/-- info: true -/
#guard_msgs in
#eval (List.range 200).all fun n =>
  Term.eval useChain_term n == useChain n && Term.eval logHalf_term n == logHalf n &&
  Term.eval downBy_term n == downBy n

end ExGlobals
