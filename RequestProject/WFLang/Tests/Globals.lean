import RequestProject.WFLang.Tests.MoreChecks

/-!
# Global functions and `@[inlinable]`

`#lean_wf_func_to_term f` treats a call of another user-defined function `g` according to
`g`'s attribute:

* `g` marked **`@[inlinable]`**: the call is inlined.  A non-recursive `g` is replaced by its
  body; a recursive `g` becomes a local recursive function (`fix`) at the call site (one copy
  per call site).
* `g` **not** marked `@[inlinable]`: `g` is a **global function** of the program.  It is
  captured once, as an entry of the global context (`PTerm.globals`, a `Globals` list whose
  entries may call the entries before them), and each call is `Expr.gCall i args` where `i`
  is `g`'s index in the global context.

Exceptions (always captured at the call site, whatever the attribute): functions with
function parameters (specialised to the function passed at each call), members of a group of
mutually recursive functions, and functions calling themselves inside a function argument.

A call of a global function only knows the postcondition of the callee (its subtype
property, if any), not its definition.  When a termination proof of the caller needs the
value computed by a non-recursive helper (e.g. `half n < n`), the helper must be
`@[inlinable]` (`logHalf` below).

The measures `PTerm.nglobals` (entries of the global context), `PTerm.gcalls` (calls of global
functions), `PTerm.fixes` (local `fix` nodes) and `PTerm.size` (statement nodes, global
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

/-- The same function, inlined (a local `fix` at each call site). -/
@[inlinable] def sumToI (n : Nat) : Nat := if n = 0 then 0 else n + sumToI (n - 1)
termination_by n

/-- Three calls of the global `sumTo` and two of the global `triple`: two global functions,
five calls. -/
def useGlobals (a b : Nat) : Nat := sumTo a + sumTo b + sumTo (triple a) + triple b

/-- The same with the inlined functions: `tripleI` disappears, and each call of `sumToI` gets
its own local `fix`. -/
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

-- Entries of the global context: `useGlobals` has `sumTo` and `triple`, `useInlined` none,
-- `useChain` has `triple` and `sumTriple`, `countTriples` and `downBy` one each, `logHalf` none
-- (`half` is inlined), `gcdTwice` one (`gcd`).
/-- info: [2, 0, 2, 1, 0, 1, 1] -/
#guard_msgs in
#eval [useGlobals_term.nglobals, useInlined_term.nglobals, useChain_term.nglobals,
  countTriples_term.nglobals, logHalf_term.nglobals, downBy_term.nglobals,
  gcdTwice_term.nglobals]

-- Calls of global functions (`sumTriple`'s body calls `triple` once).
/-- info: [5, 0, 3, 1, 0, 1, 2] -/
#guard_msgs in
#eval [useGlobals_term.gcalls, useInlined_term.gcalls, useChain_term.gcalls,
  countTriples_term.gcalls, logHalf_term.gcalls, downBy_term.gcalls, gcdTwice_term.gcalls]

-- Local `fix` nodes: one per call of the inlined `sumToI` (the recursive programs
-- `countTriples`, `logHalf`, `downBy` have one `fix` each: their own).
/-- info: [0, 3, 0, 1, 1, 1, 0] -/
#guard_msgs in
#eval [useGlobals_term.fixes, useInlined_term.fixes, useChain_term.fixes,
  countTriples_term.fixes, logHalf_term.fixes, downBy_term.fixes, gcdTwice_term.fixes]

-- Statement nodes (global bodies included): sharing `sumTo` in the global context is smaller
-- than copying it at each call site.
/-- info: [11, 19] -/
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
