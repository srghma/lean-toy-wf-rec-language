import RequestProject.WFLang.Tests.Globals

/-!
# `where` helpers, and calls with known arguments

## `where` helpers are global functions, as in Lean

A helper `go` declared in the `where` clause of `foo` is, in Lean, an ordinary top-level
constant `foo.go`: it can be called from outside `foo` (`useGo` below).  The capture treats it
exactly like any other user function: if it is not marked `@[inlinable]`, it is an entry of the
global context of the program and `foo` calls it with `Expr.gCall`; if it is marked
`@[inlinable]` (`where @[inlinable] go …`), it is inlined (a local `fix`) and does not appear in
the global context.

## Calls with known arguments are evaluated

A call `g a₁ … aₙ` of a user function whose arguments are all known (a closed term: literals
and operations on them, possibly other such calls) is evaluated when the function is captured,
and replaced by its value.  This applies to every user function, whether it is `@[inlinable]`
or a global function, recursive or not, including `where` helpers.  A function that is only
called with known arguments therefore does not appear in the program at all (neither in the
global context nor as a local `fix`).  The value is computed by the kernel, and `wf_agree`
proves the equation `g a₁ … aₙ = v` by the same kernel evaluation.
`set_option wfLang.foldCalls false` turns this off.
-/

namespace WhereEx

/-- The example of the request: `foo.go` is a top-level constant of Lean. -/
def foo (n : Nat) : Nat :=
  go n 0
where
  go (x : Nat) (acc : Nat) : Nat :=
    match x with
    | 0 => acc
    | x + 1 => go x (acc + 1)

/-- `foo.go` called from outside `foo`. -/
def useGo (a b : Nat) : Nat := foo.go a b + foo.go b a

/-- The same helper marked `@[inlinable]`: inlined into `fooI` (a local `fix`). -/
def fooI (n : Nat) : Nat :=
  go n 0
where
  @[inlinable] go (x : Nat) (acc : Nat) : Nat :=
    match x with
    | 0 => acc
    | x + 1 => go x (acc + 1)

/-- A well-founded `where` helper, with a `termination_by` clause. -/
def sumDigits (n : Nat) : Nat := go n 0
where
  go (n acc : Nat) : Nat := if n = 0 then acc else go (n / 10) (acc + n % 10)
  termination_by n
  decreasing_by omega

end WhereEx

namespace FoldEx
open WhereEx
open GlobalsEx (triple)

/-- A recursive `@[inlinable]` function. -/
@[inlinable] def fact (n : Nat) : Nat := if n = 0 then 1 else n * fact (n - 1)
termination_by n

/-- Every call has known arguments: the global functions `triple` and `sumTo`, the `where`
helper `foo.go`, the `@[inlinable]` recursive `fact` and the uploaded `gcd` are all evaluated. -/
def allKnown (a : Nat) : Nat :=
  a + triple 3 + GlobalsEx.sumTo 4 + foo.go 2 3 + fact 5 + gcd 12 18 + sumDigits 1234

/-- The same functions with unknown arguments (for comparison). -/
def noneKnown (a : Nat) : Nat :=
  a + triple a + GlobalsEx.sumTo a + foo.go 2 a + fact a + gcd a 18 + sumDigits a

/-- A known call and an unknown call of the same function: only the second one is kept. -/
def mixed (a : Nat) : Nat := GlobalsEx.sumTo 4 + GlobalsEx.sumTo a

/-- Nested calls with known arguments, and a known call in the test of an `if`. -/
def nested (a : Nat) : Nat := if a = triple (GlobalsEx.sumTo 3) then GlobalsEx.sumTo (triple 2) else a

/-- Known calls in a recursive function. -/
def countDown (n : Nat) : Nat := if n = 0 then GlobalsEx.sumTo 3 else countDown (n - 1) + triple 2
termination_by n

/-- A global function whose body contains a call with known arguments: `addSum` is a global
function (called with an unknown argument), `sumTo` does not appear in the program. -/
def addSum (n : Nat) : Nat := n + GlobalsEx.sumTo 3

def useAddSum (a : Nat) : Nat := addSum a + addSum (a + 1)

/-- Results of other types. -/
def isEven (n : Nat) : Bool := n % 2 == 0
def negTwice (i : Int) : Int := -(2 * i)
def swapPair (p : Nat × Nat) : Nat × Nat := (p.2, p.1)
def countUp (n : Nat) : List Nat := if n = 0 then [] else countUp (n - 1) ++ [n]
termination_by n

def otherTypes (b : Bool) (i : Int) (p : Nat × Nat) (l : List Nat) :
    Bool × (Int × ((Nat × Nat) × List Nat)) :=
  (b && isEven 10, i + negTwice 3, ((swapPair (1, 2)).1 + p.1, p.2), countUp 3 ++ l)

end FoldEx

namespace ExWhereFold
open WFLang PCL WhereEx FoldEx

/-! ## `where` helpers -/

def foo_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term foo
theorem foo_agree : ∀ n, Term.eval foo_term n = foo n := by wf_agree

/-- The `where` helper captured on its own. -/
def foo_go_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term foo.go
theorem foo_go_agree : ∀ x acc, Term.eval foo_go_term x acc = foo.go x acc := by wf_agree

def useGo_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useGo
theorem useGo_agree : ∀ a b, Term.eval useGo_term a b = useGo a b := by wf_agree

def fooI_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term fooI
theorem fooI_agree : ∀ n, Term.eval fooI_term n = fooI n := by wf_agree

def sumDigits_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumDigits
theorem sumDigits_agree : ∀ n, Term.eval sumDigits_term n = sumDigits n := by wf_agree

-- `foo`, `useGo` and `sumDigits` have one global function (`foo.go`, `sumDigits.go`); `foo.go`
-- captured on its own has none; `fooI` has none (its `go` is inlined as a local `fix`).
/-- info: [1, 0, 1, 0, 1] -/
#guard_msgs in
#eval [foo_term.nglobals, foo_go_term.nglobals, useGo_term.nglobals, fooI_term.nglobals,
  sumDigits_term.nglobals]

/-- info: [1, 0, 2, 0, 1] -/
#guard_msgs in
#eval [foo_term.gcalls, foo_go_term.gcalls, useGo_term.gcalls, fooI_term.gcalls,
  sumDigits_term.gcalls]

/-- info: [0, 1, 0, 1, 0] -/
#guard_msgs in
#eval [foo_term.fixes, foo_go_term.fixes, useGo_term.fixes, fooI_term.fixes,
  sumDigits_term.fixes]

/-! ## Calls with known arguments -/

def allKnown_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term allKnown
theorem allKnown_agree : ∀ a, Term.eval allKnown_term a = allKnown a := by wf_agree

def noneKnown_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term noneKnown
theorem noneKnown_agree : ∀ a, Term.eval noneKnown_term a = noneKnown a := by wf_agree

def mixed_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mixed
theorem mixed_agree : ∀ a, Term.eval mixed_term a = mixed a := by wf_agree

def nested_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term nested
theorem nested_agree : ∀ a, Term.eval nested_term a = nested a := by wf_agree

def countDown_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term countDown
theorem countDown_agree : ∀ n, Term.eval countDown_term n = countDown n := by wf_agree

def useAddSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term useAddSum
theorem useAddSum_agree : ∀ a, Term.eval useAddSum_term a = useAddSum a := by wf_agree

def otherTypes_term : Term ⟨[.bool, .int, .prod .nat .nat, .list .nat],
    .prod .bool (.prod .int (.prod (.prod .nat .nat) (.list .nat)))⟩ :=
  #lean_wf_func_to_term otherTypes
theorem otherTypes_agree : ∀ b i p l,
    Term.eval otherTypes_term b i p l = otherTypes b i p l := by wf_agree

-- With the evaluation turned off, the calls stay (global functions and local `fix`es).
set_option wfLang.foldCalls false in
def allKnownOff_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term allKnown
set_option wfLang.foldCalls false in
theorem allKnownOff_agree : ∀ a, Term.eval allKnownOff_term a = allKnown a := by wf_agree

-- Entries of the global context: `allKnown` has none (all its calls are evaluated), against
-- six for `noneKnown` and for `allKnown` with the evaluation turned off (`triple`, `sumTo`,
-- `foo.go`, `gcd`, `sumDigits.go` and `sumDigits`); `mixed` keeps `sumTo` for its unknown call;
-- `useAddSum` has `addSum` only (the body of `addSum` has the value of `sumTo 3`).
/-- info: [0, 6, 1, 0, 0, 1, 0, 6] -/
#guard_msgs in
#eval [allKnown_term.nglobals, noneKnown_term.nglobals, mixed_term.nglobals,
  nested_term.nglobals, countDown_term.nglobals, useAddSum_term.nglobals,
  otherTypes_term.nglobals, allKnownOff_term.nglobals]

-- Calls of global functions.
/-- info: [0, 6, 1, 0, 0, 2, 0, 6] -/
#guard_msgs in
#eval [allKnown_term.gcalls, noneKnown_term.gcalls, mixed_term.gcalls, nested_term.gcalls,
  countDown_term.gcalls, useAddSum_term.gcalls, otherTypes_term.gcalls,
  allKnownOff_term.gcalls]

-- Local `fix` nodes: the inlined `fact` in `noneKnown` and `allKnownOff`, and `countDown`'s own.
/-- info: [0, 1, 0, 0, 1, 0, 0, 1] -/
#guard_msgs in
#eval [allKnown_term.fixes, noneKnown_term.fixes, mixed_term.fixes, nested_term.fixes,
  countDown_term.fixes, useAddSum_term.fixes, otherTypes_term.fixes, allKnownOff_term.fixes]

-- Statement nodes (global bodies included): `allKnown` is a single `ret` of
-- `a + 9 + 10 + 5 + 120 + 6 + 10`.
/-- info: [1, 31, 31] -/
#guard_msgs in
#eval [allKnown_term.size, noneKnown_term.size, allKnownOff_term.size]

/-! ## Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun a => (List.range 30).all fun b =>
  Term.eval foo_term a == foo a && Term.eval foo_go_term a b == foo.go a b &&
  Term.eval useGo_term a b == useGo a b && Term.eval fooI_term a == fooI a

/-- info: true -/
#guard_msgs in
#eval Term.eval otherTypes_term true 5 (7, 8) [9] == otherTypes true 5 (7, 8) [9]

/-- info: true -/
#guard_msgs in
#eval (List.range 200).all fun a =>
  Term.eval sumDigits_term a == sumDigits a &&
  Term.eval allKnown_term a == allKnown a && Term.eval noneKnown_term a == noneKnown a &&
  Term.eval mixed_term a == mixed a && Term.eval nested_term a == nested a &&
  Term.eval countDown_term a == countDown a && Term.eval useAddSum_term a == useAddSum a &&
  Term.eval allKnownOff_term a == allKnown a

/-- info: 'ExWhereFold.allKnown_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allKnown_agree

end ExWhereFold
