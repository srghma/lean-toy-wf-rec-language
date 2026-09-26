import RequestProject.WFLang.Tests.Gaps
import RequestProject.WFLang.Tests.Globals

/-!
# Tail-recursive `@[inlinable]` functions are inlined as loops

A call of a **tail-recursive** `@[inlinable]` function `g` is inlined at the call site as a
loop inside the caller, with two join points:

```
join K (v) := ⟦rest of the caller's computation, using v⟧ in
joinrec L (x) [R] := ⟦body of g, where `g args` is `jump L args` and a result `r` is `jump K r`⟧ in
jump L (arguments of the call)
```

* the loop parameter `x` is the tuple of `g`'s parameters (`PCL.tupleTy`), and the relation
  `R` is Lean's well-founded relation for `g`, read on these tuples;
* the loop is **not** a closed copy of `g`: its body is part of the caller's statement, so it
  sees the caller's variables, its path condition and the caller's join points (it exits by
  jumping to `K`), and `K` may call the enclosing recursive function;
* a back edge `jump L args` carries the proof that `args` goes down along `R` (found by the
  same decreasing tactic as for recursive calls).

A recursive `@[inlinable]` function whose self calls are not all tail calls (`sumToI` in
`Tests/Globals.lean`) is a global function instead.

Each program below pins the number of loops (`loops`: `joinrec` nodes) and of global functions
(`nglobals`), has its agreement theorem proved by `wf_agree`, and is run on sample inputs.
-/

namespace LoopsEx

/-- Tail-recursive: `sumAcc n acc = acc + n + (n - 1) + … + 1`. -/
@[inlinable] def sumAcc (n acc : Nat) : Nat := if n = 0 then acc else sumAcc (n - 1) (acc + n)
termination_by n

/-- Two calls: two loops.  The rest of the computation after the second loop reads the
caller's variable `b`. -/
def useLoop (a b : Nat) : Nat := sumAcc a 0 + b * sumAcc b a

/-- A loop in a recursive function: the rest of the computation after the loop makes the
recursive call. -/
def sumSums (n : Nat) : Nat := if n = 0 then 0 else sumAcc n 0 + sumSums (n - 1)
termination_by n

/-- Euclid's algorithm, tail-recursive, with a termination proof. -/
@[inlinable] def gcdI (m n : Nat) : Nat := if n = 0 then m else gcdI n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- A loop in a branch. -/
def lcmI (a b : Nat) : Nat := if a = 0 then 0 else a * b / gcdI a b

/-- A loop with two exits. -/
@[inlinable] def smallestFactor (n d : Nat) : Nat :=
  if n ≤ d then n else if n % d = 0 then d else smallestFactor n (d + 1)
termination_by n - d

def minFac' (n : Nat) : Nat := if n < 2 then n else smallestFactor n 2

/-- A loop whose body contains a loop. -/
@[inlinable] def outer (i acc : Nat) : Nat :=
  if i = 0 then acc else outer (i - 1) (acc + sumAcc i 0)
termination_by i

def tetra (n : Nat) : Nat := outer n 0

/-- The result of a loop in the test of an `if`. -/
def classify (n : Nat) : Nat := if sumAcc n 0 > 10 then 1 else 2

/-- A loop whose body calls a global function (`GlobalsEx.triple`). -/
@[inlinable] def sumTriples (n acc : Nat) : Nat :=
  if n = 0 then acc else sumTriples (n - 1) (acc + GlobalsEx.triple n)
termination_by n

def useTriples (n : Nat) : Nat := sumTriples n 0 + 1

end LoopsEx

namespace LoopsPCL
open WFLang PCL LoopsEx

def useLoop_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term useLoop
theorem useLoop_agree : ∀ a b, Term.eval useLoop_term a b = useLoop a b := by wf_agree

def sumSums_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumSums
theorem sumSums_agree : ∀ n, Term.eval sumSums_term n = sumSums n := by wf_agree

def lcmI_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term lcmI
theorem lcmI_agree : ∀ a b, Term.eval lcmI_term a b = lcmI a b := by wf_agree

def minFac'_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term minFac'
theorem minFac'_agree : ∀ n, Term.eval minFac'_term n = minFac' n := by wf_agree

def tetra_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term tetra
theorem tetra_agree : ∀ n, Term.eval tetra_term n = tetra n := by wf_agree

def classify_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term classify
theorem classify_agree : ∀ n, Term.eval classify_term n = classify n := by wf_agree

def useTriples_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term useTriples
theorem useTriples_agree : ∀ n, Term.eval useTriples_term n = useTriples n := by wf_agree

/-! ## Shapes

`(loops, nglobals)`: `useLoop` has two loops; `sumSums` one loop and one global function (the
recursive `sumSums` itself); `tetra` two loops (one inside the other); `useTriples` one loop
and the global function `triple`.  No `@[inlinable]` tail-recursive function becomes a global
function. -/

/-- info: [(2, 0), (1, 1), (1, 0), (1, 0), (2, 0), (1, 0), (1, 1)] -/
#guard_msgs in
#eval [(useLoop_term.loops, useLoop_term.nglobals), (sumSums_term.loops, sumSums_term.nglobals),
  (lcmI_term.loops, lcmI_term.nglobals), (minFac'_term.loops, minFac'_term.nglobals),
  (tetra_term.loops, tetra_term.nglobals), (classify_term.loops, classify_term.nglobals),
  (useTriples_term.loops, useTriples_term.nglobals)]

-- Bounded loops (`for i in [a:b]`, `Nat.fold`, see `Tests/Gaps.lean`) are captured through the
-- tail-recursive `WFLang.rangeLoop`, specialised to the loop body: also loops.  So is the
-- specialised tail-recursive `Tco.iter` of `useIter`.  The recursive, not tail-recursive
-- `sumToI` of `useInlined` is a global function.
/-- info: [(1, 0), (1, 0), (1, 0), (0, 1)] -/
#guard_msgs in
#eval [(GapsPCL.forRange_term.loops, GapsPCL.forRange_term.nglobals),
  (GapsPCL.usesFold_term.loops, GapsPCL.usesFold_term.nglobals),
  (GapsPCL.useIter_term.loops, GapsPCL.useIter_term.nglobals),
  (ExGlobals.useInlined_term.loops, ExGlobals.useInlined_term.nglobals)]

/-! ## Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 25).all fun a => (List.range 25).all fun b =>
  Term.eval useLoop_term a b == useLoop a b && Term.eval lcmI_term a b == lcmI a b

/-- info: true -/
#guard_msgs in
#eval (List.range 60).all fun n =>
  Term.eval sumSums_term n == sumSums n && Term.eval minFac'_term n == minFac' n &&
  Term.eval tetra_term n == tetra n && Term.eval classify_term n == classify n &&
  Term.eval useTriples_term n == useTriples n

/-- info: [0, 1, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 17, 2, 19] -/
#guard_msgs in
#eval (List.range 20).map (Term.eval minFac'_term)

end LoopsPCL
