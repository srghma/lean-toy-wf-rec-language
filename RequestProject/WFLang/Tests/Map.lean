import RequestProject.WFLang.Tests.GapFunctions
import RequestProject.WFLang.Capture.Elab

/-!
# `List.map`, and `List.attach.map` with its proofs erased

The grammar has a statement `let v := map (fun x => body) l in k` (`PCL.Expr.map`).  Its body is
a statement over one more variable `x`: it may make calls, including recursive calls of the
enclosing function, and its path condition contains `x ∈ l`, which the decrease proofs of
these calls may use.

The grammar holds **no proof terms** except the ones that justify termination.  A Lean
`l.attach.map (fun ⟨x, h⟩ => …)` pairs each element with a proof `h : x ∈ l`, but the program
contains no such proof. It is captured as `map (fun x => …) l`: the membership becomes a fact of
the path condition, which only the termination (decrease) proofs use.  The agreement theorems
relate the two forms through `List.attach_map_val`.

For each function below: the capture, the agreement theorem (proved by `wf_agree`), the number
of `map` nodes of the program (`PTerm.maps`), and a runtime comparison with the compiled Lean
function.
-/

namespace MapTests

open WFLang

/-! ## `List.map` without recursive calls -/

def mapSq (n : Nat) : List Nat := (List.range n).map (fun i => i * i)
def mapSq_term : PCL.Term ⟨[.nat], .list .nat⟩ := #lean_wf_func_to_term mapSq
theorem mapSq_agree : ∀ n, PCL.Term.eval mapSq_term n = mapSq n := by wf_agree

def sumSq (n : Nat) : Nat := ((List.range n).map fun i => i * i).sum
def sumSq_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumSq
theorem sumSq_agree : ∀ n, PCL.Term.eval sumSq_term n = sumSq n := by wf_agree

def mapList (l : List Nat) : List Nat := l.map (· + 1)
def mapList_term : PCL.Term ⟨[.list .nat], .list .nat⟩ := #lean_wf_func_to_term mapList
theorem mapList_agree : ∀ l, PCL.Term.eval mapList_term l = mapList l := by wf_agree

/-- A `map` whose result is used twice. -/
def mapThenUse (n : Nat) : Nat :=
  let l := (List.range n).map (fun i => i + n)
  l.length + l.sum
def mapThenUse_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mapThenUse
theorem mapThenUse_agree : ∀ n, PCL.Term.eval mapThenUse_term n = mapThenUse n := by wf_agree

/-- Nested maps. -/
def nestedMap (n : Nat) : List (List Nat) :=
  (List.range n).map fun i => (List.range i).map fun j => i * j
def nestedMap_term : PCL.Term ⟨[.nat], .list (.list .nat)⟩ := #lean_wf_func_to_term nestedMap
theorem nestedMap_agree : ∀ n, PCL.Term.eval nestedMap_term n = nestedMap n := by wf_agree

def triple (k : Nat) : Nat := k * 3 + 1

/-- A `map` whose body calls another function. -/
def mapCalls (l : List Nat) : List Nat := l.map fun x => triple x + Nat.gcd x 6
def mapCalls_term : PCL.Term ⟨[.list .nat], .list .nat⟩ := #lean_wf_func_to_term mapCalls
theorem mapCalls_agree : ∀ l, PCL.Term.eval mapCalls_term l = mapCalls l := by wf_agree

/-! ## Recursive calls inside `List.attach.map`: the proofs are erased -/

-- `Gaps.underLambda n = if n = 0 then 1 else ((List.range n).attach.map fun ⟨i, _⟩ =>
-- underLambda i).sum`: the program is `map (fun i => underLambda i) (List.range n)`.
def underLambda_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Gaps.underLambda
theorem underLambda_agree : ∀ n, PCL.Term.eval underLambda_term n = Gaps.underLambda n := by
  wf_agree

/-- The membership proof is only used by the termination proof. -/
def divTree (n : Nat) : Nat :=
  if n ≤ 1 then 1 else
    1 + ((List.range (n / 2)).attach.map fun ⟨i, _⟩ => divTree i).sum
termination_by n
decreasing_by all_goals (simp at *; omega)
def divTree_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term divTree
theorem divTree_agree : ∀ n, PCL.Term.eval divTree_term n = divTree n := by wf_agree

/-- The element is read with the projection `x.1` instead of a pattern. -/
def attachVal (n : Nat) : Nat :=
  if n = 0 then 0 else ((List.range n).attach.map fun x => attachVal x.1 + 1).sum
termination_by n
decreasing_by have := x.2; simp at this; omega
def attachVal_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term attachVal
theorem attachVal_agree : ∀ n, PCL.Term.eval attachVal_term n = attachVal n := by wf_agree

/-- A recursive call in one branch of an `if` inside the body. -/
def mapIf (n : Nat) : Nat :=
  if n = 0 then 0 else
    let s := ((List.range n).attach.map fun ⟨i, _⟩ => if i % 2 = 0 then mapIf i else i).sum
    s + 1
termination_by n
decreasing_by all_goals (simp at *; omega)
def mapIf_term : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term mapIf
theorem mapIf_agree : ∀ n, PCL.Term.eval mapIf_term n = mapIf n := by wf_agree

/-! ## The shape of the programs: one `map` node per `List.map` (two for `nestedMap`) -/

/-- info: [1, 1, 1, 1, 2, 1, 1, 1, 1, 1] -/
#guard_msgs in
#eval [mapSq_term.maps, sumSq_term.maps, mapList_term.maps, mapThenUse_term.maps,
  nestedMap_term.maps, mapCalls_term.maps, underLambda_term.maps, divTree_term.maps,
  attachVal_term.maps, mapIf_term.maps]

/-! ## Runtime checks against the compiled Lean functions -/

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun n =>
  PCL.Term.eval mapSq_term n == mapSq n && PCL.Term.eval sumSq_term n == sumSq n &&
  PCL.Term.eval mapThenUse_term n == mapThenUse n &&
  PCL.Term.eval nestedMap_term n == nestedMap n &&
  PCL.Term.eval underLambda_term n == Gaps.underLambda n &&
  PCL.Term.eval divTree_term n == divTree n &&
  PCL.Term.eval attachVal_term n == attachVal n && PCL.Term.eval mapIf_term n == mapIf n

/-- info: true -/
#guard_msgs in
#eval [[], [0], [1, 2, 3], [7, 7, 12, 5]].all fun l =>
  PCL.Term.eval mapList_term l == mapList l && PCL.Term.eval mapCalls_term l == mapCalls l

/-- info: (32, 32) -/
#guard_msgs in
#eval (PCL.Term.eval underLambda_term 6, Gaps.underLambda 6)

end MapTests
