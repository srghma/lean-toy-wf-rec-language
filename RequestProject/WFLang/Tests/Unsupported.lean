import RequestProject.WFLang.Tests.MoreChecks

/-!
# What is still not supported (`UNSUPPORTED.md`)

Each function below is an ordinary Lean definition that `#lean_wf_func_to_term` does **not**
capture today.  The rejection is pinned by `#guard_msgs`, so if the capture starts accepting one
of them, the build fails and `UNSUPPORTED.md` must be updated.  `#expect_reject` (from
`MoreChecks.lean`) succeeds only if the capture fails, and reports the first line of its error.

The functions that used to be listed here and are now captured, with agreement proofs, are in
`Tests/NewTypes.lean`, `Tests/ListCombinators.lean`, `Tests/MutualSignatures.lean` and
`Tests/LeanWhile.lean` (`findDiv`).
-/

open WFLang

namespace Unsupported

/-! ## Types outside `Ty` -/

/-- A user structure. -/
structure Pt where
  a : Nat
  b : Nat

def ptSum (p : Pt) : Nat := p.a + p.b

/-- `Fin n` (a dependent type). -/
def finVal (i : Fin 5) : Nat := i.val

/-- Fixed-width integers. -/
def u64 (x : UInt64) : UInt64 := x + 1

/-! ## A `partial_fixpoint` definition that does not terminate

`partial_fixpoint` definitions are captured when one of the candidate measures decreases at
every recursive call (`Tests/PartialFixpoint.lean`); this one runs forever on every input, so no
measure works. -/

def loopUp (n : Nat) : Nat := loopUp (n + 1)
partial_fixpoint

/-! ## A recursive call inside a combinator whose termination needs `attach`

The membership proof `i ∈ List.range n` given by `attach` is what proves the decrease of the
call; it is erased for `List.map` (`Tests/Map.lean`), but not for the other combinators.  (The
capture fails with an internal error here, whose text is not stable, so only the rejection is
pinned.) -/

def depthSum (n : Nat) : Nat :=
  if n = 0 then 0 else (List.range n).attach.foldl (fun acc ⟨i, _h⟩ => acc + depthSum i) 1
termination_by n
decreasing_by simp at _h; omega

end Unsupported

/-- info: rejected: #lean_wf_func_to_term: unsupported type Unsupported.Pt (only Nat, Bool, Int, String, Char, pairs, lists, arrays, Option, Sum, Except, Unit and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.ptSum : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Fin -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.finVal : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type UInt64 (only Nat, Bool, Int, String, Char, pairs, lists, arrays, Option, Sum, Except, Unit and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.u64 : PCL.Term ⟨[.nat], .nat⟩)

#guard_msgs (drop info) in
#expect_reject (#lean_wf_func_to_term Unsupported.loopUp : PCL.Term ⟨[.nat], .nat⟩)

#guard_msgs (drop info) in
#expect_reject (#lean_wf_func_to_term Unsupported.depthSum : PCL.Term ⟨[.nat], .nat⟩)
