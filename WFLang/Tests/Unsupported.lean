import RequestProject.WFLang.Tests.MoreChecks

/-!
# What is still not supported (`UNSUPPORTED.md`)

Each function below is an ordinary Lean definition that `#lean_wf_func_to_term` does **not**
capture today.  The rejection is pinned by `#guard_msgs`, so if the capture starts accepting one
of them, the build fails and `UNSUPPORTED.md` must be updated.  `#expect_reject` (from
`MoreChecks.lean`) succeeds only if the capture fails, and reports the first line of its error.

The functions that used to be listed here and are now captured, with agreement proofs, are in
`Tests/NewTypes.lean`, `Tests/ListCombinators.lean`, `Tests/MutualSignatures.lean`,
`Tests/LeanWhile.lean` (`findDiv`), `Tests/MoreCombinators.lean`, `Tests/PartialFixpoint.lean` and
`Tests/AttachCombinators.lean` (`depthSum`).
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

/-! ## A loop that uses the membership proof and may stop early

Loops over `l.attach` (and `for h : x in l`) whose body always continues are captured
(`Tests/AttachCombinators.lean`); with an early `return` or `break` they are not. -/

def forMemRet (n : Nat) : Nat := Id.run do
  let mut s := 1
  for h : i in List.range n do
    have : i < n := List.mem_range.mp h
    if s > 100 then return s
    s := s + forMemRet i
  return s
termination_by n

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
#expect_reject (#lean_wf_func_to_term Unsupported.forMemRet : PCL.Term ⟨[.nat], .nat⟩)
