module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder

public section

/-!
# `kernel_rfl`: an equation checked by the kernel only

`rfl` (the term, or the tactic) first asks the elaborator's definitional-equality check
whether the two sides agree, and only then hands the proof to the kernel.  For the
evaluator of this language the elaborator's check is by far the slower of the two: every
extern call goes through the case splits of `LeanScript.Extern.eval` (one over the
families of the catalogue, then one over the entries of a family), and the elaborator's
reduction of such splits costs much more than the kernel's (for `hstep` in
`TermTests/FibWindowTest.lean` the elaborator takes about 9 s where the kernel takes well
under a second; before the catalogue was split in two levels it took about 15 s).  It is
also the check that counts heartbeats.

`kernel_rfl` closes a goal `a = b` with `Eq.refl a` **without** that first check.  It is
sound: the kernel type-checks the finished declaration, so if `a` and `b` are not
definitionally equal the declaration is rejected (with a kernel error at the declaration,
not at the tactic).  Use it where `rfl` is correct but slow; for a *closed* proposition
`decide +kernel` does the same job.
-/

namespace LeanScript

open Lean Elab Tactic Meta in
/-- Close a goal `a = b` by `Eq.refl a`, leaving the check that `a` and `b` are
    definitionally equal to the kernel alone (see the module doc). -/
elab "kernel_rfl" : tactic => liftMetaTactic fun g => do
  let t ← whnfR (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: the goal is not an equation{indentExpr t}"
  g.assign (← mkEqRefl lhs)
  return []

end LeanScript

end
