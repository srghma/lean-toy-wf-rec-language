import RequestProject.WFLang.Wrapper.Elab
import RequestProject.WFLang.PCL.Elab
import RequestProject.WFLang.Tail.Elab
import RequestProject.WFLang.Meas.Elab

/-!
# One capture syntax for every grammar

`#lean_wf_func_to_term f` and `wf_agree` pick the grammar from the expected type (resp. the type
of the program in the goal):

```
def gcd_term : PCL.Term  ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd   -- #lean_wf_func_to_pcl
def gcd_term : Tail.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd   -- #lean_wf_func_to_tail
def gcd_term : Meas.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd   -- #lean_wf_func_to_meas
def gcd_term : Guarded.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd -- (also GuardedAcc,
                                                                  --  FreeCall, Checked)
theorem gcd_agree : ∀ m n, PCL.Term.eval gcd_term m n = gcd m n := by wf_agree
```
-/

namespace WFLang.Capture

open Lean Meta Elab Term

/-- The grammars with their own capture elaborator. -/
inductive Grammar where
  | pcl | tail | meas | wrapper

/-- Which grammar does the (expected) program type name? -/
def grammarOf (expected : Lean.Expr) : MetaM (Option Grammar) := do
  let t ← whnfR (← instantiateMVars expected)
  if let some c := t.getAppFn.constName? then
    if c == ``WFLang.PCL.Expr then return some .pcl
    if c == ``WFLang.Tail.Expr then return some .tail
    if c == ``WFLang.Meas.Expr then return some .meas
  if ← Wrapper.Capture.isWrapperType expected then return some .wrapper
  return none

@[term_elab WFLang.Meta.wfToTerm] def elabWfToTerm : TermElab := fun stx expectedType? => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let some expected := expectedType? |
    throwError "#lean_wf_func_to_term: the expected type (e.g. `PCL.Term _`) must be known"
  let some g ← grammarOf expected |
    throwError "#lean_wf_func_to_term: {expected} is not a program type"
  match g with
  | .pcl => elabTerm (← PCL.Capture.captureStx fn) expected
  | .tail => elabTerm (← Tail.Capture.captureStx fn) expected
  | .meas => elabTerm (← Meas.Capture.captureStx fn) expected
  | .wrapper => Wrapper.Capture.captureWrapper fn expected

@[tactic WFLang.Meta.wfAgree] def evalWfAgree : Tactic.Tactic := fun _ => do
  let (t, _, _) ← Meta.agreeTarget "wf_agree"
  let some g ← grammarOf (← inferType (← mkConstWithLevelParams t.getId)) |
    throwError "wf_agree: {t} is not a program"
  match g with
  | .pcl => Tactic.evalTactic (← `(tactic| pcl_agree))
  | .tail => Tactic.evalTactic (← `(tactic| tail_agree))
  | .meas => Tactic.evalTactic (← `(tactic| meas_agree))
  | .wrapper => Wrapper.Capture.evalWrapperAgree

end WFLang.Capture
