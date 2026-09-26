import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The simp set `wflang_eval`

`wflang_eval` collects the equations of the evaluator of call-free expressions: `PExpr.eval`,
`PExprs.eval`, `Var.get`, `BinOp.eval`, `UnOp.eval`, `Ty.beq` and `Ty.default` (tagged in
`Core/PExpr.lean`).  The proofs written by the capture (`wf_dec`, `wf_agree`, the loop proofs)
use `simp [wflang_eval, …]` rather than repeating this list.
-/

/-- The equations of the evaluator of call-free `PCL` expressions. -/
register_simp_attr wflang_eval
