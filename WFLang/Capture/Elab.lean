import RequestProject.WFLang.Capture.Elab.Term
import RequestProject.WFLang.Capture.Elab.Agree

/-!
# Capturing a well-founded Lean function as a `PCL.Term`

* `Capture/Elab/Term.lean`: the term elaborator `#lean_wf_func_to_term f` (the global context
  under construction, the recursive function, the main statement);
* `Capture/Elab/Agree.lean`: the tactic `wf_agree`, which proves the agreement theorem
  `∀ xs, PCL.Term.eval f_term xs = f xs`.
-/
