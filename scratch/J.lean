import RequestProject.WFLang.Capture.Elab
open WFLang WFLang.PCL
namespace T
def h (n : Nat) : Nat :=
  if n < 2 then 0 else (if n % 2 == 0 then h (n-1) else h (n-2)) + 1
termination_by n
def h_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term h
set_option maxHeartbeats 400000 in
theorem h_agree : ∀ n, Term.eval h_term n = h n := by
  intro n
  simp only [Term.eval, Term.run, curryEnv]
  rw [h_term]
  refine Eq.trans (PTerm.ofFix_run _ _ _ (fun x _ => ⟨h x.1, trivial⟩) ?hF _ _) ?heq
  case heq => rfl
  intro x hx
  dsimp only
  obtain ⟨n, x⟩ := x
  rw [h.eq_def]
  simp only [eval_ite, eval_join, eval_fixSelfCall, eval_jump, eval_ret, JEnv.push_cons, JEnv.push_nil]
  trace_state
  sorry
end T
