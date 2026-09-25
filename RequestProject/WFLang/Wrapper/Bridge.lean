import RequestProject.WFLang.Wrapper.Guarded
import RequestProject.WFLang.Wrapper.FreeCall

/-!
# From the call-tree certificate to the guarded certificate

`FreeCall.Dec R body` ("every call in the call tree of the body is `R`-smaller,
whatever the earlier calls answered") implies `Guarded.Dec R body`.  The
capture macro proves the former, whose goals contain no dependent proofs, and
obtains the certificate of the `Guarded`/`GuardedAcc` designs from it.
-/

namespace WFLang

namespace FreeCall.Comp

theorem allCalls_bind_inv {A B σ τ : Type} (P : A → Prop) (o : A → B) (c : Comp A B σ)
    (f : σ → Comp A B τ) (h : (c.bind f).AllCalls P) :
    c.AllCalls P ∧ (f (c.runWith o)).AllCalls P := by
  induction c with
  | pure v => exact ⟨trivial, h⟩
  | call a k ih =>
    obtain ⟨ha, hk⟩ := h
    refine ⟨⟨ha, fun b => ?_⟩, (ih (o a) (hk (o a))).2⟩
    exact (ih b (hk b)).1

end FreeCall.Comp

open FreeCall in
section
variable {s : Sig} (R : Env s.args → Env s.args → Prop) (x : Env s.args)
  (ih : (y : Env s.args) → R y x → s.ret.denote) (o : Env s.args → s.ret.denote)

mutual
theorem guard_of_allCalls (hio : ∀ y h, ih y h = o y) {Γ : List Ty} (env : Env Γ) :
    ∀ {t : Ty} (e : Expr s Γ t), (evalC env e).AllCalls (R · x) →
      (Guarded.sem R x ih env e).1
  | _, .var _, _ => trivial
  | _, .lit _ _, _ => trivial
  | _, .bin op a b, h => by
      obtain ⟨ha, h⟩ := Comp.allCalls_bind_inv _ o _ _ h
      obtain ⟨hb, -⟩ := Comp.allCalls_bind_inv _ o _ _ h
      exact ⟨guard_of_allCalls hio env a ha, guard_of_allCalls hio env b hb⟩
  | _, .not a, h => by
      obtain ⟨ha, -⟩ := Comp.allCalls_bind_inv _ o _ _ h
      exact guard_of_allCalls hio env a ha
  | _, .ite c a b, h => by
      obtain ⟨hc, h⟩ := Comp.allCalls_bind_inv _ o _ _ h
      have gc := guard_of_allCalls hio env c hc
      refine ⟨gc, fun g => ⟨fun ht => ?_, fun hf => ?_⟩⟩
      · have hv : (evalC env c).runWith o = true := by
          rw [evalC_runWith, ← Guarded.sem_eq R x ih o hio env c g, ht]
        rw [hv] at h
        exact guard_of_allCalls hio env a h
      · have hv : (evalC env c).runWith o = false := by
          rw [evalC_runWith, ← Guarded.sem_eq R x ih o hio env c g, hf]
        rw [hv] at h
        exact guard_of_allCalls hio env b h
  | _, .call args, h => by
      obtain ⟨has, h⟩ := Comp.allCalls_bind_inv _ o _ _ h
      have gs := guards_of_allCalls hio env args has
      refine ⟨gs, fun g => ?_⟩
      have hv : (evalsC env args).runWith o = (Guarded.sems R x ih env args).2 g := by
        rw [evalsC_runWith, Guarded.sems_eq R x ih o hio env args g]
      rw [hv] at h
      exact h.1
theorem guards_of_allCalls (hio : ∀ y h, ih y h = o y) {Γ : List Ty} (env : Env Γ) :
    ∀ {ts : List Ty} (e : Exprs s Γ ts), (evalsC env e).AllCalls (R · x) →
      (Guarded.sems R x ih env e).1
  | _, .nil, _ => trivial
  | _, .cons a as, h => by
      obtain ⟨ha, h⟩ := Comp.allCalls_bind_inv _ o _ _ h
      obtain ⟨has, -⟩ := Comp.allCalls_bind_inv _ o _ _ h
      exact ⟨guard_of_allCalls hio env a ha, guards_of_allCalls hio env as has⟩
end

end

/-- The call-tree certificate implies the guarded certificate. -/
theorem Guarded.dec_of_freeCall {s : Sig} {R : Env s.args → Env s.args → Prop} {body : Body s}
    (h : FreeCall.Dec R body) : Guarded.Dec R body := by
  classical
  intro x ih
  let o : Env s.args → s.ret.denote := fun y => if hy : R y x then ih y hy else s.ret.default
  exact guard_of_allCalls R x ih o (fun y hy => by simp [o, hy]) x body (h x)

end WFLang
