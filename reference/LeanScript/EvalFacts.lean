module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-! # What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that the
language's application is Lean's, that a `let` binds the value of its computation, that a
join point is the function its body computes, that a delay carries nothing, and that
reading the fields of the constructor a value was built with gives them back. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf} (G : GlobalEnv Sg.decls)

/-- An abstraction is the Lean function its body computes. -/
theorem Comp.eval_lam (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Comp.eval G (.lam body) env = fun x => Term.eval G body (x, env) :=
  rfl

/-- The language's application is Lean's. -/
theorem Comp.eval_ap (f : Atom Γ (σ ⇒ τ)) (a : Atom Γ σ) (env : Env Γ) :
    Comp.eval G (.ap f a) env = (Atom.eval f env) (Atom.eval a env) :=
  rfl

/-- Applying an abstraction bound by a `let` is evaluating its body with the argument's
    value bound. -/
theorem Term.eval_beta (body : Term Sg (σ :: Γ) τ) (a : Atom ((σ ⇒ τ) :: Γ) σ)
    (env : Env Γ) :
    Term.eval G (.letE (.lam body) (.letE (.ap (.var .head) a) (.ret (.var .head)))) env =
      Term.eval G body (Atom.eval a (Comp.eval G (.lam body) env, env), env) :=
  rfl

/-- `let x = c; body` binds the value of `c`. -/
theorem Term.evalJ_letE {J : JCtx} (c : Comp Sg Γ σ) (body : Term Sg (σ :: Γ) τ J)
    (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letE c body) env jenv = Term.evalJ G body (Comp.eval G c env, env) jenv := by
  cases body <;> try rfl
  case ret a => rcases a with ⟨v⟩; cases v <;> rfl

/-- A join point is the function of its parameter its body computes: the body of the
    `letJ` sees it as the innermost join point. -/
theorem Term.evalJ_letJ {J : JCtx} (jp : Term Sg (σ :: Γ) τ J) (body : Term Sg Γ τ (σ :: J))
    (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letJ jp body) env jenv =
      Term.evalJ G body env (fun x => Term.evalJ G jp (x, env) jenv, jenv) :=
  rfl

/-- Jumping to a join point applies it to the value of the argument. -/
theorem Term.evalJ_letJ_jump {J : JCtx} (jp : Term Sg (σ :: Γ) τ J) (a : Atom Γ σ)
    (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letJ jp (.jump .head a)) env jenv =
      Term.evalJ G jp (Atom.eval a env, env) jenv :=
  rfl

/-- Forcing a delay gives back what was delayed. -/
theorem Term.eval_lazy_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.letE (.lazy_mk e) (.letE (.lazy_force (.var .head)) (.ret (.var .head)))) env =
      Term.eval G e env :=
  rfl

/-- Forcing a thunk gives back what was delayed. -/
theorem Term.eval_thunk_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.letE (.thunk_mk e) (.letE (.thunk_force (.var .head)) (.ret (.var .head)))) env =
      Term.eval G e env :=
  rfl

/-- An extern is the Lean function it implements. -/
theorem Comp.eval_extern (e : Extern τ) (env : Env Γ) :
    Comp.eval (Sg := Sg) G (.extern e) env = Extern.eval e :=
  rfl

/-- An extern applied to atoms is the Lean function called on their values. -/
theorem Comp.eval_externCall {σs : List TyWf} (args : Args Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) (env : Env Γ) :
    Comp.eval G (.externCall args call) env = Extern.eval (call (Args.eval G args env)) :=
  rfl

/-- An extern that takes a proof, applied to atoms whose values satisfy the proposition,
    delivers the Lean function called on those values, with the proof, to its
    destination. -/
theorem Term.evalJ_externCallChecked_of_some {J : JCtx} {ρ : TyWf} {σs : List TyWf}
    (args : Args Sg Γ σs) (call : TyWf.DenList σs → Option (Extern ρ)) (d : Dest J ρ τ)
    (fallback : Term Sg Γ τ J) (env : Env Γ) (jenv : JEnv τ J) (e : Extern ρ)
    (he : call (Args.eval G args env) = some e) :
    Term.evalJ G (.externCallChecked args call d fallback) env jenv =
      Dest.apply d jenv (Extern.eval e) := by
  show (match call (Args.eval G args env) with
    | some e => Dest.apply d jenv (Extern.eval e)
    | none => Term.evalJ G fallback env jenv) = _
  rw [he]

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Comp.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Args Sg Γ (l.get t ht)) (env : Env Γ) :
    (Comp.eval G (.taggedUnion_mk l t ht fields) env).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Comp.eval_taggedUnion_field? {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Args Sg Γ (l.get t ht)) (env : Env Γ) :
    TyWf.DenTU.field? t ht (Comp.eval G (.taggedUnion_mk l t ht fields) env) =
      some (Args.eval G fields env) :=
  TyWf.DenTU.field?_mk t ht _

end LeanScript

end
