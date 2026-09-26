module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# What the evaluator does with a recursive record and a recursive newtype

The analogue of the ι-rules of `LeanScript.RecUnionEvalFacts` for the two other recursive
shapes that have values.

* **Reading back.**  The unfolded fields of a record built by `Comp.recObject_mk` are the
  values of the fields it was built with (`Comp.eval_recObject_mk_unfold`), and the
  unfolded body of a newtype built by `Comp.recAlias_mk` is the value it was built with
  (`Comp.eval_recAlias_mk_unfold`).
* **ι-rules for the eliminator.**  Taking apart a value bound to the introduction form
  binds exactly those values (`Term.evalJ_recObject_casesOn_mk`,
  `Term.evalJ_recAlias_casesOn_mk`).

All of them rest on the round trips `TyWf.DenObj.unfold_mk` and `TyWf.DenAlias.unfold_mk`
of `LeanScript.Den.RecObjectAlias` (and `Ty.unroll_roll` below them).
-/

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## Recursive records -/

/-- The unfolded fields of a record built by the introduction form are the values of the
    fields it was built with. -/
theorem Comp.eval_recObject_mk_unfold {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Args Sg Γ (TyWf.recObjectUnfold fs hwf).toList) (env : Env Γ) :
    TyWf.DenObj.unfold fs hwf (Comp.eval G (.recObject_mk fs hwf fields) env) =
      Args.eval G fields env :=
  TyWf.DenObj.unfold_mk fs hwf _

/-- Taking apart a record built by the introduction form binds the values of the fields
    it was built with. -/
theorem Term.evalJ_recObject_casesOn_mk {Γ : Ctx} {τ : TyWf} {J : JCtx}
    (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Args Sg Γ (TyWf.recObjectUnfold fs hwf).toList)
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ .recObject fs hwf :: Γ) τ J)
    (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letE (.recObject_mk fs hwf fields) (.recObject_casesOn (.var .head) body))
        env jenv =
      Term.evalJ G body
        (Env.append (Args.eval G fields env) (Comp.eval G (.recObject_mk fs hwf fields) env, env))
        jenv := by
  show Term.evalJ G body
      (Env.append (TyWf.DenObj.unfold fs hwf (TyWf.DenObj.mk fs hwf _)) _) jenv = _
  rw [TyWf.DenObj.unfold_mk]

/-! ## Recursive newtypes -/

/-- The unfolded body of a newtype built by the introduction form is the value it was
    built with. -/
theorem Comp.eval_recAlias_mk_unfold {Γ : Ctx} (b : TyWfIn 1)
    (hwf : Ty.Wf (TyWf.recAliasTy b)) (value : Atom Γ (TyWf.recAliasUnfold b hwf))
    (env : Env Γ) :
    TyWf.DenAlias.unfold b hwf (Comp.eval G (.recAlias_mk b hwf value) env) =
      Atom.eval value env :=
  TyWf.DenAlias.unfold_mk b hwf _

/-- Taking apart a newtype built by the introduction form binds the value it was built
    with. -/
theorem Term.evalJ_recAlias_casesOn_mk {Γ : Ctx} {τ : TyWf} {J : JCtx} (b : TyWfIn 1)
    (hwf : Ty.Wf (TyWf.recAliasTy b)) (value : Atom Γ (TyWf.recAliasUnfold b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: .recAlias b hwf :: Γ) τ J) (env : Env Γ)
    (jenv : JEnv τ J) :
    Term.evalJ G (.letE (.recAlias_mk b hwf value) (.recAlias_casesOn (.var .head) body))
        env jenv =
      Term.evalJ G body
        (Atom.eval value env, Comp.eval G (.recAlias_mk b hwf value) env, env) jenv := by
  show Term.evalJ G body
      (TyWf.DenAlias.unfold b hwf (TyWf.DenAlias.mk b hwf _), _) jenv = _
  rw [TyWf.DenAlias.unfold_mk]

end LeanScript

end
