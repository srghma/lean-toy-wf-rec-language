module

public import LeanScript.RenameEvalFacts
public import LeanScript.ToJumpEvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# The A-normalising builders compute what the direct-style term means

`LeanScript.Expr.Build` writes a term in direct style — `Term.ap f a`, `Term.letE' e body`,
`Term.nat_casesOn' n z s`, … — and each of those functions puts the term in A-normal form:
it names every operand with a `let`, floats the `let`s of an operand out in front, renames
what it moves under them, and turns a dispatch or a fold in operand position into a join
point.  This file proves, **for all inputs**, that none of that changes the value: every
builder computes what the direct-style constructor it is named after means.

The core is `Term.eval_bindAtom` (naming an operand), `Term.evalJ_bind` (`let x = t; body`),
and `Spine.eval_bindArgs` (naming a list of operands); the builders themselves are in
`LeanScript.BuildEvalFacts.Builders`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-! ## What a list of operands in direct style means -/

/-- The values of the terms of a spine, in order. -/
def Spine.eval (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {σs : List TyWf} → Spine Sg Γ σs → Env Γ → TyWf.DenList σs
  | _, .nil, _ => PUnit.unit
  | _, .cons t ts, env => (Term.eval G t env, Spine.eval G ts env)

/-- The values of the elements of an array, in order. -/
def Terms.eval (G : GlobalEnv Sg.decls) {Γ : Ctx} {τ : TyWf} :
    Terms Sg Γ τ → Env Γ → List (TyWf.Den τ)
  | .nil, _ => []
  | .cons t ts, env => Term.eval G t env :: Terms.eval G ts env

/-- The value of a member of a mutual family, written in direct style. -/
def FamilyMemberValue.eval (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {m : LeanFamMemberSchema TyWf} → FamilyMemberValue Sg Γ m → Env Γ → TyWf.DenMember m
  | _, .ctors _ t ht fields, env => TyWf.DenTU.mk t ht (Spine.eval G fields env)
  | _, .record _ fields, env => cast (Ty.denRecord_eq _).symm (Spine.eval G fields env)
  | _, .alias _ value, env => Term.eval G value env

/-! ## Continuations that only look at the value they are given -/

/-- The continuation `k` of `Term.bindAtom` **means** `K`: in any environment that agrees
    with `env` along the renaming it is given, what it writes has the value `K` gives the
    value of its atom.  (`k` is used under the `let`s the builder writes, so it is run in a
    larger environment than `env`.) -/
def Term.BindCont (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) (env : Env Γ) (jenv : JEnv τ J)
    (K : TyWf.Den σ → TyWf.Den τ) : Prop :=
  ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (env' : Env Δ) (a : Atom Δ σ), EnvRel ρ env env' →
    Term.evalJ G (k ρ a) env' jenv = K (Atom.eval a env')

/-- `Term.BindCont`, for a continuation that is given a list of atoms. -/
def Spine.BindCont (G : GlobalEnv Sg.decls) {Γ : Ctx} {σs : List TyWf} {τ : TyWf}
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → Args Sg Δ σs → Term Sg Δ τ) (env : Env Γ)
    (K : TyWf.DenList σs → TyWf.Den τ) : Prop :=
  ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (env' : Env Δ) (as : Args Sg Δ σs), EnvRel ρ env env' →
    Term.eval G (k ρ as) env' = K (Args.eval G as env')

/-- `Term.BindCont`, for a continuation that is given the atoms of an array. -/
def Terms.BindCont (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf}
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → List (Atom Δ σ) → Term Sg Δ τ) (env : Env Γ)
    (K : List (TyWf.Den σ) → TyWf.Den τ) : Prop :=
  ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (env' : Env Δ) (as : List (Atom Δ σ)), EnvRel ρ env env' →
    Term.eval G (k ρ as) env' = K (as.map (Atom.eval · env'))

/-- `Term.BindCont`, for a continuation that is given the operands of a member of a
    mutual family. -/
def FamilyMemberValue.BindCont (G : GlobalEnv Sg.decls) {Γ : Ctx}
    {m : LeanFamMemberSchema TyWf} {τ : TyWf}
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → FamilyMemberArgs Sg Δ m → Term Sg Δ τ) (env : Env Γ)
    (K : TyWf.DenMember m → TyWf.Den τ) : Prop :=
  ∀ {Δ : Ctx} (ρ : Ren Γ Δ) (env' : Env Δ) (as : FamilyMemberArgs Sg Δ m),
    EnvRel ρ env env' → Term.eval G (k ρ as) env' = K (FamilyMemberArgs.eval G as env')

/-- `let x = c; body`, run with no join point in scope, binds the value of `c`. -/
theorem Term.eval_letE (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} (c : Comp Sg Γ σ)
    (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (.letE c body) env = Term.eval G body (Comp.eval G c env, env) :=
  Term.evalJ_letE G c body env PUnit.unit

/-! ## Naming an operand -/

/-- `Term.bindAtom.go`, on a term that is neither a variable nor a `let`: what the
    continuation writes becomes a join point, and the term jumps to it. -/
theorem Term.evalJ_bindAtom_go_joinPoint (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf}
    {J : JCtx} (t : Term Sg Γ σ) (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J)
    (env : Env Γ) (jenv : JEnv τ J) (K : TyWf.Den σ → TyWf.Den τ)
    (hk : Term.BindCont G k env jenv K) :
    Term.evalJ G (.letJ (k Ren.wk (.var .head)) (t.toJump (J₀ := []))) env jenv =
      K (Term.eval G t env) := by
  rw [Term.evalJ_letJ, Term.evalJ_toJump_nil]
  exact hk Ren.wk _ (.var .head) (EnvRel.wk _ env)

/-- `Term.bindAtom.go` computes the continuation applied to the value of the term. -/
theorem Term.evalJ_bindAtom_go (G : GlobalEnv Sg.decls) {σ τ : TyWf} {J : JCtx}
    (jenv : JEnv τ J) :
    {Γ : Ctx} → (t : Term Sg Γ σ) → (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) →
    (env : Env Γ) → (K : TyWf.Den σ → TyWf.Den τ) → Term.BindCont G k env jenv K →
    Term.evalJ G (Term.bindAtom.go t rfl k) env jenv = K (Term.eval G t env)
  | _, .ret a, k, env, K, hk => hk Ren.id env a (EnvRel.id' env)
  | _, .letE c t, k, env, K, hk => by
      show Term.evalJ G (.letE c (Term.bindAtom.go t rfl _)) env jenv = _
      rw [Term.evalJ_letE]
      exact (Term.evalJ_bindAtom_go G jenv t _ _ K
        fun ρ env' a h => hk _ env' a (h.comp (EnvRel.wk _ env))).trans
        (congrArg K (Term.evalJ_letE G c t env PUnit.unit).symm)
  | _, .letJ jp body, k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G (.letJ jp body) k env jenv K hk
  | _, .jump j _, _, _, _, _ => nomatch j
  | _, .externCallChecked .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .bool_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .nat_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .nat_rec .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .int_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .uint8_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .uint16_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .uint32_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .uint64_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .int8_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .int16_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .int32_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .int64_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .char_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .stringPosRaw_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .stringPos_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .substringRaw_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .float_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .float32_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .floatModel_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .float32Model_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .array_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .array_rec .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .enum_casesOn .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .enum_casesOnWithDefault .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .record_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .taggedUnion_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .taggedUnion_casesOnWithDefault .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recTaggedUnion_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recTaggedUnion_casesOnWithDefault .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recTaggedUnion_rec .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recObject_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recObject_rec .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recAlias_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .recAlias_rec .., k, env, K, hk => Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .mutualRecursiveFamily_casesOn .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .mutualRecursiveFamily_casesOnWithDefault .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk
  | _, .mutualRecursiveFamily_rec .., k, env, K, hk =>
      Term.evalJ_bindAtom_go_joinPoint G _ k env jenv K hk

/-- **Naming an operand does not change its value**: `t.bindAtom k` computes what the
    continuation means, at the value of `t`. -/
theorem Term.evalJ_bindAtom (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (t : Term Sg Γ σ) (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) (env : Env Γ)
    (jenv : JEnv τ J) (K : TyWf.Den σ → TyWf.Den τ) (hk : Term.BindCont G k env jenv K) :
    Term.evalJ G (t.bindAtom k) env jenv = K (Term.eval G t env) :=
  Term.evalJ_bindAtom_go G jenv t k env K hk

/-- `Term.bind.go`, on a term that is neither a variable nor a `let`: the body becomes a
    join point, and the term jumps to it. -/
theorem Term.evalJ_bind_go_joinPoint (G : GlobalEnv Sg.decls) {Γ₀ Γ : Ctx} {σ τ : TyWf}
    {J : JCtx} (body : Term Sg (σ :: Γ₀) τ J) (t : Term Sg Γ σ) (ρ : Ren Γ₀ Γ)
    (env₀ : Env Γ₀) (env : Env Γ) (jenv : JEnv τ J) (h : EnvRel ρ env₀ env) :
    Term.evalJ G (.letJ (body.rename (Ren.lift ρ)) (t.toJump (J₀ := []))) env jenv =
      Term.evalJ G body (Term.eval G t env, env₀) jenv := by
  rw [Term.evalJ_letJ, Term.evalJ_toJump_nil]
  exact Term.evalJ_rename G _ body _ _ jenv (h.lift _)

/-- `Term.bind.go` evaluates the body with the value of the term bound. -/
theorem Term.evalJ_bind_go (G : GlobalEnv Sg.decls) {Γ₀ : Ctx} {σ τ : TyWf} {J : JCtx}
    (body : Term Sg (σ :: Γ₀) τ J) (jenv : JEnv τ J) (env₀ : Env Γ₀) :
    {Γ : Ctx} → (t : Term Sg Γ σ) → (ρ : Ren Γ₀ Γ) → (env : Env Γ) → EnvRel ρ env₀ env →
    Term.evalJ G (Term.bind.go body t rfl ρ) env jenv =
      Term.evalJ G body (Term.eval G t env, env₀) jenv
  | _, .ret (.var v), ρ, env, h => Term.evalJ_rename G _ body _ _ jenv (h.cons v)
  | _, .letE c t, ρ, env, h => by
      show Term.evalJ G (.letE c (Term.bind.go body t rfl _)) env jenv = _
      rw [Term.evalJ_letE]
      exact (Term.evalJ_bind_go G body jenv env₀ t _ _ (EnvRel.comp (EnvRel.wk _ env) h)).trans
        (congrArg (fun x => Term.evalJ G body (x, env₀) jenv)
          (Term.evalJ_letE G c t env PUnit.unit).symm)
  | _, .letJ jp b, ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body (.letJ jp b) ρ env₀ env jenv h
  | _, .jump j _, _, _, _ => nomatch j
  | _, .externCallChecked .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .bool_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .nat_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .nat_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .int_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .uint8_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .uint16_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .uint32_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .uint64_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .int8_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .int16_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .int32_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .int64_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .char_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .stringPosRaw_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .stringPos_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .substringRaw_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .float_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .float32_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .floatModel_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .float32Model_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .array_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .array_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .enum_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .enum_casesOnWithDefault .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .record_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .taggedUnion_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .taggedUnion_casesOnWithDefault .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recTaggedUnion_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recTaggedUnion_casesOnWithDefault .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recTaggedUnion_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recObject_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recObject_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recAlias_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .recAlias_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .mutualRecursiveFamily_casesOn .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .mutualRecursiveFamily_casesOnWithDefault .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h
  | _, .mutualRecursiveFamily_rec .., ρ, env, h =>
      Term.evalJ_bind_go_joinPoint G body _ ρ env₀ env jenv h

/-- **`let x = t; body` binds the value of `t`**, whatever the shape of `t`: its `let`s are
    floated out, a variable it returns is renamed into `body`, and a dispatch or a fold
    sends its value to `body` as a join point. -/
theorem Term.evalJ_bind (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (t : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ J) (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (t.bind body) env jenv = Term.evalJ G body (Term.eval G t env, env) jenv :=
  Term.evalJ_bind_go G body jenv env t Ren.id env (EnvRel.id' env)

/-- `let x = e; body` in direct style binds the value of `e`. -/
theorem Term.eval_letE' (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} (e : Term Sg Γ σ)
    (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.letE' e body) env = Term.eval G body (Term.eval G e env, env) :=
  Term.evalJ_bind G e body env PUnit.unit

/-- `Term.bindAtomOr` computes what its continuations mean at the value of the term: `here`
    when the term is already an atom, `k` otherwise. -/
theorem Term.evalJ_bindAtomOr (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (t : Term Sg Γ σ) (here : Atom Γ σ → Term Sg Γ τ J)
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) (env : Env Γ) (jenv : JEnv τ J)
    (K : TyWf.Den σ → TyWf.Den τ) (hhere : ∀ a, Term.evalJ G (here a) env jenv = K (Atom.eval a env))
    (hk : Term.BindCont G k env jenv K) :
    Term.evalJ G (t.bindAtomOr here k) env jenv = K (Term.eval G t env) := by
  cases t
  case ret a => exact hhere a
  all_goals exact Term.evalJ_bindAtom G _ k env jenv K hk

/-! ## Closed steps -/

/-- A step that reads no variable, written in the empty context, has the value it had. -/
theorem Comp.eval_of_closed? (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ : TyWf}
    {c' : Comp Sg Γ σ} {c : Comp Sg [] σ} (h : c'.closed? = some c) (env : Env Γ) :
    Comp.eval G c' env = Comp.eval G c Env.nil := by
  cases c' <;> cases h <;> rfl

/-- A term that is one closed step has the value of that step. -/
theorem Term.eval_of_closedStep? (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ : TyWf}
    {t : Term Sg Γ σ} {c : Comp Sg [] σ} (h : t.closedStep? = some c) (env : Env Γ) :
    Term.eval G t env = Comp.eval G c Env.nil := by
  cases t with
  | letE c' b =>
      cases b with
      | ret a =>
          rcases a with ⟨v⟩
          cases v with
          | head => exact Comp.eval_of_closed? G h env
          | tail v => cases h
      | _ => cases h
  | _ => cases h

/-- A closed step moved into any context has the value it had. -/
theorem Comp.eval_rename_nil (G : GlobalEnv Sg.decls) {Δ : Ctx} {σ : TyWf}
    (c : Comp Sg [] σ) (env : Env Δ) :
    Comp.eval G (c.rename Ren.nil) env = Comp.eval G c Env.nil :=
  Comp.eval_rename G _ c _ env (EnvRel.nil _ env)

/-! ## Naming a list of operands -/

/-- **Naming the terms of a spine does not change their values.** -/
theorem Spine.eval_bindArgs (G : GlobalEnv Sg.decls) {Δ₀ : Ctx} {τ : TyWf} :
    {Γ : Ctx} → {σs : List TyWf} → (sp : Spine Sg Γ σs) → (ρ : Ren Γ Δ₀) → (env : Env Γ) →
    (env₀ : Env Δ₀) → EnvRel ρ env env₀ →
    (k : ∀ {Δ : Ctx}, Ren Δ₀ Δ → Args Sg Δ σs → Term Sg Δ τ) →
    (K : TyWf.DenList σs → TyWf.Den τ) → Spine.BindCont G k env₀ K →
    Term.eval G (sp.bindArgs ρ k) env₀ = K (Spine.eval G sp env)
  | _, _, .nil, _, _, env₀, _, k, K, hk => hk Ren.id env₀ .nil (EnvRel.id' env₀)
  | _, _, .cons t ts, ρ, env, env₀, h, k, K, hk => by
      unfold Spine.bindArgs
      cases hc : t.closedStep? with
      | some c =>
          simp only
          refine (Spine.eval_bindArgs G ts ρ env env₀ h _
            (fun vs => K (Comp.eval G c Env.nil, vs)) ?_).trans ?_
          · intro Δ ρ₂ env' as h₂
            show Term.eval G (.letE _ _) env' = _
            rw [Term.eval_letE]
            refine (hk _ _ _ (EnvRel.comp (EnvRel.wk _ env') h₂)).trans ?_
            show K (Comp.eval G (c.rename Ren.nil) env',
              Args.eval G (as.rename Ren.wk) (Comp.eval G (c.rename Ren.nil) env', env')) = _
            rw [Args.eval_rename G (EnvRel.wk _ env') as, Comp.eval_rename_nil]
          · show _ = K (Term.eval G t env, _)
            rw [Term.eval_of_closedStep? G hc env]
      | none =>
          simp only
          refine (Term.evalJ_bindAtom G (J := []) (t.rename ρ) _ env₀ PUnit.unit
            (fun x => K (x, Spine.eval G ts env)) ?_).trans ?_
          · intro Δ ρ₁ env₁ a h₁
            refine Spine.eval_bindArgs G ts _ env env₁ (EnvRel.comp h₁ h) _
              (fun vs => K (Atom.eval a env₁, vs)) ?_
            intro Θ ρ₂ env₂ as h₂
            refine (hk _ _ _ (EnvRel.comp h₂ h₁)).trans ?_
            show K (Atom.eval (a.rename ρ₂) env₂, _) = _
            rw [Atom.eval_rename h₂]
          · show K (Term.eval G (t.rename ρ) env₀, _) = K (Term.eval G t env, _)
            rw [Term.eval_rename G ρ t h]

/-- **Naming the elements of an array does not change their values.** -/
theorem Terms.eval_bindAtoms (G : GlobalEnv Sg.decls) {Δ₀ : Ctx} {σ τ : TyWf} :
    {Γ : Ctx} → (ts : Terms Sg Γ σ) → (ρ : Ren Γ Δ₀) → (env : Env Γ) →
    (env₀ : Env Δ₀) → EnvRel ρ env env₀ →
    (k : ∀ {Δ : Ctx}, Ren Δ₀ Δ → List (Atom Δ σ) → Term Sg Δ τ) →
    (K : List (TyWf.Den σ) → TyWf.Den τ) → Terms.BindCont G k env₀ K →
    Term.eval G (ts.bindAtoms ρ k) env₀ = K (Terms.eval G ts env)
  | _, .nil, _, _, env₀, _, k, K, hk => hk Ren.id env₀ [] (EnvRel.id' env₀)
  | _, .cons t ts, ρ, env, env₀, h, k, K, hk => by
      unfold Terms.bindAtoms
      cases hc : t.closedStep? with
      | some c =>
          simp only
          refine (Terms.eval_bindAtoms G ts ρ env env₀ h _
            (fun vs => K (Comp.eval G c Env.nil :: vs)) ?_).trans ?_
          · intro Δ ρ₂ env' as h₂
            show Term.eval G (.letE _ _) env' = _
            rw [Term.eval_letE]
            refine (hk _ _ _ (EnvRel.comp (EnvRel.wk _ env') h₂)).trans ?_
            show K (Comp.eval G (c.rename Ren.nil) env' ::
              (as.map (·.rename Ren.wk)).map
                (fun a : Atom (σ :: Δ) σ =>
                  Atom.eval a (Env.cons (Comp.eval G (c.rename Ren.nil) env') env'))) = _
            rw [Comp.eval_rename_nil, List.map_map]
            congr 2
          · show _ = K (Term.eval G t env :: _)
            rw [Term.eval_of_closedStep? G hc env]
      | none =>
          simp only
          refine (Term.evalJ_bindAtom G (J := []) (t.rename ρ) _ env₀ PUnit.unit
            (fun x => K (x :: Terms.eval G ts env)) ?_).trans ?_
          · intro Δ ρ₁ env₁ a h₁
            refine Terms.eval_bindAtoms G ts _ env env₁ (EnvRel.comp h₁ h) _
              (fun vs => K (Atom.eval a env₁ :: vs)) ?_
            intro Θ ρ₂ env₂ as h₂
            refine (hk _ _ _ (EnvRel.comp h₂ h₁)).trans ?_
            simp only [List.map_cons]
            rw [Atom.eval_rename h₂]
          · show K (Term.eval G (t.rename ρ) env₀ :: _) = K (Term.eval G t env :: _)
            rw [Term.eval_rename G ρ t h]

/-- **Naming the operands of a member of a mutual family does not change their values.** -/
theorem FamilyMemberValue.eval_bindArgs (G : GlobalEnv Sg.decls) {Γ : Ctx}
    {m : LeanFamMemberSchema TyWf} {τ : TyWf} (v : FamilyMemberValue Sg Γ m)
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → FamilyMemberArgs Sg Δ m → Term Sg Δ τ) (env : Env Γ)
    (K : TyWf.DenMember m → TyWf.Den τ) (hk : FamilyMemberValue.BindCont G k env K) :
    Term.eval G (v.bindArgs k) env = K (FamilyMemberValue.eval G v env) := by
  match m, v with
  | _, .ctors l t ht fields =>
      exact Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
        (fun vs => K (TyWf.DenTU.mk t ht vs)) fun ρ env' as h => hk ρ env' _ h
  | _, .record fs fields =>
      exact Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
        (fun vs => K (cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm vs))
        fun ρ env' as h => hk ρ env' _ h
  | _, .alias b value =>
      exact Term.evalJ_bindAtom G (J := []) value _ env PUnit.unit _ fun ρ env' a h => hk ρ env' _ h

end LeanScript

end
