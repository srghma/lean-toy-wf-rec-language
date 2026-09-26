module

public import LeanScript.Eval
public import LeanScript.EvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# Renaming does not change the value of a term

`Term.rename ρ` moves a term to another context along a renaming `ρ`.  This file proves,
for every syntactic category of the grammar at once, that the moved term computes what the
original computes, as long as the two environments agree along `ρ` (`EnvRel`):

    EnvRel ρ env env' → Term.evalJ G (t.rename ρ) env' jenv = Term.evalJ G t env jenv

(`Term.evalJ_rename`).  It is the fact every A-normalising builder of
`LeanScript.Expr.Build` relies on, since each of them renames the terms it moves under the
`let`s it writes.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-! ## Environments that agree along a renaming -/

/-- `env'` agrees with `env` along `ρ`: the variable `ρ v` has in `env'` the value `v` has
    in `env`. -/
def EnvRel {Γ Δ : Ctx} (ρ : Ren Γ Δ) (env : Env Γ) (env' : Env Δ) : Prop :=
  ∀ {τ : TyWf} (v : Γ ∋ τ), Env.get (ρ v) env' = Env.get v env

namespace EnvRel

theorem id' {Γ : Ctx} (env : Env Γ) : EnvRel Ren.id env env := fun _ => rfl

theorem wk {Γ : Ctx} {σ : TyWf} (x : TyWf.Den σ) (env : Env Γ) :
    EnvRel (Ren.wk (σ := σ)) env (x, env) := fun _ => rfl

theorem nil {Δ : Ctx} (env : Env []) (env' : Env Δ) : EnvRel Ren.nil env env' :=
  fun v => nomatch v

theorem comp {Γ Δ Θ : Ctx} {ρ : Ren Γ Δ} {ρ' : Ren Δ Θ} {env : Env Γ} {env' : Env Δ}
    {env'' : Env Θ} (h' : EnvRel ρ' env' env'') (h : EnvRel ρ env env') :
    EnvRel (Ren.comp ρ' ρ) env env'' := fun v => (h' (ρ v)).trans (h v)

theorem lift {Γ Δ : Ctx} {σ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (x : TyWf.Den σ) :
    EnvRel (Ren.lift (σ := σ) ρ) (x, env) (x, env') := by
  intro _ v
  cases v with
  | head => rfl
  | tail v => exact h v

theorem cons {Γ Δ : Ctx} {σ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (v : Δ ∋ σ) :
    EnvRel (Ren.cons v ρ) (Env.get v env', env) env' := by
  intro _ w
  cases w with
  | head => rfl
  | tail w => exact h w

theorem liftN {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') :
    (xs : List TyWf) → (vs : TyWf.DenList xs) →
      EnvRel (Ren.liftN xs ρ) (Env.append vs env) (Env.append vs env')
  | [], _ => h
  | _ :: xs, vs => lift (liftN h xs vs.2) vs.1

theorem liftNat {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (τ : TyWf) :
    (k : Nat) → (w : NatWin τ k) →
      EnvRel (Ren.liftNat τ k ρ) (Env.ofWin w env) (Env.ofWin w env')
  | 0, _ => h
  | k + 1, w => lift (liftNat h τ k w.2) w.1

end EnvRel

/-! ## Atoms and lists of atoms -/


theorem Atom.eval_rename {Γ Δ : Ctx} {τ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (a : Atom Γ τ) : Atom.eval (a.rename ρ) env' = Atom.eval a env := by
  cases a with
  | var v => exact h v

theorem Args.eval_rename (G : GlobalEnv Sg.decls) {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ}
    {env' : Env Δ} (h : EnvRel ρ env env') :
    {σs : List TyWf} → (as : Args Sg Γ σs) → Args.eval G (as.rename ρ) env' = Args.eval G as env
  | _, .nil => rfl
  | _, .cons a as => by
      show (Atom.eval (a.rename ρ) env', Args.eval G (as.rename ρ) env') = _
      rw [Atom.eval_rename h, Args.eval_rename G h as]; rfl

theorem FamilyMemberArgs.eval_rename (G : GlobalEnv Sg.decls) {Γ Δ : Ctx} {ρ : Ren Γ Δ}
    {env : Env Γ} {env' : Env Δ} (h : EnvRel ρ env env') :
    {m : LeanFamMemberSchema TyWf} → (as : FamilyMemberArgs Sg Γ m) →
      FamilyMemberArgs.eval G (as.rename ρ) env' = FamilyMemberArgs.eval G as env
  | _, .ctors _ t ht fields => congrArg (TyWf.DenTU.mk t ht) (Args.eval_rename G h fields)
  | _, .record _ fields => by
        conv => lhs; whnf
        conv => rhs; whnf
        exact Args.eval_rename G h fields
  | _, .alias _ value => Atom.eval_rename h value


/-! ## Terms -/

/-- Put both sides of an equation of values in weak head normal form: the evaluator and
    the renaming take one step each on the constructor at the head of the term. -/
local macro "unf" : tactic =>
  `(tactic| (
    conv => lhs; whnf
    conv => rhs; whnf
    try simp only [Atom.eval_rename ‹EnvRel _ _ _›, Args.eval_rename _ ‹EnvRel _ _ _›]))

mutual

/-- **Renaming does not change the value of a term**, in environments that agree along the
    renaming. -/
theorem Term.evalJ_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → {J : JCtx} → (ρ : Ren Γ Δ) → (t : Term Sg Γ τ J) →
    (env : Env Γ) → (env' : Env Δ) → (jenv : JEnv τ J) → EnvRel ρ env env' →
    Term.evalJ G (t.rename ρ) env' jenv = Term.evalJ G t env jenv
  | _, _, _, _, ρ, .ret a, env, env', jenv, h => Atom.eval_rename h a
  | _, _, _, _, ρ, .letE c body, env, env', jenv, h => by
      show Term.evalJ G (.letE (c.rename ρ) (body.rename (Ren.lift ρ))) env' jenv = _
      rw [Term.evalJ_letE, Term.evalJ_letE, Comp.eval_rename G ρ c env env' h]
      exact Term.evalJ_rename G _ body _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .letJ jp body, env, env', jenv, h => by
      show Term.evalJ G (.letJ (jp.rename (Ren.lift ρ)) (body.rename ρ)) env' jenv = _
      rw [Term.evalJ_letJ, Term.evalJ_letJ]
      have : (fun x => Term.evalJ G (jp.rename (Ren.lift ρ)) (x, env') jenv) =
          (fun x => Term.evalJ G jp (x, env) jenv) :=
        funext fun x => Term.evalJ_rename G _ jp _ _ jenv (h.lift x)
      rw [this]
      exact Term.evalJ_rename G _ body _ _ _ h
  | _, _, _, _, ρ, .jump j a, env, env', jenv, h =>
      congrArg (JEnv.get j jenv) (Atom.eval_rename h a)
  | _, _, _, _, ρ, .externCallChecked args call d fallback, env, env', jenv, h => by
      unf
      generalize call (Args.eval G args env) = o
      cases o with
      | some e => rfl
      | none => exact Term.evalJ_rename G _ fallback _ _ jenv h
  | _, _, _, _, ρ, .bool_casesOn c t e, env, env', jenv, h => by
      unf
      generalize (Atom.eval c env : Bool) = b
      cases b with
      | true => exact Term.evalJ_rename G _ t _ _ jenv h
      | false => exact Term.evalJ_rename G _ e _ _ jenv h
  | _, _, _, _, ρ, .nat_casesOn n z s, env, env', jenv, h => by
      unf
      generalize (Atom.eval n env : Nat) = m
      cases m with
      | zero => exact Term.evalJ_rename G _ z _ _ jenv h
      | succ m => exact Term.evalJ_rename G _ s _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .nat_rec k n base branch d, env, env', jenv, h => by
      unf
      congr 2
      funext m w
      exact Term.evalJ_rename G _ branch _ _ _ (EnvRel.lift (σ := TyWf.prim .nat) (EnvRel.liftNat h _ _ w) m)
  | _, _, _, _, ρ, .int_casesOn i a b, env, env', jenv, h => by
      unf
      generalize (Atom.eval i env : Int) = m
      cases m with
      | ofNat m => exact Term.evalJ_rename G _ a _ _ jenv (h.lift _)
      | negSucc m => exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .uint8_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .uint16_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .uint32_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .uint64_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .int8_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .int16_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .int32_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .int64_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .char_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .stringPosRaw_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .stringPos_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .substringRaw_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (EnvRel.lift (EnvRel.lift (EnvRel.lift h _) _) _)
  | _, _, _, _, ρ, .float_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .float32_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .floatModel_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .float32Model_casesOn v b, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .array_casesOn a z s, env, env', jenv, h => by
      unf
      generalize Array.toList (α := TyWf.Den _) (Atom.eval a env) = l
      cases l with
      | nil => exact Term.evalJ_rename G _ z _ _ jenv h
      | cons x xs => exact Term.evalJ_rename G _ s _ _ jenv (EnvRel.lift (EnvRel.lift h _) _)
  | _, _, _, _, ρ, .array_rec k a bases branch d, env, env', jenv, h => by
      unf
      congr 2
      · funext l
        exact ArrayRecBases.eval_rename G ρ bases env env' l h
      · funext hd tl w
        exact Term.evalJ_rename G _ branch _ _ _ (EnvRel.lift (EnvRel.lift (EnvRel.liftNat h _ _ w) _) _)
  | _, _, _, _, ρ, .enum_casesOn e cases, env, env', jenv, h => by
      unf; exact EnumCases.eval_rename G ρ cases env env' jenv _ h
  | _, _, _, _, ρ, .enum_casesOnWithDefault e cases dflt _, env, env', jenv, h => by
      unf
      rw [Term.evalJ_rename G ρ dflt env env' jenv h]
      exact EnumSomeCases.eval_rename G ρ cases env env' jenv _ _ h
  | _, _, _, _, ρ, .record_casesOn r body, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ body _ _ jenv (h.liftN _ _)
  | _, _, _, _, ρ, .taggedUnion_casesOn v cases, env, env', jenv, h => by
      unf; exact TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' jenv _ h
  | _, _, _, _, ρ, .taggedUnion_casesOnWithDefault v cases dflt _, env, env', jenv, h => by
      unf
      rw [Term.evalJ_rename G ρ dflt env env' jenv h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' jenv _ _ h
  | _, _, _, _, ρ, .recTaggedUnion_casesOn v cases, env, env', jenv, h => by
      unf; exact TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' jenv _ h
  | _, _, _, _, ρ, .recTaggedUnion_casesOnWithDefault v cases dflt _, env, env', jenv, h => by
      unf
      rw [Term.evalJ_rename G ρ dflt env env' jenv h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' jenv _ _ h
  | _, _, _, _, ρ, .recTaggedUnion_rec k v cases d, env, env', jenv, h => by
      unf
      congr 2
      funext node kids
      exact TaggedUnionFoldKCases.eval_rename G ρ cases env env' _ _ _ _ h
  | _, _, _, _, ρ, .recObject_casesOn v body, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ body _ _ jenv (h.liftN _ _)
  | _, _, _, _, ρ, .recObject_rec k v body d, env, env', jenv, h => by
      unf
      congr 2
      funext node kids
      exact Term.evalJ_rename G _ body _ _ _ (h.liftN _ _)
  | _, _, _, _, ρ, .recAlias_casesOn v body, env, env', jenv, h => by
      unf; exact Term.evalJ_rename G _ body _ _ jenv (h.lift _)
  | _, _, _, _, ρ, .recAlias_rec k v body d, env, env', jenv, h => by
      unf
      congr 2
      funext node kids
      exact Term.evalJ_rename G _ body _ _ _ (h.liftN _ _)
  | _, _, _, _, ρ, .mutualRecursiveFamily_casesOn v cases, env, env', jenv, h => by
      unf; exact FamilyMemberCases.eval_rename G ρ cases env env' jenv _ h
  | _, _, _, _, ρ, .mutualRecursiveFamily_casesOnWithDefault v cases dflt, env, env', jenv, h => by
      unf
      rw [Term.evalJ_rename G ρ dflt env env' jenv h]
      exact FamilyMemberSomeCases.eval_rename G ρ cases env env' jenv _ _ h
  | _, _, _, _, ρ, .mutualRecursiveFamily_rec k v cases d, env, env', jenv, h => by
      unf
      congr 2
      funext i a kids
      exact FamilyFoldKCases.eval_rename G ρ cases env env' _ _ _ h

/-- Renaming does not change the value of a computation step. -/
theorem Comp.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → (ρ : Ren Γ Δ) → (c : Comp Sg Γ τ) →
    (env : Env Γ) → (env' : Env Δ) → EnvRel ρ env env' →
    Comp.eval G (c.rename ρ) env' = Comp.eval G c env
  | _, _, _, _, .global _, _, _, _ => rfl
  | _, _, _, _, .bool_mk _, _, _, _ => rfl
  | _, _, _, _, .nat_mk _, _, _, _ => rfl
  | _, _, _, _, .int_mk _, _, _, _ => rfl
  | _, _, _, _, .bitvec_mk _ _, _, _, _ => rfl
  | _, _, _, _, .uint8_mk _, _, _, _ => rfl
  | _, _, _, _, .uint16_mk _, _, _, _ => rfl
  | _, _, _, _, .uint32_mk _, _, _, _ => rfl
  | _, _, _, _, .uint64_mk _, _, _, _ => rfl
  | _, _, _, _, .int8_mk _, _, _, _ => rfl
  | _, _, _, _, .int16_mk _, _, _, _ => rfl
  | _, _, _, _, .int32_mk _, _, _, _ => rfl
  | _, _, _, _, .int64_mk _, _, _, _ => rfl
  | _, _, _, _, .char_mk _, _, _, _ => rfl
  | _, _, _, _, .string_mk _, _, _, _ => rfl
  | _, _, _, _, .stringPos_mk _ _, _, _, _ => rfl
  | _, _, _, _, .stringPosRaw_mk _, _, _, _ => rfl
  | _, _, _, _, .substringRaw_mk _, _, _, _ => rfl
  | _, _, _, _, .stringSlice_mk _, _, _, _ => rfl
  | _, _, _, _, .float_mk _, _, _, _ => rfl
  | _, _, _, _, .float32_mk _, _, _, _ => rfl
  | _, _, _, _, .floatModel_mk _, _, _, _ => rfl
  | _, _, _, _, .float32Model_mk _, _, _, _ => rfl
  | _, _, _, ρ, .lam body, env, env', h =>
      funext fun x => Term.evalJ_rename G _ body _ _ _ (h.lift x)
  | _, _, _, ρ, .ap f a, env, env', h => by
      show Atom.eval (f.rename ρ) env' (Atom.eval (a.rename ρ) env') = _
      rw [Atom.eval_rename h, Atom.eval_rename h]; rfl
  | _, _, _, _, .extern _, _, _, _ => rfl
  | _, _, _, ρ, .externCall args call, env, env', h => by
      unf
  | _, _, _, ρ, .lazy_mk e, env, env', h => Term.evalJ_rename G ρ e env env' _ h
  | _, _, _, ρ, .lazy_force a, env, env', h => Atom.eval_rename h a
  | _, _, _, ρ, .thunk_mk e, env, env', h => Term.evalJ_rename G ρ e env env' _ h
  | _, _, _, ρ, .thunk_force a, env, env', h => Atom.eval_rename h a
  | _, _, _, ρ, .array_mk xs, env, env', h => by
      show ((xs.map (·.rename ρ)).map (Atom.eval · env')).toArray =
        (xs.map (Atom.eval · env)).toArray
      rw [List.map_map]
      congr 1
      exact List.map_congr_left fun a _ => Atom.eval_rename h a
  | _, _, _, _, .enum_mk _ _, _, _, _ => rfl
  | _, _, _, ρ, .record_mk fs fields, env, env', h =>
      by
        conv => lhs; whnf
        conv => rhs; whnf
        exact Args.eval_rename G h fields
  | _, _, _, ρ, .taggedUnion_mk _ t ht fields, env, env', h =>
      congrArg (TyWf.DenTU.mk t ht) (Args.eval_rename G h fields)
  | _, _, _, ρ, .recTaggedUnion_mk l hwf t ht fields, env, env', h =>
      congrArg (fun x => TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht x))
        (Args.eval_rename G h fields)
  | _, _, _, ρ, .recObject_mk fs hwf fields, env, env', h =>
      congrArg (TyWf.DenObj.mk fs hwf) (Args.eval_rename G h fields)
  | _, _, _, ρ, .recAlias_mk b hwf value, env, env', h =>
      congrArg (TyWf.DenAlias.mk b hwf) (Atom.eval_rename h value)
  | _, _, _, ρ, .mutualRecursiveFamily_mk f hwf value, env, env', h =>
      congrArg (TyWf.DenFam.mk f hwf) (FamilyMemberArgs.eval_rename G h value)

/-- Renaming does not change the answers of a fold of an array to its short lists. -/
theorem ArrayRecBases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {σ τ : TyWf} → {k : Nat} → (ρ : Ren Γ Δ) → (bs : ArrayRecBases Sg Γ σ τ k) →
    (env : Env Γ) → (env' : Env Δ) → (l : List (TyWf.Den σ)) → EnvRel ρ env env' →
    ArrayRecBases.eval G (bs.rename ρ) env' l = ArrayRecBases.eval G bs env l
  | _, _, _, _, _, ρ, .nil e, env, env', _, h => Term.evalJ_rename G ρ e env env' _ h
  | _, _, _, _, _, ρ, .cons e _, env, env', [], h => Term.evalJ_rename G ρ e env env' _ h
  | _, _, _, _, _, _, .cons _ more, _, _, a :: as, h =>
      ArrayRecBases.eval_rename G _ more _ _ as (h.lift a)

/-- Renaming does not change a partial dispatch on a tagged union. -/
theorem TaggedUnionSomeCases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {k lo : Nat} → {J : JCtx} →
    (ρ : Ren Γ Δ) → (cases : TaggedUnionSomeCases Sg Γ l τ k lo J) → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (v : TyWf.DenTU l) → (dflt : TyWf.Den τ) →
    EnvRel ρ env env' →
    TaggedUnionSomeCases.eval G (cases.rename ρ) env' jenv v dflt =
      TaggedUnionSomeCases.eval G cases env jenv v dflt
  | _, _, _, _, _, _, _, ρ, .last t ht branch _, env, env', jenv, v, dflt, h => by
      unf
      generalize TyWf.DenTU.field? t ht v = o
      cases o with
      | none => rfl
      | some f => exact Term.evalJ_rename G _ branch _ _ jenv (h.liftN _ _)
  | _, _, _, _, _, _, _, ρ, .cons t ht branch rest _, env, env', jenv, v, dflt, h => by
      unf
      generalize TyWf.DenTU.field? t ht v = o
      cases o with
      | none => exact TaggedUnionSomeCases.eval_rename G ρ rest env env' jenv v dflt h
      | some f => exact Term.evalJ_rename G _ branch _ _ jenv (h.liftN _ _)

/-- Renaming does not change a dispatch on an enum. -/
theorem EnumCases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {J : JCtx} → (ρ : Ren Γ Δ) →
    (cases : EnumCases Sg Γ τ s J) → (env : Env Γ) → (env' : Env Δ) → (jenv : JEnv τ J) →
    (i : Fin s.nOfConstructors) → EnvRel ρ env env' →
    EnumCases.eval G (cases.rename ρ) env' jenv i = EnumCases.eval G cases env jenv i
  | _, _, _, _, _, ρ, .three b0 b1 b2, env, env', jenv, i, h => by
      match i with
      | ⟨0, _⟩ => unf; exact Term.evalJ_rename G ρ b0 env env' jenv h
      | ⟨1, _⟩ => unf; exact Term.evalJ_rename G ρ b1 env env' jenv h
      | ⟨2, _⟩ => unf; exact Term.evalJ_rename G ρ b2 env env' jenv h
      | ⟨_ + 3, hi⟩ => exact absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, _, _, ρ, .cons b rest, env, env', jenv, i, h => by
      match i with
      | ⟨0, _⟩ => unf; exact Term.evalJ_rename G ρ b env env' jenv h
      | ⟨n + 1, hi⟩ => unf; exact EnumCases.eval_rename G ρ rest env env' jenv _ h

/-- Renaming does not change a partial dispatch on an enum. -/
theorem EnumSomeCases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {k lo : Nat} → {J : JCtx} →
    (ρ : Ren Γ Δ) → (cases : EnumSomeCases Sg Γ τ s k lo J) → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (i : Fin s.nOfConstructors) → (dflt : TyWf.Den τ) →
    EnvRel ρ env env' →
    EnumSomeCases.eval G (cases.rename ρ) env' jenv i dflt =
      EnumSomeCases.eval G cases env jenv i dflt
  | _, _, _, _, _, _, _, ρ, .last j branch _, env, env', jenv, i, dflt, h => by
      show (if i = j then Term.evalJ G (branch.rename ρ) env' jenv else dflt) =
        (if i = j then Term.evalJ G branch env jenv else dflt)
      rw [Term.evalJ_rename G ρ branch env env' jenv h]
  | _, _, _, _, _, _, _, ρ, .cons j branch rest _, env, env', jenv, i, dflt, h => by
      show (if i = j then Term.evalJ G (branch.rename ρ) env' jenv
          else EnumSomeCases.eval G (rest.rename ρ) env' jenv i dflt) =
        (if i = j then Term.evalJ G branch env jenv else EnumSomeCases.eval G rest env jenv i dflt)
      rw [Term.evalJ_rename G ρ branch env env' jenv h,
        EnumSomeCases.eval_rename G ρ rest env env' jenv i dflt h]

/-- Renaming does not change a dispatch on a tagged union. -/
theorem TaggedUnionCases.eval_rename (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ Δ : Ctx} → {l : LeanTaggedUnionSchema ι} →
    {τ : TyWf} → {J : JCtx} → (ρ : Ren Γ Δ) → (cases : TaggedUnionFoldCases Sg ι bind Γ l τ J) →
    {l' : LeanTaggedUnionSchema TyWf} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : l ≍ l') → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (v : TyWf.DenTU l') → EnvRel ρ env env' →
    TaggedUnionCases.eval G (cases.rename ρ) h1 h2 h3 env' jenv v =
      TaggedUnionCases.eval G cases h1 h2 h3 env jenv v
  | _, _, _, _, _, _, _, ρ, .payloadFirst b0 b1 rest, _, rfl, .rfl, .rfl, env, env', jenv, v, h => by
      match v with
      | ⟨⟨0, _⟩, f⟩ => unf; exact Term.evalJ_rename G _ b0 _ _ jenv (h.liftN _ _)
      | ⟨⟨1, _⟩, f⟩ => unf; exact Term.evalJ_rename G _ b1 _ _ jenv (h.liftN _ _)
      | ⟨⟨n + 2, _⟩, f⟩ =>
          unf; exact TaggedUnionCasesRest.eval_rename G ρ rest rfl .rfl .rfl env env' jenv n f h
  | _, _, _, _, _, _, _, ρ, .skip b0 rest, _, rfl, .rfl, .rfl, env, env', jenv, v, h => by
      match v with
      | ⟨⟨0, _⟩, f⟩ => unf; exact Term.evalJ_rename G _ b0 _ _ jenv h
      | ⟨⟨n + 1, _⟩, f⟩ =>
          unf; exact CtorsWithPayloadCases.eval_rename G ρ rest rfl .rfl .rfl env env' jenv n f h

/-- `TaggedUnionCases.eval_rename`, on the constructors that follow a field-less one. -/
theorem CtorsWithPayloadCases.eval_rename (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ Δ : Ctx} → {c : CtorsWithPayload ι} →
    {τ : TyWf} → {J : JCtx} → (ρ : Ren Γ Δ) →
    (cases : CtorsWithPayloadFoldCases Sg ι bind Γ c τ J) →
    {c' : CtorsWithPayload TyWf} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : c ≍ c') → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (t : Nat) → (f : TyWf.DenAtCP c' t) →
    EnvRel ρ env env' →
    CtorsWithPayloadCases.eval G (cases.rename ρ) h1 h2 h3 env' jenv t f =
      CtorsWithPayloadCases.eval G cases h1 h2 h3 env jenv t f
  | _, _, _, _, _, _, _, ρ, .here b _, _, rfl, .rfl, .rfl, env, env', jenv, 0, f, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.liftN _ _)
  | _, _, _, _, _, _, _, ρ, .here _ rest, _, rfl, .rfl, .rfl, env, env', jenv, n + 1, f, h => by
      unf; exact TaggedUnionCasesRest.eval_rename G ρ rest rfl .rfl .rfl env env' jenv n f h
  | _, _, _, _, _, _, _, ρ, .skip b _, _, rfl, .rfl, .rfl, env, env', jenv, 0, f, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv h
  | _, _, _, _, _, _, _, ρ, .skip _ rest, _, rfl, .rfl, .rfl, env, env', jenv, n + 1, f, h => by
      unf; exact CtorsWithPayloadCases.eval_rename G ρ rest rfl .rfl .rfl env env' jenv n f h

/-- `TaggedUnionCases.eval_rename`, on a plain list of constructors. -/
theorem TaggedUnionCasesRest.eval_rename (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ Δ : Ctx} → {cs : List (List ι)} →
    {τ : TyWf} → {J : JCtx} → (ρ : Ren Γ Δ) →
    (cases : TaggedUnionFoldCasesRest Sg ι bind Γ cs τ J) →
    {cs' : List (List TyWf)} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : cs ≍ cs') → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (t : Nat) → (f : TyWf.DenAtList cs' t) →
    EnvRel ρ env env' →
    TaggedUnionCasesRest.eval G (cases.rename ρ) h1 h2 h3 env' jenv t f =
      TaggedUnionCasesRest.eval G cases h1 h2 h3 env jenv t f
  | _, _, _, _, _, _, _, _, .nil, _, rfl, .rfl, .rfl, _, _, _, _, f, _ => PEmpty.elim f
  | _, _, _, _, _, _, _, ρ, .cons b _, _, rfl, .rfl, .rfl, env, env', jenv, 0, f, h => by
      unf; exact Term.evalJ_rename G _ b _ _ jenv (h.liftN _ _)
  | _, _, _, _, _, _, _, ρ, .cons _ rest, _, rfl, .rfl, .rfl, env, env', jenv, n + 1, f, h => by
      unf; exact TaggedUnionCasesRest.eval_rename G ρ rest rfl .rfl .rfl env env' jenv n f h

/-- Renaming does not change one branch of the fold of a recursive tagged union. -/
theorem FoldKBranch.eval_rename (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ Δ : Ctx} → {fs : List (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} → (ρ : Ren Γ Δ) →
    (br : FoldKBranch Sg l₀ bind Γ fs τ k outer) → (env : Env Γ) → (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : RecFrames l₀ τ outer) → (e : RecFields l₀ τ fs) → EnvRel ρ env env' →
    FoldKBranch.eval G (br.rename ρ) env' mkEnv fr e = FoldKBranch.eval G br env mkEnv fr e
  | _, _, _, _, _, _, _, _, ρ, .here body, env, env', mkEnv, _, e, h => by
      unf; exact Term.evalJ_rename G _ body _ _ _ (h.liftN _ _)
  | _, _, _, _, _, _, _, _, ρ, .deep sf cases, env, env', mkEnv, fr, e, h => by
      unf
      rcases selfFieldMemo sf e with ⟨⟨node, _⟩, kids⟩
      exact TaggedUnionFoldKCases.eval_rename G _ cases _ _ mkEnv _ _ _ (h.liftN _ _)
  | _, _, _, _, _, _, _, _, ρ, .deepOuter o cases, env, env', mkEnv, fr, e, h => by
      unf
      rcases outerSelfFieldMemo o fr with ⟨⟨node, _⟩, kids⟩
      exact TaggedUnionFoldKCases.eval_rename G _ cases _ _ mkEnv _ _ _ (h.liftN _ _)

/-- Renaming does not change the fold of a recursive tagged union at a node. -/
theorem TaggedUnionFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ Δ : Ctx} → {l : LeanTaggedUnionSchema (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} → (ρ : Ren Γ Δ) →
    (cases : TaggedUnionFoldKCases Sg l₀ bind Γ l τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : RecFrames l₀ τ outer) →
    (t : Nat) → (e : (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ)) → EnvRel ρ env env' →
    TaggedUnionFoldKCases.eval G (cases.rename ρ) env' mkEnv fr t e =
      TaggedUnionFoldKCases.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, ρ, .payloadFirst b0 _ _, env, env', mkEnv, fr, 0, e, h =>
      FoldKBranch.eval_rename G ρ b0 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .payloadFirst _ b1 _, env, env', mkEnv, fr, 1, e, h =>
      FoldKBranch.eval_rename G ρ b1 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .payloadFirst _ _ rest, env, env', mkEnv, fr, n + 2, e, h =>
      TaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr n e h
  | _, _, _, _, _, _, _, _, ρ, .skip b0 _, env, env', mkEnv, fr, 0, e, h =>
      FoldKBranch.eval_rename G ρ b0 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .skip _ rest, env, env', mkEnv, fr, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval_rename G ρ rest env env' mkEnv fr n e h

/-- `TaggedUnionFoldKCases.eval_rename`, on the constructors that follow a field-less
    one. -/
theorem CtorsWithPayloadFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ Δ : Ctx} → {c : CtorsWithPayload (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} → (ρ : Ren Γ Δ) →
    (cases : CtorsWithPayloadFoldKCases Sg l₀ bind Γ c τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : RecFrames l₀ τ outer) →
    (t : Nat) → (e : (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ)) →
    EnvRel ρ env env' →
    CtorsWithPayloadFoldKCases.eval G (cases.rename ρ) env' mkEnv fr t e =
      CtorsWithPayloadFoldKCases.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, ρ, .here b _, env, env', mkEnv, fr, 0, e, h =>
      FoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .here _ rest, env, env', mkEnv, fr, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr n e h
  | _, _, _, _, _, _, _, _, ρ, .skip b _, env, env', mkEnv, fr, 0, e, h =>
      FoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .skip _ rest, env, env', mkEnv, fr, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval_rename G ρ rest env env' mkEnv fr n e h

/-- `TaggedUnionFoldKCases.eval_rename`, on a plain list of constructors. -/
theorem TaggedUnionFoldKCasesRest.eval_rename (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ Δ : Ctx} → {cs : List (List (TyWfIn 1))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} → (ρ : Ren Γ Δ) →
    (cases : TaggedUnionFoldKCasesRest Sg l₀ bind Γ cs τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : RecFrames l₀ τ outer) →
    (t : Nat) →
    (e : (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ)) →
    EnvRel ρ env env' →
    TaggedUnionFoldKCasesRest.eval G (cases.rename ρ) env' mkEnv fr t e =
      TaggedUnionFoldKCasesRest.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, e, _ => PEmpty.elim e.1
  | _, _, _, _, _, _, _, _, ρ, .cons b _, env, env', mkEnv, fr, 0, e, h =>
      FoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, ρ, .cons _ rest, env, env', mkEnv, fr, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr n e h

/-- Renaming does not change a dispatch on a member of a mutual family. -/
theorem FamilyMemberCases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J : JCtx} →
    (ρ : Ren Γ Δ) → (cases : FamilyMemberCases Sg Γ τ m J) → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (v : TyWf.DenMember m) → EnvRel ρ env env' →
    FamilyMemberCases.eval G (cases.rename ρ) env' jenv v = FamilyMemberCases.eval G cases env jenv v
  | _, _, _, _, _, ρ, .ctors cases, env, env', jenv, v, h =>
      TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' jenv v h
  | _, _, _, _, _, _, .record body, _, _, jenv, _, h =>
      Term.evalJ_rename G _ body _ _ jenv (h.liftN _ _)
  | _, _, _, _, _, _, .alias body, _, _, jenv, _, h =>
      Term.evalJ_rename G _ body _ _ jenv (h.lift _)

/-- Renaming does not change a partial dispatch on a member of a mutual family. -/
theorem FamilyMemberSomeCases.eval_rename (G : GlobalEnv Sg.decls) :
    {Γ Δ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J : JCtx} →
    (ρ : Ren Γ Δ) → (cases : FamilyMemberSomeCases Sg Γ τ m J) → (env : Env Γ) →
    (env' : Env Δ) → (jenv : JEnv τ J) → (v : TyWf.DenMember m) → (dflt : TyWf.Den τ) →
    EnvRel ρ env env' →
    FamilyMemberSomeCases.eval G (cases.rename ρ) env' jenv v dflt =
      FamilyMemberSomeCases.eval G cases env jenv v dflt
  | _, _, _, _, _, ρ, .ctors cases _, env, env', jenv, v, dflt, h =>
      TaggedUnionSomeCases.eval_rename G ρ cases env env' jenv v dflt h

/-- Renaming does not change one branch of the fold of a mutual family. -/
theorem FamilyFoldKBranch.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} → {fs : List (TyWfIn (n + 2))} →
    {τ : TyWf} → {k : Nat} → {outer : List (List (TyWfIn (n + 2)))} → (ρ : Ren Γ Δ) →
    (br : FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer) → (env : Env Γ) → (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : FamFrames ms₀ τ outer) → (e : FamFields ms₀ τ fs) → EnvRel ρ env env' →
    FamilyFoldKBranch.eval G (br.rename ρ) env' mkEnv fr e =
      FamilyFoldKBranch.eval G br env mkEnv fr e
  | _, _, _, _, _, _, _, _, _, ρ, .here body, env, env', mkEnv, _, e, h => by
      unf; exact Term.evalJ_rename G _ body _ _ _ (h.liftN _ _)
  | _, _, _, _, _, _, _, _, _, ρ, .deep field member cases, env, env', mkEnv, fr, e, h => by
      unf; exact FamilyMemberFoldKCases.eval_rename G _ cases _ _ mkEnv _ _ (h.liftN _ _)
  | _, _, _, _, _, _, _, _, _, ρ, .deepOuter field member cases, env, env', mkEnv, fr, e, h => by
      unf; exact FamilyMemberFoldKCases.eval_rename G _ cases _ _ mkEnv _ _ (h.liftN _ _)

/-- Renaming does not change the fold of a mutual family at a node of one member. -/
theorem FamilyMemberFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} → {τ : TyWf} →
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} → (ρ : Ren Γ Δ) →
    (cases : FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : FamFrames ms₀ τ outer) → (x : (famIPF m).Obj (FamMemoAt ms₀ τ)) →
    EnvRel ρ env env' →
    FamilyMemberFoldKCases.eval G (cases.rename ρ) env' mkEnv fr x =
      FamilyMemberFoldKCases.eval G cases env mkEnv fr x
  | _, _, _, _, _, _, _, _, _, ρ, .ctors cases, env, env', mkEnv, fr, _, h =>
      FamilyTaggedUnionFoldKCases.eval_rename G ρ cases env env' mkEnv fr _ _ h
  | _, _, _, _, _, _, _, _, _, ρ, .record br, env, env', mkEnv, fr, _, h =>
      FamilyFoldKBranch.eval_rename G ρ br env env' mkEnv fr _ h
  | _, _, _, _, _, _, _, _, _, ρ, .alias br, env, env', mkEnv, fr, _, h =>
      FamilyFoldKBranch.eval_rename G ρ br env env' mkEnv fr _ h

/-- Renaming does not change the fold of a member with constructors at a node. -/
theorem FamilyTaggedUnionFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} →
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} → (ρ : Ren Γ Δ) →
    (cases : FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : FamFrames ms₀ τ outer) →
    (t : Nat) → (e : (Ty.toIPFAt (l.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ)) →
    EnvRel ρ env env' →
    FamilyTaggedUnionFoldKCases.eval G (cases.rename ρ) env' mkEnv fr t e =
      FamilyTaggedUnionFoldKCases.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, _, ρ, .payloadFirst b0 _ _, env, env', mkEnv, fr, 0, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b0 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .payloadFirst _ b1 _, env, env', mkEnv, fr, 1, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b1 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .payloadFirst _ _ rest, env, env', mkEnv, fr, t + 2, e, h =>
      FamilyTaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr t e h
  | _, _, _, _, _, _, _, _, _, ρ, .skip b0 _, env, env', mkEnv, fr, 0, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b0 env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .skip _ rest, env, env', mkEnv, fr, t + 1, e, h =>
      FamilyCtorsWithPayloadFoldKCases.eval_rename G ρ rest env env' mkEnv fr t e h

/-- `FamilyTaggedUnionFoldKCases.eval_rename`, on the constructors that follow a field-less
    one. -/
theorem FamilyCtorsWithPayloadFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} →
    {c : CtorsWithPayload (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} → (ρ : Ren Γ Δ) →
    (cases : FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ c τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : FamFrames ms₀ τ outer) →
    (t : Nat) → (e : (Ty.toIPFAtCP (c.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ)) →
    EnvRel ρ env env' →
    FamilyCtorsWithPayloadFoldKCases.eval G (cases.rename ρ) env' mkEnv fr t e =
      FamilyCtorsWithPayloadFoldKCases.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, _, ρ, .here b _, env, env', mkEnv, fr, 0, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .here _ rest, env, env', mkEnv, fr, t + 1, e, h =>
      FamilyTaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr t e h
  | _, _, _, _, _, _, _, _, _, ρ, .skip b _, env, env', mkEnv, fr, 0, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .skip _ rest, env, env', mkEnv, fr, t + 1, e, h =>
      FamilyCtorsWithPayloadFoldKCases.eval_rename G ρ rest env env' mkEnv fr t e h

/-- `FamilyTaggedUnionFoldKCases.eval_rename`, on a plain list of constructors. -/
theorem FamilyTaggedUnionFoldKCasesRest.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} →
    {cs : List (List (TyWfIn (n + 2)))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} → (ρ : Ren Γ Δ) →
    (cases : FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ cs τ k outer) → (env : Env Γ) →
    (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (fr : FamFrames ms₀ τ outer) →
    (t : Nat) →
    (e : (Ty.toIPFAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (FamMemoAt ms₀ τ)) →
    EnvRel ρ env env' →
    FamilyTaggedUnionFoldKCasesRest.eval G (cases.rename ρ) env' mkEnv fr t e =
      FamilyTaggedUnionFoldKCasesRest.eval G cases env mkEnv fr t e
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, e, _ => PEmpty.elim e.1
  | _, _, _, _, _, _, _, _, _, ρ, .cons b _, env, env', mkEnv, fr, 0, e, h =>
      FamilyFoldKBranch.eval_rename G ρ b env env' mkEnv fr e h
  | _, _, _, _, _, _, _, _, _, ρ, .cons _ rest, env, env', mkEnv, fr, t + 1, e, h =>
      FamilyTaggedUnionFoldKCasesRest.eval_rename G ρ rest env env' mkEnv fr t e h

/-- Renaming does not change the fold of a mutual family at a node of member `i`. -/
theorem FamilyFoldKCases.eval_rename (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ Δ : Ctx} → {τ : TyWf} →
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} → {k : Nat} → (ρ : Ren Γ Δ) →
    (cases : FamilyFoldKCases Sg n ms₀ bind Γ τ ms k) → (env : Env Γ) → (env' : Env Δ) →
    (mkEnv : (fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (i : Nat) → (node : (IPFunctor.at (famFs ms) i).Obj (FamMemoAt ms₀ τ)) →
    EnvRel ρ env env' →
    FamilyFoldKCases.eval G (cases.rename ρ) env' mkEnv i node =
      FamilyFoldKCases.eval G cases env mkEnv i node
  | _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, node, _ => PEmpty.elim node.1
  | _, _, _, _, _, _, _, _, ρ, .cons c _, env, env', mkEnv, 0, node, h =>
      FamilyMemberFoldKCases.eval_rename G ρ c env env' mkEnv _ node h
  | _, _, _, _, _, _, _, _, ρ, .cons _ rest, env, env', mkEnv, i + 1, node, h =>
      FamilyFoldKCases.eval_rename G ρ rest env env' mkEnv i node h

end

/-- A term, renamed and run with no join point in scope, has the value of the original. -/
theorem Term.eval_rename (G : GlobalEnv Sg.decls) {Γ Δ : Ctx} {τ : TyWf} (ρ : Ren Γ Δ)
    (t : Term Sg Γ τ) {env : Env Γ} {env' : Env Δ} (h : EnvRel ρ env env') :
    Term.eval G (t.rename ρ) env' = Term.eval G t env :=
  Term.evalJ_rename G ρ t env env' _ h

/-- A term under one more binder it does not mention has the value of the original. -/
theorem Term.evalJ_weaken (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (t : Term Sg Γ τ J) (x : TyWf.Den σ) (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (t.rename (Ren.wk (σ := σ))) (x, env) jenv = Term.evalJ G t env jenv :=
  Term.evalJ_rename G _ t env _ jenv (EnvRel.wk x env)

end LeanScript

end
