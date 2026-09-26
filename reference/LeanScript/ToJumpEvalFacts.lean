module

public import LeanScript.Eval
public import LeanScript.EvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# Sending the value of a term to a join point does not change it

`Term.toJump` makes every tail of a term that gives its value jump instead to a join point
inserted after the term's own join points.  This file proves, for every family the
function is defined on, that the result computes the join point applied to the value of
the original term, as long as the join points of the two environments agree (`JRel`):

    JRel k jenv₀ jenv' → Term.evalJ G t.toJump env jenv' = k (Term.evalJ G t env jenv₀)

(`Term.evalJ_toJump`).  It is the fact behind every join point the builders of
`LeanScript.Expr.Build` write for a dispatch or a fold in operand position.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-- The join points `jenv'` of `t.toJump` agree with the join points `jenv₀` of `t`, for the
    join point `k` inserted after them: each join point of `t` is followed by `k`, and the
    inserted one is `k` itself. -/
def JRel {σ τ : TyWf} (k : TyWf.Den σ → TyWf.Den τ) {J₀ J : JCtx} (jenv₀ : JEnv σ J₀)
    (jenv' : JEnv τ (J₀ ++ σ :: J)) : Prop :=
  (∀ {x : TyWf} (j : J₀ ∋ x) (v : TyWf.Den x),
      JEnv.get (JVar.embedL j) jenv' v = k (JEnv.get j jenv₀ v)) ∧
    ∀ v, JEnv.get (JVar.mid J₀) jenv' v = k v

namespace JRel

/-- With no join point of its own, a term's inserted join point is the innermost one. -/
theorem nil {σ τ : TyWf} {J : JCtx} (k : TyWf.Den σ → TyWf.Den τ) (jenv : JEnv τ J) :
    JRel (J₀ := []) k PUnit.unit (k, jenv) :=
  ⟨fun j => (nomatch j), fun _ => rfl⟩

/-- One more join point on both sides, the new one followed by `k`. -/
theorem cons {σ τ x : TyWf} {k : TyWf.Den σ → TyWf.Den τ} {J₀ J : JCtx} {jenv₀ : JEnv σ J₀}
    {jenv' : JEnv τ (J₀ ++ σ :: J)} (h : JRel k jenv₀ jenv')
    (f₀ : TyWf.Den x → TyWf.Den σ) (f' : TyWf.Den x → TyWf.Den τ)
    (hf : ∀ v, f' v = k (f₀ v)) :
    JRel (J₀ := x :: J₀) (J := J) k (f₀, jenv₀) (f', jenv') := by
  refine ⟨fun j v => ?_, h.2⟩
  cases j with
  | head => exact hf v
  | tail j => exact h.1 j v

end JRel

/-- A fold's destination, sent to the inserted join point, delivers `k` of what it
    delivered. -/
theorem Dest.apply_toJump {ρ σ τ : TyWf} {J₀ J : JCtx} {k : TyWf.Den σ → TyWf.Den τ}
    {jenv₀ : JEnv σ J₀} {jenv' : JEnv τ (J₀ ++ σ :: J)} (h : JRel k jenv₀ jenv')
    (d : Dest J₀ ρ σ) (v : TyWf.Den ρ) :
    Dest.apply d.toJump jenv' v = k (Dest.apply d jenv₀ v) := by
  cases d with
  | ret => exact h.2 v
  | jump j => exact h.1 j v

/-- Put the left side, and the argument of `k` on the right side, in weak head normal
    form. -/
local macro "unfk" : tactic =>
  `(tactic| (
    conv => lhs; whnf
    conv => rhs; arg 1; whnf))

mutual

/-- **Sending the value of a term to a join point** computes the join point applied to the
    value of the term. -/
theorem Term.evalJ_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {J₀ J : JCtx} → (t : Term Sg Γ σ J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    JRel k jenv₀ jenv' →
    Term.evalJ G (t.toJump (J := J) (τ := τ)) env jenv' = k (Term.evalJ G t env jenv₀)
  | _, _, _, _, _, .ret a, env, k, jenv₀, jenv', h => h.2 _
  | _, _, _, _, _, .letE c body, env, k, jenv₀, jenv', h => by
      show Term.evalJ G (.letE c body.toJump) env jenv' = _
      rw [Term.evalJ_letE, Term.evalJ_letE]
      exact Term.evalJ_toJump G body _ k jenv₀ jenv' h
  | _, _, _, _, _, .letJ jp body, env, k, jenv₀, jenv', h => by
      show Term.evalJ G (.letJ jp.toJump body.toJump) env jenv' = _
      rw [Term.evalJ_letJ, Term.evalJ_letJ]
      exact Term.evalJ_toJump G body env k _ _
        (h.cons _ _ fun v => Term.evalJ_toJump G jp _ k jenv₀ jenv' h)
  | _, _, _, _, _, .jump j a, env, k, jenv₀, jenv', h => h.1 j _
  | _, _, _, _, _, .externCallChecked args call d fallback, env, k, jenv₀, jenv', h => by
      unfk
      generalize call (Args.eval G args env) = o
      cases o with
      | some e => exact Dest.apply_toJump h d _
      | none => exact Term.evalJ_toJump G fallback env k jenv₀ jenv' h
  | _, _, _, _, _, .bool_casesOn c t e, env, k, jenv₀, jenv', h => by
      unfk
      generalize (Atom.eval c env : Bool) = b
      cases b with
      | true => exact Term.evalJ_toJump G t env k jenv₀ jenv' h
      | false => exact Term.evalJ_toJump G e env k jenv₀ jenv' h
  | _, _, _, _, _, .nat_casesOn n z s, env, k, jenv₀, jenv', h => by
      unfk
      generalize (Atom.eval n env : Nat) = m
      cases m with
      | zero => exact Term.evalJ_toJump G z env k jenv₀ jenv' h
      | succ m => exact Term.evalJ_toJump G s _ k jenv₀ jenv' h
  | _, _, _, _, _, .nat_rec _ n base branch d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _
  | _, _, _, _, _, .int_casesOn i a b, env, k, jenv₀, jenv', h => by
      unfk
      generalize (Atom.eval i env : Int) = m
      cases m with
      | ofNat m => exact Term.evalJ_toJump G a _ k jenv₀ jenv' h
      | negSucc m => exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .uint8_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .uint16_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .uint32_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .uint64_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .int8_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .int16_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .int32_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .int64_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .char_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .stringPosRaw_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .stringPos_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .substringRaw_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .float_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .float32_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .floatModel_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .float32Model_casesOn v b, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, .array_casesOn a z s, env, k, jenv₀, jenv', h => by
      unfk
      generalize Array.toList (α := TyWf.Den _) (Atom.eval a env) = l
      cases l with
      | nil => exact Term.evalJ_toJump G z env k jenv₀ jenv' h
      | cons x xs => exact Term.evalJ_toJump G s _ k jenv₀ jenv' h
  | _, _, _, _, _, .array_rec _ a bases branch d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _
  | _, _, _, _, _, .enum_casesOn e cases, env, k, jenv₀, jenv', h => by
      unfk; exact EnumCases.eval_toJump G cases env k jenv₀ jenv' _ h
  | _, _, _, _, _, .enum_casesOnWithDefault e cases dflt _, env, k, jenv₀, jenv', h => by
      unfk
      exact EnumSomeCases.eval_toJump G cases env k jenv₀ jenv' _ _ _ h
        (Term.evalJ_toJump G dflt env k jenv₀ jenv' h)
  | _, _, _, _, _, .record_casesOn r body, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G body _ k jenv₀ jenv' h
  | _, _, _, _, _, .taggedUnion_casesOn v cases, env, k, jenv₀, jenv', h => by
      unfk; exact TaggedUnionCases.eval_toJump G cases rfl .rfl .rfl env k jenv₀ jenv' _ h
  | _, _, _, _, _, .taggedUnion_casesOnWithDefault v cases dflt _, env, k, jenv₀, jenv', h => by
      unfk
      exact TaggedUnionSomeCases.eval_toJump G cases env k jenv₀ jenv' _ _ _ h
        (Term.evalJ_toJump G dflt env k jenv₀ jenv' h)
  | _, _, _, _, _, .recTaggedUnion_casesOn v cases, env, k, jenv₀, jenv', h => by
      unfk; exact TaggedUnionCases.eval_toJump G cases rfl .rfl .rfl env k jenv₀ jenv' _ h
  | _, _, _, _, _, .recTaggedUnion_casesOnWithDefault v cases dflt _, env, k, jenv₀, jenv', h => by
      unfk
      exact TaggedUnionSomeCases.eval_toJump G cases env k jenv₀ jenv' _ _ _ h
        (Term.evalJ_toJump G dflt env k jenv₀ jenv' h)
  | _, _, _, _, _, .recTaggedUnion_rec _ v cases d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _
  | _, _, _, _, _, .recObject_casesOn v body, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G body _ k jenv₀ jenv' h
  | _, _, _, _, _, .recObject_rec _ v body d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _
  | _, _, _, _, _, .recAlias_casesOn v body, env, k, jenv₀, jenv', h => by
      unfk; exact Term.evalJ_toJump G body _ k jenv₀ jenv' h
  | _, _, _, _, _, .recAlias_rec _ v body d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _
  | _, _, _, _, _, .mutualRecursiveFamily_casesOn v cases, env, k, jenv₀, jenv', h => by
      unfk; exact FamilyMemberCases.eval_toJump G cases env k jenv₀ jenv' _ h
  | _, _, _, _, _, .mutualRecursiveFamily_casesOnWithDefault v cases dflt, env, k, jenv₀,
      jenv', h => by
      unfk
      exact FamilyMemberSomeCases.eval_toJump G cases env k jenv₀ jenv' _ _ _ h
        (Term.evalJ_toJump G dflt env k jenv₀ jenv' h)
  | _, _, _, _, _, .mutualRecursiveFamily_rec _ v cases d, env, k, jenv₀, jenv', h => by
      unfk; exact Dest.apply_toJump h d _

/-- `Term.evalJ_toJump`, on a partial dispatch on a tagged union. -/
theorem TaggedUnionSomeCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {σ τ : TyWf} → {k' lo : Nat} →
    {J₀ J : JCtx} → (cases : TaggedUnionSomeCases Sg Γ l σ k' lo J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (v : TyWf.DenTU l) → (dflt₀ : TyWf.Den σ) → (dflt' : TyWf.Den τ) →
    JRel k jenv₀ jenv' → dflt' = k dflt₀ →
    TaggedUnionSomeCases.eval G (cases.toJump (J := J) (τ := τ)) env jenv' v dflt' =
      k (TaggedUnionSomeCases.eval G cases env jenv₀ v dflt₀)
  | _, _, _, _, _, _, _, _, .last t ht branch _, env, k, jenv₀, jenv', v, dflt₀, dflt', h, hd => by
      unfk
      generalize TyWf.DenTU.field? t ht v = o
      cases o with
      | none => exact hd
      | some f => exact Term.evalJ_toJump G branch _ k jenv₀ jenv' h
  | _, _, _, _, _, _, _, _, .cons t ht branch rest _, env, k, jenv₀, jenv', v, dflt₀, dflt', h,
      hd => by
      unfk
      generalize TyWf.DenTU.field? t ht v = o
      cases o with
      | none => exact TaggedUnionSomeCases.eval_toJump G rest env k jenv₀ jenv' v _ _ h hd
      | some f => exact Term.evalJ_toJump G branch _ k jenv₀ jenv' h

/-- `Term.evalJ_toJump`, on a dispatch on an enum. -/
theorem EnumCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {s : LeanEnumSchema} → {J₀ J : JCtx} →
    (cases : EnumCases Sg Γ σ s J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (i : Fin s.nOfConstructors) → JRel k jenv₀ jenv' →
    EnumCases.eval G (cases.toJump (J := J) (τ := τ)) env jenv' i =
      k (EnumCases.eval G cases env jenv₀ i)
  | _, _, _, _, _, _, .three b0 b1 b2, env, k, jenv₀, jenv', i, h => by
      match i with
      | ⟨0, _⟩ => unfk; exact Term.evalJ_toJump G b0 env k jenv₀ jenv' h
      | ⟨1, _⟩ => unfk; exact Term.evalJ_toJump G b1 env k jenv₀ jenv' h
      | ⟨2, _⟩ => unfk; exact Term.evalJ_toJump G b2 env k jenv₀ jenv' h
      | ⟨_ + 3, hi⟩ => exact absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, _, _, _, .cons b rest, env, k, jenv₀, jenv', i, h => by
      match i with
      | ⟨0, _⟩ => unfk; exact Term.evalJ_toJump G b env k jenv₀ jenv' h
      | ⟨n + 1, hi⟩ => unfk; exact EnumCases.eval_toJump G rest env k jenv₀ jenv' _ h

/-- `Term.evalJ_toJump`, on a partial dispatch on an enum. -/
theorem EnumSomeCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {s : LeanEnumSchema} → {k' lo : Nat} → {J₀ J : JCtx} →
    (cases : EnumSomeCases Sg Γ σ s k' lo J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (i : Fin s.nOfConstructors) → (dflt₀ : TyWf.Den σ) → (dflt' : TyWf.Den τ) →
    JRel k jenv₀ jenv' → dflt' = k dflt₀ →
    EnumSomeCases.eval G (cases.toJump (J := J) (τ := τ)) env jenv' i dflt' =
      k (EnumSomeCases.eval G cases env jenv₀ i dflt₀)
  | _, _, _, _, _, _, _, _, .last j branch _, env, k, jenv₀, jenv', i, dflt₀, dflt', h, hd => by
      show (if i = j then Term.evalJ G branch.toJump env jenv' else dflt') =
        k (if i = j then Term.evalJ G branch env jenv₀ else dflt₀)
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte]; exact Term.evalJ_toJump G branch env k jenv₀ jenv' h
      · simp only [hij, ↓reduceIte]; exact hd
  | _, _, _, _, _, _, _, _, .cons j branch rest _, env, k, jenv₀, jenv', i, dflt₀, dflt', h,
      hd => by
      show (if i = j then Term.evalJ G branch.toJump env jenv'
          else EnumSomeCases.eval G rest.toJump env jenv' i dflt') =
        k (if i = j then Term.evalJ G branch env jenv₀
          else EnumSomeCases.eval G rest env jenv₀ i dflt₀)
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte]; exact Term.evalJ_toJump G branch env k jenv₀ jenv' h
      · simp only [hij, ↓reduceIte]
        exact EnumSomeCases.eval_toJump G rest env k jenv₀ jenv' i _ _ h hd

/-- `Term.evalJ_toJump`, on a dispatch on a tagged union. -/
theorem TaggedUnionCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {l : LeanTaggedUnionSchema ι} →
    {σ τ : TyWf} → {J₀ J : JCtx} → (cases : TaggedUnionFoldCases Sg ι bind Γ l σ J₀) →
    {l' : LeanTaggedUnionSchema TyWf} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : l ≍ l') → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (v : TyWf.DenTU l') → JRel k jenv₀ jenv' →
    TaggedUnionCases.eval G (cases.toJump (J := J) (τ := τ)) h1 h2 h3 env jenv' v =
      k (TaggedUnionCases.eval G cases h1 h2 h3 env jenv₀ v)
  | _, _, _, _, _, _, _, _, .payloadFirst b0 b1 rest, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv',
      v, h => by
      match v with
      | ⟨⟨0, _⟩, f⟩ => unfk; exact Term.evalJ_toJump G b0 _ k jenv₀ jenv' h
      | ⟨⟨1, _⟩, f⟩ => unfk; exact Term.evalJ_toJump G b1 _ k jenv₀ jenv' h
      | ⟨⟨n + 2, _⟩, f⟩ =>
          unfk; exact TaggedUnionCasesRest.eval_toJump G rest rfl .rfl .rfl env k jenv₀ jenv' n f h
  | _, _, _, _, _, _, _, _, .skip b0 rest, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', v, h => by
      match v with
      | ⟨⟨0, _⟩, f⟩ => unfk; exact Term.evalJ_toJump G b0 _ k jenv₀ jenv' h
      | ⟨⟨n + 1, _⟩, f⟩ =>
          unfk
          exact CtorsWithPayloadCases.eval_toJump G rest rfl .rfl .rfl env k jenv₀ jenv' n f h

/-- `TaggedUnionCases.eval_toJump`, on the constructors that follow a field-less one. -/
theorem CtorsWithPayloadCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {c : CtorsWithPayload ι} →
    {σ τ : TyWf} → {J₀ J : JCtx} → (cases : CtorsWithPayloadFoldCases Sg ι bind Γ c σ J₀) →
    {c' : CtorsWithPayload TyWf} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : c ≍ c') → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (t : Nat) → (f : TyWf.DenAtCP c' t) → JRel k jenv₀ jenv' →
    CtorsWithPayloadCases.eval G (cases.toJump (J := J) (τ := τ)) h1 h2 h3 env jenv' t f =
      k (CtorsWithPayloadCases.eval G cases h1 h2 h3 env jenv₀ t f)
  | _, _, _, _, _, _, _, _, .here b _, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', 0, f, h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, _, _, _, .here _ rest, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', n + 1, f,
      h => by
      unfk; exact TaggedUnionCasesRest.eval_toJump G rest rfl .rfl .rfl env k jenv₀ jenv' n f h
  | _, _, _, _, _, _, _, _, .skip b _, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', 0, f, h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, _, _, _, .skip _ rest, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', n + 1, f,
      h => by
      unfk; exact CtorsWithPayloadCases.eval_toJump G rest rfl .rfl .rfl env k jenv₀ jenv' n f h

/-- `TaggedUnionCases.eval_toJump`, on a plain list of constructors. -/
theorem TaggedUnionCasesRest.eval_toJump (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {cs : List (List ι)} →
    {σ τ : TyWf} → {J₀ J : JCtx} → (cases : TaggedUnionFoldCasesRest Sg ι bind Γ cs σ J₀) →
    {cs' : List (List TyWf)} → (h1 : ι = TyWf) →
    (h2 : bind ≍ (id : List TyWf → List TyWf)) → (h3 : cs ≍ cs') → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (t : Nat) → (f : TyWf.DenAtList cs' t) → JRel k jenv₀ jenv' →
    TaggedUnionCasesRest.eval G (cases.toJump (J := J) (τ := τ)) h1 h2 h3 env jenv' t f =
      k (TaggedUnionCasesRest.eval G cases h1 h2 h3 env jenv₀ t f)
  | _, _, _, _, _, _, _, _, .nil, _, rfl, .rfl, .rfl, _, _, _, _, _, f, _ => PEmpty.elim f
  | _, _, _, _, _, _, _, _, .cons b _, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', 0, f, h => by
      unfk; exact Term.evalJ_toJump G b _ k jenv₀ jenv' h
  | _, _, _, _, _, _, _, _, .cons _ rest, _, rfl, .rfl, .rfl, env, k, jenv₀, jenv', n + 1, f,
      h => by
      unfk; exact TaggedUnionCasesRest.eval_toJump G rest rfl .rfl .rfl env k jenv₀ jenv' n f h

/-- `Term.evalJ_toJump`, on a dispatch on a member of a mutual family. -/
theorem FamilyMemberCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J₀ J : JCtx} →
    (cases : FamilyMemberCases Sg Γ σ m J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (v : TyWf.DenMember m) → JRel k jenv₀ jenv' →
    FamilyMemberCases.eval G (cases.toJump (J := J) (τ := τ)) env jenv' v =
      k (FamilyMemberCases.eval G cases env jenv₀ v)
  | _, _, _, _, _, _, .ctors cases, env, k, jenv₀, jenv', v, h =>
      TaggedUnionCases.eval_toJump G cases rfl .rfl .rfl env k jenv₀ jenv' v h
  | _, _, _, _, _, _, .record body, _, k, jenv₀, jenv', _, h =>
      Term.evalJ_toJump G body _ k jenv₀ jenv' h
  | _, _, _, _, _, _, .alias body, _, k, jenv₀, jenv', _, h =>
      Term.evalJ_toJump G body _ k jenv₀ jenv' h

/-- `Term.evalJ_toJump`, on a partial dispatch on a member of a mutual family. -/
theorem FamilyMemberSomeCases.eval_toJump (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J₀ J : JCtx} →
    (cases : FamilyMemberSomeCases Sg Γ σ m J₀) → (env : Env Γ) →
    (k : TyWf.Den σ → TyWf.Den τ) → (jenv₀ : JEnv σ J₀) → (jenv' : JEnv τ (J₀ ++ σ :: J)) →
    (v : TyWf.DenMember m) → (dflt₀ : TyWf.Den σ) → (dflt' : TyWf.Den τ) →
    JRel k jenv₀ jenv' → dflt' = k dflt₀ →
    FamilyMemberSomeCases.eval G (cases.toJump (J := J) (τ := τ)) env jenv' v dflt' =
      k (FamilyMemberSomeCases.eval G cases env jenv₀ v dflt₀)
  | _, _, _, _, _, _, .ctors cases _, env, k, jenv₀, jenv', v, dflt₀, dflt', h, hd =>
      TaggedUnionSomeCases.eval_toJump G cases env k jenv₀ jenv' v dflt₀ dflt' h hd

end

/-- A term with no join point of its own, whose value is sent to a join point `k`, computes
    `k` of its value. -/
theorem Term.evalJ_toJump_nil (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ : TyWf} {J : JCtx}
    (t : Term Sg Γ σ) (env : Env Γ) (k : TyWf.Den σ → TyWf.Den τ) (jenv : JEnv τ J) :
    Term.evalJ G (t.toJump (J₀ := []) (J := J) (τ := τ)) env (k, jenv) = k (Term.eval G t env) :=
  Term.evalJ_toJump G t env k PUnit.unit (k, jenv) (JRel.nil k jenv)

end LeanScript

end
