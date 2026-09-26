module

public import LeanScript.Eval
public import LeanScript.RecUnionRecFacts

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# What the evaluator does with a recursive tagged union

The recursive analogue of the facts at the end of `LeanScript.Eval`.

* **ι-rules for a dispatch.**  Taking apart a value bound to `Comp.recTaggedUnion_mk` is
  taking apart the tagged value of the *unfolded* union with the same constructor and
  fields (`Term.evalJ_recTaggedUnion_casesOn_mk`,
  `Term.evalJ_recTaggedUnion_casesOnWithDefault_mk`).  Both rest on the round trip
  `TyWf.DenRec.unfold_mk` (and `Ty.unroll_roll` / `Ty.roll_unroll` below it, in
  `LeanScript.Den.Rec`).
* **The fold, and its ι-rule.**  `TaggedUnionFoldCases.recFold` is the plain fold of the
  branches of `Term.recTaggedUnion_rec` at depth `0`, written with `WType.fold` — no memo
  — and `TaggedUnionFoldCases.recFold_mk` is its equation: the answer at a node is the
  branch of its constructor, evaluated on its fields and, after each field that is
  literally `Ty.self`, the answer of the fold at that field.
* **Depth does not change meaning.**  The evaluator folds by `WType.memo`, remembering
  every answer; `Term.eval_recTaggedUnion_rec_toFoldK` says that at **every** depth `k`,
  branches that answer where they stand (`TaggedUnionFoldCases.toFoldK`) give exactly
  that plain fold.
-/

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## ι-rules for a dispatch -/

/-- Dispatching on a value bound to the introduction form of a recursive tagged union is
    dispatching on the tagged value of its unfolded constructors. -/
theorem Term.evalJ_recTaggedUnion_casesOn_mk {Γ : Ctx} {τ : TyWf} {J : JCtx}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Args Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht))
    (cases : TaggedUnionCases Sg (.recTaggedUnion l hwf :: Γ) (TyWf.recTaggedUnionUnfold l hwf) τ J)
    (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letE (.recTaggedUnion_mk l hwf t ht fields)
        (.recTaggedUnion_casesOn (.var .head) cases)) env jenv =
      TaggedUnionCases.eval G cases rfl .rfl .rfl
        (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env, env) jenv
        (TyWf.DenTU.mk t ht (Args.eval G fields env)) := by
  show TaggedUnionCases.eval G cases rfl .rfl .rfl _ jenv
      (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)) = _
  rw [TyWf.DenRec.unfold_mk]

/-- The same, for a dispatch on some of the constructors with a default. -/
theorem Term.evalJ_recTaggedUnion_casesOnWithDefault_mk {Γ : Ctx} {τ : TyWf} {J : JCtx}
    {k : Nat}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Args Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht))
    (cases : TaggedUnionSomeCases Sg (.recTaggedUnion l hwf :: Γ)
      (TyWf.recTaggedUnionUnfold l hwf) τ k 0 J)
    (dflt : Term Sg (.recTaggedUnion l hwf :: Γ) τ J)
    (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length) (env : Env Γ) (jenv : JEnv τ J) :
    Term.evalJ G (.letE (.recTaggedUnion_mk l hwf t ht fields)
        (.recTaggedUnion_casesOnWithDefault (.var .head) cases dflt hk)) env jenv =
      let env' := (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env, env)
      TaggedUnionSomeCases.eval G cases env' jenv
        (TyWf.DenTU.mk t ht (Args.eval G fields env)) (Term.evalJ G dflt env' jenv) := by
  show TaggedUnionSomeCases.eval G cases _ jenv
      (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)) _ = _
  rw [TyWf.DenRec.unfold_mk]

/-- The tag of a value built by the introduction form is the constructor it was built
    with. -/
theorem Comp.eval_recTaggedUnion_mk_tag {Γ : Ctx}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Args Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) (env : Env Γ) :
    (TyWf.DenRec.unfold l hwf (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env)).1.val
      = t := by
  show (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)).1.val = t
  rw [TyWf.DenRec.unfold_mk]
  rfl

/-- The fields of a value built by the introduction form are the ones it was built with. -/
theorem Comp.eval_recTaggedUnion_field? {Γ : Ctx}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Args Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) (env : Env Γ) :
    TyWf.DenTU.field? t ht
        (TyWf.DenRec.unfold l hwf (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env)) =
      some (Args.eval G fields env) := by
  show TyWf.DenTU.field? t ht (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)) = _
  rw [TyWf.DenRec.unfold_mk, TyWf.DenTU.field?_mk]

/-! ## The plain fold

The environment of a branch, read off a node whose holes hold each subtree **with** the
answer of the fold at it. -/

/-- The environment a branch of the fold binds, at a constructor with fields `fs`, from
    the fields' shape with a subtree and its answer in each hole. -/
def recBindEnvOf (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l))
    (τ : TyWf) :
    (fs : List (TyWfIn 1)) →
      (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj
        (TyWf.Den (TyWf.recTaggedUnion l hwf) × TyWf.Den τ) →
      TyWf.DenList (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ fs)
  | [], _ => PUnit.unit
  | ⟨.self, _⟩ :: fs, e =>
      let p := e.prodFst.2 PUnit.unit
      (p.1, p.2, recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.familyMember _, h⟩ :: _, _ => absurd h Ty.not_wfIn_one_familyMember
  | ⟨.shape sh, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.shape sh) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recTaggedUnion l', _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recTaggedUnion l')
          ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recObject r, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recObject r) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recAlias b, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recAlias b) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.mutualRecursiveFamily f, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.mutualRecursiveFamily f)
          ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)

/-- The environment read off memos is the environment read off each memo's tree and
    answer. -/
theorem recBindEnv_eq_recBindEnvOf (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (τ : TyWf) :
    ∀ (fs : List (TyWfIn 1)) (e : RecFields l τ fs),
      recBindEnv l hwf τ fs e =
        recBindEnvOf l hwf τ fs ⟨e.1, fun p => ((e.2 p).tree, (e.2 p).answer)⟩
  | [], _ => rfl
  | ⟨.self, _⟩ :: fs, e => by
      show (_, _, recBindEnv l hwf τ fs e.prodSnd) = (_, _, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.familyMember _, h⟩ :: _, _ => absurd h Ty.not_wfIn_one_familyMember
  | ⟨.shape _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recTaggedUnion _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recObject _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recAlias _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.mutualRecursiveFamily _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl

/-! ### The branches of the plain fold, at a node -/

mutual

/-- The answer of the branches of a plain fold at a node of constructor `t`, whose fields
    are `e` — their shape, with some `Y` in each hole that `mkEnv` turns into the
    environment of the branch.  The hypothesis is the evaluator's, for the same branches
    read at any depth. -/
def TaggedUnionFoldCases.evalAt {Y : Type} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {l : LeanTaggedUnionSchema (TyWfIn 1)} →
    {τ : TyWf} → (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAt (recL l) t).Obj Y →
    TyWf.Den τ
  | _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, 0, e =>
      Term.eval G b0 (Env.append (mkEnv _ e) env)
  | _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, 1, e =>
      Term.eval G b1 (Env.append (mkEnv _ e) env)
  | _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, n + 2, e =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e
  | _, _, _, _, .skip b0 _, env, mkEnv, 0, e =>
      Term.eval G b0 (Env.append (mkEnv _ e) env)
  | _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e =>
      CtorsWithPayloadFoldCases.evalAt rest env mkEnv n e

/-- `TaggedUnionFoldCases.evalAt`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadFoldCases.evalAt {Y : Type} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {c : CtorsWithPayload (TyWfIn 1)} →
    {τ : TyWf} → (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ c τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj Y →
    TyWf.Den τ
  | _, _, _, _, .here b _, env, mkEnv, 0, e =>
      Term.eval G b (Env.append (mkEnv _ e) env)
  | _, _, _, _, .here _ rest, env, mkEnv, n + 1, e =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e
  | _, _, _, _, .skip b _, env, mkEnv, 0, e =>
      Term.eval G b (Env.append (mkEnv _ e) env)
  | _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e =>
      CtorsWithPayloadFoldCases.evalAt rest env mkEnv n e

/-- `TaggedUnionFoldCases.evalAt`, on a plain list of constructors. -/
def TaggedUnionFoldCasesRest.evalAt {Y : Type} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {cs : List (List (TyWfIn 1))} →
    {τ : TyWf} → (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ cs τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj Y →
    TyWf.Den τ
  | _, _, _, _, .nil, _, _, _, e => PEmpty.elim e.1
  | _, _, _, _, .cons b _, env, mkEnv, 0, e =>
      Term.eval G b (Env.append (mkEnv _ e) env)
  | _, _, _, _, .cons _ rest, env, mkEnv, n + 1, e =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e

end

/-- **The plain fold** of a value of `recTaggedUnion l`, for branches that answer where
    they stand: the answer at a node is its constructor's branch, evaluated on its fields
    and the answers of the fold at its occurrences.  Written with `WType.fold`, so no
    answer is stored. -/
def TaggedUnionFoldCases.recFold {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ l τ)
    (env : Env Γ) :
    TyWf.Den (TyWf.recTaggedUnion l hwf) → TyWf.Den τ :=
  WType.fold fun node kids ih =>
    TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ) node.1.val
      ⟨node.2, fun p => (kids p, ih p)⟩

/-- **The ι-rule of the fold**: the answer at a node is the branch of its constructor,
    evaluated on its fields and, after each field that is literally `Ty.self`, the subtree
    there together with the answer of the fold at it. -/
theorem TaggedUnionFoldCases.recFold_mk {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ l τ)
    (env : Env Γ)
    (node : Ty.RecNode (recL l)) (f : Ty.RecHole (recL l) node → TyWf.Den (TyWf.recTaggedUnion l hwf)) :
    TaggedUnionFoldCases.recFold G c env (WType.mk node f) =
      TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ) node.1.val
        ⟨node.2, fun p => (f p, TaggedUnionFoldCases.recFold G c env (f p))⟩ :=
  rfl

/-! ### The evaluator's fold, for branches that answer where they stand -/

section
variable {τ : TyWf} {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}

mutual

/-- The evaluator's answer at a node, for branches that answer where they stand, is the
    answer of those branches read as a plain fold. -/
theorem TaggedUnionFoldKCases.eval_toFoldK {k : Nat} {outer : List (List (TyWfIn 1))}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {l : LeanTaggedUnionSchema (TyWfIn 1)} :
    ∀ (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (fr : RecFrames l₀ τ outer)
      (t : Nat) (e : (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ)),
      TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK (k := k) c) env mkEnv fr
          t e =
        TaggedUnionFoldCases.evalAt G c env mkEnv t e
  | .payloadFirst _ _ _, _, _, _, 0, _ => rfl
  | .payloadFirst _ _ _, _, _, _, 1, _ => rfl
  | .payloadFirst _ _ rest, env, mkEnv, fr, n + 2, e =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv fr n e
  | .skip _ _, _, _, _, 0, _ => rfl
  | .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval_toFoldK rest env mkEnv fr n e

theorem CtorsWithPayloadFoldKCases.eval_toFoldK {k : Nat} {outer : List (List (TyWfIn 1))}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {c : CtorsWithPayload (TyWfIn 1)} :
    ∀ (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ c τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (fr : RecFrames l₀ τ outer)
      (t : Nat) (e : (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ)),
      CtorsWithPayloadFoldKCases.eval G (CtorsWithPayloadFoldCases.toFoldK (k := k) cs) env
          mkEnv fr t e =
        CtorsWithPayloadFoldCases.evalAt G cs env mkEnv t e
  | .here _ _, _, _, _, 0, _ => rfl
  | .here _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv fr n e
  | .skip _ _, _, _, _, 0, _ => rfl
  | .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval_toFoldK rest env mkEnv fr n e

theorem TaggedUnionFoldKCasesRest.eval_toFoldK {k : Nat} {outer : List (List (TyWfIn 1))}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {cs : List (List (TyWfIn 1))} :
    ∀ (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ cs τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (fr : RecFrames l₀ τ outer)
      (t : Nat) (e : (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ)),
      TaggedUnionFoldKCasesRest.eval G (TaggedUnionFoldCasesRest.toFoldK (k := k) r) env
          mkEnv fr t e =
        TaggedUnionFoldCasesRest.evalAt G r env mkEnv t e
  | .nil, _, _, _, _, e => PEmpty.elim e.1
  | .cons _ _, _, _, _, 0, _ => rfl
  | .cons _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv fr n e

end

end

section
variable {τ : TyWf} {Y Y' : Type} (g : Y → Y')

mutual

/-- The answer of a plain fold at a node depends on the contents of its holes only
    through the environments they give. -/
theorem TaggedUnionFoldCases.evalAt_map {bind : List (TyWfIn 1) → List TyWf}
    {Γ : Ctx} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAt (recL l) t).Obj Y),
      TaggedUnionFoldCases.evalAt G c env mkEnv t e =
        TaggedUnionFoldCases.evalAt G c env mkEnv' t (PFunctor.map _ g e)
  | .payloadFirst b0 _ _, env, 0, e => by
      exact congrArg (fun x => Term.eval G b0 (Env.append x env)) (hm _ _)
  | .payloadFirst _ b1 _, env, 1, e => by
      exact congrArg (fun x => Term.eval G b1 (Env.append x env)) (hm _ _)
  | .payloadFirst _ _ rest, env, n + 2, e =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e
  | .skip b0 _, env, 0, e => by
      exact congrArg (fun x => Term.eval G b0 (Env.append x env)) (hm _ _)
  | .skip _ rest, env, n + 1, e =>
      CtorsWithPayloadFoldCases.evalAt_map mkEnv mkEnv' hm rest env n e

theorem CtorsWithPayloadFoldCases.evalAt_map
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {c : CtorsWithPayload (TyWfIn 1)}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ c τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj Y),
      CtorsWithPayloadFoldCases.evalAt G cs env mkEnv t e =
        CtorsWithPayloadFoldCases.evalAt G cs env mkEnv' t (PFunctor.map _ g e)
  | .here b _, env, 0, e => by
      exact congrArg (fun x => Term.eval G b (Env.append x env)) (hm _ _)
  | .here _ rest, env, n + 1, e =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e
  | .skip b _, env, 0, e => by
      exact congrArg (fun x => Term.eval G b (Env.append x env)) (hm _ _)
  | .skip _ rest, env, n + 1, e =>
      CtorsWithPayloadFoldCases.evalAt_map mkEnv mkEnv' hm rest env n e

theorem TaggedUnionFoldCasesRest.evalAt_map
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {cs : List (List (TyWfIn 1))}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ cs τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj Y),
      TaggedUnionFoldCasesRest.evalAt G r env mkEnv t e =
        TaggedUnionFoldCasesRest.evalAt G r env mkEnv' t (PFunctor.map _ g e)
  | .nil, _, _, e => PEmpty.elim e.1
  | .cons b _, env, 0, e => by
      exact congrArg (fun x => Term.eval G b (Env.append x env)) (hm _ _)
  | .cons _ rest, env, n + 1, e =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e

end

end

/-- The step of the evaluator's memoised fold, for branches that answer where they
    stand. -/
abbrev TaggedUnionFoldCases.memoStep {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {k : Nat}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ l τ)
    (env : Env Γ) :
    (node : Ty.RecNode (recL l)) → (Ty.RecHole (recL l) node → RecMemo l τ) → TyWf.Den τ :=
  fun node kids =>
    TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK (k := k) (outer := []) c) env (recBindEnv l hwf τ)
      RecFrames.nil node.1.val ⟨node.2, kids⟩

/-- **The evaluator's memoised fold is the plain fold**, at every depth, for branches that
    answer where they stand. -/
theorem Term.eval_recTaggedUnion_rec_toFoldK {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat)
    (v : Atom Γ (.recTaggedUnion l hwf))
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ l τ)
    (env : Env Γ) :
    Term.eval G (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) .ret) env =
      TaggedUnionFoldCases.recFold G c env (Atom.eval v env) := by
  show (WType.memo _ (Atom.eval v env)).answer = _
  generalize Atom.eval v env = w
  induction w with
  | mk node f ih =>
      show TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK (outer := []) c) env
          (recBindEnv l hwf τ) RecFrames.nil node.1.val ⟨node.2, fun p => WType.memo _ (f p)⟩ = _
      rw [TaggedUnionFoldKCases.eval_toFoldK,
        TaggedUnionFoldCases.evalAt_map G (fun m => (WType.Memo.tree m, WType.Memo.answer m))
          (recBindEnv l hwf τ) (recBindEnvOf l hwf τ)
          (fun fs e => recBindEnv_eq_recBindEnvOf l hwf τ fs e) c env _ _]
      refine Eq.trans ?_ (TaggedUnionFoldCases.recFold_mk G c env node f).symm
      have hk : (fun p => ((WType.memo (TaggedUnionFoldCases.memoStep G (k := k) c env) (f p)).tree,
            (WType.memo (TaggedUnionFoldCases.memoStep G (k := k) c env) (f p)).answer)) =
          fun p => (f p, TaggedUnionFoldCases.recFold G c env (f p)) :=
        funext fun p => by rw [WType.memo_tree, ih p]
      exact congrArg (fun x => TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ)
        node.1.val ⟨node.2, x⟩) hk

/-- **Depth does not change meaning**: branches that answer where they stand give the same
    value at every depth. -/
theorem Term.eval_recTaggedUnion_rec_depth {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k k' : Nat)
    (v : Atom Γ (.recTaggedUnion l hwf))
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ l τ)
    (env : Env Γ) :
    Term.eval G (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) .ret) env =
      Term.eval G (.recTaggedUnion_rec k' v (TaggedUnionFoldCases.toFoldK c) .ret) env := by
  rw [Term.eval_recTaggedUnion_rec_toFoldK, Term.eval_recTaggedUnion_rec_toFoldK]

end LeanScript

end
