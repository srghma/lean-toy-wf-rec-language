module

public import LeanScript.BuildEvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# Every builder computes what its direct-style constructor means

One theorem per function of `LeanScript.Expr.Build` that takes operands: the value of the
A-normal term it builds is the value the direct-style form it is named after has — the
operands evaluated, and the step, dispatch or fold applied to their values.  They hold for
**all** terms and environments, so a translated term, however its operands are nested,
computes what it says.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## Redexes the builders take apart -/

/-- The value of an abstraction, read off its body by `Comp.lamBody?`. -/
theorem Comp.eval_of_lamBody? {Γ : Ctx} {σ τ : TyWf} {body : Term Sg (σ :: Γ) τ}
    (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → (e : ρ = TyWf.fn σ τ) → c.lamBody? e = some body →
    (e ▸ Comp.eval G c env : TyWf.Den (TyWf.fn σ τ)) = fun x => Term.eval G body (x, env)
  | _, .lam body', e, h => by
      obtain ⟨rfl, rfl⟩ := TyWf.fn_inj e
      cases h
      rfl
  | _, .global _, _, h | _, .bool_mk _, _, h | _, .nat_mk _, _, h | _, .int_mk _, _, h
  | _, .bitvec_mk _ _, _, h | _, .uint8_mk _, _, h | _, .uint16_mk _, _, h
  | _, .uint32_mk _, _, h | _, .uint64_mk _, _, h | _, .int8_mk _, _, h
  | _, .int16_mk _, _, h | _, .int32_mk _, _, h | _, .int64_mk _, _, h
  | _, .char_mk _, _, h | _, .string_mk _, _, h | _, .stringPos_mk _ _, _, h
  | _, .stringPosRaw_mk _, _, h | _, .substringRaw_mk _, _, h | _, .stringSlice_mk _, _, h
  | _, .float_mk _, _, h | _, .float32_mk _, _, h | _, .floatModel_mk _, _, h
  | _, .float32Model_mk _, _, h | _, .ap _ _, _, h | _, .extern _, _, h
  | _, .externCall _ _, _, h | _, .lazy_mk _, _, h | _, .lazy_force _, _, h
  | _, .thunk_mk _, _, h | _, .thunk_force _, _, h | _, .array_mk _, _, h
  | _, .enum_mk _ _, _, h | _, .record_mk _ _, _, h | _, .taggedUnion_mk _ _ _ _, _, h
  | _, .recTaggedUnion_mk _ _ _ _ _, _, h | _, .recObject_mk _ _ _, _, h
  | _, .recAlias_mk _ _ _, _, h | _, .mutualRecursiveFamily_mk _ _ _, _, h => by cases h

/-- A term that `Term.lamBody?` reads as an abstraction is the function its body
    computes. -/
theorem Term.eval_of_lamBody? {Γ : Ctx} {σ τ : TyWf} {f : Term Sg Γ (TyWf.fn σ τ)}
    {body : Term Sg (σ :: Γ) τ} (h : f.lamBody? = some body) (env : Env Γ) :
    Term.eval G f env = fun x => Term.eval G body (x, env) := by
  unfold Term.lamBody? at h
  split at h
  · exact Comp.eval_of_lamBody? G env _ rfl h
  · cases h

/-- The value of a step that `Comp.boolLit?` reads as a literal. -/
theorem Comp.eval_of_boolLit? {Γ : Ctx} {b : Bool} (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → c.boolLit? = some b → Comp.eval G c env ≍ b := by
  intro ρ c h
  cases c <;> cases h
  exact .rfl

/-- A term that `Term.boolLit?` reads as a literal has that value. -/
theorem Term.eval_of_boolLit? {Γ : Ctx} {t : Term Sg Γ (.prim .bool)} {b : Bool}
    (h : t.boolLit? = some b) (env : Env Γ) : (Term.eval G t env : Bool) = b := by
  unfold Term.boolLit? at h
  split at h
  · exact eq_of_heq (Comp.eval_of_boolLit? G env _ h)
  · cases h

/-- The value of a step that `Comp.natLit?` reads as a literal. -/
theorem Comp.eval_of_natLit? {Γ : Ctx} {n : Nat} (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → c.natLit? = some n → Comp.eval G c env ≍ n := by
  intro ρ c h
  cases c <;> cases h
  exact .rfl

/-- A term that `Term.natLit?` reads as a literal has that value. -/
theorem Term.eval_of_natLit? {Γ : Ctx} {t : Term Sg Γ (.prim .nat)} {n : Nat}
    (h : t.natLit? = some n) (env : Env Γ) : (Term.eval G t env : Nat) = n := by
  unfold Term.natLit? at h
  split at h
  · exact eq_of_heq (Comp.eval_of_natLit? G env _ h)
  · cases h

/-! ## Applications and extern calls -/

/-- **`f a` is Lean's application of the value of `f` to the value of `a`.**  This covers
    the three ways `Term.ap` builds it: a β-reduction when `f` is an abstraction, a closed
    `f` bound after `a`, and both operands named in order. -/
theorem Term.eval_ap {Γ : Ctx} {σ τ : TyWf} (f : Term Sg Γ (TyWf.fn σ τ)) (a : Term Sg Γ σ)
    (env : Env Γ) : Term.eval G (Term.ap f a) env = Term.eval G f env (Term.eval G a env) := by
  unfold Term.ap
  cases hl : f.lamBody? with
  | some body =>
      simp only
      rw [Term.eval_of_lamBody? G hl env]
      exact Term.evalJ_bind G a body env (J := []) PUnit.unit
  | none =>
      simp only
      cases hc : f.closedStep? with
      | some c =>
          simp only
          rw [Term.eval_of_closedStep? G hc env]
          refine Term.evalJ_bindAtom G a _ env (J := []) PUnit.unit (Comp.eval G c Env.nil) ?_
          intro Δ ρ env' aa h
          show Term.eval G (.letE _ _) env' = _
          rw [Term.eval_letE]
          show Comp.eval G (c.rename Ren.nil) env' (Atom.eval (aa.rename Ren.wk) _) = _
          rw [Comp.eval_rename_nil, Atom.eval_rename (EnvRel.wk _ env')]
      | none =>
          simp only
          refine Term.evalJ_bindAtomOr G f _ _ env (J := []) PUnit.unit (fun v => v (Term.eval G a env))
            ?_ ?_
          · intro fa
            exact Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit (Atom.eval fa env)
              (fun _ => rfl) fun ρ' env' aa h' => by
                show Atom.eval (fa.rename ρ') env' (Atom.eval aa env') = _
                rw [Atom.eval_rename h']
          · intro Δ ρ env' fa h
            refine (Term.evalJ_bindAtom G (a.rename ρ) _ env' (J := []) PUnit.unit
              (Atom.eval fa env') ?_).trans ?_
            · intro Θ ρ' env'' aa h'
              show Atom.eval (fa.rename ρ') env'' (Atom.eval aa env'') = _
              rw [Atom.eval_rename h']
            · show Atom.eval fa env' (Term.eval G (a.rename ρ) env') = _
              rw [Term.eval_rename G ρ a h]

/-- An abstraction is the Lean function its body computes. -/
theorem Term.eval_lam {Γ : Ctx} {σ τ : TyWf} (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.lam body) env = fun x => Term.eval G body (x, env) :=
  rfl

/-- An extern applied to terms is the Lean function applied to their values. -/
theorem Term.eval_externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) (env : Env Γ) :
    Term.eval G (Term.externCall args call) env = Extern.eval (call (Spine.eval G args env)) :=
  Spine.eval_bindArgs G args Ren.id env env (EnvRel.id' env) _
    (fun vs => Extern.eval (call vs)) fun _ _ _ _ => rfl

/-- An extern that takes a proof, applied to terms: the Lean function where the decided
    proposition holds, and the fallback where it does not. -/
theorem Term.eval_externCallChecked' {Γ : Ctx} {σs : List TyWf} {τ : TyWf}
    (args : Spine Sg Γ σs) (call : TyWf.DenList σs → Option (Extern τ))
    (fallback : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.externCallChecked' args call fallback) env =
      match call (Spine.eval G args env) with
      | some e => Extern.eval e
      | none => Term.eval G fallback env := by
  refine Spine.eval_bindArgs G args Ren.id env env (EnvRel.id' env) _
    (fun vs => match call vs with
      | some e => Extern.eval e
      | none => Term.eval G fallback env) ?_
  intro Δ ρ env' as h
  show (match call (Args.eval G as env') with
    | some e => Dest.apply Dest.ret (J := []) PUnit.unit (Extern.eval e)
    | none => Term.eval G (fallback.rename ρ) env') = _
  rw [Term.eval_rename G ρ fallback h]
  dsimp only
  cases call (Args.eval G as env') <;> rfl

/-! ## Dispatches on the primitive types -/

/-- **`if c then t else e`** takes the branch the value of `c` selects.  This covers the
    literal case, which `Term.bool_casesOn'` reduces while building. -/
theorem Term.eval_bool_casesOn' {Γ : Ctx} {τ : TyWf} (c : Term Sg Γ (.prim .bool))
    (t e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.bool_casesOn' c t e) env =
      bif (Term.eval G c env : Bool) then Term.eval G t env else Term.eval G e env := by
  unfold Term.bool_casesOn'
  cases hb : c.boolLit? with
  | some b =>
      rw [Term.eval_of_boolLit? G hb env]
      cases b <;> rfl
  | none =>
      simp only
      refine Term.evalJ_bindAtomOr G c _ _ env (J := []) PUnit.unit
        (fun v => bif (v : Bool) then Term.eval G t env else Term.eval G e env) ?_ ?_
      · intro a
        show (match (Atom.eval a env : Bool) with
          | true => Term.eval G t env | false => Term.eval G e env) = _
        cases (Atom.eval a env : Bool) <;> rfl
      · intro Δ ρ env' a h
        show (match (Atom.eval a env' : Bool) with
          | true => Term.eval G (t.rename ρ) env' | false => Term.eval G (e.rename ρ) env') = _
        rw [Term.eval_rename G ρ t h, Term.eval_rename G ρ e h]
        cases (Atom.eval a env' : Bool) <;> rfl

/-- **`match n with | 0 => z | k + 1 => s`** takes the branch the value of `n` selects,
    binding the predecessor in the successor branch.  This covers the literal case, which
    `Term.nat_casesOn'` reduces while building. -/
theorem Term.eval_nat_casesOn' {Γ : Ctx} {τ : TyWf} (n : Term Sg Γ (.prim .nat))
    (z : Term Sg Γ τ) (s : Term Sg (TyWf.prim .nat :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.nat_casesOn' n z s) env =
      Nat.casesOn (motive := fun _ => TyWf.Den τ) (Term.eval G n env : Nat) (Term.eval G z env)
        fun k => Term.eval G s (k, env) := by
  unfold Term.nat_casesOn'
  cases hn : n.natLit? with
  | some m =>
      rw [Term.eval_of_natLit? G hn env]
      cases m with
      | zero => rfl
      | succ m => exact Term.eval_letE G (.nat_mk m) s env
  | none =>
      simp only
      refine Term.evalJ_bindAtomOr G n _ _ env (J := []) PUnit.unit
        (fun v => Nat.casesOn (motive := fun _ => TyWf.Den τ) (v : Nat) (Term.eval G z env)
          fun k => Term.eval G s (k, env)) ?_ ?_
      · intro a
        show (match (Atom.eval a env : Nat) with
          | 0 => Term.eval G z env | k + 1 => Term.eval G s (k, env)) = _
        cases (Atom.eval a env : Nat) <;> rfl
      · intro Δ ρ env' a h
        show (match (Atom.eval a env' : Nat) with
          | 0 => Term.eval G (z.rename ρ) env'
          | k + 1 => Term.eval G (s.rename (Ren.lift ρ)) (k, env')) = _
        rw [Term.eval_rename G ρ z h]
        cases (Atom.eval a env' : Nat) with
        | zero => rfl
        | succ k => exact Term.eval_rename G _ s (EnvRel.lift (σ := TyWf.prim .nat) h k)

/-- Take an 8-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint8))
    (b : Term Sg ((TyWf.prim (.bitvec 8)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint8_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt8).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt8).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 16-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint16))
    (b : Term Sg ((TyWf.prim (.bitvec 16)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint16_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt16).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt16).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint32))
    (b : Term Sg ((TyWf.prim (.bitvec 32)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt32).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt32).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint64))
    (b : Term Sg ((TyWf.prim (.bitvec 64)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint64_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt64).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt64).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an 8-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int8))
    (b : Term Sg ((TyWf.prim .uint8) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int8_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int8).toUInt8, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int8).toUInt8, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 16-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int16))
    (b : Term Sg ((TyWf.prim .uint16) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int16_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int16).toUInt16, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int16).toUInt16, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int32))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int32).toUInt32, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int32).toUInt32, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int64))
    (b : Term Sg ((TyWf.prim .uint64) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int64_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int64).toUInt64, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int64).toUInt64, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a character apart: the branch binds its code point. -/
theorem Term.eval_char_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .char))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.char_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Char).val, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Char).val, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an unchecked position apart: the branch binds its byte index. -/
theorem Term.eval_stringPosRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .stringPosRaw))
    (b : Term Sg ((TyWf.prim .nat) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.stringPosRaw_casesOn' v b) env = Term.eval G b ((Term.eval G v env : String.Pos.Raw).byteIdx, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : String.Pos.Raw).byteIdx, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit float apart: the branch binds its model. -/
theorem Term.eval_float_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float))
    (b : Term Sg ((TyWf.prim .floatModel) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float).toModel, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float).toModel, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit float apart: the branch binds its model. -/
theorem Term.eval_float32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32))
    (b : Term Sg ((TyWf.prim .float32Model) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float32).toModel, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float32).toModel, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take the model of a 64-bit float apart: the branch binds its bits. -/
theorem Term.eval_floatModel_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .floatModel))
    (b : Term Sg ((TyWf.prim .uint64) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.floatModel_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float.Model).toBits, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float.Model).toBits, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take the model of a 32-bit float apart: the branch binds its bits. -/
theorem Term.eval_float32Model_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32Model))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float32Model_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float32.Model).toBits, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float32.Model).toBits, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- `match i with | .ofNat n => … | .negSucc n => …` takes the branch the value of `i`
    selects. -/
theorem Term.eval_int_casesOn' {Γ : Ctx} {τ : TyWf} (i : Term Sg Γ (.prim .int))
    (ofNat negSucc : Term Sg (TyWf.prim .nat :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int_casesOn' i ofNat negSucc) env =
      Int.casesOn (motive := fun _ => TyWf.Den τ) (Term.eval G i env : Int)
        (fun k => Term.eval G ofNat (k, env)) (fun k => Term.eval G negSucc (k, env)) := by
  refine Term.evalJ_bindAtomOr G i _ _ env (J := []) PUnit.unit
    (fun v => Int.casesOn (motive := fun _ => TyWf.Den τ) (v : Int)
      (fun k => Term.eval G ofNat (k, env)) (fun k => Term.eval G negSucc (k, env))) ?_ ?_
  · intro a
    show (match (Atom.eval a env : Int) with
      | .ofNat k => Term.eval G ofNat (k, env) | .negSucc k => Term.eval G negSucc (k, env)) = _
    cases (Atom.eval a env : Int) <;> rfl
  · intro Δ ρ env' a h
    show (match (Atom.eval a env' : Int) with
      | .ofNat k => Term.eval G (ofNat.rename (Ren.lift ρ)) (k, env')
      | .negSucc k => Term.eval G (negSucc.rename (Ren.lift ρ)) (k, env')) = _
    cases (Atom.eval a env' : Int) with
    | ofNat k => exact Term.eval_rename G _ ofNat (EnvRel.lift (σ := TyWf.prim .nat) h k)
    | negSucc k => exact Term.eval_rename G _ negSucc (EnvRel.lift (σ := TyWf.prim .nat) h k)

/-- Take a checked position apart: the branch binds the unchecked position. -/
theorem Term.eval_stringPos_casesOn' {Γ : Ctx} {τ : TyWf} {str : String}
    (v : Term Sg Γ (.prim (.stringPos str))) (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) τ)
    (env : Env Γ) :
    Term.eval G (Term.stringPos_casesOn' v b) env =
      Term.eval G b ((Term.eval G v env : String.Pos str).offset, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G b ((x : String.Pos str).offset, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an unchecked substring apart: the branch binds its string and its two ends. -/
theorem Term.eval_substringRaw_casesOn' {Γ : Ctx} {τ : TyWf}
    (v : Term Sg Γ (.prim .substringRaw))
    (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ)
    (env : Env Γ) :
    Term.eval G (Term.substringRaw_casesOn' v b) env =
      let x : Substring.Raw := Term.eval G v env
      Term.eval G b (x.str, x.startPos, x.stopPos, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G b ((x : Substring.Raw).str, (x : Substring.Raw).startPos,
      (x : Substring.Raw).stopPos, env))
    (fun _ => rfl) fun _ _ _ h =>
      Term.eval_rename G _ b (EnvRel.lift (EnvRel.lift (EnvRel.lift h _) _) _)

/-- A spine that `Spine.atoms?` reads as atoms has the values of those atoms. -/
theorem Spine.eval_of_atoms? {Γ : Ctx} (env : Env Γ) :
    {σs : List TyWf} → (sp : Spine Sg Γ σs) → (bs : Args Sg Γ σs) → sp.atoms? = some bs →
    Args.eval G bs env = Spine.eval G sp env
  | _, .nil, bs, h => by
      cases h
      rfl
  | _, .cons t ts, bs, h => by
      cases t with
      | ret a =>
          simp only [Spine.atoms?] at h
          cases hts : ts.atoms? with
          | none => rw [hts] at h; cases h
          | some bs' =>
              rw [hts] at h
              cases h
              show (Atom.eval a env, Args.eval G bs' env) = (Atom.eval a env, Spine.eval G ts env)
              rw [Spine.eval_of_atoms? env ts bs' hts]
      | _ => simp [Spine.atoms?] at h

/-- **The fold of a natural number** (`Nat.rec` descending `k + 1` steps) is `natFoldK` of
    the values of its bases, at the value of its argument. -/
theorem Term.eval_nat_rec' {Γ : Ctx} {τ : TyWf} (k : Nat) (n : Term Sg Γ (.prim .nat))
    (base : Spine Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ) (env : Env Γ) :
    Term.eval G (Term.nat_rec' k n base branch) env =
      natFoldK (Spine.eval G base env)
        (fun m w => Term.eval G branch (m, Env.ofWin w env)) (Term.eval G n env : Nat) := by
  refine Term.evalJ_bindAtomOr G n _ _ env (J := []) PUnit.unit
    (fun v => natFoldK (Spine.eval G base env)
      (fun m w => Term.eval G branch (m, Env.ofWin w env)) (v : Nat)) ?_ ?_
  · intro a
    show Term.evalJ (J := []) G (match base.atoms? with
      | some bs => .nat_rec k a bs branch .ret
      | none => _) env PUnit.unit = _
    split
    next bs hb =>
        show natFoldK (Args.eval G bs env) _ _ = _
        rw [Spine.eval_of_atoms? G env base bs hb]
    next hb =>
        refine Spine.eval_bindArgs G base Ren.id env env (EnvRel.id' env) _
          (fun vs => natFoldK vs (fun m w => Term.eval G branch (m, Env.ofWin w env))
            (Atom.eval a env)) ?_
        intro Δ ρ' env' bs h'
        show natFoldK (Args.eval G bs env')
          (fun m w => Term.eval G (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) ρ')))
            (m, Env.ofWin w env'))
          (Atom.eval (a.rename ρ') env') = _
        rw [Atom.eval_rename h']
        congr 1
        funext m w
        exact Term.eval_rename G _ branch (EnvRel.lift (σ := TyWf.prim .nat) (EnvRel.liftNat h' _ _ w) m)
  · intro Δ ρ env' a h
    dsimp only
    refine Spine.eval_bindArgs G base ρ env env' h _
      (fun vs => natFoldK vs (fun m w => Term.eval G branch (m, Env.ofWin w env))
        (Atom.eval a env')) ?_
    intro Θ ρ' env'' bs h'
    show natFoldK (Args.eval G bs env'')
      (fun m w => Term.eval G (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) (Ren.comp ρ' ρ))))
        (m, Env.ofWin w env''))
      (Atom.eval (a.rename ρ') env'') = _
    rw [Atom.eval_rename h']
    congr 1
    funext m w
    exact Term.eval_rename G _ branch
      (EnvRel.lift (σ := TyWf.prim .nat) (EnvRel.liftNat (EnvRel.comp h' h) _ _ w) m)

/-! ## Delays and arrays -/

/-- Forcing a delayed value is the value. -/
theorem Term.eval_lazy_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.lazy τ)) (env : Env Γ) :
    (Term.eval G (Term.lazy_force e) env : TyWf.Den τ) = (Term.eval G e env : TyWf.Den (.lazy τ)) :=
  Term.evalJ_bindAtom G e (fun _ a => .ofComp (.lazy_force a)) env (J := []) PUnit.unit
    (fun x => x) fun _ _ _ _ => rfl

/-- Forcing a thunk is the value it delays. -/
theorem Term.eval_thunk_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.thunk τ)) (env : Env Γ) :
    (Term.eval G (Term.thunk_force e) env : TyWf.Den τ) = (Term.eval G e env : TyWf.Den (.thunk τ)) :=
  Term.evalJ_bindAtom G e (fun _ a => .ofComp (.thunk_force a)) env (J := []) PUnit.unit
    (fun x => x) fun _ _ _ _ => rfl

/-- An array is the array of the values of its elements. -/
theorem Term.eval_array_mk {Γ : Ctx} {τ : TyWf} (ts : Terms Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.array_mk ts) env = (Terms.eval G ts env).toArray :=
  Terms.eval_bindAtoms G ts Ren.id env env (EnvRel.id' env) (fun _ as => .ofComp (.array_mk as))
    (fun vs => (vs.toArray : TyWf.Den (.array τ)))
    fun _ _ _ _ => rfl

/-- Taking an array apart: the empty branch, or the successor branch binding the first
    element and the rest. -/
theorem Term.eval_array_casesOn' {Γ : Ctx} {σ τ : TyWf} (a : Term Sg Γ (.array σ))
    (z : Term Sg Γ τ) (s : Term Sg (σ :: TyWf.array σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.array_casesOn' a z s) env =
      List.casesOn (motive := fun _ => TyWf.Den τ)
        (Array.toList (α := TyWf.Den σ) (Term.eval G a env)) (Term.eval G z env)
        fun x xs => Term.eval G s (x, xs.toArray, env) := by
  refine Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit
    (fun v => List.casesOn (motive := fun _ => TyWf.Den τ) (Array.toList (α := TyWf.Den σ) v)
      (Term.eval G z env) fun x xs => Term.eval G s (x, xs.toArray, env)) ?_ ?_
  · intro x
    show (match Array.toList (α := TyWf.Den σ) (Atom.eval x env) with
      | [] => Term.eval G z env | y :: ys => Term.eval G s (y, ys.toArray, env)) = _
    cases Array.toList (α := TyWf.Den σ) (Atom.eval x env) <;> rfl
  · intro Δ ρ env' x h
    show (match Array.toList (α := TyWf.Den σ) (Atom.eval x env') with
      | [] => Term.eval G (z.rename ρ) env'
      | y :: ys => Term.eval G (s.rename (Ren.lift (Ren.lift ρ))) (y, ys.toArray, env')) = _
    dsimp only
    cases Array.toList (α := TyWf.Den σ) (Atom.eval x env') with
    | nil => exact Term.eval_rename G ρ z h
    | cons y ys => exact Term.eval_rename G _ s (EnvRel.lift (EnvRel.lift h _) _)

/-- **The fold of an array** (descending `k + 1` elements) is `listFoldK` of its short-list
    answers and its branch, over the elements of its argument. -/
theorem Term.eval_array_rec' {Γ : Ctx} {σ τ : TyWf} (k : Nat) (a : Term Sg Γ (.array σ))
    (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ) (env : Env Γ) :
    Term.eval G (Term.array_rec' k a bases branch) env =
      listFoldK (fun l => ArrayRecBases.eval G bases env l)
        (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
        (Array.toList (α := TyWf.Den σ) (Term.eval G a env)) := by
  refine Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit
    (fun v => listFoldK (fun l => ArrayRecBases.eval G bases env l)
      (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
      (Array.toList (α := TyWf.Den σ) v)) (fun _ => rfl) ?_
  intro Δ ρ env' x h
  show listFoldK (fun l => ArrayRecBases.eval G (bases.rename ρ) env' l)
    (fun hd tl w => Term.eval G (branch.rename (Ren.lift (Ren.lift (Ren.liftNat τ (k + 1) ρ))))
      (hd, tl.toArray, Env.ofWin w env')) _ = _
  congr 1
  · funext l
    exact ArrayRecBases.eval_rename G ρ bases env env' l h
  · funext hd tl w
    exact Term.eval_rename G _ branch
      (EnvRel.lift (EnvRel.lift (EnvRel.liftNat h _ _ w) _) _)

/-! ## Enums, records and tagged unions -/

/-- A dispatch on an enum takes the branch of the constructor the value is. -/
theorem Term.eval_enum_casesOn' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema}
    (e : Term Sg Γ (.enum s)) (cases : EnumCases Sg Γ τ s) (env : Env Γ) :
    Term.eval G (Term.enum_casesOn' e cases) env =
      EnumCases.eval G cases env (J := []) PUnit.unit (Term.eval G e env) :=
  Term.evalJ_bindAtomOr G e _ _ env (J := []) PUnit.unit
    (fun v => EnumCases.eval G cases env (J := []) PUnit.unit v) (fun _ => rfl)
    fun ρ env' _ h => EnumCases.eval_rename G ρ cases env env' _ _ h

/-- A partial dispatch on an enum takes the first branch naming the value's constructor,
    and the default otherwise. -/
theorem Term.eval_enum_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema}
    {k : Nat} (e : Term Sg Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k) (dflt : Term Sg Γ τ)
    (hk : k < s.nOfConstructors) (env : Env Γ) :
    Term.eval G (Term.enum_casesOnWithDefault' e cases dflt hk) env =
      EnumSomeCases.eval G cases env (J := []) PUnit.unit (Term.eval G e env) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G e _ _ env (J := []) PUnit.unit
    (fun v => EnumSomeCases.eval G cases env (J := []) PUnit.unit v (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show EnumSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact EnumSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- A record is the tuple of the values of its fields. -/
theorem Term.eval_record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf)
    (fields : Spine Sg Γ fs.toList) (env : Env Γ) :
    Term.eval G (Term.record_mk fs fields) env =
      cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm (Spine.eval G fields env) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm vs) fun _ _ _ _ => rfl

/-- Taking a record apart binds its fields. -/
theorem Term.eval_record_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf}
    (r : Term Sg Γ (.record fs)) (body : Term Sg (fs.toList ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.record_casesOn' r body) env =
      Term.eval G body
        (Env.append (cast (Ty.denRecord_eq (fs.map TyWf.toTy)) (Term.eval G r env)) env) :=
  Term.evalJ_bindAtomOr G r _ _ env (J := []) PUnit.unit
    (fun v => Term.eval G body (Env.append (cast (Ty.denRecord_eq (fs.map TyWf.toTy)) v) env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.liftN _ _)

/-- A tagged value is its tag and the values of its fields. -/
theorem Term.eval_taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    Term.eval G (Term.taggedUnion_mk l t ht fields) env =
      TyWf.DenTU.mk t ht (Spine.eval G fields env) := by
  unfold Term.taggedUnion_mk
  exact Spine.eval_bindArgs (τ := .taggedUnion l) G fields Ren.id env env (EnvRel.id' env) _
    (TyWf.DenTU.mk t ht) fun _ _ _ _ => rfl

/-- A dispatch on a tagged union takes the branch of the value's tag, binding its fields. -/
theorem Term.eval_taggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
    (v : Term Sg Γ (.taggedUnion l)) (cases : TaggedUnionFoldCases Sg TyWf id Γ l τ)
    (env : Env Γ) :
    Term.eval G (Term.taggedUnion_casesOn' v cases) env =
      TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit (Term.eval G v env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit x) (fun _ => rfl)
    fun ρ env' _ h => TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' _ _ h

/-- A partial dispatch on a tagged union: the first branch naming the value's tag, and the
    default otherwise. -/
theorem Term.eval_taggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema TyWf} {k : Nat} (v : Term Sg Γ (.taggedUnion l))
    (cases : TaggedUnionSomeCases Sg Γ l τ k) (dflt : Term Sg Γ τ) (hk : k < l.length)
    (env : Env Γ) :
    Term.eval G (Term.taggedUnion_casesOnWithDefault' v cases dflt hk) env =
      TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit (Term.eval G v env)
        (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit x (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show TaggedUnionSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-! ## The recursive shapes -/

/-- A value of a recursive tagged union is the node built from its tag and fields. -/
theorem Term.eval_recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Spine Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_mk l hwf t ht fields) env =
      TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht (Spine.eval G fields env)) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht vs)) fun _ _ _ _ => rfl

/-- A dispatch on a recursive tagged union takes one level off the value. -/
theorem Term.eval_recTaggedUnion_casesOn' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ)
    (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_casesOn' v cases) env =
      TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit
        (TyWf.DenRec.unfold l hwf (Term.eval G v env)) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit
      (TyWf.DenRec.unfold l hwf x)) (fun _ => rfl)
    fun ρ env' _ h => TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' _ _ h

/-- A partial dispatch on a recursive tagged union takes one level off the value. -/
theorem Term.eval_recTaggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    {k : Nat} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k)
    (dflt : Term Sg Γ τ) (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length) (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_casesOnWithDefault' v cases dflt hk) env =
      TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenRec.unfold l hwf (Term.eval G v env)) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit (TyWf.DenRec.unfold l hwf x)
      (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show TaggedUnionSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- **The fold of a recursive tagged union** is `WType.memoFold` of its branches, at the
    value of its argument. -/
theorem Term.eval_recTaggedUnion_rec' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat)
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldKCases Sg l (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ l τ k [])
    (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_rec' k v cases) env =
      WType.memoFold
        (fun node kids =>
          TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
            node.1.val ⟨node.2, kids⟩)
        (Term.eval G v env) := by
  unfold Term.recTaggedUnion_rec'
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids =>
        TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
          node.1.val ⟨node.2, kids⟩) x) ?_ ?_
  · intro _; rfl
  intro Δ ρ env' a h
  show WType.memoFold _ (Atom.eval a env') = WType.memoFold _ (Atom.eval a env')
  congr 1
  funext node kids
  exact TaggedUnionFoldKCases.eval_rename G ρ cases env env' _ _ _ _ h

/-- A value of a recursive record is the node built from its fields. -/
theorem Term.eval_recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) (env : Env Γ) :
    Term.eval G (Term.recObject_mk fs hwf fields) env =
      TyWf.DenObj.mk fs hwf (Spine.eval G fields env) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => TyWf.DenObj.mk fs hwf vs) fun _ _ _ _ => rfl

/-- Taking a recursive record apart binds its unfolded fields. -/
theorem Term.eval_recObject_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recObject_casesOn' v body) env =
      Term.eval G body (Env.append (TyWf.DenObj.unfold fs hwf (Term.eval G v env)) env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G body (Env.append (TyWf.DenObj.unfold fs hwf x) env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.liftN _ _)

/-- **The fold of a recursive record** is `WType.memoFold` of its body, at the value of its
    argument. -/
theorem Term.eval_recObject_rec' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat) (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recObject_rec' k v body) env =
      WType.memoFold
        (fun node kids => Term.eval G body (Env.append (objRecEnv fs hwf τ k node kids) env))
        (Term.eval G v env) := by
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids => Term.eval G body (Env.append (objRecEnv fs hwf τ k node kids) env)) x)
    (fun _ => rfl) ?_
  intro Δ ρ env' a h
  show WType.memoFold (fun node kids => Term.eval G (body.rename _)
      (Env.append (objRecEnv fs hwf τ k node kids) env')) _ = _
  congr 1
  funext node kids
  exact Term.eval_rename G _ body (h.liftN _ _)

/-- A value of a recursive newtype is the node built from its body. -/
theorem Term.eval_recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b))
    (value : Term Sg Γ (TyWf.recAliasUnfold b hwf)) (env : Env Γ) :
    Term.eval G (Term.recAlias_mk b hwf value) env =
      TyWf.DenAlias.mk b hwf (Term.eval G value env) :=
  Term.evalJ_bindAtom G value _ env (J := []) PUnit.unit (fun x => TyWf.DenAlias.mk b hwf x)
    fun _ _ _ _ => rfl

/-- Taking a recursive newtype apart binds its unfolded body. -/
theorem Term.eval_recAlias_casesOn' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recAlias_casesOn' v body) env =
      Term.eval G body (TyWf.DenAlias.unfold b hwf (Term.eval G v env), env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G body (TyWf.DenAlias.unfold b hwf x, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.lift _)

/-- **The fold of a recursive newtype** is `WType.memoFold` of its body, at the value of its
    argument. -/
theorem Term.eval_recAlias_rec' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (k : Nat) (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recAlias_rec' k v body) env =
      WType.memoFold
        (fun node kids => Term.eval G body (Env.append (aliasRecEnv b hwf τ k node kids) env))
        (Term.eval G v env) := by
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids => Term.eval G body (Env.append (aliasRecEnv b hwf τ k node kids) env)) x)
    (fun _ => rfl) ?_
  intro Δ ρ env' a h
  show WType.memoFold (fun node kids => Term.eval G (body.rename _)
      (Env.append (aliasRecEnv b hwf τ k node kids) env')) _ = _
  congr 1
  funext node kids
  exact Term.eval_rename G _ body (h.liftN _ _)

/-- A value of a member of a mutual family is the node built from its operands. -/
theorem Term.eval_mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2))) (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f))
    (value : FamilyMemberValue Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_mk f hwf value) env =
      TyWf.DenFam.mk f hwf (FamilyMemberValue.eval G value env) :=
  FamilyMemberValue.eval_bindArgs G value _ env (fun x => TyWf.DenFam.mk f hwf x)
    fun _ _ _ _ => rfl

/-- A dispatch on a member of a mutual family takes one level off the value. -/
theorem Term.eval_mutualRecursiveFamily_casesOn' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_casesOn' v cases) env =
      FamilyMemberCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenFam.unfold f hwf (Term.eval G v env)) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => FamilyMemberCases.eval G cases env (J := []) PUnit.unit (TyWf.DenFam.unfold f hwf x))
    (fun _ => rfl) fun ρ env' _ h => FamilyMemberCases.eval_rename G ρ cases env env' _ _ h

/-- A partial dispatch on a member of a mutual family takes one level off the value. -/
theorem Term.eval_mutualRecursiveFamily_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (dflt : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_casesOnWithDefault' v cases dflt) env =
      FamilyMemberSomeCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenFam.unfold f hwf (Term.eval G v env)) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => FamilyMemberSomeCases.eval G cases env (J := []) PUnit.unit (TyWf.DenFam.unfold f hwf x)
      (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show FamilyMemberSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact FamilyMemberSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- **The fold of a mutual family** is `IWType.memoFold` of the branches of every member, at
    the value of its argument. -/
theorem Term.eval_mutualRecursiveFamily_rec' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (k : Nat) (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ τ f.members k)
    (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_rec' k v cases) env =
      IWType.memoFold (β := TyWf.Den τ)
        (fun i a kids => FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
        (cast (den_mutualRecursiveFamily f hwf) (Term.eval G v env)) := by
  unfold Term.mutualRecursiveFamily_rec'
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => IWType.memoFold (β := TyWf.Den τ)
      (fun i a kids => FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
      (cast (den_mutualRecursiveFamily f hwf) x)) ?_ ?_
  · intro _; rfl
  intro Δ ρ env' a h
  show IWType.memoFold (β := TyWf.Den τ) _ (cast (den_mutualRecursiveFamily f hwf) (Atom.eval a env'))
    = IWType.memoFold (β := TyWf.Den τ) _ (cast (den_mutualRecursiveFamily f hwf) (Atom.eval a env'))
  congr 1
  funext i x kids
  exact FamilyFoldKCases.eval_rename G ρ cases env env' _ _ _ h

end LeanScript

end
