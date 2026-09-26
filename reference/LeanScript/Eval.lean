module

public import LeanScript.Eval.Env
public import LeanScript.Eval.Extern
public import LeanScript.Den.Rec
public import LeanScript.Den.RecObjectAlias
public import LeanScript.Den.Family

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The evaluator, and why it stops

`Term.eval` takes a term of type `τ` in a context `Γ`, an environment holding a value for
every type of `Γ`, and an environment holding a value for every declaration of the
signature, and gives **the** value of that term: an element of `LeanScript.TyWf.Den τ`.

It is a **total Lean function, defined by structural recursion on the term**, so it
terminates on every input — there is no fuel, no `partial` and no `unsafe`, and the
answer is a value rather than a computation that might not stop.

It interprets **every** term: every type of the language has values
(`LeanScript.Ty.Den`), so there is no side condition on the term.  The four recursive
shapes have values — the W-tree of the binder's payload, or for a family the *indexed*
W-tree of its members' payloads — and all of their forms are interpreted:

* a recursive **tagged union**: `Term.recTaggedUnion_mk` builds a node
  (`TyWf.DenRec.mk`), a dispatch takes one level off (`TyWf.DenRec.unfold`), and the fold
  of any depth `k` is `WType.memoFold`, which computes the answer at every node once,
  bottom-up, and stores it beside the node, so a branch that looks further down reads
  answers that are already there;
* a recursive **record**: `Term.recObject_mk` builds a node from the unfolded fields
  (`TyWf.DenObj.mk`), `Term.recObject_casesOn` binds them again (`TyWf.DenObj.unfold`),
  and `Term.recObject_rec` is `WType.memoFold` too, its branch binding the fields and the
  window of answer trees read off the memo (`LeanScript.objRecEnv`);
* a recursive **newtype**: the same, with the body for the fields (`TyWf.DenAlias.mk`,
  `TyWf.DenAlias.unfold`, `LeanScript.aliasRecEnv`);
* a **mutual family**: `Term.mutualRecursiveFamily_mk` builds a node of the member the
  family selects from its unfolded constructors, fields or body (`TyWf.DenFam.mk`), a
  dispatch takes one level off (`TyWf.DenFam.unfold`), and the fold of any depth `k` is
  `IWType.memoFold`: the answer at every node, whichever member it is a value of, is
  computed once from *that member's* branches and stored beside the node, and a deeper
  look into an occurrence of another member reads the answers stored under it
  (`LeanScript.famBindEnv`).

All of it is structural, on the term and on the value, so the evaluator is still total
with no fuel.  `LeanScript.RecUnionEvalFacts` and `LeanScript.RecObjectAliasEvalFacts`
state what it does with them; the family forms are run, against Lean references, by
`TermTests/RecTermTest.lean` and `TermTests/FamilyRecDepthTest.lean`.

That this is possible at all is the point of the grammar: `LeanScript.Term` has no
fixpoint constructor.  The two recursive forms it does have, `Term.nat_rec` and
`Term.array_rec`, are folds — the branch is *given* the value of the recursion on the
smaller argument (as a de Bruijn index) rather than being able to call anything — so
evaluating them is `Nat.rec` and `List.rec` (an array of the language denotes a Lean
`Array`, and its fold runs over the list of its elements), and every other constructor evaluates its
immediate subterms.  In particular:

* a dispatch always has a branch to take: `EnumCases` and `TaggedUnionCases` are indexed
  by the schema, so they are exhaustive by construction, and the two `WithDefault` forms
  carry a default;
* a field is never looked up by index: an eliminator binds the fields of the constructor
  it matched, so there is no out-of-range read to fail on;
* there is no effect and no failure, so the result is a value and not an `Option` or an
  `Except`.

The evaluator is *call-by-value*, and that choice is invisible: every form is total, so
the value of a term does not depend on the order its subterms are evaluated in.  In
particular a delay (`Ty.lazy`, `Ty.thunk`) denotes the value it stands for, and the two
`WithDefault` dispatches evaluate their default eagerly.
-/

/-! ## The evaluator -/

/-! ## Atoms -/

/-- The value of an atom: the variable is read off the environment. -/
def Atom.eval {Γ : Ctx} {τ : TyWf} : Atom Γ τ → Env Γ → TyWf.Den τ
  | .var v, env => Env.get v env

/-- The values of a list of atoms, typed by the list of their types. -/
def Args.eval {Sg : Sig} (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {σs : List TyWf} → Args Sg Γ σs → Env Γ → TyWf.DenList σs
  | _, .nil, _ => PUnit.unit
  | _, .cons a as, env => (Atom.eval a env, Args.eval G as env)

/-- The value of a member of a mutual family, built from the shape that member has. -/
def FamilyMemberArgs.eval {Sg : Sig} (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {m : LeanFamMemberSchema TyWf} → FamilyMemberArgs Sg Γ m → Env Γ → TyWf.DenMember m
  | _, .ctors _ t ht fields, env => TyWf.DenTU.mk t ht (Args.eval G fields env)
  | _, .record _ fields, env => cast (Ty.denRecord_eq _).symm (Args.eval G fields env)
  | _, .alias _ value, env => Atom.eval value env

/-! ## Join points -/

/-- The values of the join points in scope, for a term of type `τ`: each join point of
    parameter type `σ` is the function `TyWf.Den σ → TyWf.Den τ` its body computes. -/
def JEnv (τ : TyWf) : JCtx → Type
  | [] => PUnit
  | σ :: J => (TyWf.Den σ → TyWf.Den τ) × JEnv τ J

/-- The function a join point stands for. -/
def JEnv.get {τ : TyWf} : {J : JCtx} → {σ : TyWf} → (J ∋ σ) → JEnv τ J →
    TyWf.Den σ → TyWf.Den τ
  | _ :: _, _, .head, jenv => jenv.1
  | _ :: _, _, .tail j, jenv => JEnv.get j jenv.2

/-- Deliver the answer of a fold to its destination: it is the value of the term, or it is
    passed to a join point. -/
def Dest.apply {J : JCtx} {ρ τ : TyWf} : Dest J ρ τ → JEnv τ J → TyWf.Den ρ → TyWf.Den τ
  | .ret, _, v => v
  | .jump j, jenv, v => JEnv.get j jenv v

/-! ## Terms -/

mutual

/-- **The value of a term**: a total function of the term, its environment, the join points
    in scope and the values of the module's top-level declarations.  It is defined by
    structural recursion on the term, so it terminates on every input, and it interprets
    every term.  A `let` binds the value of its computation; a join point is the function
    of its parameter its body computes, and a jump applies it; a dispatch takes the value
    of the branch the value it takes apart selects; and a fold delivers its answer to its
    `LeanScript.Dest`. -/
def Term.evalJ {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {J : JCtx} → (t : Term Sg Γ τ J) → Env Γ → JEnv τ J →
    TyWf.Den τ
  | _, _, _, .ret a, env, _ => Atom.eval a env
  -- `let x = c; ret x` is the value of `c`: the same as the general case below
  -- (`Term.evalJ_letE`), read off directly, which keeps the unfolding of a step in tail
  -- position as short as it would be without the `let`.
  | _, _, _, .letE c (.ret (.var .head)), env, _ => Comp.eval G c env
  | _, _, _, .letE c body, env, jenv => Term.evalJ G body (Comp.eval G c env, env) jenv
  | _, _, _, .letJ jp body, env, jenv =>
      Term.evalJ G body env (fun x => Term.evalJ G jp (x, env) jenv, jenv)
  | _, _, _, .jump j a, env, jenv => JEnv.get j jenv (Atom.eval a env)
  | _, _, _, .externCallChecked args call d fallback, env, jenv =>
      match call (Args.eval G args env) with
      | some e => Dest.apply d jenv (Extern.eval e)
      | none => Term.evalJ G fallback env jenv
  | _, _, _, .bool_casesOn c t e, env, jenv =>
      let c' : Bool := Atom.eval c env
      match c' with
      | true => Term.evalJ G t env jenv
      | false => Term.evalJ G e env jenv
  | _, _, _, .nat_casesOn n z s, env, jenv =>
      let n' : Nat := Atom.eval n env
      match n' with
      | 0 => Term.evalJ G z env jenv
      | k + 1 => Term.evalJ G s (k, env) jenv
  | _, _, _, .nat_rec _ n base branch d, env, jenv =>
      Dest.apply d jenv <|
      natFoldK (Args.eval G base env)
        (fun m w => Term.evalJ G branch (m, Env.ofWin w env) PUnit.unit)
        (show Nat from Atom.eval n env)
  | _, _, _, .int_casesOn i ofNat negSucc, env, jenv =>
      let i' : Int := Atom.eval i env
      match i' with
      | .ofNat k => Term.evalJ G ofNat (k, env) jenv
      | .negSucc k => Term.evalJ G negSucc (k, env) jenv
  | _, _, _, .uint8_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toBitVec, env) jenv
  | _, _, _, .uint16_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toBitVec, env) jenv
  | _, _, _, .uint32_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toBitVec, env) jenv
  | _, _, _, .uint64_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toBitVec, env) jenv
  | _, _, _, .int8_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toUInt8, env) jenv
  | _, _, _, .int16_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toUInt16, env) jenv
  | _, _, _, .int32_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toUInt32, env) jenv
  | _, _, _, .int64_casesOn v b, env, jenv =>
      Term.evalJ G b ((Atom.eval v env).toUInt64, env) jenv
  | _, _, _, .char_casesOn c b, env, jenv =>
      Term.evalJ G b ((Atom.eval c env).val, env) jenv
  | _, _, _, .stringPosRaw_casesOn p b, env, jenv =>
      Term.evalJ G b ((Atom.eval p env).byteIdx, env) jenv
  | _, _, _, .stringPos_casesOn p b, env, jenv =>
      Term.evalJ G b ((Atom.eval p env).offset, env) jenv
  | _, _, _, .substringRaw_casesOn s b, env, jenv =>
      let v : Substring.Raw := Atom.eval s env
      Term.evalJ G b (v.str, v.startPos, v.stopPos, env) jenv
  | _, _, _, .float_casesOn x b, env, jenv =>
      Term.evalJ G b ((Atom.eval x env).toModel, env) jenv
  | _, _, _, .float32_casesOn x b, env, jenv =>
      Term.evalJ G b ((Atom.eval x env).toModel, env) jenv
  | _, _, _, .floatModel_casesOn m b, env, jenv =>
      Term.evalJ G b ((Atom.eval m env).toBits, env) jenv
  | _, _, _, .float32Model_casesOn m b, env, jenv =>
      Term.evalJ G b ((Atom.eval m env).toBits, env) jenv
  | _, _, _, .array_casesOn a z s, env, jenv =>
      let a' : Array _ := Atom.eval a env
      match a'.toList with
      | [] => Term.evalJ G z env jenv
      | x :: xs => Term.evalJ G s (x, xs.toArray, env) jenv
  | _, _, _, .array_rec _ a bases branch d, env, jenv =>
      Dest.apply d jenv <|
      listFoldK (fun l => ArrayRecBases.eval G bases env l)
        (fun hd tl w => Term.evalJ G branch (hd, tl.toArray, Env.ofWin w env) PUnit.unit)
        (show Array _ from Atom.eval a env).toList
  | _, _, _, .enum_casesOn e cases, env, jenv =>
      EnumCases.eval G cases env jenv (Atom.eval e env)
  | _, _, _, .enum_casesOnWithDefault e cases dflt _, env, jenv =>
      EnumSomeCases.eval G cases env jenv (Atom.eval e env)
        (Term.evalJ G dflt env jenv)
  | _, _, _, .record_casesOn r body, env, jenv =>
      Term.evalJ G body (Env.append (cast (Ty.denRecord_eq _) (Atom.eval r env)) env) jenv
  | _, _, _, .taggedUnion_casesOn v cases, env, jenv =>
      TaggedUnionCases.eval G cases rfl .rfl .rfl env jenv (Atom.eval v env)
  | _, _, _, .taggedUnion_casesOnWithDefault v cases dflt _, env, jenv =>
      TaggedUnionSomeCases.eval G cases env jenv (Atom.eval v env)
        (Term.evalJ G dflt env jenv)
  | _, _, _, .recTaggedUnion_casesOn (l := l) (hwf := hwf) v cases, env, jenv =>
      TaggedUnionCases.eval G cases rfl .rfl .rfl env jenv
        (TyWf.DenRec.unfold l hwf (Atom.eval v env))
  | _, _, _, .recTaggedUnion_casesOnWithDefault (l := l) (hwf := hwf) v cases dflt _, env, jenv =>
      TaggedUnionSomeCases.eval G cases env jenv (TyWf.DenRec.unfold l hwf (Atom.eval v env))
        (Term.evalJ G dflt env jenv)
  | _, _, _, .recTaggedUnion_rec (l := l) (hwf := hwf) (ρ := τ) _ v cases d, env, jenv =>
      Dest.apply d jenv <|
      WType.memoFold
        (fun node kids =>
          TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
            node.1.val ⟨node.2, kids⟩)
        (Atom.eval v env)
  | _, _, _, .recObject_casesOn (fs := fs) (hwf := hwf) v body, env, jenv =>
      Term.evalJ G body (Env.append (TyWf.DenObj.unfold fs hwf (Atom.eval v env)) env) jenv
  | _, _, _, .recObject_rec (fs := fs) (hwf := hwf) (ρ := τ) k v body d, env, jenv =>
      Dest.apply d jenv <|
      WType.memoFold
        (fun node kids => Term.evalJ G body (Env.append (objRecEnv fs hwf τ k node kids) env) PUnit.unit)
        (Atom.eval v env)
  | _, _, _, .recAlias_casesOn (b := b) (hwf := hwf) v body, env, jenv =>
      Term.evalJ G body (TyWf.DenAlias.unfold b hwf (Atom.eval v env), env) jenv
  | _, _, _, .recAlias_rec (b := b) (hwf := hwf) (ρ := τ) k v body d, env, jenv =>
      Dest.apply d jenv <|
      WType.memoFold
        (fun node kids =>
          Term.evalJ G body (Env.append (aliasRecEnv b hwf τ k node kids) env) PUnit.unit)
        (Atom.eval v env)
  | _, _, _, .mutualRecursiveFamily_casesOn (f := f) (hwf := hwf) v cases, env, jenv =>
      FamilyMemberCases.eval G cases env jenv (TyWf.DenFam.unfold f hwf (Atom.eval v env))
  | _, _, _, .mutualRecursiveFamily_casesOnWithDefault (f := f) (hwf := hwf) v cases dflt, env, jenv =>
      FamilyMemberSomeCases.eval G cases env jenv (TyWf.DenFam.unfold f hwf (Atom.eval v env))
        (Term.evalJ G dflt env jenv)
  | _, _, _, .mutualRecursiveFamily_rec (f := f) (hwf := hwf) (ρ := τ) _ v cases d, env, jenv =>
      Dest.apply d jenv <|
      IWType.memoFold (β := TyWf.Den τ)
        (fun i a kids =>
          FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
        (cast (den_mutualRecursiveFamily f hwf) (Atom.eval v env))

/-- **The value of one computation step**: its operands are atoms, whose values are read
    off the environment (`Atom.eval`), and the terms it holds — a body, a branch — are
    evaluated by `Term.eval` in the environment extended with what they bind. -/
def Comp.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (t : Comp Sg Γ τ) → Env Γ → TyWf.Den τ
  | _, _, .global r, _ => GlobalEnv.get r G
  | _, _, .bool_mk b, _ => b
  | _, _, .nat_mk n, _ => n
  | _, _, .int_mk i, _ => i
  | _, _, .bitvec_mk _ v, _ => v
  | _, _, .uint8_mk v, _ => v
  | _, _, .uint16_mk v, _ => v
  | _, _, .uint32_mk v, _ => v
  | _, _, .uint64_mk v, _ => v
  | _, _, .int8_mk v, _ => v
  | _, _, .int16_mk v, _ => v
  | _, _, .int32_mk v, _ => v
  | _, _, .int64_mk v, _ => v
  | _, _, .char_mk c, _ => c
  | _, _, .string_mk s, _ => s
  | _, _, .stringPos_mk _ p, _ => p
  | _, _, .stringPosRaw_mk p, _ => p
  | _, _, .substringRaw_mk s, _ => s
  | _, _, .stringSlice_mk s, _ => s
  | _, _, .float_mk x, _ => x
  | _, _, .float32_mk x, _ => x
  | _, _, .floatModel_mk m, _ => m
  | _, _, .float32Model_mk m, _ => m
  | _, _, .lam body, env => fun x => Term.evalJ G body (x, env) PUnit.unit
  | _, _, .ap f a, env => (Atom.eval f env) (Atom.eval a env)
  | _, _, .extern e, _ => Extern.eval e
  | _, _, .externCall args call, env => Extern.eval (call (Args.eval G args env))
  | _, _, .lazy_mk e, env => let v := Term.evalJ G e env PUnit.unit; v
  | _, _, .lazy_force e, env => let v := Atom.eval e env; v
  | _, _, .thunk_mk e, env => let v := Term.evalJ G e env PUnit.unit; v
  | _, _, .thunk_force e, env => let v := Atom.eval e env; v
  | _, _, .array_mk ts, env => (ts.map (Atom.eval · env)).toArray
  | _, _, .enum_mk _ i, _ => i
  | _, _, .record_mk fs fields, env =>
      cast (Ty.denRecord_eq _).symm (Args.eval G fields env)
  | _, _, .taggedUnion_mk _ t ht fields, env =>
      TyWf.DenTU.mk t ht (Args.eval G fields env)
  | _, _, .recTaggedUnion_mk l hwf t ht fields, env =>
      TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht (Args.eval G fields env))
  | _, _, .recObject_mk fs hwf fields, env =>
      TyWf.DenObj.mk fs hwf (Args.eval G fields env)
  | _, _, .recAlias_mk b hwf value, env =>
      TyWf.DenAlias.mk b hwf (Atom.eval value env)
  | _, _, .mutualRecursiveFamily_mk f hwf value, env =>
      TyWf.DenFam.mk f hwf (FamilyMemberArgs.eval G value env)

/-- The answer a fold of an array gives to a list shorter than its window: the elements
    are peeled off one at a time and bound, and the answer of the list that is left is
    read off the answers of one lower depth.  A list that is **not** short — one the fold
    never consults these answers for — runs out of depth and gets the answer of the empty
    list of the innermost block. -/
def ArrayRecBases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {k : Nat} → (bs : ArrayRecBases Sg Γ σ τ k) → Env Γ →
    List (TyWf.Den σ) → TyWf.Den τ
  | _, _, _, _, .nil e, env, _ => Term.evalJ G e env PUnit.unit
  | _, _, _, _, .cons e _, env, [] => Term.evalJ G e env PUnit.unit
  | _, _, _, _, .cons _ more, env, a :: as =>
      ArrayRecBases.eval G more (a, env) as

/-- The value of the branch a value of a tagged union takes.  The branches are indexed by
    the schema and the value carries a tag that the schema has, so there is always
    exactly one branch to take.

    A plain dispatch is the fold-case family at `ι := TyWf` and `bind := id`
    (`LeanScript.TaggedUnionCases`).  Structural recursion needs the indices of the family
    to be variables, so the evaluator is stated for any `ι` and `bind` together with the
    equations that pin them — the caller passes `rfl`, and matching on those `rfl`s makes
    a branch's context `fs ++ Γ` again. -/
def TaggedUnionCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {l : LeanTaggedUnionSchema ι} →
    {τ : TyWf} → {J : JCtx} → (cases : TaggedUnionFoldCases Sg ι bind Γ l τ J) →
    {l' : LeanTaggedUnionSchema TyWf} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    l ≍ l' → Env Γ → JEnv τ J → TyWf.DenTU l' → TyWf.Den τ
  | _, _, _, _, _, _, .payloadFirst b0 b1 rest, _, rfl, .rfl, .rfl, env, jenv, v =>
      match v with
      | ⟨⟨0, _⟩, f⟩ => Term.evalJ G b0 (Env.append (cast (Ty.denNE_eq _) f) env) jenv
      | ⟨⟨1, _⟩, f⟩ => Term.evalJ G b1 (Env.append f env) jenv
      | ⟨⟨n + 2, _⟩, f⟩ => TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env jenv n f
  | _, _, _, _, _, _, .skip b0 rest, _, rfl, .rfl, .rfl, env, jenv, v =>
      match v with
      | ⟨⟨0, _⟩, _⟩ => Term.evalJ G b0 env jenv
      | ⟨⟨n + 1, _⟩, f⟩ => CtorsWithPayloadCases.eval G rest rfl .rfl .rfl env jenv n f

/-- `TaggedUnionCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {c : CtorsWithPayload ι} →
    {τ : TyWf} → {J : JCtx} → (cases : CtorsWithPayloadFoldCases Sg ι bind Γ c τ J) →
    {c' : CtorsWithPayload TyWf} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    c ≍ c' → Env Γ → JEnv τ J → (t : Nat) → TyWf.DenAtCP c' t → TyWf.Den τ
  | _, _, _, _, _, _, .here b _, _, rfl, .rfl, .rfl, env, jenv, 0, f =>
      Term.evalJ G b (Env.append (cast (Ty.denNE_eq _) f) env) jenv
  | _, _, _, _, _, _, .here _ rest, _, rfl, .rfl, .rfl, env, jenv, n + 1, f =>
      TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env jenv n f
  | _, _, _, _, _, _, .skip b _, _, rfl, .rfl, .rfl, env, jenv, 0, _ => Term.evalJ G b env jenv
  | _, _, _, _, _, _, .skip _ rest, _, rfl, .rfl, .rfl, env, jenv, n + 1, f =>
      CtorsWithPayloadCases.eval G rest rfl .rfl .rfl env jenv n f

/-- `TaggedUnionCases.eval`, on a plain list of constructors.  A tag past the end of the
    list has no value — `Ty.DenAtList [] n` is `PEmpty` — which is why the empty list of
    branches needs no branch. -/
def TaggedUnionCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {cs : List (List ι)} →
    {τ : TyWf} → {J : JCtx} → (cases : TaggedUnionFoldCasesRest Sg ι bind Γ cs τ J) →
    {cs' : List (List TyWf)} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    cs ≍ cs' → Env Γ → JEnv τ J → (t : Nat) → TyWf.DenAtList cs' t → TyWf.Den τ
  | _, _, _, _, _, _, .nil, _, rfl, .rfl, .rfl, _, _, _, f => PEmpty.elim f
  | _, _, _, _, _, _, .cons b _, _, rfl, .rfl, .rfl, env, jenv, 0, f =>
      Term.evalJ G b (Env.append f env) jenv
  | _, _, _, _, _, _, .cons _ rest, _, rfl, .rfl, .rfl, env, jenv, n + 1, f =>
      TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env jenv n f

/-- The value of a dispatch on **some** of the constructors of a tagged union: the first
    branch whose constructor the value has, and the default if it has none of them. -/
def TaggedUnionSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {k lo : Nat} → {J : JCtx} →
    (cases : TaggedUnionSomeCases Sg Γ l τ k lo J) → Env Γ → JEnv τ J → TyWf.DenTU l →
    TyWf.Den τ → TyWf.Den τ
  | _, _, _, _, _, _, .last t ht branch _, env, jenv, v, dflt =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.evalJ G branch (Env.append f env) jenv
      | none => dflt
  | _, _, _, _, _, _, .cons t ht branch rest _, env, jenv, v, dflt =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.evalJ G branch (Env.append f env) jenv
      | none => TaggedUnionSomeCases.eval G rest env jenv v dflt

/-- The value of the branch a constructor of an enum takes.  The branches are indexed by
    the schema, so there is always exactly one branch to take. -/
def EnumCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {J : JCtx} →
    (cases : EnumCases Sg Γ τ s J) → Env Γ → JEnv τ J → Fin s.nOfConstructors → TyWf.Den τ
  | _, _, _, _, .three b0 b1 b2, env, jenv, i =>
      match i with
      | ⟨0, _⟩ => Term.evalJ G b0 env jenv
      | ⟨1, _⟩ => Term.evalJ G b1 env jenv
      | ⟨2, _⟩ => Term.evalJ G b2 env jenv
      | ⟨_ + 3, hi⟩ => absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, _, .cons b rest, env, jenv, i =>
      match i with
      | ⟨0, _⟩ => Term.evalJ G b env jenv
      | ⟨n + 1, hi⟩ =>
          EnumCases.eval G rest env jenv ⟨n, by
            simp only [LeanEnumSchema.nOfConstructors] at hi ⊢; omega⟩

/-- The value of a dispatch on **some** of the constructors of an enum: the first branch
    whose constructor the value is, and the default if it is none of them. -/
def EnumSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {k lo : Nat} → {J : JCtx} →
    (cases : EnumSomeCases Sg Γ τ s k lo J) → Env Γ → JEnv τ J → Fin s.nOfConstructors →
    TyWf.Den τ → TyWf.Den τ
  | _, _, _, _, _, _, .last j branch _, env, jenv, i, dflt =>
      if i = j then Term.evalJ G branch env jenv else dflt
  | _, _, _, _, _, _, .cons j branch rest _, env, jenv, i, dflt =>
      if i = j then Term.evalJ G branch env jenv
      else EnumSomeCases.eval G rest env jenv i dflt

/-- The answer of one branch of the fold of a recursive tagged union, at a node whose
    fields are `e` — their shape, with the memo of the subtree in each hole — below the
    nodes `fr` dispatched on above it.  An answer is its term, in the environment `mkEnv`
    reads off the node; a deeper look takes the memo of the occurrence it names, at this
    node or at one above, and dispatches on *its* node, so every answer it reads below is
    already stored there and nothing is recomputed. -/
def FoldKBranch.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {fs : List (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (br : FoldKBranch Sg l₀ bind Γ fs τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer → RecFields l₀ τ fs → TyWf.Den τ
  | _, _, _, _, _, _, _, .here body, env, mkEnv, _, e =>
      Term.evalJ G body (Env.append (mkEnv _ e) env) PUnit.unit
  | _, _, _, _, _, _, _, .deep sf cases, env, mkEnv, fr, e =>
      match selfFieldMemo sf e with
      | .mk (node, _) kids =>
          TaggedUnionFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
            node.1.val ⟨node.2, kids⟩
  | _, _, _, _, _, _, _, .deepOuter o cases, env, mkEnv, fr, e =>
      match outerSelfFieldMemo o fr with
      | .mk (node, _) kids =>
          TaggedUnionFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
            node.1.val ⟨node.2, kids⟩

/-- The answer of the fold of a recursive tagged union at a node of constructor `t`: the
    branch of that constructor, as `TaggedUnionCases.eval` selects it. -/
def TaggedUnionFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {l : LeanTaggedUnionSchema (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : TaggedUnionFoldKCases Sg l₀ bind Γ l τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, fr, 0, e =>
      FoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, fr, 1, e =>
      FoldKBranch.eval G b1 env mkEnv fr e
  | _, _, _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, fr, n + 2, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e
  | _, _, _, _, _, _, _, .skip b0 _, env, mkEnv, fr, 0, e =>
      FoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv fr n e

/-- `TaggedUnionFoldKCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {c : CtorsWithPayload (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : CtorsWithPayloadFoldKCases Sg l₀ bind Γ c τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .here b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .here _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e
  | _, _, _, _, _, _, _, .skip b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv fr n e

/-- `TaggedUnionFoldKCases.eval`, on a plain list of constructors; past the end there is
    no node. -/
def TaggedUnionFoldKCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {cs : List (List (TyWfIn 1))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : TaggedUnionFoldKCasesRest Sg l₀ bind Γ cs τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ) →
      TyWf.Den τ
  | _, _, _, _, _, _, _, .nil, _, _, _, _, e => PEmpty.elim e.1
  | _, _, _, _, _, _, _, .cons b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e

/-- The value of the branch a value of a member of a mutual family takes: a dispatch on its
    constructor for a member with constructors, and the one branch, binding what the value
    holds, for a record or a newtype member. -/
def FamilyMemberCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J : JCtx} →
    FamilyMemberCases Sg Γ τ m J → Env Γ → JEnv τ J → TyWf.DenMember m → TyWf.Den τ
  | _, _, _, _, .ctors cases, env, jenv, v =>
      TaggedUnionCases.eval G cases rfl .rfl .rfl env jenv v
  | _, _, _, _, .record body, env, jenv, v =>
      Term.evalJ G body (Env.append (cast (Ty.denRecord_eq _) v) env) jenv
  | _, _, _, _, .alias body, env, jenv, v => Term.evalJ G body (v, env) jenv

/-- The value of a partial dispatch on a member of a mutual family: the first branch whose
    constructor the value has, and the default if it has none of them. -/
def FamilyMemberSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} → {J : JCtx} →
    FamilyMemberSomeCases Sg Γ τ m J → Env Γ → JEnv τ J → TyWf.DenMember m → TyWf.Den τ →
    TyWf.Den τ
  | _, _, _, _, .ctors cases _, env, jenv, v, dflt =>
      TaggedUnionSomeCases.eval G cases env jenv v dflt

/-- The answer of one branch of the fold of a mutual family, at a node whose fields are
    `e` — their shape, with the memo of the subtree in each hole — below the nodes `fr`
    dispatched on above it.  An answer is its term, in the environment `mkEnv` reads off
    the node; a deeper look takes the memo of the occurrence it names, at this node or at
    one above, and dispatches on *its* node — whichever member it is a value of — so every
    answer it reads below is already stored there and nothing is recomputed. -/
def FamilyFoldKBranch.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {fs : List (TyWfIn (n + 2))} →
    {τ : TyWf} → {k : Nat} → {outer : List (List (TyWfIn (n + 2)))} →
    FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer → FamFields ms₀ τ fs → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .here body, env, mkEnv, _, e =>
      Term.evalJ G body (Env.append (mkEnv _ e) env) PUnit.unit
  | _, _, _, _, _, _, _, _, .deep field member cases, env, mkEnv, fr, e =>
      FamilyMemberFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
        (FamW.memoNodeAt _ _ member.at_famFs (famFieldMemo field e)).2
  | _, _, _, _, _, _, _, _, .deepOuter field member cases, env, mkEnv, fr, e =>
      FamilyMemberFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
        (FamW.memoNodeAt _ _ member.at_famFs (famOuterFieldMemo field fr)).2

/-- The answer of the fold of a mutual family at a node of a given member: the branch of
    that member's constructor, field list or body. -/
def FamilyMemberFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {τ : TyWf} →
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer → (famIPF m).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .ctors cases, env, mkEnv, fr, x =>
      FamilyTaggedUnionFoldKCases.eval G cases env mkEnv fr x.1.1.val ⟨x.1.2, x.2⟩
  | _, _, _, _, _, _, _, _, .record br, env, mkEnv, fr, x =>
      FamilyFoldKBranch.eval G br env mkEnv fr x
  | _, _, _, _, _, _, _, _, .alias br, env, mkEnv, fr, x =>
      FamilyFoldKBranch.eval G br env mkEnv fr
        (IPFunctor.Obj.pair x ⟨PUnit.unit, fun p => PEmpty.elim p⟩)

/-- The answer of the fold of a member with constructors, at a node of constructor `t`. -/
def FamilyTaggedUnionFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAt (l.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, fr, 1, e =>
      FamilyFoldKBranch.eval G b1 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, fr, t + 2, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e
  | _, _, _, _, _, _, _, _, .skip b0 _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyCtorsWithPayloadFoldKCases.eval G rest env mkEnv fr t e

/-- `FamilyTaggedUnionFoldKCases.eval`, on the constructors that follow a field-less one. -/
def FamilyCtorsWithPayloadFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {c : CtorsWithPayload (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ c τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAtCP (c.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .here b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .here _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e
  | _, _, _, _, _, _, _, _, .skip b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyCtorsWithPayloadFoldKCases.eval G rest env mkEnv fr t e

/-- `FamilyTaggedUnionFoldKCases.eval`, on a plain list of constructors; past the end
    there is no node. -/
def FamilyTaggedUnionFoldKCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {cs : List (List (TyWfIn (n + 2)))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ cs τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (FamMemoAt ms₀ τ) →
    TyWf.Den τ
  | _, _, _, _, _, _, _, _, .nil, _, _, _, _, e => PEmpty.elim e.1
  | _, _, _, _, _, _, _, _, .cons b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e

/-- The answer of the fold of a mutual family at a node of member `i`: the branches of
    member `i`, found by walking the members in declaration order.  The node is given as a
    shape of whatever container is *the* container of member `i` of the members still to
    walk, so walking past a member costs no `cast`; past the last member there is no
    node. -/
def FamilyFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {τ : TyWf} →
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} → {k : Nat} →
    FamilyFoldKCases Sg n ms₀ bind Γ τ ms k → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (i : Nat) → (IPFunctor.at (famFs ms) i).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .nil, _, _, _, node => PEmpty.elim node.1
  | _, _, _, _, _, _, _, .cons c _, env, mkEnv, 0, node =>
      FamilyMemberFoldKCases.eval G c env mkEnv FamFrames.nil node
  | _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, i + 1, node =>
      FamilyFoldKCases.eval G rest env mkEnv i node

end

/-- **The value of a term** with no join points in scope: `Term.evalJ` with the empty
    environment of join points. -/
abbrev Term.eval {Sg : Sig} (G : GlobalEnv Sg.decls) {Γ : Ctx} {τ : TyWf}
    (t : Term Sg Γ τ) (env : Env Γ) : TyWf.Den τ :=
  Term.evalJ G t env PUnit.unit

/-! ## Running a closed term -/

/-- The value of a term of the empty context: a closed program, run against the values of
    the module's top-level declarations. -/
def Term.run {Sg : Sig} {τ : TyWf} (G : GlobalEnv Sg.decls) (t : Term Sg [] τ) : TyWf.Den τ :=
  Term.eval G t Env.nil

/-- The value of a term of the empty context of a module with no top-level
    declarations. -/
def Term.run' {τ : TyWf} (t : Term ⟨[], List.nodup_nil⟩ [] τ) : TyWf.Den τ :=
  Term.eval GlobalEnv.nil t Env.nil

end LeanScript

end
