module
public import LeanScript.Expr.Term

@[expose] public section

set_option autoImplicit false

/-!
# Renaming

A **renaming** `Ren Γ Δ` sends every variable of `Γ` to a variable of `Δ` at the same
type.  Renaming a term moves it to another context: the operation that lets a term be put
under more binders than it was written under (`Term.weaken`), which is what the
A-normalising builders of `LeanScript.Expr.Build` need when they name an operand with a
`let` and then write the rest of the term under it.

Renaming is structural on the term, and goes under a binder by `Ren.lift` (one binder),
`Ren.liftN` (a block `xs ++ Γ`) or `Ren.liftNat` (a block `natRecCtx τ k Γ`), the three
shapes a context of the grammar is extended by.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- A renaming from `Γ` to `Δ`: a variable of `Δ` for every variable of `Γ`, at the same
    type. -/
abbrev Ren (Γ Δ : Ctx) : Type := ∀ {τ : TyWf}, Γ ∋ τ → Δ ∋ τ

/-- The identity renaming. -/
def Ren.id {Γ : Ctx} : Ren Γ Γ := fun v => v

/-- The renaming that skips one binder: every variable of `Γ` is a variable of `σ :: Γ`,
    one binder further out. -/
def Ren.wk {Γ : Ctx} {σ : TyWf} : Ren Γ (σ :: Γ) := fun v => .tail v

/-- A renaming, under one more binder: the variable just bound is sent to itself. -/
def Ren.lift {Γ Δ : Ctx} {σ : TyWf} (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ) :=
  fun {_} v =>
    match v with
    | .head => .head
    | .tail v => .tail (ρ v)

/-- A renaming, under a block `xs` of binders. -/
def Ren.liftN {Γ Δ : Ctx} : (xs : List TyWf) → Ren Γ Δ → Ren (xs ++ Γ) (xs ++ Δ)
  | [], ρ => ρ
  | _ :: xs, ρ => Ren.lift (Ren.liftN xs ρ)

/-- A renaming, under a block of `k` answers of type `τ` (`natRecCtx`). -/
def Ren.liftNat {Γ Δ : Ctx} (τ : TyWf) : (k : Nat) → Ren Γ Δ →
    Ren (natRecCtx τ k Γ) (natRecCtx τ k Δ)
  | 0, ρ => ρ
  | k + 1, ρ => Ren.lift (Ren.liftNat τ k ρ)

/-- The renaming that skips a whole block `xs` of binders. -/
def Ren.wkN {Γ : Ctx} : (xs : List TyWf) → Ren Γ (xs ++ Γ)
  | [] => Ren.id
  | _ :: xs => fun v => .tail (Ren.wkN xs v)

variable {Sg : Sig}

/-- An atom — a variable — renamed: it is sent where the renaming sends it. -/
def Atom.rename {Γ Δ : Ctx} {τ : TyWf} (ρ : Ren Γ Δ) : Atom Γ τ → Atom Δ τ
  | .var v => .var (ρ v)

/-- A list of atoms, renamed. -/
def Args.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : {σs : List TyWf} → Args Sg Γ σs → Args Sg Δ σs
  | _, .nil => .nil
  | _, .cons a as => .cons (a.rename ρ) (Args.rename ρ as)

/-- The operands of a value of a member of a mutual family, renamed. -/
def FamilyMemberArgs.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) :
    {m : LeanFamMemberSchema TyWf} → FamilyMemberArgs Sg Γ m → FamilyMemberArgs Sg Δ m
  | _, .ctors l t ht fields => .ctors l t ht (fields.rename ρ)
  | _, .record fs fields => .record fs (fields.rename ρ)
  | _, .alias b value => .alias b (value.rename ρ)

mutual

/-- **A term, renamed**: moved to the context `Δ` along `ρ`.  Join points are not
    variables, so they are left as they are. -/
def Term.rename {Γ Δ : Ctx} {τ : TyWf} {J : JCtx} (ρ : Ren Γ Δ) :
    Term Sg Γ τ J → Term Sg Δ τ J
  | .ret a => .ret (a.rename ρ)
  | .letE c body => .letE (c.rename ρ) (body.rename (Ren.lift ρ))
  | .letJ jp body => .letJ (jp.rename (Ren.lift ρ)) (body.rename ρ)
  | .jump j a => .jump j (a.rename ρ)
  | .externCallChecked args call d fallback =>
      .externCallChecked (args.rename ρ) call d (fallback.rename ρ)
  | .bool_casesOn c t e => .bool_casesOn (c.rename ρ) (t.rename ρ) (e.rename ρ)
  | .nat_casesOn n z s => .nat_casesOn (n.rename ρ) (z.rename ρ) (s.rename (Ren.lift ρ))
  | .nat_rec k n base branch d =>
      .nat_rec k (n.rename ρ) (base.rename ρ) (branch.rename (Ren.lift (Ren.liftNat _ (k + 1) ρ))) d
  | .int_casesOn i a b => .int_casesOn (i.rename ρ) (a.rename (Ren.lift ρ)) (b.rename (Ren.lift ρ))
  | .uint8_casesOn v b => .uint8_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .uint16_casesOn v b => .uint16_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .uint32_casesOn v b => .uint32_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .uint64_casesOn v b => .uint64_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .int8_casesOn v b => .int8_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .int16_casesOn v b => .int16_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .int32_casesOn v b => .int32_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .int64_casesOn v b => .int64_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .char_casesOn v b => .char_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .stringPosRaw_casesOn v b => .stringPosRaw_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .stringPos_casesOn v b => .stringPos_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .substringRaw_casesOn v b =>
      .substringRaw_casesOn (v.rename ρ) (b.rename (Ren.lift (Ren.lift (Ren.lift ρ))))
  | .float_casesOn v b => .float_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .float32_casesOn v b => .float32_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .floatModel_casesOn v b => .floatModel_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .float32Model_casesOn v b => .float32Model_casesOn (v.rename ρ) (b.rename (Ren.lift ρ))
  | .array_casesOn a z s => .array_casesOn (a.rename ρ) (z.rename ρ) (s.rename (Ren.lift (Ren.lift ρ)))
  | .array_rec k a bases branch d =>
      .array_rec k (a.rename ρ) (bases.rename ρ)
        (branch.rename (Ren.lift (Ren.lift (Ren.liftNat _ (k + 1) ρ)))) d
  | .enum_casesOn e cases => .enum_casesOn (e.rename ρ) (cases.rename ρ)
  | .enum_casesOnWithDefault e cases dflt hk =>
      .enum_casesOnWithDefault (e.rename ρ) (cases.rename ρ) (dflt.rename ρ) hk
  | .record_casesOn (fs := fs) r body =>
      .record_casesOn (r.rename ρ) (body.rename (Ren.liftN fs.toList ρ))
  | .taggedUnion_casesOn v cases => .taggedUnion_casesOn (v.rename ρ) (cases.rename ρ)
  | .taggedUnion_casesOnWithDefault v cases dflt hk =>
      .taggedUnion_casesOnWithDefault (v.rename ρ) (cases.rename ρ) (dflt.rename ρ) hk
  | .recTaggedUnion_casesOn v cases => .recTaggedUnion_casesOn (v.rename ρ) (cases.rename ρ)
  | .recTaggedUnion_casesOnWithDefault v cases dflt hk =>
      .recTaggedUnion_casesOnWithDefault (v.rename ρ) (cases.rename ρ) (dflt.rename ρ) hk
  | .recTaggedUnion_rec k v cases d => .recTaggedUnion_rec k (v.rename ρ) (cases.rename ρ) d
  | .recObject_casesOn (fs := fs) (hwf := hwf) v body =>
      .recObject_casesOn (v.rename ρ)
        (body.rename (Ren.liftN (TyWf.recObjectUnfold fs hwf).toList ρ))
  | .recObject_rec (fs := fs) (hwf := hwf) (ρ := μ) k v body d =>
      .recObject_rec k (v.rename ρ)
        (body.rename (Ren.liftN (TyWf.recObjectRecBinders fs hwf μ k) ρ)) d
  | .recAlias_casesOn v body => .recAlias_casesOn (v.rename ρ) (body.rename (Ren.lift ρ))
  | .recAlias_rec (b := b) (hwf := hwf) (ρ := μ) k v body d =>
      .recAlias_rec k (v.rename ρ)
        (body.rename (Ren.liftN (TyWf.recAliasRecBinders b hwf μ k) ρ)) d
  | .mutualRecursiveFamily_casesOn v cases =>
      .mutualRecursiveFamily_casesOn (v.rename ρ) (cases.rename ρ)
  | .mutualRecursiveFamily_casesOnWithDefault v cases dflt =>
      .mutualRecursiveFamily_casesOnWithDefault (v.rename ρ) (cases.rename ρ) (dflt.rename ρ)
  | .mutualRecursiveFamily_rec k v cases d =>
      .mutualRecursiveFamily_rec k (v.rename ρ) (cases.rename ρ) d

/-- A computation, renamed. -/
def Comp.rename {Γ Δ : Ctx} {τ : TyWf} (ρ : Ren Γ Δ) : Comp Sg Γ τ → Comp Sg Δ τ
  | .global r => .global r
  | .bool_mk b => .bool_mk b
  | .nat_mk n => .nat_mk n
  | .int_mk i => .int_mk i
  | .bitvec_mk h v => .bitvec_mk h v
  | .uint8_mk v => .uint8_mk v
  | .uint16_mk v => .uint16_mk v
  | .uint32_mk v => .uint32_mk v
  | .uint64_mk v => .uint64_mk v
  | .int8_mk v => .int8_mk v
  | .int16_mk v => .int16_mk v
  | .int32_mk v => .int32_mk v
  | .int64_mk v => .int64_mk v
  | .char_mk c => .char_mk c
  | .string_mk s => .string_mk s
  | .stringPos_mk s p => .stringPos_mk s p
  | .stringPosRaw_mk p => .stringPosRaw_mk p
  | .substringRaw_mk s => .substringRaw_mk s
  | .stringSlice_mk s => .stringSlice_mk s
  | .float_mk x => .float_mk x
  | .float32_mk x => .float32_mk x
  | .floatModel_mk m => .floatModel_mk m
  | .float32Model_mk m => .float32Model_mk m
  | .lam body => .lam (body.rename (Ren.lift ρ))
  | .ap f a => .ap (f.rename ρ) (a.rename ρ)
  | .extern e => .extern e
  | .externCall args call => .externCall (args.rename ρ) call
  | .lazy_mk e => .lazy_mk (e.rename ρ)
  | .lazy_force a => .lazy_force (a.rename ρ)
  | .thunk_mk e => .thunk_mk (e.rename ρ)
  | .thunk_force a => .thunk_force (a.rename ρ)
  | .array_mk xs => .array_mk (xs.map (·.rename ρ))
  | .enum_mk s i => .enum_mk s i
  | .record_mk fs fields => .record_mk fs (fields.rename ρ)
  | .taggedUnion_mk l t ht fields => .taggedUnion_mk l t ht (fields.rename ρ)
  | .recTaggedUnion_mk l hwf t ht fields => .recTaggedUnion_mk l hwf t ht (fields.rename ρ)
  | .recObject_mk fs hwf fields => .recObject_mk fs hwf (fields.rename ρ)
  | .recAlias_mk b hwf value => .recAlias_mk b hwf (value.rename ρ)
  | .mutualRecursiveFamily_mk f hwf value =>
      .mutualRecursiveFamily_mk f hwf (value.rename ρ)

/-- The answers of a fold of an array to its short lists, renamed. -/
def ArrayRecBases.rename {Γ Δ : Ctx} {σ τ : TyWf} {k : Nat} (ρ : Ren Γ Δ) :
    ArrayRecBases Sg Γ σ τ k → ArrayRecBases Sg Δ σ τ k
  | .nil e => .nil (e.rename ρ)
  | .cons e more => .cons (e.rename ρ) (more.rename (Ren.lift ρ))

/-- The branches of a partial dispatch on a tagged union, renamed. -/
def TaggedUnionSomeCases.rename {Γ Δ : Ctx} {l : LeanTaggedUnionSchema TyWf} {τ : TyWf}
    {k lo : Nat} {J : JCtx} (ρ : Ren Γ Δ) :
    TaggedUnionSomeCases Sg Γ l τ k lo J → TaggedUnionSomeCases Sg Δ l τ k lo J
  | .last t ht branch hi => .last t ht (branch.rename (Ren.liftN _ ρ)) hi
  | .cons t ht branch rest hi =>
      .cons t ht (branch.rename (Ren.liftN _ ρ)) (rest.rename ρ) hi

/-- The branches of a dispatch on an enum, renamed. -/
def EnumCases.rename {Γ Δ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {J : JCtx} (ρ : Ren Γ Δ) :
    EnumCases Sg Γ τ s J → EnumCases Sg Δ τ s J
  | .three b0 b1 b2 => .three (b0.rename ρ) (b1.rename ρ) (b2.rename ρ)
  | .cons b rest => .cons (b.rename ρ) (rest.rename ρ)

/-- The branches of a partial dispatch on an enum, renamed. -/
def EnumSomeCases.rename {Γ Δ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {k lo : Nat}
    {J : JCtx} (ρ : Ren Γ Δ) : EnumSomeCases Sg Γ τ s k lo J → EnumSomeCases Sg Δ τ s k lo J
  | .last i branch hi => .last i (branch.rename ρ) hi
  | .cons i branch rest hi => .cons i (branch.rename ρ) (rest.rename ρ) hi

/-- The branches of a dispatch on, or a fold over, a sum type, renamed. -/
def TaggedUnionFoldCases.rename {ι : Type} {bind : List ι → List TyWf} {Γ Δ : Ctx}
    {l : LeanTaggedUnionSchema ι} {τ : TyWf} {J : JCtx} (ρ : Ren Γ Δ) :
    TaggedUnionFoldCases Sg ι bind Γ l τ J → TaggedUnionFoldCases Sg ι bind Δ l τ J
  | .payloadFirst b0 b1 rest =>
      .payloadFirst (b0.rename (Ren.liftN _ ρ)) (b1.rename (Ren.liftN _ ρ)) (rest.rename ρ)
  | .skip b0 rest => .skip (b0.rename (Ren.liftN _ ρ)) (rest.rename ρ)

/-- `TaggedUnionFoldCases.rename`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldCases.rename {ι : Type} {bind : List ι → List TyWf} {Γ Δ : Ctx}
    {c : CtorsWithPayload ι} {τ : TyWf} {J : JCtx} (ρ : Ren Γ Δ) :
    CtorsWithPayloadFoldCases Sg ι bind Γ c τ J → CtorsWithPayloadFoldCases Sg ι bind Δ c τ J
  | .here b rest => .here (b.rename (Ren.liftN _ ρ)) (rest.rename ρ)
  | .skip b rest => .skip (b.rename (Ren.liftN _ ρ)) (rest.rename ρ)

/-- `TaggedUnionFoldCases.rename`, on a plain list of constructors. -/
def TaggedUnionFoldCasesRest.rename {ι : Type} {bind : List ι → List TyWf} {Γ Δ : Ctx}
    {cs : List (List ι)} {τ : TyWf} {J : JCtx} (ρ : Ren Γ Δ) :
    TaggedUnionFoldCasesRest Sg ι bind Γ cs τ J → TaggedUnionFoldCasesRest Sg ι bind Δ cs τ J
  | .nil => .nil
  | .cons b rest => .cons (b.rename (Ren.liftN _ ρ)) (rest.rename ρ)

/-- One branch of a depth-`k` fold of a recursive tagged union, renamed. -/
def FoldKBranch.rename {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ Δ : Ctx} {fs : List (TyWfIn 1)} {τ : TyWf}
    {k : Nat} {outer : List (List (TyWfIn 1))} (ρ : Ren Γ Δ) :
    FoldKBranch Sg l₀ bind Γ fs τ k outer → FoldKBranch Sg l₀ bind Δ fs τ k outer
  | .here body => .here (body.rename (Ren.liftN _ ρ))
  | .deep sf cases => .deep sf (cases.rename (Ren.liftN _ ρ))
  | .deepOuter o cases => .deepOuter o (cases.rename (Ren.liftN _ ρ))

/-- The branches of a depth-`k` fold of a recursive tagged union, renamed. -/
def TaggedUnionFoldKCases.rename {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ Δ : Ctx} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn 1))} (ρ : Ren Γ Δ) :
    TaggedUnionFoldKCases Sg l₀ bind Γ l τ k outer →
      TaggedUnionFoldKCases Sg l₀ bind Δ l τ k outer
  | .payloadFirst b0 b1 rest => .payloadFirst (b0.rename ρ) (b1.rename ρ) (rest.rename ρ)
  | .skip b0 rest => .skip (b0.rename ρ) (rest.rename ρ)

/-- `TaggedUnionFoldKCases.rename`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldKCases.rename {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ Δ : Ctx} {c : CtorsWithPayload (TyWfIn 1)}
    {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn 1))} (ρ : Ren Γ Δ) :
    CtorsWithPayloadFoldKCases Sg l₀ bind Γ c τ k outer →
      CtorsWithPayloadFoldKCases Sg l₀ bind Δ c τ k outer
  | .here b rest => .here (b.rename ρ) (rest.rename ρ)
  | .skip b rest => .skip (b.rename ρ) (rest.rename ρ)

/-- `TaggedUnionFoldKCases.rename`, on a plain list of constructors. -/
def TaggedUnionFoldKCasesRest.rename {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ Δ : Ctx} {cs : List (List (TyWfIn 1))}
    {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn 1))} (ρ : Ren Γ Δ) :
    TaggedUnionFoldKCasesRest Sg l₀ bind Γ cs τ k outer →
      TaggedUnionFoldKCasesRest Sg l₀ bind Δ cs τ k outer
  | .nil => .nil
  | .cons b rest => .cons (b.rename ρ) (rest.rename ρ)

/-- The branches of a dispatch on a member of a mutual family, renamed. -/
def FamilyMemberCases.rename {Γ Δ : Ctx} {τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J : JCtx} (ρ : Ren Γ Δ) : FamilyMemberCases Sg Γ τ m J → FamilyMemberCases Sg Δ τ m J
  | .ctors cases => .ctors (cases.rename ρ)
  | .record (fs := fs) body => .record (body.rename (Ren.liftN fs.toList ρ))
  | .alias body => .alias (body.rename (Ren.lift ρ))

/-- The branches of a partial dispatch on a member of a mutual family, renamed. -/
def FamilyMemberSomeCases.rename {Γ Δ : Ctx} {τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J : JCtx} (ρ : Ren Γ Δ) :
    FamilyMemberSomeCases Sg Γ τ m J → FamilyMemberSomeCases Sg Δ τ m J
  | .ctors cases hk => .ctors (cases.rename ρ) hk

/-- The branches of a fold over one member of a mutual family, renamed. -/
def FamilyMemberFoldCases.rename {ι : Type} {bind : List ι → List TyWf} {Γ Δ : Ctx}
    {τ : TyWf} {m : LeanFamMemberSchema ι} (ρ : Ren Γ Δ) :
    FamilyMemberFoldCases Sg ι bind Γ τ m → FamilyMemberFoldCases Sg ι bind Δ τ m
  | .ctors cases => .ctors (cases.rename ρ)
  | .record body => .record (body.rename (Ren.liftN _ ρ))
  | .alias body => .alias (body.rename (Ren.liftN _ ρ))

/-- The branches of a fold over a mutual family, renamed. -/
def FamilyFoldCases.rename {ι : Type} {bind : List ι → List TyWf} {Γ Δ : Ctx}
    {τ : TyWf} {ms : List (LeanFamMemberSchema ι)} (ρ : Ren Γ Δ) :
    FamilyFoldCases Sg ι bind Γ τ ms → FamilyFoldCases Sg ι bind Δ τ ms
  | .nil => .nil
  | .cons m ms => .cons (m.rename ρ) (ms.rename ρ)

/-- One branch of a depth-`k` fold of a mutual family, renamed. -/
def FamilyFoldKBranch.rename {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx} {fs : List (TyWfIn (n + 2))}
    {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn (n + 2)))} (ρ : Ren Γ Δ) :
    FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer →
      FamilyFoldKBranch Sg n ms₀ bind Δ fs τ k outer
  | .here body => .here (body.rename (Ren.liftN _ ρ))
  | .deep field member cases => .deep field member (cases.rename (Ren.liftN _ ρ))
  | .deepOuter field member cases => .deepOuter field member (cases.rename (Ren.liftN _ ρ))

/-- The branches of a depth-`k` fold over one member of a mutual family, renamed. -/
def FamilyMemberFoldKCases.rename {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx} {τ : TyWf}
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} {k : Nat}
    {outer : List (List (TyWfIn (n + 2)))} (ρ : Ren Γ Δ) :
    FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k outer →
      FamilyMemberFoldKCases Sg n ms₀ bind Δ τ m k outer
  | .ctors cases => .ctors (cases.rename ρ)
  | .record br => .record (br.rename ρ)
  | .alias br => .alias (br.rename ρ)

/-- `TaggedUnionFoldKCases.rename`, for a member of a mutual family. -/
def FamilyTaggedUnionFoldKCases.rename {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} {τ : TyWf} {k : Nat}
    {outer : List (List (TyWfIn (n + 2)))} (ρ : Ren Γ Δ) :
    FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer →
      FamilyTaggedUnionFoldKCases Sg n ms₀ bind Δ l τ k outer
  | .payloadFirst b0 b1 rest => .payloadFirst (b0.rename ρ) (b1.rename ρ) (rest.rename ρ)
  | .skip b0 rest => .skip (b0.rename ρ) (rest.rename ρ)

/-- `CtorsWithPayloadFoldKCases.rename`, for a member of a mutual family. -/
def FamilyCtorsWithPayloadFoldKCases.rename {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx}
    {c : CtorsWithPayload (TyWfIn (n + 2))} {τ : TyWf} {k : Nat}
    {outer : List (List (TyWfIn (n + 2)))} (ρ : Ren Γ Δ) :
    FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ c τ k outer →
      FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Δ c τ k outer
  | .here b rest => .here (b.rename ρ) (rest.rename ρ)
  | .skip b rest => .skip (b.rename ρ) (rest.rename ρ)

/-- `TaggedUnionFoldKCasesRest.rename`, for a member of a mutual family. -/
def FamilyTaggedUnionFoldKCasesRest.rename {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx}
    {cs : List (List (TyWfIn (n + 2)))} {τ : TyWf} {k : Nat}
    {outer : List (List (TyWfIn (n + 2)))} (ρ : Ren Γ Δ) :
    FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ cs τ k outer →
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Δ cs τ k outer
  | .nil => .nil
  | .cons b rest => .cons (b.rename ρ) (rest.rename ρ)

/-- The branches of a depth-`k` fold of a mutual family, renamed. -/
def FamilyFoldKCases.rename {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ Δ : Ctx} {τ : TyWf}
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} {k : Nat} (ρ : Ren Γ Δ) :
    FamilyFoldKCases Sg n ms₀ bind Γ τ ms k → FamilyFoldKCases Sg n ms₀ bind Δ τ ms k
  | .nil => .nil
  | .cons m ms => .cons (m.rename ρ) (ms.rename ρ)

end

/-- A term, under one more binder it does not mention. -/
abbrev Term.weaken {Γ : Ctx} {σ τ : TyWf} (t : Term Sg Γ τ) : Term Sg (σ :: Γ) τ :=
  t.rename Ren.wk

end LeanScript

end
