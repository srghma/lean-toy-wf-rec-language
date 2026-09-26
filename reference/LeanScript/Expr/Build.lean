module
public import LeanScript.Expr.Rename
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# Building A-normal terms

`LeanScript.Term` is in A-normal form by construction, so a term whose operands are
themselves computations cannot be written with its constructors directly: each operand has
to be named by a `let` first.  The functions of this file do that naming.  Each of them is
named like the constructor of the *direct-style* grammar it stands for (`Term.ap`,
`Term.nat_casesOn`, `Term.record_mk`, …) and takes arbitrary terms as operands; it binds
every operand that is not already a variable with `Term.letE`, left to right, and applies the
computation step to the atoms it got.  The branches and bodies it is given are moved under
those `let`s by renaming (`LeanScript.Expr.Rename`).

So a term written in direct style,

    .ap (.global f) (.ap (.global g) (.nat_mk 1))

*is* the A-normal term

    .letE (.nat_mk 1)
      (.letE (.global g) (.letE (.ap (.var (v♯0)) (.var (v♯1)))
        (.letE (.global f) (.letE (.ap (.var (v♯0)) (.var (v♯1)))
          (.ret (.var (v♯0)))))))

— every operand is a variable: a declaration and a literal are steps like any other, and
are named by a `let` too (a step that reads no variable is named last, right before the
step that uses it: see "Closed steps" below); a variable operand is used as it is.  A step
that gives the value of the term is named as well, and the term returns that name
(`Term.ofComp`).  A `let` never binds a mere variable: naming a variable, as
`let x = y; body`, is `body` renamed (`Term.bind`).

The lists of operands of the direct style — `LeanScript.Spine`, `LeanScript.Terms` and
`LeanScript.FamilyMemberValue` — are here too; the grammar itself holds lists of atoms
(`LeanScript.Args`, `List Atom`, `LeanScript.FamilyMemberArgs`).
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- Renamings compose. -/
def Ren.comp {Γ Δ Θ : Ctx} (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) : Ren Γ Θ := fun v => ρ' (ρ v)

variable {Sg : Sig}

/-- The renaming that sends the variable just bound to `v`, and the others along `ρ`: what
    a copy `let x = v; body` would mean, done by renaming `body` instead, since a `let`
    never binds a mere variable. -/
def Ren.cons {Γ Δ : Ctx} {σ : TyWf} (v : Δ ∋ σ) (ρ : Ren Γ Δ) : Ren (σ :: Γ) Δ :=
  fun {_} w =>
    match w with
    | .head => v
    | .tail w => ρ w

/-- **One computation step, as a term**: `let x = c; ret x`.  A block ends by returning a
    variable, so this is the one way a step gives the value of a term. -/
abbrev Term.ofComp {Γ : Ctx} {τ : TyWf} {J : JCtx} (c : Comp Sg Γ τ) : Term Sg Γ τ J :=
  .letE c (.ret (.var .head))

/-! ## Sending the value of a term to a join point -/

/-- A join point of `J₀`, in the context of join points `J₀ ++ σ :: J`. -/
def JVar.embedL {x σ : TyWf} {J : JCtx} : {J₀ : JCtx} → J₀ ∋ x → (J₀ ++ σ :: J) ∋ x
  | _ :: _, .head => .head
  | _ :: _, .tail v => .tail (JVar.embedL v)

/-- The join point inserted after `J₀`, in the context `J₀ ++ σ :: J`. -/
def JVar.mid {σ : TyWf} {J : JCtx} : (J₀ : JCtx) → (J₀ ++ σ :: J) ∋ σ
  | [] => .head
  | _ :: J₀ => .tail (JVar.mid J₀)

/-- Where a fold's answer goes, once the value of the term it ends is sent to the join
    point `JVar.mid J₀`. -/
def Dest.toJump {ρ σ τ : TyWf} {J₀ J : JCtx} : Dest J₀ ρ σ → Dest (J₀ ++ σ :: J) ρ τ
  | .ret => .jump (JVar.mid J₀)
  | .jump j => .jump (JVar.embedL j)

mutual

/-- **Send the value of `t` to a join point.**  Every tail of `t` that gives the value of
    `t` — a last computation, or a fold that answers with it — is made to jump instead to
    the join point inserted after the join points `J₀` of `t`, whose parameter has the type
    `σ` of `t`.  The result answers with the type `τ` of that join point.  A dispatch sends
    each of its branches; the branches of a fold, and bodies of functions and delays, are
    left alone, since they do not give the value of `t`. -/
def Term.toJump {Γ : Ctx} {σ τ : TyWf} {J₀ J : JCtx} :
    Term Sg Γ σ J₀ → Term Sg Γ τ (J₀ ++ σ :: J)
  | .ret a => .jump (JVar.mid J₀) a
  | .letE c body => .letE c body.toJump
  | .letJ jp body => .letJ jp.toJump body.toJump
  | .jump j a => .jump (JVar.embedL j) a
  | .externCallChecked args call d fallback =>
      .externCallChecked args call d.toJump fallback.toJump
  | .bool_casesOn c t e => .bool_casesOn c t.toJump e.toJump
  | .nat_casesOn n z s => .nat_casesOn n z.toJump s.toJump
  | .nat_rec k n base branch d => .nat_rec k n base branch d.toJump
  | .int_casesOn i a b => .int_casesOn i a.toJump b.toJump
  | .uint8_casesOn v b => .uint8_casesOn v b.toJump
  | .uint16_casesOn v b => .uint16_casesOn v b.toJump
  | .uint32_casesOn v b => .uint32_casesOn v b.toJump
  | .uint64_casesOn v b => .uint64_casesOn v b.toJump
  | .int8_casesOn v b => .int8_casesOn v b.toJump
  | .int16_casesOn v b => .int16_casesOn v b.toJump
  | .int32_casesOn v b => .int32_casesOn v b.toJump
  | .int64_casesOn v b => .int64_casesOn v b.toJump
  | .char_casesOn v b => .char_casesOn v b.toJump
  | .stringPosRaw_casesOn v b => .stringPosRaw_casesOn v b.toJump
  | .stringPos_casesOn v b => .stringPos_casesOn v b.toJump
  | .substringRaw_casesOn v b => .substringRaw_casesOn v b.toJump
  | .float_casesOn v b => .float_casesOn v b.toJump
  | .float32_casesOn v b => .float32_casesOn v b.toJump
  | .floatModel_casesOn v b => .floatModel_casesOn v b.toJump
  | .float32Model_casesOn v b => .float32Model_casesOn v b.toJump
  | .array_casesOn a z s => .array_casesOn a z.toJump s.toJump
  | .array_rec k a bases branch d => .array_rec k a bases branch d.toJump
  | .enum_casesOn e cases => .enum_casesOn e cases.toJump
  | .enum_casesOnWithDefault e cases dflt hk =>
      .enum_casesOnWithDefault e cases.toJump dflt.toJump hk
  | .record_casesOn r body => .record_casesOn r body.toJump
  | .taggedUnion_casesOn v cases => .taggedUnion_casesOn v cases.toJump
  | .taggedUnion_casesOnWithDefault v cases dflt hk =>
      .taggedUnion_casesOnWithDefault v cases.toJump dflt.toJump hk
  | .recTaggedUnion_casesOn v cases => .recTaggedUnion_casesOn v cases.toJump
  | .recTaggedUnion_casesOnWithDefault v cases dflt hk =>
      .recTaggedUnion_casesOnWithDefault v cases.toJump dflt.toJump hk
  | .recTaggedUnion_rec k v cases d => .recTaggedUnion_rec k v cases d.toJump
  | .recObject_casesOn v body => .recObject_casesOn v body.toJump
  | .recObject_rec k v body d => .recObject_rec k v body d.toJump
  | .recAlias_casesOn v body => .recAlias_casesOn v body.toJump
  | .recAlias_rec k v body d => .recAlias_rec k v body d.toJump
  | .mutualRecursiveFamily_casesOn v cases => .mutualRecursiveFamily_casesOn v cases.toJump
  | .mutualRecursiveFamily_casesOnWithDefault v cases dflt =>
      .mutualRecursiveFamily_casesOnWithDefault v cases.toJump dflt.toJump
  | .mutualRecursiveFamily_rec k v cases d => .mutualRecursiveFamily_rec k v cases d.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on a tagged union. -/
def TaggedUnionSomeCases.toJump {Γ : Ctx} {l : LeanTaggedUnionSchema TyWf} {σ τ : TyWf}
    {k lo : Nat} {J₀ J : JCtx} :
    TaggedUnionSomeCases Sg Γ l σ k lo J₀ → TaggedUnionSomeCases Sg Γ l τ k lo (J₀ ++ σ :: J)
  | .last t ht branch hi => .last t ht branch.toJump hi
  | .cons t ht branch rest hi => .cons t ht branch.toJump rest.toJump hi

/-- `Term.toJump`, on each branch of a dispatch on an enum. -/
def EnumCases.toJump {Γ : Ctx} {σ τ : TyWf} {s : LeanEnumSchema} {J₀ J : JCtx} :
    EnumCases Sg Γ σ s J₀ → EnumCases Sg Γ τ s (J₀ ++ σ :: J)
  | .three b0 b1 b2 => .three b0.toJump b1.toJump b2.toJump
  | .cons b rest => .cons b.toJump rest.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on an enum. -/
def EnumSomeCases.toJump {Γ : Ctx} {σ τ : TyWf} {s : LeanEnumSchema} {k lo : Nat}
    {J₀ J : JCtx} : EnumSomeCases Sg Γ σ s k lo J₀ → EnumSomeCases Sg Γ τ s k lo (J₀ ++ σ :: J)
  | .last i branch hi => .last i branch.toJump hi
  | .cons i branch rest hi => .cons i branch.toJump rest.toJump hi

/-- `Term.toJump`, on each branch of a dispatch on a sum type. -/
def TaggedUnionFoldCases.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema ι} {σ τ : TyWf} {J₀ J : JCtx} :
    TaggedUnionFoldCases Sg ι bind Γ l σ J₀ → TaggedUnionFoldCases Sg ι bind Γ l τ (J₀ ++ σ :: J)
  | .payloadFirst b0 b1 rest => .payloadFirst b0.toJump b1.toJump rest.toJump
  | .skip b0 rest => .skip b0.toJump rest.toJump

/-- `TaggedUnionFoldCases.toJump`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldCases.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {c : CtorsWithPayload ι} {σ τ : TyWf} {J₀ J : JCtx} :
    CtorsWithPayloadFoldCases Sg ι bind Γ c σ J₀ →
      CtorsWithPayloadFoldCases Sg ι bind Γ c τ (J₀ ++ σ :: J)
  | .here b rest => .here b.toJump rest.toJump
  | .skip b rest => .skip b.toJump rest.toJump

/-- `TaggedUnionFoldCases.toJump`, on a plain list of constructors. -/
def TaggedUnionFoldCasesRest.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {cs : List (List ι)} {σ τ : TyWf} {J₀ J : JCtx} :
    TaggedUnionFoldCasesRest Sg ι bind Γ cs σ J₀ →
      TaggedUnionFoldCasesRest Sg ι bind Γ cs τ (J₀ ++ σ :: J)
  | .nil => .nil
  | .cons b rest => .cons b.toJump rest.toJump

/-- `Term.toJump`, on each branch of a dispatch on a member of a mutual family. -/
def FamilyMemberCases.toJump {Γ : Ctx} {σ τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J₀ J : JCtx} : FamilyMemberCases Sg Γ σ m J₀ → FamilyMemberCases Sg Γ τ m (J₀ ++ σ :: J)
  | .ctors cases => .ctors cases.toJump
  | .record body => .record body.toJump
  | .alias body => .alias body.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on a member of a mutual family. -/
def FamilyMemberSomeCases.toJump {Γ : Ctx} {σ τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J₀ J : JCtx} :
    FamilyMemberSomeCases Sg Γ σ m J₀ → FamilyMemberSomeCases Sg Γ τ m (J₀ ++ σ :: J)
  | .ctors cases hk => .ctors cases.toJump hk

end

/-! ## Naming an operand -/

/-- **Name the value of `t`** and go on with an atom for it.  The continuation `k` is
    given the atom in a context `Δ` that extends `Γ`, together with the renaming from `Γ`
    into `Δ`, so that what it writes after can be moved there.

    * If `t` is already a variable nothing is bound and `k` gets it in `Γ` itself.
    * If `t` is a block that returns a variable — the one shape a computation has — its
      `let`s are floated out and `k` gets that variable.
    * If `t` ends in a dispatch or a fold — which cannot be bound by a `let` — what `k`
      writes becomes a **join point**, and every tail of `t` jumps to it with the value it
      gives (`Term.toJump`).  `k` is used once in every case, so nothing is duplicated. -/
def Term.bindAtom {Γ : Ctx} {σ τ : TyWf} {J : JCtx} (t : Term Sg Γ σ)
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) : Term Sg Γ τ J :=
  go t rfl k
where
  /-- `Term.bindAtom`, by structural recursion: the join points of the term being bound
      are a variable `J₀`, pinned to `[]` by an equation, so that the recursion is on a
      family whose indices are variables (and the builders reduce by `rfl`). -/
  go {Γ : Ctx} {J₀ : JCtx} :
      Term Sg Γ σ J₀ → J₀ = [] → (∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) →
      Term Sg Γ τ J
    | .ret a, _, k => k Ren.id a
    | .letE c t, h, k => .letE c (go t h fun ρ a => k (Ren.comp ρ Ren.wk) a)
    | t, h, k => .letJ (k Ren.wk (.var .head)) ((h ▸ t : Term Sg Γ σ).toJump (J₀ := []))

/-- **`let x = t; body`**, for any term `t`: the `let`s of `t` are floated out in front,
    and the variable `t` ends by returning stands for `x` in `body` (`body` is renamed, so
    no copy `let x = y` is written); if `t` ends in a dispatch or a fold, `body` becomes a
    join point that every tail of `t` jumps to. -/
def Term.bind {Γ₀ : Ctx} {σ τ : TyWf} {J : JCtx} (t : Term Sg Γ₀ σ)
    (body : Term Sg (σ :: Γ₀) τ J) : Term Sg Γ₀ τ J :=
  go t rfl Ren.id
where
  /-- `Term.bind`, by structural recursion, as `Term.bindAtom.go`.  The renaming `ρ` from
      the context of `body` to the context reached is accumulated, so that `body` is
      renamed once, when it is put in place. -/
  go {Γ : Ctx} {J₀ : JCtx} :
      Term Sg Γ σ J₀ → J₀ = [] → Ren Γ₀ Γ → Term Sg Γ τ J
    | .ret (.var v), _, ρ => body.rename (Ren.cons v ρ)
    | .letE c t, h, ρ => .letE c (go t h (Ren.comp Ren.wk ρ))
    | t, h, ρ => .letJ (body.rename (Ren.lift ρ)) ((h ▸ t : Term Sg Γ σ).toJump (J₀ := []))

/-- `Term.bindAtom`, with a shortcut: if `t` is already an atom, `here` gets it as it is,
    so that what `k` would have renamed along the identity is not renamed at all.  This
    is what keeps a dispatch on a variable — the common case — exactly the term one would
    write by hand. -/
def Term.bindAtomOr {Γ : Ctx} {σ τ : TyWf} {J : JCtx} (t : Term Sg Γ σ)
    (here : Atom Γ σ → Term Sg Γ τ J)
    (k : ∀ {Δ : Ctx}, Ren Γ Δ → Atom Δ σ → Term Sg Δ τ J) : Term Sg Γ τ J :=
  match t with
  | .ret a => here a
  | t => t.bindAtom k

/-- `let x = e; body` in direct style, with no join point in scope: `Term.bind`. -/
def Term.letE' {Γ : Ctx} {σ τ : TyWf} (e : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ) :
    Term Sg Γ τ :=
  e.bind body

/-! ## Closed steps

A declaration, a literal, an extern applied to values and a constructor of an enum are
steps that read no variable.  Where one of them is an operand, the builders bind it
**last**, right before the step that uses it: the operands after it are then not moved
under its `let`, which keeps the terms they build from being renamed over and over.  (The
language is pure and total, so the order of the `let`s does not change the value.) -/

/-- The empty renaming: the empty context has no variable. -/
def Ren.nil {Δ : Ctx} : Ren [] Δ := fun v => nomatch v

/-- The step `c`, if it reads no variable, written in the empty context. -/
def Comp.closed? {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option (Comp Sg [] τ)
  | .global r => some (.global r)
  | .bool_mk b => some (.bool_mk b)
  | .nat_mk n => some (.nat_mk n)
  | .int_mk i => some (.int_mk i)
  | .bitvec_mk h v => some (.bitvec_mk h v)
  | .uint8_mk v => some (.uint8_mk v)
  | .uint16_mk v => some (.uint16_mk v)
  | .uint32_mk v => some (.uint32_mk v)
  | .uint64_mk v => some (.uint64_mk v)
  | .int8_mk v => some (.int8_mk v)
  | .int16_mk v => some (.int16_mk v)
  | .int32_mk v => some (.int32_mk v)
  | .int64_mk v => some (.int64_mk v)
  | .char_mk c => some (.char_mk c)
  | .string_mk s => some (.string_mk s)
  | .stringPos_mk s p => some (.stringPos_mk s p)
  | .stringPosRaw_mk p => some (.stringPosRaw_mk p)
  | .substringRaw_mk s => some (.substringRaw_mk s)
  | .stringSlice_mk s => some (.stringSlice_mk s)
  | .float_mk x => some (.float_mk x)
  | .float32_mk x => some (.float32_mk x)
  | .floatModel_mk m => some (.floatModel_mk m)
  | .float32Model_mk m => some (.float32Model_mk m)
  | .extern e => some (.extern e)
  | .enum_mk s i => some (.enum_mk s i)
  | _ => none

/-- The step `c`, if the term is `let x = c; ret x` and `c` reads no variable. -/
def Term.closedStep? {Γ : Ctx} {σ : TyWf} : Term Sg Γ σ → Option (Comp Sg [] σ)
  | .letE c (.ret (.var .head)) => c.closed?
  | _ => none

/-! ## Redexes taken apart while building

Three shapes of operand have a value the builder can see without running anything, and
the builders use it instead of naming the operand:

* **an abstraction applied to an argument** — `Term.ap (Term.lam body) a` is
  `let x = a; body` (`Term.bind`), with no closure built and no call made.  This is the
  shape a translated instance method or local function takes once it is applied, so it is
  the redex that shrinks translated terms the most;
* **a dispatch on a boolean literal** — `if true then t else e` is `t`;
* **a dispatch on a natural-number literal** — `match 0 with …` is its zero branch, and
  `match m + 1 with …` binds the literal `m` in the successor branch.

The language is pure and total, so each of these has the value of the term it replaces:
`Term.eval_ap`, `Term.eval_bool_casesOn'` and `Term.eval_nat_casesOn'` in
`LeanScript.BuildEvalFacts.Builders` hold for every input, redex or not. -/

/-- A function type determines its domain and its codomain. -/
theorem TyWf.fn_inj {σ₁ τ₁ σ τ : TyWf} (h : TyWf.fn σ₁ τ₁ = TyWf.fn σ τ) : σ₁ = σ ∧ τ₁ = τ := by
  have h' : Ty.shape (.fn σ₁.toTy τ₁.toTy) = Ty.shape (.fn σ.toTy τ.toTy) :=
    congrArg TyWf.toTy h
  injection h' with h'
  injection h' with h1 h2
  exact ⟨TyWf.ext h1, TyWf.ext h2⟩

/-- The body of the step `c`, if it is an abstraction, at the domain and codomain the
    equation `h` names. -/
def Comp.lamBody? {Γ : Ctx} : {ρ : TyWf} → Comp Sg Γ ρ → {σ τ : TyWf} → ρ = TyWf.fn σ τ →
    Option (Term Sg (σ :: Γ) τ)
  | _, .lam body, _, _, h => some (cast (by obtain ⟨rfl, rfl⟩ := TyWf.fn_inj h; rfl) body)
  | _, _, _, _, _ => none

/-- The body of the term, if it is an abstraction: `let f = fun x => body; ret f`. -/
def Term.lamBody? {Γ : Ctx} {σ τ : TyWf} : Term Sg Γ (TyWf.fn σ τ) → Option (Term Sg (σ :: Γ) τ)
  | .letE c (.ret (.var .head)) => c.lamBody? rfl
  | _ => none

/-- The value of the step `c`, if it is a boolean literal. -/
def Comp.boolLit? {Γ : Ctx} : {ρ : TyWf} → Comp Sg Γ ρ → Option Bool
  | _, .bool_mk b => some b
  | _, _ => none

/-- The value of the term, if it is a boolean literal. -/
def Term.boolLit? {Γ : Ctx} {ρ : TyWf} : Term Sg Γ ρ → Option Bool
  | .letE c (.ret (.var .head)) => c.boolLit?
  | _ => none

/-- The value of the step `c`, if it is a natural-number literal. -/
def Comp.natLit? {Γ : Ctx} : {ρ : TyWf} → Comp Sg Γ ρ → Option Nat
  | _, .nat_mk n => some n
  | _, _ => none

/-- The value of the term, if it is a natural-number literal. -/
def Term.natLit? {Γ : Ctx} {ρ : TyWf} : Term Sg Γ ρ → Option Nat
  | .letE c (.ret (.var .head)) => c.natLit?
  | _ => none

/-! ## Lists of operands, in direct style -/

/-- The elements of an array, in direct style: any number of terms, all of one type. -/
inductive Terms (Sg : Sig) : Ctx → TyWf → Type 1
  /-- No more elements. -/
  | nil : ∀ {Γ τ}, Terms Sg Γ τ
  /-- One more element, at the front. -/
  | cons : ∀ {Γ τ}, Term Sg Γ τ → Terms Sg Γ τ → Terms Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    fields of a constructor, in direct style. -/
inductive Spine (Sg : Sig) : Ctx → List TyWf → Type 1
  /-- No more arguments. -/
  | nil : ∀ {Γ}, Spine Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- A value of one member of a mutual recursive family, in direct style: its fields (or
    its body) are terms. -/
inductive FamilyMemberValue (Sg : Sig) : Ctx → LeanFamMemberSchema TyWf → Type 1
  /-- A member with constructors: constructor `t` of it, and that constructor's
      fields. -/
  | ctors {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
      FamilyMemberValue Sg Γ (.ctors l)
  /-- A record member: its fields, in declaration order. -/
  | record {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Spine Sg Γ fs.toList) :
      FamilyMemberValue Sg Γ (.record fs)
  /-- A newtype member: a value of its body, whose wrapper is erased. -/
  | alias {Γ : Ctx} (b : TyWf) (value : Term Sg Γ b) : FamilyMemberValue Sg Γ (.alias b)

/-- Name every element of a list, left to right, after moving it along `ρ`, and go on with
    the atoms. -/
def Terms.bindAtoms {Γ Δ₀ : Ctx} {σ τ : TyWf} :
    Terms Sg Γ σ → Ren Γ Δ₀ →
    (∀ {Δ : Ctx}, Ren Δ₀ Δ → List (Atom Δ σ) → Term Sg Δ τ) → Term Sg Δ₀ τ
  | .nil, _, k => k Ren.id []
  | .cons t ts, ρ, k =>
      match t.closedStep? with
      | some c =>
          ts.bindAtoms ρ fun ρ₂ as =>
            .letE (c.rename Ren.nil)
              (k (Ren.comp Ren.wk ρ₂) (.var .head :: as.map (·.rename Ren.wk)))
      | none =>
          (t.rename ρ).bindAtom fun ρ₁ a =>
            ts.bindAtoms (Ren.comp ρ₁ ρ) fun ρ₂ as => k (Ren.comp ρ₂ ρ₁) (a.rename ρ₂ :: as)

/-- Name every term of a spine, left to right, after moving it along `ρ`, and go on with
    the atoms. -/
def Spine.bindArgs {Γ Δ₀ : Ctx} {τ : TyWf} :
    {σs : List TyWf} → Spine Sg Γ σs → Ren Γ Δ₀ →
    (∀ {Δ : Ctx}, Ren Δ₀ Δ → Args Sg Δ σs → Term Sg Δ τ) → Term Sg Δ₀ τ
  | _, .nil, _, k => k Ren.id .nil
  | _, .cons t ts, ρ, k =>
      match t.closedStep? with
      | some c =>
          ts.bindArgs ρ fun ρ₂ as =>
            .letE (c.rename Ren.nil) (k (Ren.comp Ren.wk ρ₂) (.cons (.var .head) (as.rename Ren.wk)))
      | none =>
          (t.rename ρ).bindAtom fun ρ₁ a =>
            ts.bindArgs (Ren.comp ρ₁ ρ) fun ρ₂ as => k (Ren.comp ρ₂ ρ₁) (.cons (a.rename ρ₂) as)

/-- The atoms of a spine that holds only atoms, and `none` otherwise. -/
def Spine.atoms? {Γ : Ctx} : {σs : List TyWf} → Spine Sg Γ σs → Option (Args Sg Γ σs)
  | _, .nil => some .nil
  | _, .cons (.ret a) ts => (ts.atoms?).map (.cons a)
  | _, .cons _ _ => none

/-- Name the operands of a value of a member of a mutual family, and go on with them. -/
def FamilyMemberValue.bindArgs {Γ : Ctx} {m : LeanFamMemberSchema TyWf} {τ : TyWf} :
    FamilyMemberValue Sg Γ m →
    (∀ {Δ : Ctx}, Ren Γ Δ → FamilyMemberArgs Sg Δ m → Term Sg Δ τ) → Term Sg Γ τ
  | .ctors l t ht fields, k => fields.bindArgs Ren.id fun ρ as => k ρ (.ctors l t ht as)
  | .record fs fields, k => fields.bindArgs Ren.id fun ρ as => k ρ (.record fs as)
  | .alias b value, k => value.bindAtom fun ρ a => k ρ (.alias b a)

/-! ## The direct-style forms -/

/-- A variable of `Γ`. -/
abbrev Term.var {Γ : Ctx} {τ : TyWf} (v : Γ ∋ τ) : Term Sg Γ τ := .ret (.var v)

/-- A reference to a top-level declaration of the module's signature. -/
abbrev Term.global {Γ : Ctx} {τ : TyWf} (r : GlobalRef Sg.decls τ) : Term Sg Γ τ :=
  .ofComp (.global r)

/-- An atom, as a term. -/
abbrev Term.atom {Γ : Ctx} {τ : TyWf} (a : Atom Γ τ) : Term Sg Γ τ := .ret a

/-- A boolean literal. -/
abbrev Term.bool_mk {Γ : Ctx} (b : Bool) : Term Sg Γ (.prim .bool) := .ofComp (.bool_mk b)
/-- A natural number literal. -/
abbrev Term.nat_mk {Γ : Ctx} (n : Nat) : Term Sg Γ (.prim .nat) := .ofComp (.nat_mk n)
/-- An integer literal. -/
abbrev Term.int_mk {Γ : Ctx} (i : Int) : Term Sg Γ (.prim .int) := .ofComp (.int_mk i)
/-- A bit-vector literal, of a positive width. -/
abbrev Term.bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
    Term Sg Γ (.prim (.bitvec n h_positive)) := .ofComp (.bitvec_mk h_positive v)
/-- An 8-bit unsigned literal. -/
abbrev Term.uint8_mk {Γ : Ctx} (v : UInt8) : Term Sg Γ (.prim .uint8) := .ofComp (.uint8_mk v)
/-- A 16-bit unsigned literal. -/
abbrev Term.uint16_mk {Γ : Ctx} (v : UInt16) : Term Sg Γ (.prim .uint16) :=
  .ofComp (.uint16_mk v)
/-- A 32-bit unsigned literal. -/
abbrev Term.uint32_mk {Γ : Ctx} (v : UInt32) : Term Sg Γ (.prim .uint32) :=
  .ofComp (.uint32_mk v)
/-- A 64-bit unsigned literal. -/
abbrev Term.uint64_mk {Γ : Ctx} (v : UInt64) : Term Sg Γ (.prim .uint64) :=
  .ofComp (.uint64_mk v)
/-- An 8-bit signed literal. -/
abbrev Term.int8_mk {Γ : Ctx} (v : Int8) : Term Sg Γ (.prim .int8) := .ofComp (.int8_mk v)
/-- A 16-bit signed literal. -/
abbrev Term.int16_mk {Γ : Ctx} (v : Int16) : Term Sg Γ (.prim .int16) := .ofComp (.int16_mk v)
/-- A 32-bit signed literal. -/
abbrev Term.int32_mk {Γ : Ctx} (v : Int32) : Term Sg Γ (.prim .int32) := .ofComp (.int32_mk v)
/-- A 64-bit signed literal. -/
abbrev Term.int64_mk {Γ : Ctx} (v : Int64) : Term Sg Γ (.prim .int64) := .ofComp (.int64_mk v)
/-- A character literal. -/
abbrev Term.char_mk {Γ : Ctx} (c : Char) : Term Sg Γ (.prim .char) := .ofComp (.char_mk c)
/-- A string literal. -/
abbrev Term.string_mk {Γ : Ctx} (s : String) : Term Sg Γ (.prim .string) :=
  .ofComp (.string_mk s)
/-- A literal position into the string `s`. -/
abbrev Term.stringPos_mk {Γ : Ctx} (s : String) (p : String.Pos s) :
    Term Sg Γ (.prim (.stringPos s)) := .ofComp (.stringPos_mk s p)
/-- A literal unchecked byte position. -/
abbrev Term.stringPosRaw_mk {Γ : Ctx} (p : String.Pos.Raw) : Term Sg Γ (.prim .stringPosRaw) :=
  .ofComp (.stringPosRaw_mk p)
/-- A literal unchecked substring. -/
abbrev Term.substringRaw_mk {Γ : Ctx} (s : Substring.Raw) : Term Sg Γ (.prim .substringRaw) :=
  .ofComp (.substringRaw_mk s)
/-- A literal string slice. -/
abbrev Term.stringSlice_mk {Γ : Ctx} (s : String.Slice) : Term Sg Γ (.prim .stringSlice) :=
  .ofComp (.stringSlice_mk s)
/-- A 64-bit floating point literal. -/
abbrev Term.float_mk {Γ : Ctx} (x : Float) : Term Sg Γ (.prim .float) := .ofComp (.float_mk x)
/-- A 32-bit floating point literal. -/
abbrev Term.float32_mk {Γ : Ctx} (x : Float32) : Term Sg Γ (.prim .float32) :=
  .ofComp (.float32_mk x)
/-- A literal of the model of a 64-bit float. -/
abbrev Term.floatModel_mk {Γ : Ctx} (m : Float.Model) : Term Sg Γ (.prim .floatModel) :=
  .ofComp (.floatModel_mk m)
/-- A literal of the model of a 32-bit float. -/
abbrev Term.float32Model_mk {Γ : Ctx} (m : Float32.Model) : Term Sg Γ (.prim .float32Model) :=
  .ofComp (.float32Model_mk m)

/-- `fun x => body`. -/
abbrev Term.lam {Γ : Ctx} {σ τ : TyWf} (body : Term Sg (σ :: Γ) τ) : Term Sg Γ (σ ⇒ τ) :=
  .ofComp (.lam body)

/-- `f a`, for any terms `f` and `a`.  If `f` is an abstraction `fun x => body`, this is
    `let x = a; body` (a β-reduction: no closure is built).  Otherwise both are named, `f`
    first — unless `f` is a closed step (a declaration, typically), which is named last. -/
def Term.ap {Γ : Ctx} {σ τ : TyWf} (f : Term Sg Γ (σ ⇒ τ)) (a : Term Sg Γ σ) : Term Sg Γ τ :=
  match f.lamBody? with
  | some body => a.bind body
  | none =>
  match f.closedStep? with
  | some c =>
      a.bindAtom fun _ aa =>
        .letE (c.rename Ren.nil) (.ofComp (.ap (.var .head) (aa.rename Ren.wk)))
  | none =>
      f.bindAtomOr
        (fun fa => a.bindAtomOr (fun aa => .ofComp (.ap fa aa))
          fun ρ' aa => .ofComp (.ap (fa.rename ρ') aa))
        fun ρ fa => (a.rename ρ).bindAtom fun ρ' aa => .ofComp (.ap (fa.rename ρ') aa)

/-- A pure extern of `Init` applied to values. -/
abbrev Term.extern {Γ : Ctx} {τ : TyWf} (e : Extern τ) : Term Sg Γ τ := .ofComp (.extern e)

/-- A pure extern of `Init` applied to the terms of its arguments. -/
def Term.externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun _ as => .ofComp (.externCall as call)

/-- A pure extern of `Init` that takes a proof, applied to the terms of its arguments. -/
def Term.externCallChecked' {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun ρ as => (.externCallChecked as call .ret (fallback.rename ρ))

/-- `if c then t else e`; on a literal condition, the branch it selects. -/
def Term.bool_casesOn' {Γ : Ctx} {τ : TyWf} (c : Term Sg Γ (.prim .bool))
    (t e : Term Sg Γ τ) : Term Sg Γ τ :=
  match c.boolLit? with
  | some true => t
  | some false => e
  | none =>
      c.bindAtomOr (fun a => (.bool_casesOn a t e))
        fun ρ a => (.bool_casesOn a (t.rename ρ) (e.rename ρ))

/-- `match n with | 0 => … | k + 1 => …`; on a literal, the branch it selects. -/
def Term.nat_casesOn' {Γ : Ctx} {τ : TyWf} (n : Term Sg Γ (.prim .nat)) (z : Term Sg Γ τ)
    (s : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  match n.natLit? with
  | some 0 => z
  | some (m + 1) => .letE (.nat_mk m) s
  | none =>
      n.bindAtomOr (fun a => (.nat_casesOn a z s))
        fun ρ a => (.nat_casesOn a (z.rename ρ) (s.rename (Ren.lift ρ)))

/-- `Nat.rec` that descends `k + 1` steps. -/
def Term.nat_rec' {Γ : Ctx} {τ : TyWf} (k : Nat := 0) (n : Term Sg Γ (.prim .nat))
    (base : Spine Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  n.bindAtomOr
    (fun a => match base.atoms? with
      | some bs => .nat_rec k a bs branch .ret
      | none =>
          base.bindArgs Ren.id fun ρ' bs =>
            (.nat_rec k (a.rename ρ') bs
              (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) ρ'))) .ret))
    fun ρ a =>
    base.bindArgs ρ fun ρ' bs =>
      (.nat_rec k (a.rename ρ') bs
        (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) (Ren.comp ρ' ρ)))) .ret)

/-- `match i with | .ofNat n => … | .negSucc n => …`. -/
def Term.int_casesOn' {Γ : Ctx} {τ : TyWf} (i : Term Sg Γ (.prim .int))
    (ofNat negSucc : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  i.bindAtomOr (fun a =>
    (.int_casesOn a ofNat negSucc))
    fun ρ a =>
    (.int_casesOn a (ofNat.rename (Ren.lift ρ)) (negSucc.rename (Ren.lift ρ)))

/-- Take an 8-bit unsigned value apart. -/
def Term.uint8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint8))
    (b : Term Sg (TyWf.prim (.bitvec 8) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint8_casesOn a b))
    fun ρ a => (.uint8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit unsigned value apart. -/
def Term.uint16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint16))
    (b : Term Sg (TyWf.prim (.bitvec 16) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint16_casesOn a b))
    fun ρ a => (.uint16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit unsigned value apart. -/
def Term.uint32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint32))
    (b : Term Sg (TyWf.prim (.bitvec 32) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint32_casesOn a b))
    fun ρ a => (.uint32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit unsigned value apart. -/
def Term.uint64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint64))
    (b : Term Sg (TyWf.prim (.bitvec 64) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint64_casesOn a b))
    fun ρ a => (.uint64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an 8-bit signed value apart. -/
def Term.int8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int8))
    (b : Term Sg (TyWf.prim .uint8 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int8_casesOn a b))
    fun ρ a => (.int8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit signed value apart. -/
def Term.int16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int16))
    (b : Term Sg (TyWf.prim .uint16 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int16_casesOn a b))
    fun ρ a => (.int16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit signed value apart. -/
def Term.int32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int32))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int32_casesOn a b))
    fun ρ a => (.int32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit signed value apart. -/
def Term.int64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int64))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int64_casesOn a b))
    fun ρ a => (.int64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a character apart. -/
def Term.char_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .char))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.char_casesOn a b))
    fun ρ a => (.char_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked position apart. -/
def Term.stringPosRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .stringPosRaw))
    (b : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.stringPosRaw_casesOn a b))
    fun ρ a => (.stringPosRaw_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a checked position apart. -/
def Term.stringPos_casesOn' {Γ : Ctx} {τ : TyWf} {s : String}
    (v : Term Sg Γ (.prim (.stringPos s)))
    (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.stringPos_casesOn a b))
    fun ρ a => (.stringPos_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked substring apart. -/
def Term.substringRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .substringRaw))
    (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.substringRaw_casesOn a b))
    fun ρ a =>
    (.substringRaw_casesOn a (b.rename (Ren.lift (Ren.lift (Ren.lift ρ)))))

/-- Take a 64-bit float apart. -/
def Term.float_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float))
    (b : Term Sg (TyWf.prim .floatModel :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float_casesOn a b))
    fun ρ a => (.float_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit float apart. -/
def Term.float32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32))
    (b : Term Sg (TyWf.prim .float32Model :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float32_casesOn a b))
    fun ρ a => (.float32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 64-bit float apart. -/
def Term.floatModel_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .floatModel))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.floatModel_casesOn a b))
    fun ρ a => (.floatModel_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 32-bit float apart. -/
def Term.float32Model_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32Model))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float32Model_casesOn a b))
    fun ρ a => (.float32Model_casesOn a (b.rename (Ren.lift ρ)))

/-- Delay a value, unmemoised. -/
abbrev Term.lazy_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.lazy τ) :=
  .ofComp (.lazy_mk e)

/-- Run a delayed value. -/
def Term.lazy_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.lazy τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ofComp (.lazy_force a)

/-- Delay a value and remember it: a `Thunk`. -/
abbrev Term.thunk_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.thunk τ) :=
  .ofComp (.thunk_mk e)

/-- Force a thunk. -/
def Term.thunk_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.thunk τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ofComp (.thunk_force a)

/-- An array, from its elements, in order. -/
def Term.array_mk {Γ : Ctx} {τ : TyWf} (ts : Terms Sg Γ τ) : Term Sg Γ (.array τ) :=
  ts.bindAtoms Ren.id fun _ as => .ofComp (.array_mk as)

/-- Take an array apart. -/
def Term.array_casesOn' {Γ : Ctx} {σ τ : TyWf} (a : Term Sg Γ (.array σ)) (z : Term Sg Γ τ)
    (s : Term Sg (σ :: TyWf.array σ :: Γ) τ) : Term Sg Γ τ :=
  a.bindAtomOr (fun x => (.array_casesOn x z s))
    fun ρ x => (.array_casesOn x (z.rename ρ) (s.rename (Ren.lift (Ren.lift ρ))))

/-- The fold of an array that descends `k + 1` elements at a time. -/
def Term.array_rec' {Γ : Ctx} {σ τ : TyWf} (k : Nat := 0) (a : Term Sg Γ (.array σ))
    (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  a.bindAtomOr (fun x =>
    (.array_rec k x bases
      branch .ret))
    fun ρ x =>
    (.array_rec k x (bases.rename ρ)
      (branch.rename (Ren.lift (Ren.lift (Ren.liftNat τ (k + 1) ρ)))) .ret)

/-- A constructor of an enum. -/
abbrev Term.enum_mk {Γ : Ctx} (s : LeanEnumSchema) (i : Fin s.nOfConstructors) :
    Term Sg Γ (.enum s) := .ofComp (.enum_mk s i)

/-- A dispatch on an enum. -/
def Term.enum_casesOn' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} (e : Term Sg Γ (.enum s))
    (cases : EnumCases Sg Γ τ s) : Term Sg Γ τ :=
  e.bindAtomOr (fun a => (.enum_casesOn a cases))
    fun ρ a => (.enum_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of an enum, with a default. -/
def Term.enum_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {k : Nat}
    (e : Term Sg Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k) (dflt : Term Sg Γ τ)
    (hk : k < s.nOfConstructors := by ctor_lt) : Term Sg Γ τ :=
  e.bindAtomOr (fun a => (.enum_casesOnWithDefault a cases dflt hk))
    fun ρ a => (.enum_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A record, from its fields. -/
def Term.record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Spine Sg Γ fs.toList) :
    Term Sg Γ (.record fs) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.record_mk fs as)

/-- The eliminator of a record. -/
def Term.record_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf}
    (r : Term Sg Γ (.record fs)) (body : Term Sg (fs.toList ++ Γ) τ) : Term Sg Γ τ :=
  r.bindAtomOr (fun a => (.record_casesOn a body))
    fun ρ a => (.record_casesOn a (body.rename (Ren.liftN fs.toList ρ)))

/-- A tagged value. -/
def Term.taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
    (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
    Term Sg Γ (.taggedUnion l) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.taggedUnion_mk l t ht as)

/-- The eliminator of a tagged union. -/
def Term.taggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
    (v : Term Sg Γ (.taggedUnion l)) (cases : TaggedUnionFoldCases Sg TyWf id Γ l τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.taggedUnion_casesOn a cases))
    fun ρ a => (.taggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a tagged union, with a default. -/
def Term.taggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema TyWf} {k : Nat} (v : Term Sg Γ (.taggedUnion l))
    (cases : TaggedUnionSomeCases Sg Γ l τ k) (dflt : Term Sg Γ τ)
    (hk : k < l.length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.taggedUnion_casesOnWithDefault a cases dflt hk))
    fun ρ a =>
    (.taggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A value of a recursive tagged union. -/
def Term.recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l) := by ty_wf) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_tag)
    (fields : Spine Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) :
    Term Sg Γ (.recTaggedUnion l hwf) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.recTaggedUnion_mk l hwf t ht as)

/-- The eliminator of a recursive tagged union. -/
def Term.recTaggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recTaggedUnion_casesOn a cases))
    fun ρ a => (.recTaggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a recursive tagged union, with a default. -/
def Term.recTaggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    {k : Nat} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k)
    (dflt : Term Sg Γ τ)
    (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recTaggedUnion_casesOnWithDefault a cases dflt hk))
    fun ρ a =>
    (.recTaggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- The fold of a recursive tagged union. -/
def Term.recTaggedUnion_rec' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat := 0)
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldKCases Sg l
      (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ l τ k []) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recTaggedUnion_rec k a cases .ret))
    fun ρ a => (.recTaggedUnion_rec k a (cases.rename ρ) .ret)

/-- A value of a recursive record. -/
def Term.recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs) := by ty_wf)
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) :
    Term Sg Γ (.recObject fs hwf) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.recObject_mk fs hwf as)

/-- The eliminator of a recursive record. -/
def Term.recObject_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recObject_casesOn a body))
    fun ρ a =>
    (.recObject_casesOn a (body.rename (Ren.liftN (TyWf.recObjectUnfold fs hwf).toList ρ)))

/-- The fold of a recursive record. -/
def Term.recObject_rec' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat := 0) (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recObject_rec k a body .ret))
    fun ρ a =>
    (.recObject_rec k a (body.rename (Ren.liftN (TyWf.recObjectRecBinders fs hwf τ k) ρ)) .ret)

/-- A value of a recursive newtype. -/
def Term.recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b) := by ty_wf)
    (value : Term Sg Γ (TyWf.recAliasUnfold b hwf)) : Term Sg Γ (.recAlias b hwf) :=
  value.bindAtom fun _ a => .ofComp (.recAlias_mk b hwf a)

/-- The eliminator of a recursive newtype. -/
def Term.recAlias_casesOn' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recAlias_casesOn a body))
    fun ρ a => (.recAlias_casesOn a (body.rename (Ren.lift ρ)))

/-- The fold of a recursive newtype. -/
def Term.recAlias_rec' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
    (k : Nat := 0) (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recAlias_rec k a body .ret))
    fun ρ a =>
    (.recAlias_rec k a (body.rename (Ren.liftN (TyWf.recAliasRecBinders b hwf τ k) ρ)) .ret)

/-- A value of one member of a mutual recursive family. -/
def Term.mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f) := by ty_wf)
    (value : FamilyMemberValue Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ (.mutualRecursiveFamily f hwf) :=
  value.bindArgs fun _ as => .ofComp (.mutualRecursiveFamily_mk f hwf as)

/-- The eliminator of a member of a mutual family. -/
def Term.mutualRecursiveFamily_casesOn' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.mutualRecursiveFamily_casesOn a cases))
    fun ρ a => (.mutualRecursiveFamily_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a member of a mutual family, with a
    default. -/
def Term.mutualRecursiveFamily_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (dflt : Term Sg Γ τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.mutualRecursiveFamily_casesOnWithDefault a cases dflt))
    fun ρ a =>
    (.mutualRecursiveFamily_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ))

/-- The fold of a mutual family. -/
def Term.mutualRecursiveFamily_rec' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} (k : Nat := 0)
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ τ f.members k) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.mutualRecursiveFamily_rec k a cases .ret))
    fun ρ a => (.mutualRecursiveFamily_rec k a (cases.rename ρ) .ret)

/-! ## Reading the answers out of a window of answer trees

What `#leanscript_to_term` binds beside the window of a fold of depth above `0`, at a field
that is a function or a delay (`LeanScript.RecFnFieldFacts` proves their values). -/

/-- **The function of the answers at a function field**, as the translation writes it: the
    window `w : σ ⇒ ⟨τ, W⟩` holds, at every argument, the answer tree there, and the term
    is `fun a => (w a).1`. It is a `lam` around a `record_casesOn'` of `w a` that returns
    the first field. -/
def Term.fnTreeAnswer {Γ : Ctx} {σ τ W : TyWf} (w : Γ ∋ (σ ⇒ .record ⟨τ, W, []⟩)) :
    Term Sg Γ (σ ⇒ τ) :=
  Term.lam (Term.record_casesOn' (fs := ⟨τ, W, []⟩)
    (Term.ap (Term.var (Var.tail w)) (Term.var Var.head)) (Term.var Var.head))

/-- **The delayed answer at a delayed field**, as the translation writes it: the window
    `w : thunk ⟨τ, W⟩` holds the delayed answer tree, and the term delays the first field
    of it, `thunk_mk (thunk_force w).1`. -/
def Term.thunkTreeAnswer {Γ : Ctx} {τ W : TyWf} (w : Γ ∋ .thunk (.record ⟨τ, W, []⟩)) :
    Term Sg Γ (.thunk τ) :=
  Term.thunk_mk (Term.record_casesOn' (fs := ⟨τ, W, []⟩)
    (Term.thunk_force (Term.var w)) (Term.var Var.head))

end LeanScript

end
