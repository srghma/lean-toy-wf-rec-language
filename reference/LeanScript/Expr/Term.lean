module
public import LeanScript.Expr.Atom
public import LeanScript.Expr.NatRecCtx
public import LeanScript.Expr.Extern
public import LeanScript.Expr.SelfField
public import LeanScript.Ty.Unfold
public import LeanScript.Ty.TyWfIn
public import LeanScript.Ty.Wf
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# `Term`: the one grammar, terminating by construction

The grammar itself: `Term` and the families of branches it dispatches through, as one
`mutual` block.  The prose that explains the recursion discipline, and how this block
came to be, is in `LeanScript.Expr.Design`.

**No `DecidableEq`/`BEq`.**  The float literals (`Term.float_mk`, `Term.float32_mk`,
`Term.floatModel_mk`, `Term.float32Model_mk`) are not what prevents it: `Float`, `Float32`
and their models have `DecidableEq`.  What does is that some constructors hold
**functions**: `Term.externCall` and `Term.externCallChecked` hold
`call : TyWf.DenList σs → Extern τ` (resp. `→ Option (Extern τ)`), and `Term.extern` holds
a `LeanScript.Extern`, which has no decidable equality either (see
`LeanScript.LeanInitPureExtern`).  Equality of such functions cannot be decided.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

mutual

/-- A term of the language, in **strict A-normal form**: a block of `let`s, each naming the
    value of one computation step (`LeanScript.Comp`), ending in a **tail**: the return of
    a variable, a jump to a join point, or a dispatch or a fold.  It is typed, in
    a context `Γ` of the types in scope, a context `J` of the join points in scope (their
    argument types; every one of them answers with `τ`), and against the signature `Sg` of
    the module's top-level declarations.  It is total by construction — it has no fixpoint
    constructor, no effect and no partial operation.

    Strict A-normal form is a property of the *type*: the operands of every step are atoms
    (`LeanScript.Atom`), which are **variables only** — a declaration and a literal are
    steps, named by a `let` like any other; a `let` binds a `LeanScript.Comp`, never
    another `let`, never a mere variable (there is no copy `let x = y`), never a dispatch
    and never a fold; a block ends by returning a variable (`Term.ret`), so a step is never
    in tail position unnamed; and a dispatch or a fold is always the last thing a block
    does.  A dispatch whose value is used by what follows is written with a **join point**
    (`Term.letJ`): what follows becomes the join point, and each branch ends by jumping to
    it (`Term.jump`).  A fold delivers its answer to a `LeanScript.Dest`: either it is the
    value of the term, or it is passed to a join point.  Join points live in their own
    context `J`, apart from the variables, and they are not values: they can only be jumped
    to, from tail position, and a function body, a delay or a fold branch starts with none.

    `J` is an `optParam` that defaults to `[]`, so `Term Sg Γ τ` is a term with no join
    point in scope — a whole function body.  The functions named like the constructors of
    the direct-style grammar (`LeanScript.Term.ap`, `LeanScript.Term.nat_rec`, …, in
    `LeanScript.Expr.Build`) take arbitrary terms and put them in this form. -/
inductive Term (Sg : Sig) : Ctx → TyWf → optParam JCtx [] → Type 1
  /-- `ret x` — the end of a block: the value of the variable `x` is the value of the
      term.  Only a variable can be returned: a computation whose value is the term's is
      bound by a `let` first (`let x = c; ret x`), so every step of a block is named, and a
      block has one shape whatever its last step is. -/
  | ret : ∀ {Γ τ} {J : JCtx}, Atom Γ τ → Term Sg Γ τ J
  /-- `let x = c; body` — the value of the computation `c` is bound as de Bruijn index `0`
      of `body`. -/
  | letE : ∀ {Γ σ τ} {J : JCtx}, Comp Sg Γ σ → Term Sg (σ :: Γ) τ J → Term Sg Γ τ J
  /-- `join j x = jp; body` — the join point `jp`, whose parameter is de Bruijn index `0`
      of its own body, is bound as join point `0` of `body`.  It is not recursive: `jp` sees
      the join points in scope before it, not itself. -/
  | letJ : ∀ {Γ σ τ} {J : JCtx}, (jp : Term Sg (σ :: Γ) τ J) → (body : Term Sg Γ τ (σ :: J)) →
      Term Sg Γ τ J
  /-- `jump j a` — go to the join point `j` with the atom `a` as its argument: its answer
      is the value of the term. -/
  | jump : ∀ {Γ σ τ} {J : JCtx}, (j : J ∋ σ) → Atom Γ σ → Term Sg Γ τ J
  /-- A pure extern of `Init` that takes a proof, applied to the terms of its arguments.
      The language erases propositions, so the proof is not in hand when the term runs:
      `call` **decides** the proposition on the values of the arguments and builds the
      entry of the catalogue with the proof it gets (`fun vs => if h : vs.2.1 < vs.1.size
      then some (.lean_array_fget αt vs.1 vs.2.1 h) else none`), and the value is
      `Extern.eval` of it.  Where the proposition does not hold — which cannot happen in a
      term translated from a Lean program, since that program had to supply the proof —
      the value is `fallback`'s. -/
  | externCallChecked : ∀ {Γ σs ρ τ} {J : JCtx}, Args Sg Γ σs →
      (call : TyWf.DenList σs → Option (Extern ρ)) → (d : Dest J ρ τ) →
      (fallback : Term Sg Γ τ J) → Term Sg Γ τ J
  -- LeanPrimTy recursors/eliminators
  /-- `if c then t else e`. -/
  | bool_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .bool) → Term Sg Γ τ J → Term Sg Γ τ J → Term Sg Γ τ J
  /-- `match n with | 0 => … | k + 1 => …`: the successor branch **binds** the
      predecessor as de Bruijn index `0`.  There is no recursive value — this is
      `Nat.casesOn`, and the fold is `Term.nat_rec`. -/
  | nat_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .nat) →
      Term Sg Γ τ J → Term Sg (TyWf.prim .nat :: Γ) τ J → Term Sg Γ τ J
  /-- `Nat.rec` that descends `k + 1` steps.  `base` holds the answers at `k, …, 1, 0` —
      **nearest first**, so it reads `(f k, …, f 0)` — and the branch for `n + k + 1` binds
      `n` (index `0`) and then the answers at `n + k, …, n + 1, n` (indices `1 … k + 1`).

      At the default depth `k = 0` this is `Nat.rec` with a non-dependent motive: one base
      value, and a branch binding the predecessor as index `0` and the value of the fold
      at it as index `1`.

      It is terminating by construction, at every depth: the branch is *given* the answers
      at the `k + 1` predecessors, so there is no call it could make on anything larger.
      It is also **linear**: the evaluator carries the window of the last `k + 1` answers
      and shifts it, so no answer is ever recomputed. -/
  | nat_rec : ∀ {Γ ρ τ} {J : JCtx} (k : Nat := 0), Atom Γ (.prim .nat) →
      Args Sg Γ (natRecCtx ρ (k + 1) []) →
      Term Sg (TyWf.prim .nat :: natRecCtx ρ (k + 1) Γ) ρ →
      (d : Dest J ρ τ) → Term Sg Γ τ J
  /-- `match i with | .ofNat n => … | .negSucc n => …`: each branch binds its `nat`. -/
  | int_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .int) →
      Term Sg (TyWf.prim .nat :: Γ) τ J → Term Sg (TyWf.prim .nat :: Γ) τ J → Term Sg Γ τ J
  /-- Take an 8-bit unsigned value apart: its branch binds the bit vector. -/
  | uint8_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .uint8) →
      Term Sg (TyWf.prim (.bitvec 8) :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 16-bit unsigned value apart: its branch binds the bit vector. -/
  | uint16_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .uint16) →
      Term Sg (TyWf.prim (.bitvec 16) :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 32-bit unsigned value apart: its branch binds the bit vector. -/
  | uint32_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .uint32) →
      Term Sg (TyWf.prim (.bitvec 32) :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 64-bit unsigned value apart: its branch binds the bit vector. -/
  | uint64_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .uint64) →
      Term Sg (TyWf.prim (.bitvec 64) :: Γ) τ J → Term Sg Γ τ J
  /-- Take an 8-bit signed value apart: its branch binds the unsigned value. -/
  | int8_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .int8) →
      Term Sg (TyWf.prim .uint8 :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 16-bit signed value apart: its branch binds the unsigned value. -/
  | int16_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .int16) →
      Term Sg (TyWf.prim .uint16 :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 32-bit signed value apart: its branch binds the unsigned value. -/
  | int32_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .int32) →
      Term Sg (TyWf.prim .uint32 :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 64-bit signed value apart: its branch binds the unsigned value. -/
  | int64_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .int64) →
      Term Sg (TyWf.prim .uint64 :: Γ) τ J → Term Sg Γ τ J
  /-- Take a character apart: its branch binds the code point, a `uint32`.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | char_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .char) →
      Term Sg (TyWf.prim .uint32 :: Γ) τ J → Term Sg Γ τ J
  /-- Take an unchecked position apart: its branch binds the byte index. -/
  | stringPosRaw_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .stringPosRaw) →
      Term Sg (TyWf.prim .nat :: Γ) τ J → Term Sg Γ τ J
  /-- Take a checked position apart: its branch binds the unchecked one.  The proof that
      it is valid is a proposition, so it is erased and is not bound. -/
  | stringPos_casesOn : ∀ {Γ τ} {J : JCtx} {s : String}, Atom Γ (.prim (.stringPos s)) →
      Term Sg (TyWf.prim .stringPosRaw :: Γ) τ J → Term Sg Γ τ J
  /-- Take an unchecked substring apart: its branch binds the string and the two
      positions, in declaration order. -/
  | substringRaw_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .substringRaw) →
      Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ J →
      Term Sg Γ τ J
  /-- Take a 64-bit float apart: its branch binds its model. -/
  | float_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .float) →
      Term Sg (TyWf.prim .floatModel :: Γ) τ J → Term Sg Γ τ J
  /-- Take a 32-bit float apart: its branch binds its model. -/
  | float32_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .float32) →
      Term Sg (TyWf.prim .float32Model :: Γ) τ J → Term Sg Γ τ J
  /-- Take the model of a 64-bit float apart: its branch binds its bits.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | floatModel_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .floatModel) →
      Term Sg (TyWf.prim .uint64 :: Γ) τ J → Term Sg Γ τ J
  /-- Take the model of a 32-bit float apart: its branch binds its bits.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | float32Model_casesOn : ∀ {Γ τ} {J : JCtx}, Atom Γ (.prim .float32Model) →
      Term Sg (TyWf.prim .uint32 :: Γ) τ J → Term Sg Γ τ J
  /-- Take an array apart: an empty branch, and a non-empty branch that **binds** the
      first element and the rest of the array, in that order.  This is the case
      analysis — the branch gets the rest of the array, not the value of a fold over
      it; that is `Term.array_rec`. -/
  | array_casesOn : ∀ {Γ σ τ} {J : JCtx}, Atom Γ (.array σ) →
      Term Sg Γ τ J → Term Sg (σ :: TyWf.array σ :: Γ) τ J → Term Sg Γ τ J
  /-- The fold of an array that descends `k + 1` elements at a time.  Its branch, at a
      list `a :: as` whose tail is at least `k` long, **binds** the first element (de
      Bruijn index `0`), the rest of the array (index `1`) and then the values of the
      fold at the `k + 1` suffixes `as`, `as.drop 1`, …, `as.drop k` — **nearest first**,
      so indices `2 … k + 2`.  The lists that are shorter than that — the ones that have
      no such block of suffixes — are answered by `LeanScript.ArrayRecBases`, which binds
      their elements.

      At the default depth `k = 0` this is `List.rec` with a non-dependent motive: one
      value for the empty list, and a branch binding the head at index `0`, the tail at
      index `1` and the value of the fold over that tail at index `2`.

      As with `Term.nat_rec`, the recursive value is given rather than called, so a term
      is still terminating by construction, at every depth; and the evaluator carries the
      window of the last `k + 1` answers rather than recomputing them, so the fold is
      linear. -/
  | array_rec : ∀ {Γ σ ρ τ} {J : JCtx} (k : Nat := 0), Atom Γ (.array σ) →
      ArrayRecBases Sg Γ σ ρ k →
      Term Sg (σ :: TyWf.array σ :: natRecCtx ρ (k + 1) Γ) ρ → (d : Dest J ρ τ) → Term Sg Γ τ J
  /-- A dispatch on an enum: one branch per constructor, and no default, so it cannot
      fall off the end. -/
  | enum_casesOn : ∀ {Γ τ} {J : JCtx} {s : LeanEnumSchema},
      Atom Γ (.enum s) → EnumCases Sg Γ τ s J → Term Sg Γ τ J
  /-- A dispatch on an enum that branches on **some** of the constructors and sends the
      rest to a default branch.  The branches are given as a list of
      (constructor number, branch) pairs, in the order they are tried, and the last
      argument is the default.  Nothing is missing — the default catches every
      constructor that has no branch — so this is still total.

      The branches name their constructors in **strictly increasing** order, there is at
      least one of them, and there are **fewer of them than the enum has constructors**
      (`hk`, written by `ctor_lt`).  So no constructor can be named twice, the form is
      not a roundabout way of writing its own default, and it is not a roundabout way of
      writing an exhaustive `Term.enum_casesOn` either: the default branch is always
      reachable. -/
  | enum_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {J : JCtx} {s : LeanEnumSchema} {k : Nat}
      (e : Atom Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k 0 J) (dflt : Term Sg Γ τ J)
      (hk : k < s.nOfConstructors := by ctor_lt) : Term Sg Γ τ J
  /-- The eliminator of a record: it **binds** every field, in declaration order, so de
      Bruijn index `0` of the body is the record's first field.  A projection is this
      node followed by a variable. -/
  | record_casesOn : ∀ {Γ τ} {J : JCtx} {fs : LeanRecordSchema TyWf},
      Atom Γ (.record fs) → Term Sg (fs.toList ++ Γ) τ J → Term Sg Γ τ J
  /-- The eliminator of a tagged union: one branch per constructor, each binding that
      constructor's fields, and no default. -/
  | taggedUnion_casesOn : ∀ {Γ τ} {J : JCtx} {l : LeanTaggedUnionSchema TyWf},
      Atom Γ (.taggedUnion l) → TaggedUnionFoldCases Sg TyWf id Γ l τ J → Term Sg Γ τ J
  /-- A dispatch on a tagged union that branches on **some** of the constructors and
      sends the rest to a default branch.  A branch names its constructor by number —
      with the same `t < l.length` bound, written by `ctor_tag` — and binds that
      constructor's fields; the last argument is the default.  Every constructor without
      a branch goes to the default, so this is still total.

      The branches name their constructors in **strictly increasing** order, there is at
      least one of them, and there are **fewer of them than the union has constructors**
      (`hk`, written by `ctor_lt`).  So no constructor can be named twice, the form is
      not a roundabout way of writing its own default, and it is not a roundabout way of
      writing an exhaustive `Term.taggedUnion_casesOn` either: the default branch is
      always reachable. -/
  | taggedUnion_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {J : JCtx} {l : LeanTaggedUnionSchema TyWf}
      {k : Nat} (v : Atom Γ (.taggedUnion l))
      (cases : TaggedUnionSomeCases Sg Γ l τ k 0 J) (dflt : Term Sg Γ τ J)
      (hk : k < l.length := by ctor_lt) : Term Sg Γ τ J
  /-- The eliminator of a recursive tagged union: one branch per constructor, each
      binding that constructor's **unfolded** fields, and no default.  It takes the value
      *one level* apart — a field that is an occurrence of the union is bound as a value
      of the union, not descended into; descending is `Term.recTaggedUnion_rec`. -/
  | recTaggedUnion_casesOn : ∀ {Γ τ} {J : JCtx} {l : LeanTaggedUnionSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)},
      Atom Γ (.recTaggedUnion l hwf) →
      TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ J → Term Sg Γ τ J
  /-- A dispatch on **some** of the constructors of a recursive tagged union, with a
      default for the rest.  As for a non-recursive union the branches name their
      constructors in strictly increasing order, there is at least one of them, and there
      are fewer of them than the union has constructors, so the default is reachable. -/
  | recTaggedUnion_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {J : JCtx}
      {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
      {k : Nat} (v : Atom Γ (.recTaggedUnion l hwf))
      (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k 0 J)
      (dflt : Term Sg Γ τ J)
      (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_lt) : Term Sg Γ τ J
  /-- **The fold of a recursive tagged union**, its `Xxx.rec` with a non-dependent
      motive, that descends `k + 1` constructors at a time: one branch per constructor,
      each binding that constructor's fields and, right after a field that is an
      occurrence of the union, the value of the fold at that field (`TyWf.recBinders`),
      and each branch free to **look further down** — to dispatch on one of those
      occurrences again, and so be given *its* fields and the values of the fold at
      them, or on an occurrence at a node above it that it has not looked into yet (a
      sibling of the subvalue it looked into, `LeanScript.FoldKBranch.deepOuter`), so
      that it can read below **several** subvalues.  `LeanScript.TaggedUnionFoldKCases`
      is that case tree; a branch may stop looking at any point, and at depth `k` it may
      look at most `k` times in all.

      At the default depth `k = 0` this is the plain fold: no branch can descend, so the
      branches are exactly one term each, in the context that binds the constructor's
      fields and the values of the fold at its occurrences
      (`LeanScript.RecUnionRecFacts` proves the two families are the same at that
      depth).  At depth `1` a branch reads the answer at a field *and* at that field's
      own occurrences — which is what a `fib`-shaped recursion on a Peano-style union
      does, reading the answer two constructors down.

      The recursive value is *given* to the branch rather than called by it, exactly as
      in `Term.nat_rec` and `Term.array_rec`, and a deeper look is taken only into a
      **subvalue** (`LeanScript.SelfField` and `LeanScript.OuterSelfField` pick the
      occurrence descended into, at a node on the path), so a term is still terminating
      by construction, at every depth. -/
  | recTaggedUnion_rec : ∀ {Γ ρ τ} {J : JCtx} {l : LeanTaggedUnionSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat := 0),
      Atom Γ (.recTaggedUnion l hwf) →
      TaggedUnionFoldKCases Sg l
        (TyWf.recBinders (.recTaggedUnion l hwf) ρ) Γ l ρ k [] →
      (d : Dest J ρ τ) → Term Sg Γ τ J
  /-- The eliminator of a recursive record: it **binds** every field, unfolded, in
      declaration order.  A record has one constructor, so there is nothing to dispatch
      on and no partial form: `Term.recObject_casesOnWithDefault` would be this node with
      a branch that is never taken. -/
  | recObject_casesOn : ∀ {Γ τ} {J : JCtx} {fs : LeanRecordSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recObjectTy fs)},
      Atom Γ (.recObject fs hwf) →
      Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ J → Term Sg Γ τ J
  /-- **The fold of a recursive record**, its `Xxx.rec` with a non-dependent motive, that
      reads `k + 1` levels at a time.  A record has one constructor, so there is one
      branch and nothing to dispatch on: the branch binds every field, unfolded — what
      `Term.recObject_casesOn` binds — and then the fold's **lookback window**
      (`TyWf.recObjectRecBinders`), which holds the answer at each immediate subvalue
      and, `k` levels deep, the answers below it.

      The answers are given in the shape of the record's own fields
      (`TyWf.recObjectAnswerTree`), because a recursive record never has a field that is
      *literally* an occurrence of it: all of its fields have to have values, so a field
      written `Ty.self` would leave the record with none
      (`LeanScript.RecObjectRecFacts`).  At the default depth `k = 0` the branch binds
      the fields and the answers at the immediate subvalues — the plain fold of a record,
      which is what a catamorphism over it takes.

      As in `Term.nat_rec`, `Term.array_rec` and `Term.recTaggedUnion_rec` the answers
      are *given* to the branch rather than called by it, and they are the answers at
      **subvalues** of the value being folded, so a term is terminating by construction
      at every depth. -/
  | recObject_rec : ∀ {Γ ρ τ} {J : JCtx} {fs : LeanRecordSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat := 0),
      Atom Γ (.recObject fs hwf) →
      Term Sg (TyWf.recObjectRecBinders fs hwf ρ k ++ Γ) ρ → (d : Dest J ρ τ) → Term Sg Γ τ J
  /-- The eliminator of a recursive newtype: its one branch **binds** the body.  As for a
      record there is one constructor, so there is no partial form. -/
  | recAlias_casesOn : ∀ {Γ τ} {J : JCtx} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)},
      Atom Γ (.recAlias b hwf) → Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ J →
      Term Sg Γ τ J
  /-- **The fold of a recursive newtype**, its `Xxx.rec` with a non-dependent motive, that
      reads `k + 1` levels at a time.  A newtype has one constructor, so there is one
      branch and nothing to dispatch on: the branch binds the body, unfolded — what
      `Term.recAlias_casesOn` binds — and then the fold's **lookback window**
      (`TyWf.recAliasRecBinders`), which holds the answer at each immediate subvalue and,
      `k` levels deep, the answers below it.

      The answers are given in the shape of the newtype's own body
      (`TyWf.recAliasAnswerTree`), because a recursive newtype never has a body that is
      *literally* an occurrence of it: `μX. X` is the equation `T = T`, which no value
      satisfies (`LeanScript.RecAliasRecFacts`).  At the default depth `k = 0` the branch
      binds the body and the answers at the immediate subvalues — the plain fold of a
      newtype, which is what a catamorphism over it takes.

      As in `Term.nat_rec`, `Term.array_rec`, `Term.recTaggedUnion_rec` and
      `Term.recObject_rec` the answers are *given* to the branch rather than called by it,
      and they are the answers at **subvalues** of the value being folded, so a term is
      terminating by construction at every depth. -/
  | recAlias_rec : ∀ {Γ ρ τ} {J : JCtx} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
      (k : Nat := 0),
      Atom Γ (.recAlias b hwf) →
      Term Sg (TyWf.recAliasRecBinders b hwf ρ k ++ Γ) ρ → (d : Dest J ρ τ) → Term Sg Γ τ J
  /-- The eliminator of a member of a mutual family: the branches of the shape *that
      member* has — one per constructor for a `ctors` member, the one branch binding the
      fields for a `record` member, the one branch binding the body for an `alias`
      member — and no default. -/
  | mutualRecursiveFamily_casesOn : ∀ {Γ τ} {J : JCtx} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)},
      Atom Γ (.mutualRecursiveFamily f hwf) →
      FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)) J → Term Sg Γ τ J
  /-- A dispatch on **some** of the constructors of a member of a mutual family, with a
      default for the rest.  Only a member that *has* constructors to choose between — a
      `ctors` member — can be dispatched on partially, which is what
      `LeanScript.FamilyMemberSomeCases` says by having no other case. -/
  | mutualRecursiveFamily_casesOnWithDefault : ∀ {Γ τ} {J : JCtx} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)},
      Atom Γ (.mutualRecursiveFamily f hwf) →
      FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)) J →
      Term Sg Γ τ J → Term Sg Γ τ J
  /-- **The fold of a mutual family**, that descends `k + 1` constructors at a time: the
      branches of *every* member of the family, in declaration order, each binding its
      fields and, right after a field that is an occurrence of a member, the value of the
      fold at that field (`TyWf.famRecBinders`) — and, right after a field that holds
      members *inside* it (an `Array`, a function or a `Thunk` of members, `List (Array T)`),
      the values of the fold at those members in the field's shape
      (`TyWf.famAnswerBinders`) — and each branch free to **look further
      down** — to dispatch on one of those occurrences again, whichever member it belongs
      to, or on an occurrence it has not looked into yet at a node above it on the path
      (`LeanScript.FamilyFoldKBranch.deepOuter`), and so be given *its* fields and the
      values of the fold at them.  One motive
      `τ` answers for every member, which is what lets one list of branches describe the
      whole family, and it is what a deeper look into another member answers with too.

      `LeanScript.FamilyFoldKCases` is that case tree; a branch may stop looking at any
      point, and at depth `k` it may descend at most `k` times.  At the default depth
      `k = 0` this is the plain fold: no branch can descend, so the branches are exactly
      one term each, in the context that binds the member's fields and the values of the
      fold at its occurrences (`LeanScript.FamilyRecFacts` proves the two families are
      the same at that depth).  At depth `1` a branch reads the answer at a field *and*
      at that field's own occurrences — which is what a `fib`-shaped recursion over a
      family does, reading the answer two constructors down, possibly through another
      member.

      The recursive value is *given* to the branch rather than called by it, exactly as
      in `Term.nat_rec`, `Term.array_rec` and `Term.recTaggedUnion_rec`, and a deeper
      look is taken only into a **subvalue** (`LeanScript.FamilyMemberField` and
      `LeanScript.FamilyOuterMemberField` pick the occurrence descended into), so a term is still terminating by construction, at
      every depth. -/
  | mutualRecursiveFamily_rec : ∀ {Γ ρ τ} {J : JCtx} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} (k : Nat := 0),
      Atom Γ (.mutualRecursiveFamily f hwf) →
      FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf ρ) Γ ρ f.members k →
      (d : Dest J ρ τ) → Term Sg Γ τ J

/-- **One computation step**, whose operands are atoms and which neither branches nor
    folds: the steps a `let` may bind.  The terms it holds are bodies it does not run when
    it is evaluated — of a function or of a delay — so they start with no join point in
    scope. -/
inductive Comp (Sg : Sig) : Ctx → TyWf → Type 1
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Comp Sg Γ τ
  /-- A boolean literal. -/
  | bool_mk : ∀ {Γ}, Bool → Comp Sg Γ (.prim .bool)
  /-- A natural number literal. -/
  | nat_mk : ∀ {Γ}, Nat → Comp Sg Γ (.prim .nat)
  /-- An integer literal. -/
  | int_mk : ∀ {Γ}, Int → Comp Sg Γ (.prim .int)
  /-- A bit-vector literal.  The width is positive, because `BitVec 0` is a unit type and
      unit types are erased. -/
  | bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
      Comp Sg Γ (.prim (.bitvec n h_positive))
  /-- An 8-bit unsigned literal. -/
  | uint8_mk : ∀ {Γ}, UInt8 → Comp Sg Γ (.prim .uint8)
  /-- A 16-bit unsigned literal. -/
  | uint16_mk : ∀ {Γ}, UInt16 → Comp Sg Γ (.prim .uint16)
  /-- A 32-bit unsigned literal. -/
  | uint32_mk : ∀ {Γ}, UInt32 → Comp Sg Γ (.prim .uint32)
  /-- A 64-bit unsigned literal. -/
  | uint64_mk : ∀ {Γ}, UInt64 → Comp Sg Γ (.prim .uint64)
  /-- An 8-bit signed literal. -/
  | int8_mk : ∀ {Γ}, Int8 → Comp Sg Γ (.prim .int8)
  /-- A 16-bit signed literal. -/
  | int16_mk : ∀ {Γ}, Int16 → Comp Sg Γ (.prim .int16)
  /-- A 32-bit signed literal. -/
  | int32_mk : ∀ {Γ}, Int32 → Comp Sg Γ (.prim .int32)
  /-- A 64-bit signed literal. -/
  | int64_mk : ∀ {Γ}, Int64 → Comp Sg Γ (.prim .int64)
  /-- A character literal. -/
  | char_mk : ∀ {Γ}, Char → Comp Sg Γ (.prim .char)
  /-- A string literal. -/
  | string_mk : ∀ {Γ}, String → Comp Sg Γ (.prim .string)
  /-- A literal position **into the string `s`**: the type of a checked position names
      the string it is into, so the string is part of the type. -/
  | stringPos_mk : ∀ {Γ} (s : String), String.Pos s → Comp Sg Γ (.prim (.stringPos s))
  /-- A literal unchecked byte position. -/
  | stringPosRaw_mk : ∀ {Γ}, String.Pos.Raw → Comp Sg Γ (.prim .stringPosRaw)
  /-- A literal unchecked substring. -/
  | substringRaw_mk : ∀ {Γ}, Substring.Raw → Comp Sg Γ (.prim .substringRaw)
  /-- A literal string slice. -/
  | stringSlice_mk : ∀ {Γ}, String.Slice → Comp Sg Γ (.prim .stringSlice)
  /-- A 64-bit floating point literal. -/
  | float_mk : ∀ {Γ}, Float → Comp Sg Γ (.prim .float)
  /-- A 32-bit floating point literal. -/
  | float32_mk : ∀ {Γ}, Float32 → Comp Sg Γ (.prim .float32)
  /-- A literal of the model of a 64-bit float: its bits, with their validity. -/
  | floatModel_mk : ∀ {Γ}, Float.Model → Comp Sg Γ (.prim .floatModel)
  /-- A literal of the model of a 32-bit float: its bits, with their validity. -/
  | float32Model_mk : ∀ {Γ}, Float32.Model → Comp Sg Γ (.prim .float32Model)
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ σ τ}, Term Sg (σ :: Γ) τ → Comp Sg Γ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap : ∀ {Γ σ τ}, Atom Γ (σ ⇒ τ) → Atom Γ σ → Comp Sg Γ τ
  -- externs
  /-- A pure extern of `Init` applied to values: an entry of the catalogue
      `LeanScript.LeanInitPureExtern` with all of its arguments, and the proofs it takes
      (`Term.extern (.lean_array_fget αt a i h)`).  Its value is `LeanScript.Extern.eval`,
      the Lean function called on them.  Externs are not declarations of the signature. -/
  | extern : ∀ {Γ τ}, Extern τ → Comp Sg Γ τ
  /-- A pure extern of `Init` applied to the terms of its arguments, which are computed
      when the term runs.  `call` builds the entry of the catalogue from their values
      (`fun vs => .lean_nat_add vs.1 vs.2.1`); the value is `Extern.eval` of it.  This is
      the form for an extern that takes no proof. -/
  | externCall : ∀ {Γ σs τ}, Args Sg Γ σs → (call : TyWf.DenList σs → Extern τ) →
      Comp Sg Γ τ
  -- `bitvec_casesOn`, `string_casesOn` and `stringSlice_casesOn` are not here: see this
  -- section's header for why their fields have no type in this language.
  -- LeanPrimTyCovariant intro and elimination
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes once the one
      value of the unit type is erased.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazy_mk : ∀ {Γ τ}, Term Sg Γ τ → Comp Sg Γ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazy_force : ∀ {Γ τ}, Atom Γ (.lazy τ) → Comp Sg Γ τ
  /-- Delay a value and remember it: a `Thunk`.

      **Memoised**: the JavaScript printed for it runs the body at the first force and
      answers with the stored value afterwards.  Forcing it is `Term.thunk_force`.  At
      this layer the distinction from `Term.lazy_mk` is not visible — a `Term` is a total
      Lean function of its environment, so running the body twice gives the same answer
      as running it once — and what it decides is the code that is printed. -/
  | thunk_mk : ∀ {Γ τ}, Term Sg Γ τ → Comp Sg Γ (.thunk τ)
  /-- Force a thunk: the value it stands for, computed at most once. -/
  | thunk_force : ∀ {Γ τ}, Atom Γ (.thunk τ) → Comp Sg Γ τ
  /-- An array, from its elements, in order. -/
  | array_mk : ∀ {Γ τ}, List (Atom Γ τ) → Comp Sg Γ (.array τ)
  /-- A constructor of an enum: its **number**, which is what the runtime holds. -/
  | enum_mk : ∀ {Γ} (s : LeanEnumSchema), Fin s.nOfConstructors → Comp Sg Γ (.enum s)
  /-- A record, from its fields, in declaration order. -/
  | record_mk : ∀ {Γ} (fs : LeanRecordSchema TyWf),
      Args Sg Γ fs.toList → Comp Sg Γ (.record fs)
  /-- A tagged value: constructor `t` of the union — a number **with the proof that the
      union has it** — and exactly that constructor's fields.

      The bound is against `LeanTaggedUnionSchema.length`, the number of constructors,
      and it is written by `ctor_tag` unless one is given, so a concrete tag needs
      nothing written by hand. -/
  | taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Args Sg Γ (l.get t ht)) :
      Comp Sg Γ (.taggedUnion l)
  -- The four recursive shapes of `Ty`.  A value of one of them is a value of the shape the binder holds with the binder's
  -- occurrences (`Ty.self`, `Ty.familyMember i`) instantiated to the binder itself, so an
  -- introduction form for one needs the *unfolding* of a `Ty`, which is
  -- `LeanScript.Ty.unfoldSelf` (`LeanScript.Ty.Unfold`).
  /-- A value of a **recursive** tagged union: constructor `t` of the union — a number
      with the proof that the union has it — and exactly that constructor's fields,
      **unfolded**: a field written `Ty.self` is a value of the union again.

      The payload is a schema of `LeanScript.TyWfIn` — trees written in the scope the
      binder opens, each with the proof that it is well formed there — and `hwf`, written
      by `ty_wf` unless one is given, is what says that the binder itself describes a
      **type**: that it mentions itself, only in positive position, and has values.  It
      comes before the fields because their types are stated in terms of it.

      The bound is against the unfolded schema, which has the same constructors as `l` in
      the same order, and it is written by `ctor_tag` unless one is given. -/
  | recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
      (hwf : Ty.Wf (TyWf.recTaggedUnionTy l) := by ty_wf) (t : Nat)
      (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_tag)
      (fields : Args Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) :
      Comp Sg Γ (.recTaggedUnion l hwf)
  /-- A value of a **recursive record**: its fields, in declaration order, unfolded.
      `hwf`, written by `ty_wf`, is the proof that the record describes a type; note that
      a recursive record with a field written `Ty.self` states the equation
      `T = … × T × …`, which no value satisfies, so it has no value here. -/
  | recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
      (hwf : Ty.Wf (TyWf.recObjectTy fs) := by ty_wf)
      (fields : Args Sg Γ (TyWf.recObjectUnfold fs hwf).toList) :
      Comp Sg Γ (.recObject fs hwf)
  /-- A value of a **recursive newtype**: a value of its body, unfolded.  The wrapper is
      erased, so the two have the same runtime representation.  `hwf`, written by
      `ty_wf`, is the proof that the newtype describes a type. -/
  | recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b) := by ty_wf)
      (value : Atom Γ (TyWf.recAliasUnfold b hwf)) : Comp Sg Γ (.recAlias b hwf)
  /-- A value of one member of a **mutual recursive family**: whichever of the three
      shapes that member has, with its fields unfolded in the scope of the whole family,
      so that a field written `Ty.familyMember i` is a value of member `i`.

      A family has at least two members, so its payload is written in a scope of `n + 2`;
      `hwf`, written by `ty_wf`, is the proof that the family describes types: every
      member is mentioned, no occurrence is in the domain of a function, and every member
      has values. -/
  | mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
      (f : LeanMutualRecFamily (TyWfIn (n + 2)))
      (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f) := by ty_wf)
      (value : FamilyMemberArgs Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) :
      Comp Sg Γ (.mutualRecursiveFamily f hwf)

/-- The answers a depth-`k` fold of an array (`LeanScript.Term.array_rec`) gives to the
    lists that are **shorter than its window**: the lists of fewer than `k + 1` elements,
    which have no block of `k + 1` shorter suffixes for the branch to be given.

    It is read by peeling one element at a time, and each element peeled is **bound**: at
    depth `j + 1` there is the answer for the empty list, which binds nothing, and then —
    with the first element bound as de Bruijn index `0` — the answers of depth `j` for
    what is left of the list.  So the branch for a list of `j` elements is written in the
    context `natRecCtx σ j Γ`, in which index `0` is the **last** of those elements and
    index `j - 1` the first.

    At depth `0` only the empty list is short, so there is one answer and it binds
    nothing: that is the base value of an ordinary `List.rec`. -/
inductive ArrayRecBases (Sg : Sig) : Ctx → TyWf → TyWf → Nat → Type 1
  /-- Depth zero: the answer for the empty list. -/
  | nil : ∀ {Γ σ τ}, Term Sg Γ τ → ArrayRecBases Sg Γ σ τ 0
  /-- The answer for the empty list, and — with the first element bound as de Bruijn
      index `0` — the answers for the one-element-shorter lists that are left. -/
  | cons : ∀ {Γ σ τ} {j : Nat}, Term Sg Γ τ → ArrayRecBases Sg (σ :: Γ) σ τ j →
      ArrayRecBases Sg Γ σ τ (j + 1)

/-- The branches of a dispatch on **some** of the constructors of a tagged union, used
    with a default: a list of (constructor number, branch) pairs, in the order they are
    tried.  The number carries the same `t < l.length` bound as
    `LeanScript.Term.taggedUnion_mk`, written by `ctor_tag` unless it is given, and the
    branch binds that constructor's fields.  A constructor may be left out — that is the
    point — and `LeanScript.Term.taggedUnion_casesOnWithDefault` supplies the branch it
    then takes.

    The list is **validated by its type**, exactly as `LeanScript.EnumSomeCases` is, so a
    dispatch that is not well formed cannot be written at all:

    * the constructor numbers **strictly increase**, and so are in order and no number is
      named twice: the extra index `lo` is the smallest number a branch of the list may
      still name, and the tail after the branch of `t` starts at `t + 1`;
    * there is **at least one** branch: the list ends with `last`, not with an empty
      case, so a `LeanScript.Term.taggedUnion_casesOnWithDefault` that names nothing —
      which is just its default — is unwritable.

    The list also **counts its branches**, in the index `k`, which is what
    `LeanScript.Term.taggedUnion_casesOnWithDefault` compares with the number of
    constructors of the union: a list that names *every* constructor is an exhaustive
    dispatch whose default is unreachable, and the bound `k < l.length` there makes it
    unwritable.

    `lo` is an `optParam` that starts at `0`, so `TaggedUnionSomeCases Sg Γ l τ k` is the
    type of a whole list of `k` branches; and the bound `lo ≤ t` is the last argument of
    each constructor, with `ctor_ge` as its default, so a list of concrete numbers needs
    nothing written by hand. -/
inductive TaggedUnionSomeCases (Sg : Sig) :
    Ctx → LeanTaggedUnionSchema TyWf → TyWf → Nat → optParam Nat 0 → optParam JCtx [] → Type 1
  /-- The last branch: the constructor of number `t`, whose fields it binds, and no
      constructor after it has a branch. -/
  | last {Γ : Ctx} {l : LeanTaggedUnionSchema TyWf} {τ : TyWf} {J : JCtx} {lo : Nat} (t : Nat)
      (ht : t < l.length := by ctor_tag) (branch : Term Sg (l.get t ht ++ Γ) τ J)
      (hi : lo ≤ t := by ctor_ge) : TaggedUnionSomeCases Sg Γ l τ 1 lo J
  /-- One more branch, for constructor `t`, binding that constructor's fields; every
      branch after it names a **bigger** constructor. -/
  | cons {Γ : Ctx} {l : LeanTaggedUnionSchema TyWf} {τ : TyWf} {J : JCtx} {k lo : Nat} (t : Nat)
      (ht : t < l.length := by ctor_tag) (branch : Term Sg (l.get t ht ++ Γ) τ J)
      (rest : TaggedUnionSomeCases Sg Γ l τ k (t + 1) J)
      (hi : lo ≤ t := by ctor_ge) : TaggedUnionSomeCases Sg Γ l τ (k + 1) lo J

/-- The branches of a dispatch on an enum: one per constructor, in constructor order,
    binding nothing, and **indexed by the schema itself** rather than by the number of
    constructors it denotes.  So the family has the same shape as
    `LeanScript.LeanEnumSchema`: an enum has three constructors at minimum, which is the
    base case `three`, and one more branch for each constructor beyond them.

    There is no end-of-list before the constructors run out and no default, so a
    dispatch is exhaustive by construction. -/
inductive EnumCases (Sg : Sig) : Ctx → TyWf → LeanEnumSchema → optParam JCtx [] → Type 1
  /-- The branches of the three constructors an enum has at minimum, in constructor
      order. -/
  | three : ∀ {Γ τ} {J : JCtx} {shift : Int},
      Term Sg Γ τ J → Term Sg Γ τ J → Term Sg Γ τ J → EnumCases Sg Γ τ ⟨0, shift⟩ J
  /-- The branch of the first constructor, and the branches of the ones after it — one
      constructor beyond the schema of the rest. -/
  | cons : ∀ {Γ τ} {J : JCtx} {extra : Nat} {shift : Int},
      Term Sg Γ τ J → EnumCases Sg Γ τ ⟨extra, shift⟩ J →
      EnumCases Sg Γ τ ⟨extra + 1, shift⟩ J

/-- The branches of a dispatch on **some** of the constructors of the enum `s`, used with
    a default: (constructor number, branch) pairs.  A constructor may be left out — that
    is the point — and `LeanScript.Term.enum_casesOnWithDefault` supplies the branch it
    then takes.

    The list is **validated by its type**, so a dispatch that is not well formed cannot
    be written at all:

    * the constructor numbers **strictly increase**, and so are in order and no number
      is named twice: the extra index `lo` is the smallest number a branch of the list
      may still name, and the tail after the branch of `i` starts at `i + 1`;
    * there is **at least one** branch: the list ends with `last`, not with an empty
      case, so a `LeanScript.Term.enum_casesOnWithDefault` that names nothing — which is
      just its default — is unwritable.

    The list also **counts its branches**, in the index `k`, which is what
    `LeanScript.Term.enum_casesOnWithDefault` compares with the number of constructors of
    the enum: a list that names *every* constructor is an exhaustive dispatch whose
    default is unreachable, and the bound `k < s.nOfConstructors` there makes it
    unwritable.

    The list is indexed by the **schema** of the enum it dispatches on, exactly as
    `LeanScript.TaggedUnionSomeCases` is indexed by the schema of its union, so branches
    written for one enum are not branches for another.

    `lo` is an `optParam` that starts at `0`, so `EnumSomeCases Sg Γ τ s k` is the type of
    a whole list of `k` branches; and the bound `lo ≤ i` is the last argument of each
    constructor, with `ctor_ge` as its default, so a list of concrete numbers needs
    nothing written by hand. -/
inductive EnumSomeCases (Sg : Sig) :
    Ctx → TyWf → LeanEnumSchema → Nat → optParam Nat 0 → optParam JCtx [] → Type 1
  /-- The last branch: the constructor of this number, and no constructor after it has a
      branch. -/
  | last {Γ : Ctx} {τ : TyWf} {J : JCtx} {s : LeanEnumSchema} {lo : Nat}
      (i : Fin s.nOfConstructors) (branch : Term Sg Γ τ J) (hi : lo ≤ i.val := by ctor_ge) :
      EnumSomeCases Sg Γ τ s 1 lo J
  /-- One more branch, for the constructor of this number; every branch after it names a
      **bigger** number. -/
  | cons {Γ : Ctx} {τ : TyWf} {J : JCtx} {s : LeanEnumSchema} {k lo : Nat}
      (i : Fin s.nOfConstructors)
      (branch : Term Sg Γ τ J) (rest : EnumSomeCases Sg Γ τ s k (i.val + 1) J)
      (hi : lo ≤ i.val := by ctor_ge) : EnumSomeCases Sg Γ τ s (k + 1) lo J

/-- The branches of a dispatch on, or a **fold** over, a sum type: one per constructor,
    in constructor order, **indexed by the schema itself** rather than by the list of
    constructors it denotes.  So the family has the same shape as
    `LeanScript.LeanTaggedUnionSchema`: a schema whose first constructor carries fields
    wants that constructor's branch, the branch of the constructor that must follow it,
    and then the branches of the rest; a schema that starts with field-less constructors
    wants a branch for each of them, through `LeanScript.CtorsWithPayloadFoldCases`.

    A branch binds `bind` of its constructor's field types, in declaration order.  A
    plain dispatch (`LeanScript.TaggedUnionCases`) is the family at `ι := TyWf` and
    `bind := id`: a branch binds the **fields** of its constructor, so de Bruijn index `0`
    of its body is that constructor's first field.

    `bind` is how the value of the fold reaches the branch: `LeanScript.TyWf.recBinders`
    binds each field, unfolded, and follows a field that is an occurrence of the type
    being folded over by the value of the fold at it, and
    `LeanScript.TyWf.famRecBinders` does the same for a member of a mutual family.  The
    schema the family is indexed by is the one the binder holds — written in *its* scope,
    not unfolded — because that is what says which fields are occurrences, and `ι` is
    what that scope is: `TyWfIn 1` for a lone binder, `TyWfIn (n + 2)` for a family.

    There is no default branch and no end-of-list before the constructors run out, so a
    fold is exhaustive by construction. -/
inductive TaggedUnionFoldCases (Sg : Sig) :
    (ι : Type) → (List ι → List TyWf) → Ctx → LeanTaggedUnionSchema ι → TyWf →
    optParam JCtx [] → Type 1
  /-- The branch of constructor `0` (which carries fields), the branch of the constructor
      after it, and the branches of the remaining constructors. -/
  | payloadFirst : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx}
      {fields : NonEmptyList ι} {next : List ι} {rest : List (List ι)},
      Term Sg (bind fields.toList ++ Γ) τ J → Term Sg (bind next ++ Γ) τ J →
      TaggedUnionFoldCasesRest Sg ι bind Γ rest τ J →
      TaggedUnionFoldCases Sg ι bind Γ (.payloadFirst fields next rest) τ J
  /-- The branch of constructor `0`, which carries no fields, and the branches of the
      constructors after it. -/
  | skip : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx}
      {rest : CtorsWithPayload ι},
      Term Sg (bind [] ++ Γ) τ J → CtorsWithPayloadFoldCases Sg ι bind Γ rest τ J →
      TaggedUnionFoldCases Sg ι bind Γ (.skip rest) τ J

/-- `LeanScript.TaggedUnionFoldCases`, on the constructors a
    `LeanScript.CtorsWithPayload` holds. -/
inductive CtorsWithPayloadFoldCases (Sg : Sig) :
    (ι : Type) → (List ι → List TyWf) → Ctx → CtorsWithPayload ι → TyWf →
    optParam JCtx [] → Type 1
  /-- The branch of the first constructor that carries fields, and the branches of the
      constructors after it. -/
  | here : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx}
      {fields : NonEmptyList ι} {rest : List (List ι)},
      Term Sg (bind fields.toList ++ Γ) τ J → TaggedUnionFoldCasesRest Sg ι bind Γ rest τ J →
      CtorsWithPayloadFoldCases Sg ι bind Γ (.here fields rest) τ J
  /-- The branch of a field-less constructor, and the branches of the constructors after
      it. -/
  | skip : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx}
      {rest : CtorsWithPayload ι},
      Term Sg (bind [] ++ Γ) τ J → CtorsWithPayloadFoldCases Sg ι bind Γ rest τ J →
      CtorsWithPayloadFoldCases Sg ι bind Γ (.skip rest) τ J

/-- `LeanScript.TaggedUnionFoldCases`, on the constructors a schema leaves
    unconstrained: one branch per constructor still to be given one. -/
inductive TaggedUnionFoldCasesRest (Sg : Sig) :
    (ι : Type) → (List ι → List TyWf) → Ctx → List (List ι) → TyWf →
    optParam JCtx [] → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx},
      TaggedUnionFoldCasesRest Sg ι bind Γ [] τ J
  /-- The branch of the next constructor. -/
  | cons : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {J : JCtx} {fs : List ι}
      {rest : List (List ι)},
      Term Sg (bind fs ++ Γ) τ J → TaggedUnionFoldCasesRest Sg ι bind Γ rest τ J →
      TaggedUnionFoldCasesRest Sg ι bind Γ (fs :: rest) τ J

/-- **What one branch of a depth-`k` fold of a recursive tagged union is**: either an
    answer, or a deeper look.

    `here` is an answer: a term in the context that binds the constructor's fields and,
    after each field that is an occurrence of the union, the value of the fold at it —
    `bind fs ++ Γ`, which is the branch of the plain fold.

    `deep` is a look one constructor further down: it names an occurrence among the
    fields (`LeanScript.SelfField`) and dispatches on it, with a depth one smaller, in
    that same context.  Each of *those* branches binds that subvalue's fields and the
    values of the fold at them, so a branch of the whole tree sees the answers at
    everything on the path it descended.

    `deepOuter` is a look into an occurrence among the fields of a node **above** this
    one, which the fold dispatched on earlier along the path (`LeanScript.OuterSelfField`):
    after looking into a node's left child a branch can still look into its right child,
    and so read the answers below **both**.  `outer` lists those nodes, innermost first;
    it is `[]` at the root, and a deeper look pushes the node it stands at.

    A look is only ever taken into a field of a node on the path, so every answer a
    branch is given is the answer at a **subvalue** of the value being folded.  Each look
    costs one unit of depth, so at depth `k` a branch looks at most `k` times in all.

    At depth `0` there is no `deep` and no `deepOuter`, so a branch is an answer and
    nothing else. -/
inductive FoldKBranch (Sg : Sig) :
    LeanTaggedUnionSchema (TyWfIn 1) → (List (TyWfIn 1) → List TyWf) → Ctx →
    List (TyWfIn 1) → TyWf → Nat → List (List (TyWfIn 1)) → Type 1
  /-- The answer, in the context that binds this constructor's fields and the values of
      the fold at its occurrences. -/
  | here : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ : Ctx} {fs : List (TyWfIn 1)} {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn 1))},
      Term Sg (bind fs ++ Γ) τ → FoldKBranch Sg l₀ bind Γ fs τ k outer
  /-- A deeper look: dispatch on one of this constructor's occurrences of the union, at
      a depth one smaller. -/
  | deep : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ : Ctx} {fs : List (TyWfIn 1)} {τ : TyWf} {k : Nat} {outer : List (List (TyWfIn 1))},
      SelfField fs → TaggedUnionFoldKCases Sg l₀ bind (bind fs ++ Γ) l₀ τ k (fs :: outer) →
      FoldKBranch Sg l₀ bind Γ fs τ (k + 1) outer
  /-- A deeper look into an occurrence of the union among the fields of a node above this
      one on the path — a sibling of a subvalue looked into before — at a depth one
      smaller. -/
  | deepOuter : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
      {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {fs : List (TyWfIn 1)} {τ : TyWf}
      {k : Nat} {outer : List (List (TyWfIn 1))},
      OuterSelfField outer →
      TaggedUnionFoldKCases Sg l₀ bind (bind fs ++ Γ) l₀ τ k (fs :: outer) →
      FoldKBranch Sg l₀ bind Γ fs τ (k + 1) outer

/-- The branches of a **depth-`k` fold** over a recursive tagged union: the same shape as
    `LeanScript.TaggedUnionFoldCases` — one branch per constructor, in constructor order,
    indexed by the schema itself, with no default and no end before the constructors run
    out — except that a branch is a `LeanScript.FoldKBranch`, which may look further down
    instead of answering.

    `l₀` is the union the fold is over, which a deeper look dispatches on again; `bind`
    is how the value of the fold reaches a branch, as for the plain fold; `outer` are the
    nodes dispatched on above, innermost first, whose other occurrences a branch may
    still look into (`[]` for the fold itself). -/
inductive TaggedUnionFoldKCases (Sg : Sig) :
    LeanTaggedUnionSchema (TyWfIn 1) → (List (TyWfIn 1) → List TyWf) → Ctx →
    LeanTaggedUnionSchema (TyWfIn 1) → TyWf → Nat → List (List (TyWfIn 1)) → Type 1
  /-- The branch of constructor `0` (which carries fields), the branch of the constructor
      after it, and the branches of the remaining constructors. -/
  | payloadFirst : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
      {bind : List (TyWfIn 1) → List TyWf} {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))}
      {fields : NonEmptyList (TyWfIn 1)} {next : List (TyWfIn 1)}
      {rest : List (List (TyWfIn 1))},
      FoldKBranch Sg l₀ bind Γ fields.toList τ k outer →
      FoldKBranch Sg l₀ bind Γ next τ k outer →
      TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ k outer →
      TaggedUnionFoldKCases Sg l₀ bind Γ (.payloadFirst fields next rest) τ k outer
  /-- The branch of constructor `0`, which carries no fields, and the branches of the
      constructors after it. -/
  | skip : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))} {rest : CtorsWithPayload (TyWfIn 1)},
      FoldKBranch Sg l₀ bind Γ [] τ k outer →
      CtorsWithPayloadFoldKCases Sg l₀ bind Γ rest τ k outer →
      TaggedUnionFoldKCases Sg l₀ bind Γ (.skip rest) τ k outer

/-- `LeanScript.TaggedUnionFoldKCases`, on the constructors a
    `LeanScript.CtorsWithPayload` holds. -/
inductive CtorsWithPayloadFoldKCases (Sg : Sig) :
    LeanTaggedUnionSchema (TyWfIn 1) → (List (TyWfIn 1) → List TyWf) → Ctx →
    CtorsWithPayload (TyWfIn 1) → TyWf → Nat → List (List (TyWfIn 1)) → Type 1
  /-- The branch of the first constructor that carries fields, and the branches of the
      constructors after it. -/
  | here : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))} {fields : NonEmptyList (TyWfIn 1)}
      {rest : List (List (TyWfIn 1))},
      FoldKBranch Sg l₀ bind Γ fields.toList τ k outer →
      TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ k outer →
      CtorsWithPayloadFoldKCases Sg l₀ bind Γ (.here fields rest) τ k outer
  /-- The branch of a field-less constructor, and the branches of the constructors after
      it. -/
  | skip : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))} {rest : CtorsWithPayload (TyWfIn 1)},
      FoldKBranch Sg l₀ bind Γ [] τ k outer →
      CtorsWithPayloadFoldKCases Sg l₀ bind Γ rest τ k outer →
      CtorsWithPayloadFoldKCases Sg l₀ bind Γ (.skip rest) τ k outer

/-- `LeanScript.TaggedUnionFoldKCases`, on the constructors a schema leaves
    unconstrained: one branch per constructor still to be given one. -/
inductive TaggedUnionFoldKCasesRest (Sg : Sig) :
    LeanTaggedUnionSchema (TyWfIn 1) → (List (TyWfIn 1) → List TyWf) → Ctx →
    List (List (TyWfIn 1)) → TyWf → Nat → List (List (TyWfIn 1)) → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))},
      TaggedUnionFoldKCasesRest Sg l₀ bind Γ [] τ k outer
  /-- The branch of the next constructor. -/
  | cons : ∀ {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf}
      {Γ τ} {k : Nat} {outer : List (List (TyWfIn 1))} {fs : List (TyWfIn 1)}
      {rest : List (List (TyWfIn 1))},
      FoldKBranch Sg l₀ bind Γ fs τ k outer →
      TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ k outer →
      TaggedUnionFoldKCasesRest Sg l₀ bind Γ (fs :: rest) τ k outer

/-- The branches of a dispatch on one member of a mutual family: whichever branches that
    member's shape calls for, and no default.  A `ctors` member is dispatched on by
    `LeanScript.TaggedUnionCases` over its unfolded schema — so one branch per
    constructor, in order — and the two single-constructor members have the one branch
    that binds what they hold. -/
inductive FamilyMemberCases (Sg : Sig) :
    Ctx → TyWf → LeanFamMemberSchema TyWf → optParam JCtx [] → Type 1
  /-- One branch per constructor of a member that has constructors. -/
  | ctors : ∀ {Γ τ} {J : JCtx} {l : LeanTaggedUnionSchema TyWf},
      TaggedUnionFoldCases Sg TyWf id Γ l τ J → FamilyMemberCases Sg Γ τ (.ctors l) J
  /-- The one branch of a record member, which binds its fields in declaration order. -/
  | record : ∀ {Γ τ} {J : JCtx} {fs : LeanRecordSchema TyWf},
      Term Sg (fs.toList ++ Γ) τ J → FamilyMemberCases Sg Γ τ (.record fs) J
  /-- The one branch of a newtype member, which binds its body. -/
  | alias : ∀ {Γ τ} {J : JCtx} {b : TyWf},
      Term Sg (b :: Γ) τ J → FamilyMemberCases Sg Γ τ (.alias b) J

/-- The branches of a dispatch on **some** of the constructors of one member of a mutual
    family, used with a default.  There is one case and not three: a member with a single
    constructor has nothing to leave out, so a partial dispatch on it would be its
    `LeanScript.Term.mutualRecursiveFamily_casesOn` or its default and nothing else, and
    the type makes that unwritable. -/
inductive FamilyMemberSomeCases (Sg : Sig) :
    Ctx → TyWf → LeanFamMemberSchema TyWf → optParam JCtx [] → Type 1
  /-- Branches for some of the constructors of a member that has constructors, named in
      strictly increasing order, at least one of them, and fewer of them than the member
      has constructors — so the default of the dispatch is reachable. -/
  | ctors {Γ : Ctx} {τ : TyWf} {J : JCtx} {l : LeanTaggedUnionSchema TyWf} {k : Nat}
      (cases : TaggedUnionSomeCases Sg Γ l τ k 0 J) (hk : k < l.length := by ctor_lt) :
      FamilyMemberSomeCases Sg Γ τ (.ctors l) J

/-- The branches of a **fold** over one member of a mutual family: as
    `LeanScript.FamilyMemberCases`, but each branch is also given the value of the fold
    at every field that is an occurrence of a member of the family
    (`LeanScript.TyWf.famRecBinders`), so this one is indexed by the member as the family
    holds it rather than by its unfolding. -/
inductive FamilyMemberFoldCases (Sg : Sig) :
    (ι : Type) → (List ι → List TyWf) → Ctx → TyWf → LeanFamMemberSchema ι → Type 1
  /-- One branch per constructor of a member that has constructors. -/
  | ctors : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ}
      {l : LeanTaggedUnionSchema ι},
      TaggedUnionFoldCases Sg ι bind Γ l τ → FamilyMemberFoldCases Sg ι bind Γ τ (.ctors l)
  /-- The one branch of a record member. -/
  | record : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {fs : LeanRecordSchema ι},
      Term Sg (bind fs.toList ++ Γ) τ → FamilyMemberFoldCases Sg ι bind Γ τ (.record fs)
  /-- The one branch of a newtype member. -/
  | alias : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {b : ι},
      Term Sg (bind [b] ++ Γ) τ → FamilyMemberFoldCases Sg ι bind Γ τ (.alias b)

/-- The branches of a fold over a whole mutual family: the branches of each member, in
    declaration order.  `LeanScript.Term.mutualRecursiveFamily_rec` asks for the list
    indexed by `f.members`, so **every** member has its branches and a fold cannot fall
    off the end wherever the recursion goes. -/
inductive FamilyFoldCases (Sg : Sig) :
    (ι : Type) → (List ι → List TyWf) → Ctx → TyWf → List (LeanFamMemberSchema ι) →
    Type 1
  /-- Every member has its branches. -/
  | nil : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ}, FamilyFoldCases Sg ι bind Γ τ []
  /-- The branches of the next member. -/
  | cons : ∀ {ι : Type} {bind : List ι → List TyWf} {Γ τ} {m : LeanFamMemberSchema ι}
      {ms : List (LeanFamMemberSchema ι)},
      FamilyMemberFoldCases Sg ι bind Γ τ m → FamilyFoldCases Sg ι bind Γ τ ms →
      FamilyFoldCases Sg ι bind Γ τ (m :: ms)

/-- **What one branch of a depth-`k` fold of a mutual family is**: either an answer, or a
    deeper look.  It is `LeanScript.FoldKBranch` in the scope of a family.

    `here` is an answer: a term in the context that binds the constructor's fields and,
    after each field that is an occurrence of a member of the family, the value of the
    fold at it — `bind fs ++ Γ`, which is the branch of the plain fold.

    `deep` is a look one constructor further down: it names a field that is an occurrence
    of member `i` (`LeanScript.FamilyMemberField`), says which member of the family that
    is (`LeanScript.FamilyMemberAt`), and dispatches on **that member** — which need not
    be the member the branch belongs to — with a depth one smaller, in that same context.
    Each of those branches binds the
    subvalue's fields and the values of the fold at them, so a branch of the whole tree
    sees the answers at everything on the path it descended.

    `deepOuter` is a look into an occurrence among the fields of a node **above** this
    one, which the fold dispatched on earlier along the path
    (`LeanScript.FamilyOuterMemberField`): after looking into one field of a node a branch
    can still look into another, and so read the answers below **several** subvalues.
    `outer` lists those nodes, innermost first; it is `[]` at the root, and a deeper look
    pushes the node it stands at.

    A look is only ever taken into a field of a node on the path, so every answer a branch
    is given is the answer at a **subvalue** of the value being folded.  Each look costs
    one unit of depth, so at depth `k` a branch looks at most `k` times in all.

    `ms₀` is the whole family — every member, in declaration order — because that is
    what says which member `i` names; at depth `0` there is no `deep` and no `deepOuter`,
    so a branch is an answer and nothing else. -/
inductive FamilyFoldKBranch (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → List (TyWfIn (n + 2)) → TyWf → Nat →
    List (List (TyWfIn (n + 2))) → Type 1
  /-- The answer, in the context that binds this constructor's fields and the values of
      the fold at its occurrences. -/
  | here : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
      {fs : List (TyWfIn (n + 2))} {τ : TyWf} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))},
      Term Sg (bind fs ++ Γ) τ → FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer
  /-- A deeper look: dispatch on the member this field is an occurrence of, at a depth
      one smaller. -/
  | deep {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {fs : List (TyWfIn (n + 2))}
      {τ : TyWf} {k i : Nat} {m : LeanFamMemberSchema (TyWfIn (n + 2))}
      {outer : List (List (TyWfIn (n + 2)))}
      (field : FamilyMemberField i fs) (member : FamilyMemberAt ms₀ i m)
      (cases : FamilyMemberFoldKCases Sg n ms₀ bind (bind fs ++ Γ) τ m k (fs :: outer)) :
      FamilyFoldKBranch Sg n ms₀ bind Γ fs τ (k + 1) outer
  /-- A deeper look into an occurrence of a member among the fields of a node above this
      one on the path — a sibling of a subvalue looked into before — at a depth one
      smaller. -/
  | deepOuter {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {fs : List (TyWfIn (n + 2))}
      {τ : TyWf} {k i : Nat} {m : LeanFamMemberSchema (TyWfIn (n + 2))}
      {outer : List (List (TyWfIn (n + 2)))}
      (field : FamilyOuterMemberField i outer) (member : FamilyMemberAt ms₀ i m)
      (cases : FamilyMemberFoldKCases Sg n ms₀ bind (bind fs ++ Γ) τ m k (fs :: outer)) :
      FamilyFoldKBranch Sg n ms₀ bind Γ fs τ (k + 1) outer

/-- The branches of a **depth-`k` fold** over one member of a mutual family: as
    `LeanScript.FamilyMemberFoldCases`, except that a branch is a
    `LeanScript.FamilyFoldKBranch`, which may look further down instead of answering.
    `outer` are the nodes dispatched on above, innermost first, whose other occurrences a
    branch may still look into (`[]` for the fold itself). -/
inductive FamilyMemberFoldKCases (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → TyWf →
    LeanFamMemberSchema (TyWfIn (n + 2)) → Nat → List (List (TyWfIn (n + 2))) → Type 1
  /-- One branch per constructor of a member that has constructors. -/
  | ctors : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {l : LeanTaggedUnionSchema (TyWfIn (n + 2))},
      FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer →
      FamilyMemberFoldKCases Sg n ms₀ bind Γ τ (.ctors l) k outer
  /-- The one branch of a record member. -/
  | record : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {fs : LeanRecordSchema (TyWfIn (n + 2))},
      FamilyFoldKBranch Sg n ms₀ bind Γ fs.toList τ k outer →
      FamilyMemberFoldKCases Sg n ms₀ bind Γ τ (.record fs) k outer
  /-- The one branch of a newtype member. -/
  | alias : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))} {b : TyWfIn (n + 2)},
      FamilyFoldKBranch Sg n ms₀ bind Γ [b] τ k outer →
      FamilyMemberFoldKCases Sg n ms₀ bind Γ τ (.alias b) k outer

/-- `LeanScript.TaggedUnionFoldKCases`, for a member of a mutual family: one branch per
    constructor, in constructor order, indexed by the member's schema, with no default
    and no end before the constructors run out. -/
inductive FamilyTaggedUnionFoldKCases (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → LeanTaggedUnionSchema (TyWfIn (n + 2)) →
    TyWf → Nat → List (List (TyWfIn (n + 2))) → Type 1
  /-- The branch of constructor `0` (which carries fields), the branch of the constructor
      after it, and the branches of the remaining constructors. -/
  | payloadFirst : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {fields : NonEmptyList (TyWfIn (n + 2))} {next : List (TyWfIn (n + 2))}
      {rest : List (List (TyWfIn (n + 2)))},
      FamilyFoldKBranch Sg n ms₀ bind Γ fields.toList τ k outer →
      FamilyFoldKBranch Sg n ms₀ bind Γ next τ k outer →
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ k outer →
      FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ (.payloadFirst fields next rest) τ k outer
  /-- The branch of constructor `0`, which carries no fields, and the branches of the
      constructors after it. -/
  | skip : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {rest : CtorsWithPayload (TyWfIn (n + 2))},
      FamilyFoldKBranch Sg n ms₀ bind Γ [] τ k outer →
      FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ rest τ k outer →
      FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ (.skip rest) τ k outer

/-- `LeanScript.FamilyTaggedUnionFoldKCases`, on the constructors a
    `LeanScript.CtorsWithPayload` holds. -/
inductive FamilyCtorsWithPayloadFoldKCases (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → CtorsWithPayload (TyWfIn (n + 2)) →
    TyWf → Nat → List (List (TyWfIn (n + 2))) → Type 1
  /-- The branch of the first constructor that carries fields, and the branches of the
      constructors after it. -/
  | here : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {fields : NonEmptyList (TyWfIn (n + 2))} {rest : List (List (TyWfIn (n + 2)))},
      FamilyFoldKBranch Sg n ms₀ bind Γ fields.toList τ k outer →
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ k outer →
      FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ (.here fields rest) τ k outer
  /-- The branch of a field-less constructor, and the branches of the constructors after
      it. -/
  | skip : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {rest : CtorsWithPayload (TyWfIn (n + 2))},
      FamilyFoldKBranch Sg n ms₀ bind Γ [] τ k outer →
      FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ rest τ k outer →
      FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ (.skip rest) τ k outer

/-- `LeanScript.FamilyTaggedUnionFoldKCases`, on the constructors a schema leaves
    unconstrained: one branch per constructor still to be given one. -/
inductive FamilyTaggedUnionFoldKCasesRest (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → List (List (TyWfIn (n + 2))) → TyWf →
    Nat → List (List (TyWfIn (n + 2))) → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))},
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ [] τ k outer
  /-- The branch of the next constructor. -/
  | cons : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {outer : List (List (TyWfIn (n + 2)))}
      {fs : List (TyWfIn (n + 2))} {rest : List (List (TyWfIn (n + 2)))},
      FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer →
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ k outer →
      FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ (fs :: rest) τ k outer

/-- The branches of a **depth-`k` fold** over a whole mutual family: the branches of each
    member, in declaration order, as `LeanScript.FamilyFoldCases` — so **every** member
    has its branches and a fold cannot fall off the end wherever the recursion goes, nor
    wherever a deeper look lands. -/
inductive FamilyFoldKCases (Sg : Sig) :
    (n : Nat) → List (LeanFamMemberSchema (TyWfIn (n + 2))) →
    (List (TyWfIn (n + 2)) → List TyWf) → Ctx → TyWf →
    List (LeanFamMemberSchema (TyWfIn (n + 2))) → Nat → Type 1
  /-- Every member has its branches. -/
  | nil : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat},
      FamilyFoldKCases Sg n ms₀ bind Γ τ [] k
  /-- The branches of the next member. -/
  | cons : ∀ {n : Nat} {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
      {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ τ} {k : Nat}
      {m : LeanFamMemberSchema (TyWfIn (n + 2))}
      {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))},
      FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k [] →
      FamilyFoldKCases Sg n ms₀ bind Γ τ ms k →
      FamilyFoldKCases Sg n ms₀ bind Γ τ (m :: ms) k

end

/-! ## Plain dispatches

A plain dispatch on a tagged union is the fold-case family at `ι := TyWf` and
`bind := id`, so a branch's context `id fs ++ Γ` is `fs ++ Γ` by definition.  These
abbreviations are the names the rest of the project uses for it. -/

/-- The branches of a dispatch on a tagged union: one per constructor, in constructor
    order, each binding its constructor's fields, and no default — exhaustive by
    construction.  It is `LeanScript.TaggedUnionFoldCases` at `ι := TyWf`, `bind := id`. -/
abbrev TaggedUnionCases (Sg : Sig) (Γ : Ctx) (l : LeanTaggedUnionSchema TyWf) (τ : TyWf)
    (J : JCtx := []) : Type 1 :=
  TaggedUnionFoldCases Sg TyWf id Γ l τ J

/-- The branches of the constructors a `LeanScript.CtorsWithPayload` holds: the tail of
    `LeanScript.TaggedUnionCases`. -/
abbrev CtorsWithPayloadCases (Sg : Sig) (Γ : Ctx) (c : CtorsWithPayload TyWf) (τ : TyWf)
    (J : JCtx := []) : Type 1 :=
  CtorsWithPayloadFoldCases Sg TyWf id Γ c τ J

/-- The branches of the constructors a schema leaves unconstrained: one branch per
    constructor still to be given one, each binding that constructor's fields. -/
abbrev TaggedUnionCasesRest (Sg : Sig) (Γ : Ctx) (cs : List (List TyWf)) (τ : TyWf)
    (J : JCtx := []) : Type 1 :=
  TaggedUnionFoldCasesRest Sg TyWf id Γ cs τ J

end LeanScript

end
