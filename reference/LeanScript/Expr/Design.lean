module

/-!
# The design of `LeanScript.Term`

This module carries the prose of the grammar: why the recursion discipline is what it is,
and the four decisions that turned the original, untyped sketch of the term language into
the `mutual` block of `LeanScript.Expr.Term`.  It
declares nothing, so it costs nothing to import; the grammar itself is in
`LeanScript.Expr.Term`, and the context of `k` previous answers a fold is written in is in
`LeanScript.Expr.NatRecCtx`.
-/

/-!
# `Term`: the one grammar, terminating by construction

## The recursion discipline, and why four of the six kinds are unrepresentable

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | using specialized Term.natFix, arrayFix, etc |
| well-founded recursive | not supported yet |
| partial fixpoint | unrepresentable: there is no constructor for a fixpoint that does not descend |
| coinductive / inductive fixpoint | unrepresentable: `Ty` has no coinductive former and `Term` has no free fixpoint |
| `partial` | unrepresentable: same |
| `unsafe` | unrepresentable: same |

* **No `IO`, and no effect at all.**  `Ty` has no effectful former, so an `IO`-returning
  declaration has no image in this language.

* **No failure.**
  1. an exhausted recursion is not possible;
  2. an out-of-range index is not possible: a constructor is a *number with a proof* that
     the type has it, and a field is read by an eliminator that *binds* the fields of the
     constructor it matched, never by a lookup;
  3. a schema is never consulted for a default — there is no `Ty.dflt`.

* **A delay is not a memo cell.**  `Term.lazyForce (Term.lazyMk e)` runs `e`, and
  running it twice runs `e` twice: there is no memoisation.  `LeanScript.Den` makes
  `Ty.lazy` the identity on values — at this layer a delay carries nothing beyond the
  value, and the wrapper only decides what JavaScript is printed later.  `Ty.thunk`,
  which *is* memoised in JavaScript, has `Term.thunkMk` and `Term.thunkForce`: they
  denote the same identity, and the difference between the two wrappers is the code
  printed for them, not the value.  `task` and `promise` are commented out of
  `LeanPrimTyCovariant`.
-/

/-! ## The grammar

The `mutual` block of `LeanScript.Expr.Term` is the original sketch of the term language
(an untyped grammar with `sorry` in type position; it is in the git history), made to
elaborate.  Four things had to be decided to get there.

**A term is indexed by a *type of the language*, not by a tree.**  `Ty` is a tree, and not
every tree is a type: a binder may mention itself nowhere, may mention itself in the
domain of a function, or may state an equation no value satisfies.  `Term` is therefore
indexed by `LeanScript.TyWf` — a tree **with** the proof that it is a type — and `Ctx` is a
list of those, so a tree that is not a type has no term of it at all, and the proof is
composed once where the type is written rather than checked again at each use.  A payload
written inside a binder is `LeanScript.TyWfIn n`, the same bundle for the scope the binder
opens, and the schemas of the grammar are schemas **of bundles**: the fields of a record
are a `LeanRecordSchema TyWf`, the payload of a recursive union a
`LeanTaggedUnionSchema (TyWfIn 1)`, the members of a mutual family a
`LeanMutualRecFamily (TyWfIn (n + 2))` — a family has at least two members.  The trees are
the `map` of the schema to `toTy`, so nothing is rechecked and nothing is carried twice.

**A literal is a literal *of its own type*.**  The sketch wrote `bool_mk : ∀ {Γ σ τ}, Bool`,
which says nothing about the term being built.  Here every introduction form ends in the
type it introduces: `bool_mk : Bool → Term Sg Γ (.prim .bool)`, and likewise for each leaf
of `LeanScript.LeanPrimTy`.  `bitvec_mk` carries the width's positivity proof, defaulted
by `by decide`, because `LeanPrimTy.bitvec` carries it; `stringPos_mk` carries the string
the position is into, because `LeanPrimTy.stringPos` is indexed by it.

**A `_casesOn` is a `match`; a `_rec` really is a recursor.**  The name of an eliminator
now says which of the two it is.

* `xxx_casesOn` is the *case analysis* of `xxx` — its `Xxx.casesOn`, with the fields of
  the matched constructor **bound** in the branch, no motive and no recursive value.
  So `nat_casesOn` has a zero branch and a successor branch binding the predecessor,
  `int_casesOn` has an `ofNat` branch and a `negSucc` branch each binding a `nat`, and
  the wrapper types (`uint8`, …, `int64`, `char`, `float`, `float32`, `floatModel`,
  `float32Model`, `stringPosRaw`, `stringPos`, `substringRaw`) each have the one branch
  that binds their representation, with the proof fields erased — they are propositions,
  so they carry nothing at runtime.
* `xxx_rec` is `Xxx.rec` with a **non-dependent motive**: a fold.  Its branch is given
  the value of the recursion on the smaller value, so it is not a call the branch can
  make on anything it likes, and a term is still terminating by construction.  Only the
  two recursive types of the language have one: `nat_rec` (`Nat.rec`) and `array_rec`
  (the fold of a list, `List.rec`).  For every other type here `Xxx.rec` and
  `Xxx.casesOn` are the same eliminator — the type is not recursive — and only the
  `_casesOn` name is given, since that is the one that describes what the constructor
  does.

Forcing a delay is not an eliminator of an inductive type at all — `Ty.lazy` is an erased
unit function and `Ty.thunk` is a `Thunk`, whose eliminator is `Thunk.get` — so the two
are called `lazy_force` and `thunk_force` rather than `_rec`.

**Three eliminators are deliberately absent**, because their fields have no type in this
language:

* `bitvec_casesOn` would bind a `Fin (2 ^ w)`, and `Fin` is not a `LeanPrimTy`;
* `string_casesOn` would bind a `ByteArray`, which is commented out of `LeanPrimTy` (a
  string is a leaf here, taken apart by the runtime operations rather than by a `match`);
* `stringSlice_casesOn` would bind two `String.Pos s` where `s` is the string bound by
  the *same* branch, and `Ctx` is a list of types, so it cannot express a binding whose
  type mentions an earlier binding of the same branch.

**The branches of a dispatch follow the *schema*, not a list.**  `TaggedUnionCases` is
indexed by the `LeanTaggedUnionSchema TyWf` itself, so its constructors mirror that
schema's: `payloadFirst` wants the branch of constructor `0` (binding its fields), the
branch of the constructor that must follow it, and `TaggedUnionCasesRest` for the rest;
`skip` wants the branch of the field-less constructor `0` and then
`CtorsWithPayloadCases`, which mirrors `CtorsWithPayload` in the same way.  Nothing has
to be said about `toList` to write or to take apart a dispatch.  `EnumCases` is indexed
by the `LeanEnumSchema` itself in the same way: `three` is the branches of the three
constructors an enum has at minimum, and `cons` is one more branch for one more
constructor.

**A dispatch may name only some constructors, if it has a default.**
`enum_casesOnWithDefault` and `taggedUnion_casesOnWithDefault` take a *list* of branches
(`EnumSomeCases`, `TaggedUnionSomeCases`) — each naming its constructor by number, and,
for a union, binding that constructor's fields — plus the default branch every
unnamed constructor takes.  The term is still total: the default covers everything the
list leaves out.

Both lists are moreover **validated by their type**: `EnumSomeCases` and
`TaggedUnionSomeCases` each carry the smallest constructor number a branch may still
name, so the numbers strictly increase — they are in order and none is named twice —
and neither list has an empty case, so at least one constructor is named.

**The four recursive shapes of `Ty` have the same four forms as the others.**  A value of
`Ty.recTaggedUnion l` — and of `Ty.recObject`, `Ty.recAlias`,
`Ty.mutualRecursiveFamily` — is a value of the shape the binder holds with the binder's
own occurrences (`Ty.self`, `Ty.familyMember i`) instantiated to the binder itself, which
is the *unfolding* of `LeanScript.Ty.Unfold`.  So an introduction form takes the fields
**unfolded** (`TyWf.recTaggedUnionUnfold`, `TyWf.recObjectUnfold`, `TyWf.recAliasUnfold`),
and a `_casesOn` branches on the unfolded schema — which has the same constructors, in
the same order, as the one the binder holds, so the branch families above serve unchanged
and a dispatch is still exhaustive by construction.

Each of the four also has a `_rec`: the fold, `Xxx.rec` with a non-dependent motive.  Its
branches are `LeanScript.TaggedUnionFoldCases` (or the single branch of a record or a
newtype).  `TaggedUnionCases` *is* that family, at `ι := TyWf` and `bind := id` (an
abbreviation declared after the `mutual` block); a fold differs only in what a branch binds:
`LeanScript.TyWf.recBinders` binds every field, unfolded, and follows a field that *is* an
occurrence of the type being folded over by the value of the fold at that field.  As in
`nat_rec` and `array_rec` the recursive value is *given* to the branch, so a term is still
terminating by construction.  A field that mentions the type only inside another former
(an array of it, say) is bound as it is: folding it would be a map, which the grammar does
not have.

**An introduction form builds a value of a type, not of a tree.**  A `Ty` is a tree, and
not every tree is a type: a binder may mention itself nowhere, may mention itself in the
*domain* of a function — `μX. X ⇒ Nat`, at which a term language diverges — or may state
an equation no value satisfies, like `μX. Nat × X`.  `LeanScript.Ty.Wf` is the
proposition that rules all three out, and the four recursive introduction forms carry it
for the tree they build a value of, with `ty_wf` as its default, so a tree that is not a
type has no value in the grammar and nothing has to be written by hand for a schema
written out.  The eliminators do not carry it: a tree that is not a type has no value to
take apart in the first place.

The partial forms follow the same rule as elsewhere: `recTaggedUnion_casesOnWithDefault`
and `mutualRecursiveFamily_casesOnWithDefault` exist because those shapes have
constructors to leave out, while a recursive record and a recursive newtype have one
constructor each and so have no partial form at all.  A mutual family is dispatched on
member by member (`LeanScript.FamilyMemberValue`, `LeanScript.FamilyMemberCases`), and
its fold asks for the branches of **every** member (`LeanScript.FamilyFoldKCases`), with
one motive answering for all of them, and a branch of that fold may look one constructor
further down — into an occurrence of any member — as the fold of a recursive tagged union
may.
-/

/-! ## Strict A-normal form, with join points

The grammar is in **strict A-normal form by construction**, as three layers:

* `LeanScript.Atom` — an operand: a **variable**, and nothing else;
* `LeanScript.Comp` — **one** computation step whose operands are atoms and which neither
  branches nor folds: a reference to a top-level declaration, a literal of a terminal
  type, an application, an extern call, a constructor, a delay, a force or a `fun`.  The
  terms it holds are bodies it does not run — of a function or a delay;
* `LeanScript.Term` — a block of `let`s (`Term.letE`), each binding a `Comp`, ending in a
  **tail**: `Term.ret x` of a variable, a dispatch (`…_casesOn…`), a fold (`…_rec`), a
  checked extern call, or a jump to a join point.

So every intermediate value — a declaration and a literal included — is named by a `let`
before it is used; a `let` never binds another `let`, a mere variable (there is no copy
`let x = y`), a dispatch or a fold; a step is never in tail position unnamed (a block whose
value is that of a step `c` is `let x = c; ret x`, `Term.ofComp`), so each block has one
shape; and a dispatch or a fold is always the last thing its block does.  A dispatch or a fold whose value is **used** by what
follows is written with a **join point**: `Term.letJ jp body` binds `jp` — a term with one
parameter — as join point `0` of `body`, and each branch of the dispatch in `body` ends by
jumping to it (`Term.jump j a`, with an atom as argument).  A fold hands its answer to a
`LeanScript.Dest`: `Dest.ret` when it is the value of the whole term, `Dest.jump j` when it
goes to a join point.

**Join points have their own context.**  `Term Sg Γ τ J` is indexed by `J : JCtx`, the
parameter types of the join points in scope, apart from the context `Γ` of variables: a
join point is not a value, it cannot be passed, stored or called, only jumped to from tail
position, and every one of them answers with the `τ` of the term that binds it.  A join
point is not recursive (`jp` sees the join points bound before it, not itself), so the
grammar stays terminating by construction.  A function body, a delay and a fold branch
start with `J = []`: a fold branch runs once per step of the fold, so jumping out of it
would not be a tail.  `J` is an `optParam` defaulting to `[]`, so `Term Sg Γ τ` is a
whole body.

**Direct style is still writable.**  `LeanScript.Expr.Build` gives each constructor of the
direct-style grammar a function of the same name (`Term.ap`, `Term.nat_rec'`,
`Term.record_mk`, `Term.letE'`, …) that takes arbitrary terms: an operand that is already
a variable is used as it is, one that ends in a computation is let-bound (a step that reads
no variable — a declaration, a literal — is bound last, right before its use), and one
that ends in a dispatch or a fold becomes the tail, with the rest of the computation as a
join point (`Term.bindAtom`, `Term.toJump`).  `let x = y; body` in direct style is `body`
renamed (`Term.bind`).  `TermTests.AnfTest` pins the exact terms these build.
-/
