# `LeanScript/Ty/` — the type language

Everything about `Ty` lives here: the tree, the proposition that a tree is a type, the
class that gives a Lean type its tree, and the `deriving` handler that writes one.
Nothing else in `LeanScript/` defines any of it; `LeanScript/ExprCtx.lean` and
`LeanScript/Expr/` are consumers — a context and the type of a term are `TyWf`, the
bundle, so every type a term mentions is a type by construction — and
`LeanScript/LeanPrimTy.lean` and `LeanScript/LeanPrimTyCovariant.lean` are the leaf types,
which say nothing about recursion and are shared with the backends.

There is no module that gathers the others: a file imports the modules it uses, one by
one.

## Reading order

| module | what it holds |
| :-- | :-- |
| `LeanScript.Ty.Schema` | the shapes a source declaration can have, parametrised by a type language, with their counting invariants in their types |
| `LeanScript.Ty.Shape` | `TyShape α` — one node of the language, with its children abstracted |
| `LeanScript.Ty.Traversable` | the `LawfulTraversable` / `LawfulFunctor` instances of the schemas, `LeanPrimTyCovariant` and `TyShape`, derived together in one module |
| `LeanScript.Ty.Ty` | `Ty`: one tree for a closed type and for a type inside a recursive declaration alike, its shapes as patterns, its children and its equality |
| `LeanScript.Ty.TyBEq` | that `Ty.beq` *is* equality, and the `LawfulBEq` and `DecidableEq` instances that follow |
| `LeanScript.Ty.Wf` | `Ty.Wf` — that a tree *is* a type — as an inductive proposition: scope, real recursion, positivity and inhabitation (`Ty.HabIn`) |
| `LeanScript.Ty.WfFacts` | inversion for `Ty.Wf`, and what it therefore rules out: a free or captured occurrence, a binder that recurses on nothing, a type with no values, a negative occurrence |
| `LeanScript.Ty.Unfold` | putting a binder back in for its own occurrences: the unfolding of each recursive shape, and what a branch of a fold over one binds |
| `LeanScript.Ty.WfSubst` | that unfolding a type gives types, which is what makes the bundled unfoldings below well formed |
| `LeanScript.Ty.WfTactic` | `ty_wf`, which writes that proof, reusing the proof of every subtree that has one |
| `LeanScript.Ty.TyWf` | `TyWf`: a tree together with the proof that it is one, whose proof field is written by `ty_wf` unless one is given |
| `LeanScript.Ty.TyWfIn` | `TyWfIn n` — the same bundle for a tree written inside a binder — and the language's constructors at the level of bundles (`TyWf.prim`, `⇒`, `TyWf.record`, `TyWf.taggedUnion`, the four recursive shapes, and their unfoldings), each composing its proof out of its arguments' |
| `LeanScript.Ty.Class` | `LeanScriptTyWf`: the bundled tree of a Lean type, with `tyWfOf`, `tyOf` and `tyWf` |
| `LeanScript.Ty.Instances` | the instances the language comes with: the terminal types, `Array`, `Thunk`, `→`, and the library types |
| `LeanScript.Ty.Deriving` | `deriving LeanScriptTyWf`, and the table that lets two declarations with the same tree share one |

`LeanScript.Ty.WfTactic` comes *before* `LeanScript.Ty.TyWf` because the bundle's proof
field is `:= by ty_wf`; the tactic therefore does not import the bundle, and names the two
projections it recognises a tree of one by instead.

## What is not modelled

A declaration with a field whose value is a **type** — `State : Type`, and any field whose
type ends in `Type` — hides a type from the language, and `deriving LeanScriptTyWf`
refuses it: *existential typing is not yet supported*.  `TyTests/InductiveTypesTest/`
pins that refusal for a stream `Unfold`, a client/server pair and a compiler engine, and
shows the parameterised declarations (`ClientTwin`, `ServerTwin`) that *are* modelled.
Values of such declarations, and functions of the non-recursive ones, are still translated
to terms (`LeanScript/ToTerm/ExistentialArgs.lean`, `TermTests/StructRecTest/Existential.lean`,
`TermTests/StructRecTest/ExistentialUnion.lean`).

A type field that no value depends on is not an existential: in a family indexed by types
(`TExpr : Type → Type`, with `pair {α β} (a : TExpr α) (b : TExpr β) : TExpr (α × β)`) the
`α` and `β` appear only in indices, which are erased, so the declaration has one tree
(`TermTests/StructRecTest/IndexedGADT.lean`).

## Tests

`TyTests/InductiveTypesTest/` — what each shape of Lean declaration is modelled by,
and what is refused; `TyTests/SharedTreesTest.lean` — one tree per shape, one check per
type; `TyTests/CrossModuleSharingTest.lean` — that the sharing spans modules;
`TyTests/WfTest.lean` — what `Ty.Wf` admits and refuses;
`TyTests/DocumentedMistakesTest.lean` — every defect of the earlier representations with
the theorem or the message that excludes it now.

Tests of terms, evaluation and `#leanscript_to_term` (including
`TermTests/InductiveTypesTest/Existentials.lean`) live in `TermTests/`.
