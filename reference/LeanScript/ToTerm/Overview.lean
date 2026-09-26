module

/-!
# `#leanscript_to_term`: a Lean definition, as a `Term`

```lean
def addOne (n : Nat) : Nat := n + 1   -- with `add` declared in the signature

def addOne_term : Term sg [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term addOne
```

`#leanscript_to_term e` reads the Lean definition `e` and builds the `LeanScript.Term`
that means the same thing.  It is a **term** elaborator, so the type it is checked
against says which signature and which context the term is written in: the expected type
is a `LeanScript.Term Sg Γ τ`, and `Sg` is the signature the translation resolves
top-level names against.

The signature can be named instead of read off the expected type, and then the type of
the translation does not have to be written at all:

```lean
def addOne_term' := #leanscript_to_term (sig := sg) addOne
```

With neither an expected type nor a `(sig := …)`, the empty signature and the empty
context are used.

## What may appear in a translated definition

| Lean | `Term` |
| :-- | :-- |
| `fun x => b`, `f a`, `let x := v; b` | `lam`, `ap`, `letE` |
| a literal of a terminal type | `bool_mk`, `nat_mk`, `int_mk`, `string_mk`, … |
| `if b then t else e` (`b : Bool`), `cond` | `bool_casesOn` |
| `if n = 0 then t else e` (`n : Nat`) | `nat_casesOn` |
| `fun _ : Unit => b` | `b`: a `Unit` binder is erased, as a `Unit` argument is |
| a constructor of a datatype with existentials | its `#leanscript_ctor` constructor function (see below) |
| a constructor of a record-shaped type | `record_mk` |
| a constructor of a tagged union | `taggedUnion_mk` |
| a constructor of an enum | `enum_mk` |
| an array literal | `array_mk` |
| a constructor of `List` | `recTaggedUnion_mk` |
| `Thunk.mk (fun _ => e)`, `t.get` | `thunk_mk`, `thunk_force` |
| `match`, `X.casesOn`, a projection | `record_casesOn`, `taggedUnion_casesOn`, `enum_casesOn`, `bool_casesOn`, `recTaggedUnion_casesOn`, `nat_casesOn`; on a recursive record, a recursive newtype or a member of a `mutual` block, `recObject_casesOn`, `recAlias_casesOn`, `mutualRecursiveFamily_casesOn` (`LeanScript.ToTerm.TransRecCases`) |
| a `match` that leaves constructors out | `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault`, `recTaggedUnion_casesOnWithDefault` |
| `Nat.rec`, `List.rec` (non-dependent motive), a structural recursion Lean compiled through `Nat.brecOn` / `List.brecOn` | `nat_rec`, `recTaggedUnion_rec 0` — or `nat_casesOn` / `recTaggedUnion_casesOn`, when the branch does not use the value of the fold |
| a recursion on a `Nat` that descends `k + 1` steps (`fib`, the tribonacci numbers, …) | `nat_rec k` |
| `go a.toList`, where `go` is a structural recursion on lists that descends `k + 1` elements and reads only the head, the next `k` elements and the values at the suffixes | `array_rec k` on the array `a` — see `TermTests/ArrayRecToTermTest/` |
| a structural recursion on a **list** that descends `k + 1` constructors (`fib` of the length, the tribonacci numbers, …) | `recTaggedUnion_rec k` — see `TermTests/RecUnionToTermTest/` and `LeanScript.ToTerm.TransRecUnion` |
| a structural recursion on a **recursive tagged union** — an inductive type with several constructors whose fields are the type itself or values that do not mention it, such as `inductive Tree \| leaf \| node (l : Tree) (v : Nat) (r : Tree)` — whose branches look at most `k` times further down, into one subvalue or into several (the grandchildren below both children of a node) | `recTaggedUnion_rec k` — see `TermTests/RecUnionToTermTest/` and `LeanScript.ToTerm.TransRecUnion` |
| a structural recursion on a **recursive record** — an inductive type with one constructor that mentions itself inside a union field, such as `inductive Cell \| mk (label : Nat) (next : Option Cell)` — that reads the labels and the values of the recursion at most `k + 1` levels down (`fib` on a chain, the tribonacci numbers, …) | `recObject_rec k` — see `TermTests/RecObjectToTermTest/` and `LeanScript.ToTerm.TransRecObject` |
| a constructor of a recursive record | `recObject_mk` |
| a structural recursion on a **recursive newtype** — an inductive type with one constructor of one field that mentions itself inside a union, such as `inductive Chain \| mk (link : Link Chain)` — that reads the labels and the values of the recursion at most `k + 1` levels down | `recAlias_rec k` — see `TermTests/RecAliasToTermTest/` and `LeanScript.ToTerm.TransRecObject` |
| a constructor of a recursive newtype | `recAlias_mk` |
| a structural recursion on a member of a **`mutual` block of inductive types** (a `mutual` block of functions, or one function whose recursion goes through the other members), whose branches look at most `k` times further down, into any member, into one subvalue or into several (the grandchildren below both children of a node) | `mutualRecursiveFamily_rec k` — see `TermTests/MutualFamilyToTermTest/` and `LeanScript.ToTerm.TransRecFamily` |
| a constructor of a member of a `mutual` block | `mutualRecursiveFamily_mk` |
| a `mutual` block of functions over **one** type (`isEven`/`isOdd` on `Nat`, two folds of one `List`, `Tree`, recursive record or newtype, or several per member of a `mutual` block) | the fold of that type, answering the tuple (`PProd`) of the functions' answers, of which the function translated reads its own |
| a structural recursion on a **nested inductive** whose recursive occurrence sits under `List` (`inductive Rose \| node (v : Nat) (kids : List Rose)`), with helpers on `List Rose`, `List (List Rose)`, … | `mutualRecursiveFamily_rec k` on the family `Rose`, `List Rose`, … that `deriving LeanScriptTyWf` gives it — see `TermTests/ShapesTest/Nested.lean` |
| a recursion on a `mutual` block whose members answer different types (`Tree → Bool` with `Forest → Nat`) | `mutualRecursiveFamily_rec k` answering the tuple of the types, each member filling in its own component (the others are a default: the answer type's `Inhabited` instance, or else a value built from its constructors, so a map `P → P`, `Q → Q` needs no instance — `LeanScript.ToTerm.synthDefault?`) |
| a structural recursion on a **nested inductive through `Array`** (`inductive ATree \| node (v : Nat) (kids : Array ATree)`), written as a `mutual` block over `ATree`, `Array ATree` and `List ATree` | `recObject_rec k` (or `recAlias_rec k`), whose window holds the array of the answers at the children — see `TermTests/StructRecTest/NestedArray.lean` |
| a structural recursion on a nested inductive of **several constructors** whose occurrence sits inside another type (`inductive UTree \| leaf \| node (v : Nat) (kids : Array UTree)`, a JSON-like type, `Option T` or `Nat × T` inside a constructor) | `recAlias_rec k`: `deriving LeanScriptTyWf` gives such a declaration the tree of a recursive newtype whose body is the union of its constructors (`Ty.recAlias (Ty.taggedUnion …)`), whose constructors are `recAlias_mk` around `taggedUnion_mk` and whose `match` is `recAlias_casesOn` around `taggedUnion_casesOn` — see `TermTests/StructRecTest/NestedOther.lean` |
| a structural recursion whose occurrences sit in an **array of values that hold the type** (`Array (Array T)`, `Array (Option T)`, `Array (String × T)`), under a **function** (`node (f : Nat → T)`) or under a **delay** (`Thunk T`) | `recObject_rec k` / `recAlias_rec k`, the window holding the array of the elements' windows, the function of the answer trees or the delayed answer tree — see `TermTests/StructRecTest/NestedOther.lean` and, for folds deeper than `0` through functions and delays, `TermTests/StructRecTest/NestedFnDeep.lean` |
| a structural recursion on a `mutual` block whose members **also occur nested** (`Option Q` inside `P`) | `mutualRecursiveFamily_rec k` on the family `P`, `Q`, `Option Q` — see `TermTests/StructRecTest/MutualNested.lean`; occurrences both ways (`Option P` inside `Q` too), a member under `List`, several wrappers (`Option (Option Q)`), a type parameter, a product or a user structure around a member, and recursions started at any member, including an auxiliary one such as `Option (Option Q)`, in `TermTests/StructRecTest/MutualNestedMore.lean` |
| a structural recursion on a family one of whose members holds a member inside an **array, a function or a delay** (`List (Array T)`, `Array (List T)`, `node (qs : Array Q)` in a `mutual` block, `node (f : Nat → G)`, `Thunk Q`) | `mutualRecursiveFamily_rec k`: the fold now hands over the answers at every member nested inside a field (`Ty.famRecBinders`, `famAnswerField`), which at an array are the fold of each element (`famAnswerField_array_memo` in `LeanScript/FamilyNestedFacts.lean`) — see `TermTests/StructRecTest/NestedFamily.lean` and `TermTests/StructRecTest/NestedOther.lean` |
| a structural recursion on a **recursive newtype whose body is a structure** (`Pair2 \| mk (Nat × Option Pair2)`) | `recAlias_rec k` — see `TermTests/StructRecTest/NewtypeStruct.lean` |
| the same with a **user-defined structure** as the body (`Pair3 \| mk (Cell Pair3)`, `structure Cell (α) where val : Nat; next : Option α`), including nested structures, a type parameter, and a `List α` field | `recAlias_rec k` (or a family fold for the `List` field) — see `TermTests/StructRecTest/NewtypeUserStruct.lean` |
| a structural recursion on an **inductive family with indices** (`Vec α n`) | the fold of its tree, the index erased and a value index an ordinary field — see `TermTests/StructRecTest/IndexedFamily.lean` |
| a structural recursion on a family **indexed by types** (a GADT, `TExpr : Type → Type` with `pair {α β} (a : TExpr α) (b : TExpr β) : TExpr (α × β)`), whose type fields only indices mention | the fold of its tree: the type fields hide nothing and are erased, and are Lean variables of each branch; a look into a subvalue at an index that rules a constructor out (`neg : V 1` below a field of type `V 0`) holds a default in that branch — see `TermTests/StructRecTest/IndexedGADT.lean` |
| a structural recursion **split across top-level definitions** (`callGo n := go n 0`), whatever the callee's attributes: through any chain of wrappers, across files, via a `where` helper, partially applied (`l.map (go 2)`), written with `Nat.rec`/`List.rec`, or a member of a `mutual` block that Lean compiles on its own | the fold of the callee, inlined — see `TermTests/StructRecTest/SplitRecursion.lean` and `TermTests/StructRecTest/SplitRecursionMore.lean` |
| a function of a **structure with an existentially quantified type field** (`Unfold`, whose `State` is hidden) | specialized to its argument when that is a value written out; otherwise a Lean function of the trees of the hidden types, `fun State => (… : Term Sg Γ (Unfold.mk.leanScriptLayout α State ⇒ …))` — see `TermTests/StructRecTest/Existential.lean` and `LeanScript.ToTerm.ExistentialArgs` |
| a function of a **non-recursive datatype with existentials of several constructors** (`Src`, whose `gen` hides a type), or of an **indexed** one (a GADT, `Tag : Type → Type` with `wrap {α} (x : α) … : Tag (List α)`) | specialized to its argument when that is a value written out (the `match` on it reduces to the branch of its constructor); otherwise a Lean function of the trees of the hidden types of every constructor, whose argument is `TyWf.oneOf` of the constructors' layouts (a field-less alternative for a constructor that carries no value) and which dispatches with `taggedUnion_casesOn` — see `TermTests/StructRecTest/ExistentialUnion.lean` |
| `do` in `Id` — `Id.run`, `pure`, `>>=`, `<$>`, and `let mut` | the `let`s and applications it stands for |
| `for i in [:n] do …` in `Id`, over `Std.Legacy.Range` | `nat_rec`, folding the state of the loop |
| `for i in [a:n:k] do …` (also `[a:n]`, `[:n:k]`), a range with a start or a step | the loop over `[:(n - a + k - 1) / k]` whose body reads the index `a + j * k`, translated as above — see `TermTests/ToTermTest/ForRangeStep.lean` |
| `for x in l do …` and `for h : x in l do …` in `Id`, over a **list** (`if`, `continue`, `match`, several `let mut`s, nested loops inside) | `l.foldl` of the body read as the next state (over `l.attach` when `h` is read), translated as any `List.foldl` — see `TermTests/ToTermTest/ForList.lean` |
| `for h : i in r do …` over a range, the form that names the membership proof `h : i ∈ r` | when the body does not read `h`, the loop `for i in r`; otherwise the loop over `[:size]` whose body, at `j`, is guarded by `if hj : j < size` and reads the index `start + j * step` with the proof `Std.Legacy.Range.mem_start_add_mul_step r hj` (the test always holds; the proof is erased) — see `TermTests/ToTermTest/ForRangeMem.lean` |
| `have h : p := proof` | the body with the proof in place of `h`, where it is erased |
| a `for` whose body can `break` (or `return` from inside it), over a list or a range | the fold (`List.foldl`, or `Nat.rec` for a range) of the **step** `ForInStep β` (the tagged union `done \| yield`): a `done` step is kept, and the state of the last step is the value — see `TermTests/ToTermTest/ForBreak.lean` and `TermTests/ToTermTest/ForReturn.lean`; without a `let mut` the state `Option ρ × Unit` is modelled as `Option ρ` |
| `List.map`, `List.foldl`, `List.contains`, `List.range`, … — the library's structural recursions | the fold of the list (or of the `Nat`), inlined — see `TermTests/ToTermTest/ListLibrary.lean` |
| a structural recursion whose `match` has a catch-all pattern (`List.get?Internal`, so `l[i]?` and `List.getD`) | the fold: the `_sparseCasesOn_` auxiliary the `match` compiles to is reduced at the shape the branch is instantiated at (`LeanScript.ToTerm.reduceSparseCasesOnCtor?`) |
| `panic! msg` (and so `l[i]!` out of range) | `default` of its `Inhabited` instance, which is what `panic!` is in Lean's logic |
| `l[i]` on a list, with its proof | `l.getD i d`, for a default `d` of the elements (equal whenever the proof holds) |
| a subtype `{x // p x}`; `List.attach`, `List.attachWith`; `⟨x, h⟩`, `s.1`, a `match` on `⟨x, h⟩` | the tree of `α`, the proof erased; `l.attach` is `l` |
| a name of the signature | `global` |

**A list and an array are different types here.**  `Array α` is `Ty.array`, the one
sequence the grammar has an introduction form for: it takes every element at once, so an
array literal translates and a non-literal array does not.  `List α` is the tree its
`LeanScriptTyWf` instance gives it — the recursive tagged union `nil | cons α self` — so
`[]` and `hd :: tl` are `recTaggedUnion_mk`, a `match` on a list is
`recTaggedUnion_casesOn` and `List.rec` is `recTaggedUnion_rec`.  A list therefore does
not have to be written out.

The two are different types.  `Array.toList` is the pure extern `lean_array_to_list`, so
it translates (to `Term.externCall`), but a `match` on an array has no term.  A
structurally recursive function on lists applied to `a.toList` is the fold of the array
`a`, `array_rec k`, since Lean cannot recurse structurally on an array itself.  Its branch is given the head, the tail and the
values at the `k + 1` nearest suffixes, and it may read the first `k` elements of the tail
(taken off it by `array_casesOn`), so a `go` that reads the list after them is refused.  A list is a recursive tagged union, which `LeanScript.Ty.Den` gives the W-tree
of its constructors as values, so a translated list program is run by
`LeanScript.Term.eval` like any other, and `LeanScript.Ty.DenRec.toList` reads a list
back as a Lean list.

## Which calls are allowed

A **constructor is inlinable**: an application of one is built in place, as the
`record_mk`, `taggedUnion_mk`, `enum_mk` or `array_mk` node it denotes.  So are
projections and anything marked `@[inline]`, `@[macro_inline]`, `@[always_inline]` or
`@[reducible]` (an `abbrev`): their definition is translated and cached, and the
translation is used at the call site.  Three refinements keep the result the term one
would write by hand:

* a projection of a (non-class) structure, `p.1` or `s.field`, becomes a
  `record_casesOn` that reads the field;
* an inlined definition whose translation is the eta-expansion of a declaration of the
  signature, `lam … lam (global g (var …) …)` (what `a + b` unfolds to when `Nat.add`
  is declared), is used as `global g` itself, so `a + b` is `global add a b`;
* an inlined call whose arguments are variables and literals, at least one a variable,
  is **substituted**: the body of the definition is translated with the arguments in
  place (so an `@[inline]` fold called on the argument is the fold itself, not a
  function applied to it).  A call on closed arguments only is cached as above.

A `let (a, b) := e; …` (a `match` on a structure) is kept as **one** `record_casesOn`,
also inside the branch of a fold.

A call of a function implemented by a **pure extern of `Init`** is the entry of the
catalogue `LeanScript.LeanInitPureExtern` that models it (`LeanScript/ToTerm/Extern.lean`):
`Term.externCall`, the terms of the arguments and the function that builds the entry from
their values; for an entry that takes a proof (`Array.getInternal`, `Array.set`, ...),
`Term.externCallChecked`, which decides the proposition when the term runs and hands the
proof to the entry, with a fallback for the values that do not satisfy it (a Lean program
cannot give those); and, when every argument is a closed Lean value, `Term.extern` with the
program's own proof.  `Nat.gcd` is the exception: it is treated as if it had no
`@[extern]`, and `Nat.gcd._unary` is read as `Nat.gcd`.

Two more kinds of call are inlined although they are neither marked nor declared:

* a **structural recursion** defined on its own (a definition Lean compiled through a
  `brecOn`, or one whose body applies the recursor of a recursive type, such as `Nat.rec`),
  and a **wrapper** that calls one, through any number of further wrappers: the call is
  the fold the callee compiles to, so a recursion split across top-level definitions
  translates without `@[inline]` and without a declaration
  (`TermTests/StructRecTest/SplitRecursion.lean`,
  `TermTests/StructRecTest/SplitRecursionMore.lean`).  The recursion may be defined in
  any module; the wrappers followed are those of the program's own modules (the modules
  whose name has the same first component as the wrapper's), never definitions of `Init`,
  `Std` or `Mathlib`.  A non-recursive helper that reaches no recursion — a higher-order
  `applyTwice f x := f (f x)`, even applied to a recursion — is not a wrapper;
* a call on, or building, a value of a **datatype with existentials** (`countdown.take n`,
  `firstOut countdown`, `countFrom k`): such a value has no tree, so the function could not
  be declared in the signature; it is inlined and **specialized** to the value, whose
  projections then reduce (`LeanScript.ToTerm.ExistentialArgs`).

Every **other** top-level function must be declared in the signature: it is translated
to `Term.global`, the reference the signature gives it.  A call of a function that is
neither inlinable nor declared is refused, naming the function.

The definition `#leanscript_to_term` is *applied to* is always unfolded: it is the thing
being translated.

## What is refused

* `partial` and `unsafe` definitions, and `opaque` constants and axioms: they have no
  total value to translate.
* well-founded recursion (`WellFounded.fix`, `Acc.rec`) and partial fixpoints
  (`Lean.Order.fix`).
* a recursion on a `Nat` that does **not** descend by a fixed number of steps: a call at
  `n / 2`, say.  A recursion that descends `k + 1` steps for some fixed `k` — `fib` reads
  its value at `n` and at `n + 1`, the hexanacci numbers at the six previous arguments —
  is translated as `nat_rec k`, and the depth is read off the compiled recursion: it is
  the smallest number of steps at which the *history* the `brecOn` hands the branch is
  fully read.  A recursion on a recursive record or a recursive newtype is translated as
  `recObject_rec k` or `recAlias_rec k`, the depth read off the same way
  (`LeanScript.ToTerm.TransRecObject`); one on a recursive tagged union (a `List`
  included) or on a member of a `mutual` block as `recTaggedUnion_rec k` or
  `mutualRecursiveFamily_rec k` (`LeanScript.ToTerm.TransRecUnion`,
  `LeanScript.ToTerm.TransRecFamily`).  The branches of `recTaggedUnion_rec k` and of
  `mutualRecursiveFamily_rec k` may look into several subvalues (after the left child,
  the right one), each look costing one unit of depth; the window of `recObject_rec k`
  and `recAlias_rec k` holds the answers below every child at once, and so does that of
  `nat_rec k` and `array_rec k` along their one chain.  A recursive record or newtype is
  folded when each occurrence of it sits, through unions, structures and arrays
  (`Link Chain`, `Option Chain`, `Option (Nat × Chain)`, `Array (Option Chain)`), in a
  field that is the type itself, a function into it (`Nat → Chain`) or a delay of it
  (`Thunk Chain`).  A function or a delay is read at any depth, as the answers at its
  values (`(f a).foo`, `(g ()).foo`); what cannot be read is the value `f a` taken apart,
  which Lean's structural recursion itself does not accept
  (`TermTests/StructRecTest/NestedFnDeep.lean`).
* a `match` on a field of a value that the recursion takes apart but does not descend
  into (a value of *another* `mutual` block, say), written directly in the branch of a
  structural recursion: Lean passes the history of the recursion through that `match`.
  Moving the `match` into a small `@[inline]` function makes it translatable
  (`TermTests/MutualFamilyToTermTest/CrossBlock/`).
* a nested inductive whose recursive occurrence sits under a type former that is neither
  a shape of the language (`List`, `Array`, `Thunk`, a function, a union, a structure)
  nor a type with a `LeanScriptTyWf` instance of its own; and an inductive family whose
  index the language cannot erase (one whose tree changes with the index): a value field
  whose type is a type field (`lit {α} (x : α) : E α` — an existential, see below), or a
  function whose *answer's* type is the index (`eval : TExpr α → α`), which is refused as a
  dependent motive.
* inside a structural recursion on a **family** whose member holds a member inside an
  array, a function or a delay (`List (Array T)`, `node (qs : Array Q)`), the answers at
  those nested members are the answers of the fold itself; a call that looks *deeper*
  than one level through such a field is not read as the fold.
* a fold deeper than the translation looks for.  The bounds are options
  (`LeanScript/ToTerm/Options.lean`), with defaults `64` for `nat_rec k` / `array_rec k`,
  `24` for `recObject_rec k` / `recAlias_rec k` and `16` for `recTaggedUnion_rec k` /
  `mutualRecursiveFamily_rec k`, and each can be raised with `set_option`
  (`TermTests/StructRecTest/DeepFolds.lean`).
* a call of a function that is neither inlinable, nor declared in the signature, nor a
  structural recursion (or a wrapper of one) — see *Which calls are allowed*.
* a recursion written with the recursor of a **user-defined** type (`Tree.rec …`) instead
  of by pattern matching: only `Nat.rec` and `List.rec` are read as folds; pattern
  matching on the type translates.
* a function of a **recursive** datatype with existentials (`Process`, whose hidden types
  may differ from node to node) whose argument is not a value written out; and a function
  of a non-recursive one at an index that is not a variable of its own (`Tag Nat → …`,
  rather than `{β} → Tag β → …`).
* `do` in any monad other than `Id`, which is the only one that is not an effect.

## Which dispatch a `match` becomes

A `match` is translated by the shape of the type it takes apart and by **which
constructors it names**:

* it names them all, and no branch uses the value of a fold: the exhaustive dispatch,
  `enum_casesOn`, `taggedUnion_casesOn`, `record_casesOn`, `recTaggedUnion_casesOn`,
  `nat_casesOn`, `bool_casesOn`;
* it leaves constructors out (a wildcard, or fewer patterns than constructors): the
  partial dispatch, `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` or
  `recTaggedUnion_casesOnWithDefault`, whose default branch is the one the wildcard
  wrote — the dispatch is *not* expanded into one branch per constructor;
* it is the branch of a recursion whose body uses the value at the smaller argument: the
  fold, `nat_rec` or `recTaggedUnion_rec`.
* a dependent motive, a dependent function type, and any type with no
  `LeanScript.LeanScriptTyWf` instance — except a datatype with existentials, below.

## Datatypes with existentials

A datatype one of whose constructors hides a type (`Process`, whose `step` hides the type
of its state), and every datatype in its `mutual` block, has no `LeanScriptTyWf` instance:
the type of a value depends on the hidden types it chooses.  A *closed* value of it is
still translated, constructor for constructor, by **the constructor functions of
`#leanscript_ctor`** (`LeanScript.CtorFn`), generated on first use and taken from their
cache afterwards:

```lean
def mixedProcess_term   := #leanscript_to_term (sig := sig) mixedProcess
def varyingProcess_term := #leanscript_to_term (sig := sig) varyingProcess
```

* each type argument of the constructor function is the tree of the Lean type the
  application uses — parameter, type index or hidden type;
* the tree of a field the constructor function leaves open (an occurrence of the datatype,
  `procTy`, `transTy`) is read off the translation of that field, so the type of the term
  is **inferred** from the value; one that nothing fixes (a `proc` field of a `none` that
  is never filled) is `nat`;
* a hidden type that is `Unit` is erased: the constructor function generated for that use
  (suffix `_erased…`) drops the `Unit` fields and `Unit` binders, and a `fun _ : Unit => b`
  is translated as `b`;
* where two values of different types meet — the branches of an `if`, or of an
  `if n = 0 then … else …`, which is `nat_casesOn` — the types are joined: a hole of a
  layout hole by hole, and two different layouts as `TyWf.oneOf`, the tagged union with one
  constructor per layout, into which each branch is injected.

A **function** of such a value is translated too, when the datatype is not recursive: a
structure with existentially quantified type fields (`Unfold`, whose `State` is hidden), a
datatype of several constructors (`Src`), or an indexed one (`Tag`)
(`LeanScript.ToTerm.ExistentialArgs`):

* called on a value written out (`countdown.take n`, `(countFrom k).take n`), it is
  specialized to that value, and its projections are the value's own;
* translated itself (`#leanscript_to_term (Unfold.take (α := Nat))`), it is a Lean function
  of the trees of the hidden types, a term for each choice of them:
  `fun State => (… : Term Sg Γ (Unfold.mk.leanScriptLayout (.prim .nat) State ⇒ …))`.
  Applied to the tree a value chose, it applies to that value;
* of several constructors, it is a Lean function of the hidden types of every constructor,
  and its argument is **one of** the constructors' layouts, `TyWf.oneOf`, in the order of the
  constructors (a constructor that carries no value is an alternative with no field); the
  function dispatches on which (`taggedUnion_casesOn`), and each branch is the function at
  that constructor, at the constructor's indices for an indexed datatype.

`TermTests/StructRecTest/Existential.lean` and `TermTests/StructRecTest/ExistentialUnion.lean`
run both.

This is `LeanScript.ToTerm.Existential`.  `TermTests/InductiveTypesTest/Existentials.lean`
translates `mixedProcess` and `varyingProcess` and checks, by `rfl`, what they evaluate to.

## The cache

Every closed definition that is inlined is translated **once**: the translation is
stored as a function of the context, `fun Γ => …`, which is what makes one translation
usable at every depth it is called from.

Two definitions that translate to the *same shape* share one entry: the produced tree is
hashed (`Lean.Expr.hash`) and compared against the entries of that hash, and an equal
one is returned as the **same object**, so the duplicate is not built twice and the two
call sites point at one tree in memory.  `#leanscript_to_term_cache_stats` reports how
many entries, cache hits and shape merges there have been, and
`#leanscript_to_term_cache_clear` empties the cache.

`TermTests/ToTermTest/` runs all of this: it translates about twenty definitions and
checks, by the kernel, that `LeanScript.Term.eval` gives each translation the value the
Lean definition has — the lists included, whose values are read back with
`LeanScript.Ty.DenRec.toList` — and it pins what the translation refuses.

## Normalizing the result

The translation writes its term with the direct-style builders of
`LeanScript.Expr.Build`, which compute the A-normal form (the `let`s naming every operand,
the renamings, the join points).  Left as it is, that computation is redone by the kernel
in every proof that runs the term.  So `#leanscript_to_term` reduces its result once, to
constructors of the grammar (`LeanScript.ToTerm.Normalize`), when the term has at most
`leanscript.toTerm.normalizeMaxNodes` nodes (default `1000`); a larger term is left in
direct style, since each run of it only reduces the branches it takes.
`set_option leanscript.toTerm.normalize false` turns this off.  The normalized term is
definitionally equal to the direct-style one, so an equation stated about either holds
of both; `TermTests/NormalizeTest.lean` proves the equation for sample terms, closed and
generic in a hidden type.

Two term elaborators read pieces back out of a translated term, for proofs about a fold
that name its step: `#leanscript_fold_branch t` is the branch (or the cases) of the first
fold in the term `t`, in the context the fold gives it, and `#leanscript_fold_bases t` the
answers for the short arguments of the first `nat_rec k` or `array_rec k` in `t`.

The translation itself is split across the modules of this directory:
`LeanScript.ToTerm.ObjectExpr` (the expressions of the object language),
`LeanScript.ToTerm.TyView` (a tree as a view, and the tree of a Lean type),
`LeanScript.ToTerm.Ctx` (where a translation stands, and the signature),
`LeanScript.ToTerm.Cache` (the cache, and what may be translated at all),
`LeanScript.ToTerm.Pieces` (literals, and small pieces of the object language),
`LeanScript.ToTerm.Match` (a dispatch Lean compiled with a default),
`LeanScript.ToTerm.Brec` (the compiled form of a structural recursion),
`LeanScript.ToTerm.TransRecObject` (a structural recursion on a recursive record),
`LeanScript.ToTerm.Existential` (datatypes with existentials, through the constructor
functions),
`LeanScript.ToTerm.ExistentialArgs` (functions of a structure with an existential type
field),
`LeanScript.ToTerm.Trans` (the translation proper),
`LeanScript.ToTerm.Normalize` (the result, reduced once to constructors of the grammar) and
`LeanScript.ToTerm.Elab` (the elaborator, which is what a user imports).

Each of these modules imports only the modules whose declarations it uses, not simply the
one before it in this list, so that independent modules (`Cache`, `Match`, `Brec`,
`Existential`, `Extern`) build in parallel.  When a module starts to use a declaration of
another one, add that import.
-/
