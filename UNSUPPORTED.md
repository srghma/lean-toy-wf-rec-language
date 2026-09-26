# What `#lean_wf_func_to_term` and `PCL` still do not support

This is an assessment of the current state of the project. The original goal was a small typed
language with a terminating, sound evaluator, and a command that turns a well-founded Lean function
(such as `gcd`) into a program `t` with a theorem `∀ m n, Term.eval t m n = gcd m n`. That goal
is met: see `README.md`, `GRAMMAR.md` and `GAPS.md` for what is supported. This file lists only
what is **not** supported.

How much evidence each entry has:

* **[pinned]**: a test fixes the rejection with `#guard_msgs`. If the capture starts accepting
  the function, `lake build` fails. Most of these tests are in
  `RequestProject/WFLang/Tests/Unsupported.lean`; the others are in the test file named in the entry.
* **[documented]**: described in earlier notes (`GAPS.md`, `STACK_OVERFLOW.md`,
  `CONTEXTS_ASSESSMENT.md`, the header comments) but not re-tested for this file.

The whole project, including `Tests/Unsupported.lean`, builds with `lake build`, with no `sorry`.

---

## 0. Lifted since the previous version of this file

Everything below was listed here as unsupported, and is now captured, with its agreement theorem
proved by `wf_agree` and checked on sample inputs by `#guard`:

| was unsupported | now | test |
|---|---|---|
| `Option`, `Except`, `Sum` (`optDown`), also only as an intermediate value (`optInside`) | object types `option t`, `sum s t`, `except e t`, with `match` on them | `Tests/NewTypes.lean` |
| `String`, `Char` (`strLen`) | object types `string`, `char` (length, `++`, `push`, `toList`, `ofList`, `Char.toNat`, `Char.ofNat`) | `Tests/NewTypes.lean` |
| `Array` (`arrSize`) | object type `array t` (`size`, `push`, `toList`, `ofList`, `Array.range`, `a[i]?`) | `Tests/NewTypes.lean` |
| `Unit` | object type `unit` | `Tests/NewTypes.lean` |
| `match` on `Int` constructors (`intCases`) | the test `0 ≤ i` and `toNat` projections | `Tests/NewTypes.lean` |
| `List.getD`, `l[i]!` (`listGetD`, `listIdx`) | `getElem?`, `take`, `drop` operators | `Tests/NewTypes.lean` |
| `List.foldl`, `List.contains` (`listFoldl`, `listHas3`), and `foldr`, `any`, `all`, `elem`, `find?`, `filter` | first-order recursive functions in `Core/ListLoops.lean`, specialised to the function argument | `Tests/ListCombinators.lean` |
| a recursive call under a `fun` given to one of these combinators | recursion through a function argument (`fsum`, `anyRec`) | `Tests/ListCombinators.lean` |
| `decide (∀ i < n, …)` (`boundedAll`); also `∃ i < n`, `∀ x ∈ l`, `∃ x ∈ l`, in `decide` or an `if` | `listAll` / `listAny` | `Tests/ListCombinators.lean` |
| `for x in l` (`forList`) | `listFoldl`, or `listLoopN` if the body may stop | `Tests/ListCombinators.lean` |
| `break` (`forBreak`), early `return` (`forReturn`) in a `for` loop | `rangeLoopN` / `listLoopN` (the body returns a `ForInStep`, whose case split is pushed into the branches) | `Tests/ListCombinators.lean` |
| ranges with a step, `[0:n:2]` (`forStep`) | `rangeLoopN` with `(b - a + s - 1) / s` iterations | `Tests/ListCombinators.lean` |
| `return` inside Lean's `while` (`findDiv`) | the loop state holds an `Option` | `Tests/LeanWhile.lean` |
| mutual recursion with different parameter or result types (`mA`/`mB`, `rA`/`rB`) | padded parameters after the tag; a tuple of results | `Tests/MutualSignatures.lean` |
| a decrease that Lean proves but the capture could not re-prove after translation (`nestMin`) | the decrease tactic splits the `if`s of the translated goal and calls `omega` | `Tests/MutualSignatures.lean` |

## 1. What the approach does not prove

* **The capture itself is not verified.** `#lean_wf_func_to_term` is metaprogramming and has no
  correctness theorem. Each captured function gets its own agreement theorem, proved by the
  `wf_agree` tactic. So you get certainty for every function you capture and prove, not a proof
  that "every accepted function is translated correctly". If `wf_agree` fails, the capture might
  still be wrong, and nothing states otherwise.
* **No completeness.** There is no characterisation of which well-founded Lean functions can be
  captured. The boundary is the list below, found by testing.
* **Decrease proofs are reused only in part.** The relation comes from Lean. The decrease
  obligations of the program are re-proved with Lean's own proof terms as hypotheses, but after
  translation, with `omega`/`simp` fallbacks (now including splitting the `if`s of the goal).
  A decrease whose proof needs more than that can still fail after translation even though it
  is true.

## 2. Types

`Ty` has `Nat`, `Bool`, `Int`, pairs, lists, `Option`, `Sum`, `Except`, `String`, `Char`,
`Array` and `Unit`. Subtypes of these can be results, as postconditions, and proof arguments can
be preconditions. Anything else is rejected with `unsupported type … (only Nat, Bool, Int, String,
Char, pairs, lists, arrays, Option, Sum, Except, Unit and subtypes of them)`.

| not supported | example | evidence |
|---|---|---|
| user structures and inductive types | `ptSum (p : Pt)` | [pinned] |
| `Fin n` | `finVal (i : Fin 5)` | [pinned] |
| `UInt8`…`UInt64` | `u64 (x : UInt64)` | [pinned] (`UInt64`) |
| `Float`, `BitVec` | – | not in `Ty` (by reading the code) |
| propositions as results | `Tco.Safe : Nat → Prop` | [pinned] (`Tests/Sources.lean`) |
| function types (parameters or values) | `Tco.iter` unspecialised | [pinned] (`Tests/Sources.lean`); see §3 |

The restriction also applies to intermediate values.

What would lift it: user structures could be encoded as nested pairs (and simple enumerations as
sums of `unit`), but the agreement statement `Term.eval t p = f p` would then relate values of
different types, so the capture would need an encoding function and `wf_agree` would have to go
through it. `Fin n` depends on a value, which `Ty` does not allow; `UInt*` would need their own
operators and overflow semantics.

## 3. Library functions, higher-order code and `do` notation

The capture reads the definitions of user functions. Library functions are translated only if they
map to one of the `PCL` operators (arithmetic, comparisons, bitwise, `gcd`, `lcm`, `log2`, `Int`
arithmetic, pairs, list, option, sum, `Except`, string, character and array operations), to
`List.map` (a statement of the grammar), or to one of the first-order combinators of
`Core/ListLoops.lean` (`foldl`, `foldr`, `any`, `all`, `contains`, `elem`, `find?`, `filter`,
`for x in l`, bounded quantifiers). Any other library call is `unsupported expression`.

| not supported | example | evidence |
|---|---|---|
| other library functions with a function argument (`List.zipWith`, `List.partition`, `Array.foldl`, `Array.map`, …) | – | by reading the code |
| a recursive call inside a combinator other than `List.map` whose decrease needs the membership proof of `attach` | `depthSum` (`(List.range n).attach.foldl (fun acc ⟨i, h⟩ => acc + depthSum i) 1`) | [pinned] (rejection only: the capture fails with an internal error) |
| `for` loops in a monad other than `Id` | – | by reading the code |
| a function parameter with no known argument | `#lean_wf_func_to_term Tco.iter` | [pinned] (`Tests/Sources.lean`) |

**Restrictions of recursion through a function argument** ([documented], `GAPS.md` §7): only one
specialised function per captured function; `f` and the higher-order `g` must have the same result
type; no proof parameters or subtype results; the calls of `f` inside the function argument may not
be under another binder.

## 4. Recursion schemes and termination arguments

| not supported | example | evidence |
|---|---|---|
| Lean's own `while` in a recursive function, or without a provable measure | `LeanWhileRejected.recLoop`, `Tco.ackWhile`, `Tco.ackNoDataStructure` | [pinned] (`Tests/LeanWhile.lean`, `Tests/Sources.lean`) |
| `partial def` | | [documented] |
| `partial_fixpoint` | `pfix` → `recursive call … outside its definition` | [pinned] |
| mutually recursive functions with proof parameters or subtype results | – | by reading the code (`fnSig`) |
| a call inside the test or body of a well-founded `wf_while` loop | `WhileEx.callInBody` | [pinned] (`Tests/While.lean`) |
| a termination proof that needs the *value* of a helper that is not `@[inlinable]` | `GlobalsEx.logHalfG` | [documented] (`Tests/Globals.lean`) |

Details:

* **Non-well-founded definitions.** Lean builds `partial` and `partial_fixpoint` without
  a termination proof that can be reused, and the evaluator of `PCL` is total, so there is
  nothing to translate. The workaround is to rewrite the loop with `wf_while … termination_by μ`
  or `WFLang.whileWF` (`Core/While.lean`), as `Tests/WhileFunctions.lean` does for
  `diagonalWhile`, `mc91While` and Newton's `isqrt`, or as well-founded recursion.
  `ackWhile` / `ackNoDataStructure` would need a measure on the stack (a multiset order) and have
  not been rewritten.
* **What a decrease proof may use.** Inside a program, a decrease proof sees only the path
  condition (the `if` tests taken, preconditions) and the **postconditions** of earlier calls. A
  call to a global helper contributes only its declared postcondition (usually `True`). So:
  * a helper whose value the termination argument needs must be `@[inlinable]`, or must return a
    subtype that states the needed fact;
  * nested recursion (`f (f n)`) is captured only if `f` returns a subtype whose property proves
    the outer decrease (`nestedBound` in `Tests/GapFunctions.lean`), or if the decrease holds
    whatever the inner value (`nestMin`).

## 5. The evaluator at runtime

* **Stack depth** (fixed for loops and tail calls, `STACK_OVERFLOW.md`). Compiled code and
  `#eval` run the jump machine (`PCL/Lang/Machine.lean`, `PCL/Lang/Fix.lean`), proved equal to
  `Expr.eval` and substituted for it by `@[csimp]` lemmas: loop iterations and tail calls
  (`let v := self args in ret v`) run as jumps and use no stack.  Non-tail recursive calls
  (`ack`, `hyper`, `diagonal`) still use one stack segment per nested call.
* **No sharing** ([documented], `GRAMMAR.md`). A Lean `let` with a call-free value is substituted,
  so a value used twice is computed twice. For example, `let x := n * n; x + x` is accepted and
  evaluates `n * n` twice. A pure `let` statement would fix this; it is listed as a possible next
  step, not implemented.
* **Inlined loops are per call site** ([documented], `Tests/Loops.lean`). A tail-recursive
  `@[inlinable]` helper called twice gives two loops, as inlining does. Recursive helpers with
  non-tail self calls are shared as global functions (the local-function context was removed,
  see `CONTEXTS_ASSESSMENT.md`).

## 6. Capture and tooling rough edges ([documented])

* **Same-body clash:** if one program contains two global functions with the same body and
  signature (e.g. `sumTo a + sumToI a`, where the non-tail-recursive `@[inlinable]` `sumToI` is a
  global function too), `wf_agree` can confuse them and fail.
* **Calls with all arguments known** are evaluated by the kernel at capture time, with no cost limit:
  a slow closed call (a large Ackermann value) makes the capture slow. Turn this off with
  `set_option wfLang.foldCalls false`.
* **Constant folding does not regroup:** `a + 9 + 10` stays as it is and is not simplified to
  `a + 19`.
* **Join points are not used after a call with a subtype result.** The rest of the computation is
  copied into both branches instead, which can blow up exponentially with several such `if`s in a
  row. `GRAMMAR.md` sketches how to lift this.
* **Error quality:** many different causes give the same message, `unsupported expression`, with no
  pointer to the offending subterm.

## 7. Priorities, if work continues

Ordered by how many ordinary Lean functions each item would unlock, as a judgement call:

1. **User structures**, encoded as tuples, with an encoding function in the agreement statement.
2. **Erasing `attach` proofs for all combinators**, not only `List.map`, so that recursion over
   the elements of a list can use `x ∈ l` in its termination proof.
3. **More combinators** (`zipWith`, `partition`, `Array.foldl`/`map`, …) through the same
   first-order-function pattern as `Core/ListLoops.lean`.
4. **An explicit-stack evaluator for non-tail calls** (loops and tail calls already run in
   constant stack), or compiling programs to closures to cut the interpretive overhead.
5. **General user inductive types**: the largest change, touching `Ty`, `PExpr`, the translation
   and `wf_agree`.
