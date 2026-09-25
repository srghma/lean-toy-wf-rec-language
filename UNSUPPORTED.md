# What `#lean_wf_func_to_term` and `PCL` still do not support

This is an assessment of the current state of the project. The original goal was a small typed
language with a terminating, sound evaluator, and a command that turns a well-founded Lean function
(such as `gcd`) into a program `t` with a theorem `∀ m n, Term.eval t m n = gcd m n`. That goal
is met: see `README.md`, `GRAMMAR.md` and `GAPS.md` for what is supported. This file lists only
what is **not** supported.

How much evidence each entry has:

* **[pinned]**: a test fixes the rejection with `#guard_msgs`. If the capture starts accepting
  the function, `lake build` fails. Most of these tests are in the new file
  `RequestProject/WFLang/Tests/Unsupported.lean`; the others are in the test file named in the entry.
* **[documented]**: described in earlier notes (`GAPS.md`, `STACK_OVERFLOW.md`,
  `CONTEXTS_ASSESSMENT.md`, the header comments) but not re-tested for this file.

The whole project, including `Tests/Unsupported.lean`, builds with `lake build`, with no `sorry`.

---

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
  translation. When the translation changes the shape of the argument, this can fail even though
  the goal is true (§4, `nestMin`).

## 2. Types

`Ty` has only `Nat`, `Bool`, `Int`, pairs and lists. Subtypes of these can be results, as
postconditions, and proof arguments can be preconditions. Anything else is rejected with
`unsupported type … (only Nat, Bool, Int, pairs, lists and subtypes of them)`.

| not supported | example | evidence |
|---|---|---|
| `Option`, `Except`, `Sum` | `optDown : Nat → Option Nat` | [pinned] |
| `String`, `Char` | `strLen (s : String)` | [pinned] (`String`) |
| user structures and inductive types | `ptSum (p : Pt)` | [pinned] |
| `Array` | `(Array.range n).size` | [pinned] |
| `Fin n`, `UInt8`…`UInt64`, `Float`, `BitVec` | – | not in `Ty` (by reading the code) |
| propositions as results | `Tco.Safe : Nat → Prop` | [pinned] (`Tests/Sources.lean`) |
| function types (parameters or values) | `Tco.iter` unspecialised | [pinned] (`Tests/Sources.lean`); see §3 |

The restriction also applies to **intermediate values**. `match (if n > 3 then some n else none)
with …` is rejected even though `Option` never shows up in the signature (`optInside`, [pinned]).
A `match` on the constructors of `Int` (`.ofNat` / `.negSucc`) is rejected too (`intCases`, [pinned]).

What would lift it: sum and option types in `Ty`, with a `case` statement, would cover `Option`,
`Except` and simple enumerations. General user inductive types would need a generic encoding
(sums of products) plus a translation of `casesOn`/matchers into it.

## 3. Library functions, higher-order code and `do` notation

The capture reads the definitions of user functions. Library functions are translated only if they
map to one of the `PCL` operators (`+ - * / %`, `^`, shifts, bitwise, `gcd`, `lcm`, `log2`, `Int`
arithmetic and comparisons, pairs, `::`, `++`, `head`, `tail`, `isNil`, `length`, and a few
rewrites: `min`, `max`, `∣`, `pred`, `!=`). Any other library call is `unsupported expression`.

| not supported | example | evidence |
|---|---|---|
| `List.map`, `List.foldl`, `List.contains`, `List.getD`, `l[i]!`, … | `mapSq`, `listFoldl`, `listHas3`, `listGetD`, `listIdx` | [pinned] |
| a recursive call under a `fun` given to a library combinator | `underLambda`: `(List.range n).attach.map fun ⟨i, _⟩ => underLambda i` | [pinned] (`Tests/Gaps.lean`) |
| `decide` on a proposition with a bounded quantifier | `decide (∀ i < n, i * i ≠ 7)` → `unsupported condition` | [pinned] |
| `for x in l` over a **list** | `forList` | [pinned] |
| `break` in a `for` loop | `forBreak` | [pinned] |
| early `return` from a `for` loop | `forReturn` | [pinned] |
| ranges with a step, `[0:n:2]` | `forStep` | [pinned] |
| a function parameter with no known argument | `#lean_wf_func_to_term Tco.iter` | [pinned] (`Tests/Sources.lean`) |

Supported for comparison: `for i in [a:b]` in `Id` that always continues, `Nat.fold`, `let mut` with
`if` in `do` blocks, `let rec`, `where` helpers, and a function parameter once it is specialised
to a concrete argument.

**Restrictions of recursion through a function argument** ([documented], `GAPS.md` §6): only one
specialised function per captured function; `f` and the higher-order `g` must have the same result
type; no proof parameters or subtype results; the calls of `f` inside the function argument may not
be under another binder.

What would lift it: first-order replacements for the common combinators (`map`, `foldl`, `any`/`all`,
`for x in l`, loops with early exit), like `rangeLoop` for `for` over a range, whose function
argument receives the membership proof (`i ∈ l`) that termination proofs use.

## 4. Recursion schemes and termination arguments

| not supported | example | evidence |
|---|---|---|
| Lean's own `while` in `do` notation, `partial def` | `Tco.ackWhile`, `Tco.mc91While`, `Tco.diagonalWhile`, `isqrt` | [pinned] (`Tests/Sources.lean`, `Tests/While.lean`) |
| `partial_fixpoint` | `pfix` → `recursive call … outside its definition` | [pinned] |
| mutual recursion with different parameter or result types | `mA : Nat → Nat` / `mB : Nat → Bool → Nat`; `rA : Nat → Nat` / `rB : Nat → Bool` | [pinned] |
| a call inside the test or body of a well-founded `wf_while` loop | `WhileEx.callInBody` | [pinned] (`Tests/While.lean`) |
| a termination proof that needs the *value* of a helper that is not `@[inlinable]` | `GlobalsEx.logHalfG` | [documented] (`Tests/Globals.lean`) |
| a decrease that Lean proves but the capture cannot re-prove after translation | `nestMin` | [pinned] |

Details:

* **Non-well-founded definitions.** Lean builds `while`, `partial` and `partial_fixpoint` without
  a termination proof that can be reused, so there is nothing to translate. The workaround is to
  rewrite the loop with `wf_while … termination_by μ` or `WFLang.whileWF` (`Core/While.lean`), as
  `Tests/WhileFunctions.lean` does for `diagonalWhile`, `mc91While` and Newton's `isqrt`. Those
  rewrites match the originals only on sample inputs, not by proof: the originals are opaque.
  `ackWhile` / `ackNoDataStructure` would need a measure on the stack (a multiset order) and have
  not been rewritten.
* **What a decrease proof may use.** Inside a program, a decrease proof sees only the path
  condition (the `if` tests taken, preconditions) and the **postconditions** of earlier calls. A
  call to a global helper contributes only its declared postcondition (usually `True`). So:
  * a helper whose value the termination argument needs must be `@[inlinable]`, or must return a
    subtype that states the needed fact;
  * nested recursion (`f (f n)`) is captured only if `f` returns a subtype whose property proves
    the outer decrease (`nestedBound` in `Tests/GapFunctions.lean`).
* **`nestMin`.** `nestMin (n+1) = nestMin (min n (nestMin n)) + 1` terminates because
  `min n _ ≤ n`, and Lean proves it with `omega`. The capture turns `min` into an `if` (in
  simplified form, `if n+1 ≤ v+1 then n else v`). Lean's proof term, which talks about `n ⊓ x n ⋯`,
  then no longer matches, and the capture reports `failed to prove termination` on a goal that is
  true. This is a gap in the capture's proof automation, not in the language. Splitting the `if`
  and calling `omega` on the translated goal would probably close this case, but that has not been
  tried. It is also a case where the capture logs an error instead of failing outright, so
  `#expect_reject` cannot be used; the test pins the full error message instead.

## 5. The evaluator at runtime

* **Stack depth** ([documented], `STACK_OVERFLOW.md`). `Expr.eval` uses one native stack frame per
  object-level recursive call, **tail calls included**, because the result of a recursive call is
  an argument of the continuation. Measured on single runs (not proofs):
  * compiled code with an 8 MB stack overflows at around 80k nested calls;
  * `#eval` in the interpreter aborts the whole `lean` process at around 2–3k nested calls (for
    example, `Term.eval sumTo_term 2500 0`).

  Native Lean compiles these tail-recursive functions to loops, so it has no such limit. This does
  not affect termination or soundness, only resources. A fix would need an evaluator with an
  explicit continuation stack and a new agreement proof.
* **No sharing** ([documented], `GRAMMAR.md`). A Lean `let` with a call-free value is substituted,
  so a value used twice is computed twice. For example, `let x := n * n; x + x` is accepted and
  evaluates `n * n` twice. A pure `let` statement would fix this; it is listed as a possible next
  step, not implemented.
* **Loops use stack too** ([documented], `STACK_OVERFLOW.md`). A loop (recursive join point,
  including a `wf_while` loop) runs each iteration as a jump through `WellFounded.fix`, which
  uses a few stack frames per iteration in the interpreter; the runtime check of
  `diagonalWhile` in `Tests/While.lean` is limited to about 1 000 iterations for this reason.
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

1. **`Option`/sum types with a `case` statement.** `Option` is very common, even as an intermediate
   value only.
2. **List combinators and `for x in l` / `break` / early `return`**, via first-order loop
   replacements (the `rangeLoop` pattern).
3. **More robust decrease re-proofs.** Normalise `min`/`max`/`if` in the translated goal and fall
   back to `omega`/`simp` when Lean's proof term does not match (`nestMin`).
4. **Mutual recursion with different signatures**, by padding parameters and tagging results, as
   is already done for recursion through a function argument.
5. **An explicit-stack evaluator**, to remove the stack-depth limit for tail calls.
6. **User inductive types**: the largest change, touching `Ty`, `PExpr`, the translation and
   `wf_agree`.
