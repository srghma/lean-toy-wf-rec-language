# Three languages with well-founded recursion in the grammar

Earlier versions of this project (`ASSESSMENT.md`, directory `Wrapper/`: `Guarded.lean`,
`GuardedAcc.lean`, `FreeCall.lean`, `Checked.lean`, `Elab.lean`) kept one expression type and put the
well-founded relation and the decrease proofs in a wrapper structure *outside* the grammar.
This document is about the three newer languages, where recursion is a constructor of
`inductive Expr` itself. Each language has its own evaluator and its own capture
elaborator. All three share the types, operators and environments of `Common/Types.lean`, and the call-free
expressions `PExpr` of `Common/PExpr.lean`
(`Ty = nat | bool`, `BinOp` with `+ - * / %`, `==`, `<`, `≤`, `&&`, `||`).

| language | file | recursion constructor | evaluator | elaborator |
|---|---|---|---|---|
| **PCL** (proof-carrying calls) | `RequestProject/WFLang/PCL/Lang.lean` | `Expr.fix params r R wf body args k` and `Expr.call args dec k` | `PCL.Expr.eval` (uses `WellFounded.fix`) | `#lean_wf_func_to_pcl`, `pcl_agree` (`PCL/Elab.lean`) |
| **Tail** (well-founded loops) | `RequestProject/WFLang/Tail/Lang.lean` | `Expr.loop ps r R wf body args k`; the loop body is `Body.done / next args dec / ite` | `Tail.Expr.eval`, `Tail.Loop.run` | `#lean_wf_func_to_tail`, `tail_agree` (`Tail/Elab.lean`) |
| **Meas** (in-language measure) | `RequestProject/WFLang/Meas/Lang.lean` | `Expr.fix ps r μ₁ μ₂ body args` and `Expr.call args`; `(μ₁, μ₂)` are object-language `Nat` expressions, ordered lexicographically | `Meas.Expr.eval` (uses `measFix`) | `#lean_wf_func_to_meas`, `meas_agree` (`Meas/Elab.lean`) |

* **PCL**: `call` is a typed `let v := self args in k`. It carries a proof `dec` that the
  arguments are `R`-smaller than the current parameters, under the path condition `G`
  collected from the enclosing `ite` branches (so `if n = 0 then m else gcd n (m % n)`
  type-checks because the `else` branch knows `n ≠ 0`). `fix` binds a local recursive
  function with a relation `R` and a proof `wf : WellFounded R`. Evaluation has no runtime
  checks and needs no fuel. Correctness: `fixFn_eq` (the fixpoint equation) and `fixFn_unique`.
* **Tail**: `loop` is a well-founded `while` loop. Its body can only finish (`done`), jump
  back with new state (`next`, which carries its decrease proof), or branch. Only
  tail-recursive functions can be written this way. `Loop.run` is a self tail call.
  Correctness: `Loop.run_eq`, `Loop.run_unique`.
* **Meas**: direct style. Calls can appear anywhere inside expressions, including nested
  (`ack m (ack (m+1) n)`). The termination argument is a measure written *in the language*,
  so there are no Lean proofs in the syntax. `measFix` compares measures with `lexLt` at run
  time and returns a default value if a call does not decrease. The capture elaborator
  proves that this default is never reached for captured functions. Correctness:
  `measFix_eq`, `measFix_unique`.

`#lean_wf_func_to_term f` (`Capture.lean`) picks the right elaborator from the expected
type, and `wf_agree` picks the right agreement tactic:

```lean
def gcd_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, PCL.Term.eval gcd_term m n = gcd m n := by wf_agree
```

All agreement theorems are in `RequestProject/WFLang/Examples/Langs.lean`. They build
without `sorry`, and their axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Which functions of the uploaded `Tco*.lean` files are supported

The uploaded files import a module `LeanScript` that does not exist in this project, so
the functions were copied verbatim into `RequestProject/WFLang/Examples/Functions.lean`
(namespace `Tco`). The rejections are checked with `#guard_msgs` in
`RequestProject/WFLang/Examples/LangChecks.lean`.

| file | function | PCL | Tail | Meas | note |
|---|---|:-:|:-:|:-:|---|
| TcoAck | `ack` | ✓ | ✗ | ✓ | nested call, so not tail recursive |
| TcoAck | `pair` | ✓ | ✓ | ✓ | non-recursive |
| TcoAck | `ackInner`, `ack2` | ✗ | ✗ | ✗ | higher order (`Nat → Nat` values) |
| TcoAck | `ackWhile`, `isqrt`, `ackNoDataStructure` | ✗ | ✗ | ✗ | `while` loop (`Loop.forIn`): no termination proof to capture; `ackWhile` also uses `List` |
| TcoDiagonal | `diagonal` | ✓ | ✗ | ✓ | `diagonal n 0 + 1` is not a tail call |
| TcoDiagonal | `diagonal_tr` | ✓ | ✓ | ✓ | lexicographic measure `(m+n, m)` |
| TcoDiagonal | `diagonalWhile` | ✗ | ✗ | ✗ | `while` loop |
| TcoHyper | `hyper` | ✓ | ✗ | ✓ | nested calls |
| TcoHyper | `hyperBase` | ✓ | ✓ | ✓ | non-recursive (a `match`) |
| TcoHyper | `hyperLoop`, `hyperTCO`, `hyperWhile` | ✗ | ✗ | ✗ | higher order (`hyperTCO` passes the function `hyperTCO n a` to `hyperLoop`) / `for` loop |
| TcoMc91 | `mc91` | ✓ | ✓ | ✓ | non-recursive in the uploaded version |
| TcoMc91 | `mc91Loop` | ✓ | ✓ | ✓ | measure `2*(111-n) + 21*c` |
| TcoMc91 | `mc91TR` | ✓ | ✓ | ✓ | calls another recursive function (`mc91Loop`), captured as a nested local recursive function (`Examples/More.lean`) |
| TcoMc91 | `iter`, `mc91While` | ✗ | ✗ | ✗ | higher order / `while` loop |
| TcoBoom | `boom` | ✗ | ✗ | ✗ | takes a proof argument `Safe n` and diverges without it, so it is not a total `Nat` function |

In the table, ✓ means captured with `#lean_wf_func_to_term`, with an agreement theorem
proved in `Examples/Langs.lean`. The non-recursive `mc91`, `hyperBase` and `pair` are in
section `ExNonRec`. The rejections are checked with `#guard_msgs`: `boom`, `iter`, `ack` (in
Tail), `diagonalWhile`, `ack2` and `hyperTCO` in `Examples/LangChecks.lean`, and `ackWhile`,
`isqrt`, `mc91While`, `hyperWhile`, `hyperLoop`, `iter` (in Tail) and `boom` (in Meas) in
`Examples/MoreChecks.lean`. `ackNoDataStructure` uses the same `while` construct and is not
tested separately. Both files also compare the evaluators with the Lean functions on test
vectors.

## Features added later: fixed parameters, structural recursion, calls to other functions

(Examples: `Examples/MoreFunctions.lean`, captures and agreement theorems: `Examples/More.lean`,
runtime checks and rejections: `Examples/MoreChecks.lean`.)

* **Fixed parameters.** Lean keeps a parameter that every recursive call passes unchanged (e.g.
  `k` in `def addK (k : Nat) (n : Nat) …`) outside of its `WellFounded.fix`. The capture now finds
  the fixpoint under these parameters and uses the relation `WFLang.fixedRel` (in
  `Common/Types.lean`): related environments agree on the fixed parameter, and the rest is related
  by Lean's own relation for that value of the parameter. `fixedRel_wf` proves it well-founded.
  Works in every grammar, including measures that mention a fixed parameter (`termination_by n - k`).
* **Structural recursion.** Functions defined by structural recursion on a `Nat` parameter (no
  `termination_by`; e.g. `fact`, `fib`, `evenS`) are captured with the relation "the recursion
  parameter decreases" (and, in `Meas`, the measure "the recursion parameter"). Works in every
  grammar.
* **Calls to other functions.**
  * Calls of *non-recursive* user-defined first-order functions are inlined, using their unfolding
    equations (every grammar); the agreement tactic unfolds them in the same way.
  * Calls of *recursive* user-defined functions become nested local recursive functions: a nested
    `fix` node in `PCL` and `Meas`, and a nested `loop` node in `Tail` (outside of loop bodies only).
    This applies transitively (e.g. `chain` calls `gcdSum`, which calls `gcd`). A call inside the
    test of an `if` that is not in tail position is evaluated first, which does not change the result
    because every function is total. The agreement tactic replaces each nested node by the Lean
    function it captures, via the node's uniqueness lemma (`fixFn_unique`, `measFix_unique`,
    `Loop.run_unique`), and proves the node's equation from the callee's `eq_def`.
  * Not supported: mutual recursion (rejected with a message), calls inside a `Tail` loop body, and
    calls of other recursive functions in the wrapper designs (single recursive body).
* The `#expect_reject t` command in `Examples/MoreChecks.lean` succeeds only if elaborating `t`
  fails, and prints the first line of the error for `#guard_msgs`.

## Is the C output optimized?

The generated C is in `c_output/lang/`: the evaluators are in `PCL_Lang.c`, `Tail_Lang.c`
and `Meas_Lang.c`, the programs in `LangExamples.c`, and native Lean for comparison in
`TcoExamples.c`. Short answer: **no. What gets compiled is an interpreter, not the program.**

1. **Captured programs are data.** `ExPCL.gcd_run` compiles to "load the static AST
   `ExPCL.gcd_term`, call `WFLang.PCL.Term.eval` on it, apply the result". The same holds
   for Tail and Meas. Lean's compiler does not partially evaluate the interpreter on the
   known term, so every step walks the AST, looks variables up in the tuple environment, and
   dispatches on `BinOp`.
2. **Proofs are erased.** PCL and Tail carry `dec` proofs and `wf` in the syntax, but none
   of it appears in the C: there are no runtime termination checks. Meas does check at run
   time: `WFLang.Meas.lexLt` (two `lean_nat_dec_lt`) runs on every recursive call.
3. **Tail calls.**
   * `Tail.Loop.run` compiles to a real `goto _start` loop (see `Tail_Lang.c`): the loop
     runs in constant stack space.
   * PCL's `fix` goes through `WellFounded.fixC`, and Meas's `fix` through `measFix`. A
     recursive call in the object language becomes a nested C call of the interpreter, even
     when the source call was a tail call. So stack depth grows with the number of calls.
   * Native Lean compiles the originals `Tco.diagonal_tr` and `Tco.mc91Loop` to `goto`
     loops (`TcoExamples.c`).

Measured with `lake exe wfbench <native|tail|pcl|meas> <m>` (`Bench.lean`, which computes
`diagonal_tr m 0 0`, about `m²/2` tail calls). These are single runs on this machine, so
treat the timings as rough:

| m (calls) | native | Tail | PCL | Meas |
|---|---|---|---|---|
| 100 (~5k) | – | – | 3 ms | 3 ms |
| 300 (~45k) | – | – | 25 ms | stack overflow (SIGSEGV) |
| 600 (~180k) | – | – | stack overflow | stack overflow |
| 1000 (~500k) | 1 ms | 49 ms | stack overflow | stack overflow |
| 3000 (~4.5M) | 4 ms | 420 ms | stack overflow | stack overflow |

In short: all three evaluators are total and proved sound for the captured functions.
Only Tail keeps tail recursion as a loop in C, and it is still about 100× slower than
native Lean because it interprets the AST. Getting native-quality C would take a compiler
from `Expr` to Lean or C (for example, a meta-level code generator that emits a Lean
`def`), together with a proof that the generated code agrees with `Expr.eval`. That step is
not implemented here.
