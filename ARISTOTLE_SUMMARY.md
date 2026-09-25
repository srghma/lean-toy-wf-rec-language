# Summary of changes for run ebcc0f51-6ff3-48bf-a7c2-d1436d664f80
I removed the broken `ackWhile`. The corrected loop is now the only version and is called `Tco.ackWhile`. `lake build` succeeds with no errors, and there is no `sorry` in the project.

**Changes**
- **`Tests/Functions.lean`:** `Tco.ackWhile` now has the corrected push order `top :: (top - 1) :: stack` for the case `A(m, n) = A(m-1, A(m, n-1))`. The file's header now says that the uploaded functions were copied unchanged except for this one.
- **`Tests/Sources.lean`:**
  - Removed `ackWhileFixed`, the one-iteration copy of the loop `ackWhileStep`, the `ackWhile_1_1_cycles` theorem, the check that the old version agreed with `ack` only when m = 0, and the section explaining the bug.
  - What's left for `ackWhile`:
    - The check that `#lean_wf_func_to_term` still rejects it (it is a `while` loop).
    - One check that `Tco.ackWhile m n` equals the PCL program for `ack` for m ≤ 3 and n ≤ 4. This compares sample inputs only; it is not a proof, because a `while` loop can't be reasoned about in this Lean version.
  - The table row for `ackWhile` now says "runtime check below" instead of "diverges".
- **`README.md`:** removed the reference to the "ackWhile bug".
- **Properties table:** removed the entry for the divergence of the old `ackWhile`.

# Summary of changes for run da667d5d-3b43-4c7d-b100-06ec4b62c6dc
You were right: the files in `sources/` weren't built. They imported an external `LeanScript` package, and some of their proofs don't compile with this project's Lean version (4.28). Every function in them is now in the test suite and is either captured by PCL or rejected, with a test for each. `sources/` has been deleted. `lake build` and `lake build wfbench` succeed with no errors, warnings or `sorry`. The new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Where things went**
- **`Tests/Functions.lean`** (namespace `Tco`): every function from the five files, copied unchanged. That includes `ack999`, `ack2`, `ackWhile`, the Cantor-pairing namespace (`pair`, `isqrt`, `unpairLeft`, `unpairRight`, `ackNoDataStructure`), `diagonalWhile`, `hyperLoop`, `hyperTCO`, `hyperWhile`, `mc91While` and `Safe`. `pair` now sits in its original namespace, and the existing tests use that name.
- **`Tests/SourceProofs.lean`** (new): the theorems from those files. Two changes:
  - In `mc91Loop_eq`, one `grind =>` step became `simp`, because that syntax doesn't exist in 4.28.
  - `diagonalWhile_eq` is left out. Its proof relies on a later Lean's support for reasoning about `while` loops. In 4.28 a `while` loop is built on a private `partial` function that proofs can't look inside, so the statement can't be proved here. It is checked on sample inputs instead.
  - I also added one theorem, `hyperWhile_eq_hyper`: a `for` loop is a fold over a list, so unlike a `while` loop it can be reasoned about.
- **`Tests/Sources.lean`** (new): a table covering every function from the files, plus the tests behind it. The scattered copies and rejection tests in `BasicChecks.lean` and `MoreChecks.lean` were merged into it.

**Results per function**
- **Captured, with a proved agreement theorem:** `ack`, `diagonal`, `diagonal_tr`, `hyper`, `hyperBase`, `mc91`, `mc91Loop`, `mc91TR`, `pair`, and now also `ack999`. `ack999` takes no arguments, and its theorem is proved without computing `ack 999 1`.
- **Rejected, but proved equal to a captured program:** using the theorems from your files, `ack2` equals the PCL program for `ack`. `hyperTCO` and `hyperWhile` equal the program for `hyper`, and `iter mc91` equals the program for `mc91Loop`.
- **Rejected, each with a checked error message:**
  - `while` loops: `ackWhile`, `isqrt`, `unpairLeft`, `unpairRight` (their `isqrt` call is a loop), `ackNoDataStructure`, `diagonalWhile`, `mc91While`.
  - A recursive call inside a `for` loop: `hyperWhile`.
  - Function arguments or results: `ack2`, `hyperLoop`, `hyperTCO`, `iter`.
  - A proposition: `Safe`.
  - A proof argument: `boom`.
- **Loop functions checked only on sample inputs:** `diagonalWhile` and `mc91While` against their PCL counterparts; `ackNoDataStructure` against PCL `ack` for m ≤ 2, n ≤ 3; `isqrt` as an integer square root; `unpairLeft`/`unpairRight` as inverses of the captured `pair`. These are sample-input checks, not proofs.

**A bug in your `ackWhile`:** it doesn't compute Ackermann. It runs forever on `ackWhile 1 1` and `ackWhile 2 0`, for example. In the case `A(m, n) = A(m-1, A(m, n-1))` it pushes `(top - 1) :: top :: stack`, so the outer call comes off the stack before the inner one. From m = 1, n = 1 the loop returns to the state (`[1]`, `1`) after two iterations.
- `ackWhile_1_1_cycles` proves that cycle, but for a hand-written copy of one loop iteration, since the loop itself can't be unfolded in a proof. The rest of the evidence is that running `ackWhile 1 1` doesn't finish.
- `ackWhile` does agree with PCL `ack` when m = 0, and at m = 1, n = 0.
- A corrected copy, `ackWhileFixed`, with the two pushes swapped, agrees with PCL `ack` for all tested inputs.
- Separately, the files' comment that `ackNoDataStructure 3 2` gives 29 didn't hold up in practice: my attempts at inputs like that didn't finish, because the stack encoding grows extremely fast. That's why its checks stop at m ≤ 2.

`README.md` shows the new file layout. In the Properties table, I updated the entries for the uploaded functions and added one for the derived agreement theorems and one for the `ackWhile` cycle. The two older entries still point at lines in the original uploaded files, because the table wouldn't accept a blank source reference.

# Summary of changes for run 2531a267-9d30-4b09-85c3-a34bfe0ddd13
The project now contains only PCL, reorganised into four folders, and the whole PCL test suite is still there. `lake build` succeeds with no errors, warnings or `sorry`, and the `wfbench` executable builds too. I checked the axioms of `ExPCL.gcd_agree`, `MorePCL.chain_agree`, `fix_body_reaches_base` and `Term.eval_fix_eq`: they use only `propext`, `Quot.sound` and, for `chain_agree`, `Classical.choice`.

**Removed**
- The other grammars: `Tail`, `Meas` and the `Wrapper` grammar with its four designs (`Guarded`, `GuardedAcc`, `FreeCall`, `Checked`, `Bridge`).
- The alternative designs `Designs/VC.lean`, `Designs/Ext.lean` and their examples.
- The tests and examples for those grammars, and `WFBox` and `Ty.default`, which only they used.
- The unused `RequestProject/Main.lean`.
- The out-of-date C snapshots in `c_output/`, which still used old module names.
- The notes that described several grammars: `ASSESSMENT.md`, `DESIGNS.md`, `LANGUAGES.md`, `STRUCTURE.md`.

**New layout** (under `RequestProject/WFLang/`, all imported by `RequestProject/WFLang.lean`)
- `Core/`: `Types.lean` (types, environments, variables, operators, `fixedRel`) and `PExpr.lean` (expressions without recursive calls).
- `PCL/`: `Lang.lean` (the language, evaluator and soundness proofs) and `Termination.lean`.
- `Capture/`: `Meta.lean`, `Translate.lean` and `Elab.lean`.
- `Tests/`: `Functions.lean`, `Basic.lean`, `BasicChecks.lean`, `MoreFunctions.lean`, `More.lean`, `MoreChecks.lean`.
- The uploaded `Tco*.lean` files are now in `sources/`, unchanged. They import a `LeanScript` module that isn't in the project, so they aren't built; their functions are copied into `Tests/Functions.lean`.

**Refactoring**
- There is now one capture command, `#lean_wf_func_to_term`, and one tactic, `wf_agree`. The separate `#lean_wf_func_to_pcl` and `pcl_agree` names are gone, and all error messages start with `#lean_wf_func_to_term:`.
- The Lean-to-syntax translator no longer supports several target grammars; it produces PCL expressions directly.
- `wf_close` no longer has the proof steps that only the runtime-checked grammars needed. Every agreement proof still goes through.
- `Bench.lean` now compares native Lean with PCL only: `lake exe wfbench <native|pcl> <m>`.

**PCL test suite**
- 30 agreement theorems in total: 12 in `Basic.lean` (`gcd`, `isPow2`, `digitSum`, `sumTo` and the `Tco` functions) and 18 in `More.lean`.
- All runtime `#guard_msgs` checks were kept. Where a check compared PCL with other grammars, it now checks PCL alone.
- The `fib` output check used to run on `Meas`; it now runs on PCL.
- Rejection tests that targeted another grammar but also apply to PCL now target PCL: mutual recursion, `while` loops, higher-order functions and `boom`. Rejections that only made sense for the removed grammars were dropped, such as "not tail recursive" for `Tail`.

`README.md` now describes the PCL language, the capture and the file layout.

In the Properties table, I removed the entries for the deleted grammars and designs. The remaining entries point at the new file paths, and their descriptions now cover PCL only.

The files still don't start with `module`, as before; switching them over would have been a separate change to every file. The Mathlib dependency stays because `PCL/Termination.lean` uses `Relation.ReflTransGen`.

# Summary of changes for run 6fceaade-4cd1-4e9d-b6cc-c57836d635cc
**Short answer:** in PCL, evaluating a well-typed program can't fail to terminate. There is no error case and no default value. `Expr.eval` returns a value of the result type directly (not an `Option`), and Lean only accepted its definition because it is total. `#print axioms WFLang.PCL.Expr.eval` reports that it uses no axioms at all.

**Why it terminates, even without an explicit check for a return inside the body:**
- `Expr.eval` recurses structurally on the syntax tree, which is always finite. The only exception is a `fix` node, which runs its body through `WellFounded.fix` on the relation `R` stored in that node.
- Inside a `fix` body, the only way to recurse is a `call` node. The evaluator makes that call through a handler with the type `(y : Env params) → R y current → result`, so it can't make the call without the proof `dec` that the arguments are `R`-smaller. That proof is a required field of `call`.
- Together with `wf : WellFounded R` (also a required field of `fix`), this is exactly what `WellFounded.fix` needs. No infinite chain of calls exists, so no fuel and no runtime check are needed.

**Is there a proof that a base case exists?** The evaluator doesn't need one, but it follows from the typing rules. I proved it in the new file `RequestProject/WFLang/PCL/Termination.lean`, with no `sorry`, using only `propext` and `Quot.sound`:
- `Expr.firstCall body x` gives the arguments of the first recursive call the body makes on input `x`, or `none` if it returns without calling itself.
- `fix_body_reaches_base`: from any argument `x`, following first calls reaches, in finitely many `R`-steps, an argument where the body returns without recursing. So a body where every path calls itself can't be written with a well-founded `R`.
- `fix_body_has_base_case` is the corollary: every `fix` body has at least one base-case input.
- `loop_unbuildable`: the looping program `fix self x. let v := self x in v` can't be built, because its `call` node would need a proof of `R x x` for every `x`, and no well-founded `R` allows that.

The file is imported by `RequestProject/WFLang.lean`, the whole project builds, and both theorems are in the Properties table. It doesn't start with `module`, because none of the project's existing files are modules and a module file can only import other modules.

**Limits of this guarantee:**
1. **It depends on real proofs.** The proofs are erased in compiled code. If someone supplies `wf` or `dec` using `sorry` or a made-up axiom (for example, claiming a relation that isn't well-founded is), the compiled program could genuinely run forever. Lean warns about such definitions and `#eval` refuses to run them, but nothing is checked at runtime.
2. **Terminating isn't the same as fast.** A captured Ackermann function terminates in theory but may not finish in practice.
3. **Resources can still run out.** Compiled PCL uses real recursion, and earlier benchmarks hit stack overflows at about 180k calls. That is a machine limit, not non-termination.

This differs from `Meas`, where the measure is only checked at runtime and a wrong measure makes the evaluator silently return a default value. In PCL, a wrong relation simply means the program can't be written.

# Summary of changes for run 7c368437-a280-45dd-bbb3-ff7688e97e32
**What happens when the measure is wrong in `Meas`?** The evaluator returns the default value of the result type (`0` for `nat`, `false` for `bool`) for the call that fails the check. It reports nothing, and the rest of the computation uses that made-up value. I proved this on an example: with the wrong measure `(m, 0)`, `gcd 4 6` evaluates to `0` instead of `2` (`ExMeasWrong.gcdWrong_4_6`). Functions captured with `#lean_wf_func_to_term` never hit this case. But you're right that nothing in the language stops a hand-written program from having a bad measure, and the failure is hidden.

I built two alternative designs in `RequestProject/WFLang/Designs/`. The whole project builds with no `sorry` or warnings, and the key theorems use only the standard axioms. The full comparison with pros and cons is in `DESIGNS.md`.

**PCL-VC** (`Designs/VC.lean`): proof-free syntax, one proof per program.
- It is `PCL` with the proofs removed from each call: a call is just `let v := self args in k`.
- `Expr.VC` gathers every "this call decreases" obligation into one statement, and the evaluator takes one proof of it.
- Proved: the fixpoint equation and that it has a unique solution. Removing the proofs from any `PCL` program gives a program that still satisfies `VC` and computes the same value (`erase_vc`, `erase_eval`).
- So the existing capture works here too: `ExVC.gcd_agree` and `ExVC.ack_agree`.
- A `gcd` written with a wrong relation is valid syntax, but its `VC` is provably false, so it can't be run (`gcdWrong_not_certified`).
- Pros: programs are plain data that are easy to write, generate and transform; termination is proved once, separately; no runtime cost.
- Cons: the proof must be redone after every program transformation; the relation is still written inside the program.

**PCL-Ext** (`Designs/Ext.lean`): the measure is chosen from outside. This is the direct answer to your criticism.
- The program contains no relation, measure or proof. Whoever runs it supplies a measure `μ : Env → ℕ × ℕ` (compared lexicographically) as an ordinary Lean function.
- It has three evaluators:
  - `eval p μ hμ` needs a proof that `μ` decreases at every call and does no runtime checks. With a wrong measure the proof doesn't exist, so the evaluator can't be called.
  - `runChecked p μ` needs no proof. It returns an **error** naming the failing measures, e.g. `.error (.notDecreasing (6,0) (4,0))` for `gcd 4 6` with the wrong measure (`gcd_wrong_error`). It never returns a default value.
  - `runFuel p n` returns `.error .outOfFuel` when fuel runs out. It is simple structural recursion, so concrete runs can be checked with `rfl`.
- Proved:
  - The evaluator satisfies the program's recursive equation (which doesn't mention the measure) and is its only solution.
  - Any two correct measures give the same function (`eval_measure_irrelevant`): the measure only justifies termination, it never changes a result.
  - With a proved measure, the checked evaluator always succeeds (`runChecked_eq_ok`), so an error proves the measure is wrong (`not_decreases_of_error`).
  - For a proved `ℕ` measure `f`, fuel `f x + 1` is always enough (`runFuel_measure`).
- Examples (`Designs/Examples.lean`):
  - `gcd` and `Tco.ack` agree with the Lean functions, and a second correct measure for `ack` gives the same function.
  - Wrong measures for `gcd` and `ack` produce errors and have no proof of decrease.
  - Runtime `#guard_msgs` checks compare the evaluators with `gcd` and `Tco.ack`.
- Pros: termination is fully external; wrong measures are either impossible (with a proof) or reported as errors.
- Cons: only one recursive function per program; the measure must be a pair of naturals; there is no capture command yet, so the examples are written by hand.

`DESIGNS.md` also briefly describes four designs I did not implement: a domain predicate (Bove–Capretta), a partiality monad, structural-only recursion, and a termination-proof (`Acc`) argument on each call. `STRUCTURE.md` lists the new files, and the Properties table has entries for the new designs and results.

# Summary of changes for run 4f67535c-3ac9-4434-9b2e-915257847fae
I added the three features that were still missing from the capture, plus a set of new tests. The whole project builds with no `sorry` and no warnings, and so does the `wfbench` executable. I spot-checked several of the new agreement theorems (`MorePCL.chain_agree`, `MoreMeas.chain_agree`, `MoreTail.twoLoops_agree`, `MorePCL.mc91TR_agree`, `MoreMeas.fib_agree`, `MoreWrapper.addK_checked_agree`), and they use only the standard axioms.

**New features** (in the shared capture code, `Common/Meta.lean` and `Common/Translate.lean`, and each grammar's `Elab.lean`):
- **Fixed parameters.** A function like `def addK (k : Nat) (n : Nat) …`, where `k` is passed unchanged to every recursive call, used to fail with an internal error. It now works in every grammar, including measures that mention the fixed parameter (e.g. `termination_by n - k`). This uses a new relation `WFLang.fixedRel`, with a proof that it is well-founded (`fixedRel_wf`, in `Common/Types.lean`).
- **Structural recursion.** Functions without `termination_by` that recurse on a `Nat` argument, such as `fact`, `fib` (with an `n + 2` pattern) and `evenS`, used to be rejected. They now work in every grammar.
- **Calls to other functions.**
  - Calls to non-recursive helpers are inlined, in every grammar.
  - Calls to recursive functions become nested recursive functions in PCL and Meas. Tail supports them too, except inside a loop body. This works through chains of calls: `chain` calls `gcdSum`, which calls `gcd`.
  - A call inside an `if` test that is not in tail position is evaluated first, which doesn't change the result because every function terminates.
  - `wf_agree` proves these cases too, using each language's existing uniqueness lemma.
  - As a result, your `Tco.mc91TR` is now captured, with agreement proved in PCL, Tail and Meas.
  - Still rejected, with a clear error message: mutual recursion, a call inside a Tail loop body, and calls to other recursive functions in the four wrapper designs (their grammar has only one recursive body).

**New tests:**
- `Examples/MoreFunctions.lean` holds 19 new test functions.
- `Examples/More.lean` has 54 agreement theorems covering PCL, Tail, Meas and the four wrapper designs. A table at the top of the file shows which language supports which function.
- `Examples/MoreChecks.lean` has 31 `#guard_msgs` checks:
  - It runs every new program and compares it with the Lean function on sample inputs.
  - It adds a test command, `#expect_reject t`, which passes only if the capture fails, and checks the first line of the error.
  - It uses that command to confirm the expected rejections: mutual recursion, a call inside a Tail loop body, the wrapper designs, a mismatched signature, and your `ackWhile`, `isqrt`, `mc91While`, `hyperWhile`, `hyperLoop`, `iter` and `boom`.
- `Examples/LangChecks.lean` now also runs `isPow2`, `digitSum`, `sumTo`, `mc91`, `hyperBase` and `pair`, which had no runtime checks before. The old check that `mc91TR` is rejected is replaced by a note pointing to `More.lean`. The expected error text for `hyperTCO` is updated because the error message has changed.

Two small fixes along the way: a function that merely calls a recursive function is no longer mistaken for a recursive one, and the Checked wrapper design can now handle an `if` whose result is combined with a recursive call (the case `countAbove` needs).

**Still not possible:** higher-order functions (`iter`, `ack2`, `hyperLoop`, `hyperTCO`) and `while`/`for` loops. Loops are built without any termination proof, so there is nothing to capture. `ackNoDataStructure` also uses a `while` loop but has no separate test.

`LANGUAGES.md` has a new section describing these features and an updated support table, and `STRUCTURE.md` and `ASSESSMENT.md` are updated to match.

# Summary of changes for run 2055f354-9e46-45a5-a122-cec8ac15a2a2
I reorganised the project into a `Common/` directory plus one directory per grammar, and removed the duplicated code. Everything still builds with no `sorry` and no warnings, including the `wfbench` executable. The `#guard_msgs` checks still pass, and the agreement theorems I spot-checked (`ExGuarded.gcd_agree`, `ExPCL.ack_agree`, `ExMeas.hyper_agree`, `ExTail.mc91Loop_agree`, `Tco.CK.hyper_agree`) use only `propext`, `Classical.choice` and `Quot.sound`.

**New layout** (also written up in `STRUCTURE.md`):
- `RequestProject/WFLang/Common/` holds what every grammar shares:
  - `Types.lean`: `Ty`, `Env`, `Var`, `Sig`, `FnType`, currying and `BinOp`.
  - `WFBox.lean`: the helper for `termination_by` on a stored relation.
  - `PExpr.lean`: the call-free expressions, which used to live inside PCL even though Tail and Meas use them too.
  - `Meta.lean`: the `#lean_wf_func_to_term` / `wf_agree` syntax, the code that reads a Lean function (its signature, `eq_def`, `WellFounded.fix`, the call-site proofs, the relation), and the shared `wf_dec` / `wf_close` tactics and agreement-proof skeleton.
  - `Translate.lean`: turns a Lean term into object-language syntax. It works for any grammar, and one shared function recognises `if` / `match` / `cond` / `&&` / `||`.
- **One directory per grammar:**
  - `Wrapper/` holds the old single grammar (`Expr.lean`) and its four designs (`Guarded`, `GuardedAcc`, `FreeCall`, `Checked`), plus `Bridge` and `Elab`.
  - `PCL/`, `Tail/` and `Meas/` each contain `Lang.lean` and `Elab.lean`.
- `Capture.lean` is now the only place that registers `#lean_wf_func_to_term` and `wf_agree`. It picks the grammar from the type, for all four grammars.
- `Examples/` contains `Functions.lean` (your `gcd`, the helper functions and the `Tco` functions, each defined once), `Wrapper.lean`, `WrapperChecks.lean`, `Langs.lean` and `LangChecks.lean`.

**Duplication removed:**
- The wrapper capture had its own 130-line term translator. It now uses the shared one and elaborates the result against `Body sig`.
- Signature extraction, reading `eq_def`, the relation setup and parsing the agreement goal each appeared 3–4 times; each now exists once.
- The four agreement tactics share one skeleton and one closing tactic (`wf_close`).
- The "`t.eval = f`" proof, repeated across 7 evaluators, is now one lemma (`curryEnv_eq`).
- The duplicated `stmt` / `body` control-flow code in PCL and Tail now shares one branch recogniser.

Line count under `RequestProject/` went from about 3,100 to about 3,000, even with new module docs.

**Things that changed for users:**
- Public names are unchanged except that the call-free expressions are now `WFLang.PExpr` / `WFLang.PExprs` rather than `WFLang.PCL.PExpr`.
- Errors from the shared translator now start with `#lean_wf_func_to_term:`. They used to say `#lean_wf_func_to_pcl:` even for Meas, and `Examples/LangChecks.lean` is updated to match.
- `ASSESSMENT.md` and `LANGUAGES.md` now point to the new file paths.
- The C files in `c_output/` were generated before the move, so they still carry the old module names; `STRUCTURE.md` says so.
- The Properties table points at the new files.

# Summary of changes for run 58692e9d-b11a-4cec-b1b9-52a85a2f45ad
Some of your functions are supported and some aren't. The C output is **not** optimized: the compiled code is an interpreter walking the captured syntax tree, not the program itself. Everything builds with no `sorry`; the agreement theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Full write-up: `LANGUAGES.md`.

**The three languages.** Each has well-founded recursion as a constructor of its own `inductive Expr`, its own evaluator, and its own capture command. `#lean_wf_func_to_term` and `wf_agree` pick the right one from the expected type.
- **PCL** (`RequestProject/WFLang/PCL/`): `fix` carries a relation `R` and a proof that it is well-founded; each `call` carries its own proof that the arguments decrease, using the enclosing `if` conditions. Evaluation needs no fuel or runtime checks.
- **Tail** (`RequestProject/WFLang/Tail/`): a well-founded `loop` whose body can only return, jump back with new state, or branch. Only tail-recursive functions fit.
- **Meas** (`RequestProject/WFLang/Meas/`): calls can go anywhere, including nested ones; the termination measure is a pair of `Nat` expressions written in the language. The evaluator checks that it decreases at run time.

For each language I proved the evaluator satisfies the recursion equation and is its unique solution.

**Your `Tco*.lean` files.** They import a module `LeanScript` that isn't in the project, so I copied the functions verbatim into `TcoExamples.lean`. Agreement theorems are in `LangExamples.lean`:

| Supported in | Functions |
|---|---|
| PCL and Meas | `ack`, `diagonal`, `diagonal_tr`, `hyper`, `mc91Loop` |
| Tail | `diagonal_tr`, `mc91Loop` |
| All three (non-recursive) | `mc91`, `hyperBase`, `pair` |

Not supported:
- `boom`: takes a proof argument.
- `mc91TR`: calls another top-level function; only self-recursion is supported.
- `iter`, `ack2`/`ackInner`, `hyperLoop`/`hyperTCO`: take or return functions.
- The `while`/`for` versions (`ackWhile`, `isqrt`, `ackNoDataStructure`, `diagonalWhile`, `hyperWhile`, `mc91While`): Lean builds these loops with no termination proof, so there is nothing to capture.
- `ack`, `diagonal`, `hyper` in Tail: not tail recursive.

`LangChecks.lean` confirms most of these rejections (`boom`, `mc91TR`, `iter`, `ack2`, `hyperTCO`, `diagonalWhile`, `ack` in Tail) and compares every evaluator with the Lean functions on sample inputs. I checked `isqrt` and `hyperWhile` once by hand; the remaining ✗ entries weren't tested individually. I also fixed PCL: `mc91TR` used to give a confusing type error and now gets a clear "unsupported expression" message.

**C output** (`c_output/lang/`), from reading the generated C and single benchmark runs — observations, not proofs:
- Each `*_run` function just hands a fixed syntax tree to the compiled evaluator; Lean doesn't specialise the evaluator to it.
- The decrease proofs are erased, so PCL and Tail have no runtime checks. Meas compares measures on every recursive call.
- Only Tail's loop compiles to a `goto` loop with constant stack. In PCL and Meas every recursive call, even a tail call, is a nested C call.
- Timing uses `lake exe wfbench <native|tail|pcl|meas> <m>` (`Bench.lean` and a `wfbench` target added to `lakefile.toml`), computing `diagonal_tr m 0 0`, about m²/2 calls:

| Calls | Native Lean | Tail | PCL | Meas |
|---|---|---|---|---|
| ~45k | – | – | 25 ms | stack overflow |
| ~180k | – | – | stack overflow | stack overflow |
| ~4.5M | 4 ms | 420 ms | stack overflow | stack overflow |

Native Lean itself compiles `diagonal_tr` and `mc91Loop` to `goto` loops. Getting C close to native would need a compiler from `Expr` to Lean code plus a correctness proof; that isn't implemented.

The earlier wrapper-based designs are unchanged and are now imported by `RequestProject/WFLang.lean`.

# Summary of changes for run 236d074f-ed1e-4f96-8de2-26374fac093e
I built the toy language, four evaluator designs, and the `#lean_wf_func_to_term` capture, then compared the generated C. Three of the four designs produce no fuel-like data structures. Everything builds with no `sorry`, and the theorems use only the standard axioms (`propext`, `Quot.sound`). The code is in `RequestProject/WFLang/`, the write-up is in `ASSESSMENT.md`, and copies of the generated C are in `c_output/`.

**The language** (`Syntax.lean`) is typed (`nat`, `bool`), with variables, literals, `+ - * / %`, `<`, `≤`, `bool_eq`, `&&`, `||`, `!`, if-then-else and a recursive self-call. Neither the syntax, nor any `Term`, nor any evaluator contains fuel, a measure or `AccT`. Each program carries a relation `R`; `WellFounded R` and the "recursive calls get smaller" condition are ordinary `Prop`s.

**Terminating and sound, per design.** Each evaluator is a normal total Lean `def`, which is what makes it terminating. For each design I proved two things:
- `Term.run_isFix`: the evaluator satisfies the function's recursive equation.
- `Term.isFix_unique`: any function satisfying that equation equals the evaluator.

**The four designs:**
1. **`Guarded`**: a "delayed" semantics where each expression yields a condition in `Prop` plus a function from that condition to the value. Recursion uses `termination_by` on `R`.
2. **`FreeCall`**: the body is first turned into a tree of pending recursive calls (a free monad), and the `Prop` condition is that every call in the tree is `R`-smaller. Recursion uses `WellFounded.fix`.
3. **`GuardedAcc`**: the same condition as 1, but recursion uses `Acc.rec` on the ordinary `Prop`-valued `Acc`, not `AccT`.
4. **`Checked`**, included for contrast: a weaker condition (the body only depends on `R`-smaller calls) plus a decidable `R`, so the evaluator has to check `R` before every call.

**Capturing a Lean function** (`Reify.lean`). You write:
`def gcd_term : Term ⟨[.nat,.nat],.nat⟩ := #lean_wf_func_to_term gcd`
The macro:
- turns the right-hand side of `gcd.eq_def` into a term;
- reuses the well-founded relation and proof that Lean built for `gcd`;
- pulls out the proofs at each recursive call (including your `decreasing_by` proof) to discharge the design's condition.

Which design you get is picked from the expected type. A tactic `wf_agree` then proves agreement.

In `Examples.lean`, `gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n` is proved for all four designs. The same capture-and-agree pattern is proved for `digitSum`, `isPow2` (Bool result) and `sumTo`. Runtime checks run as part of the build and confirm all four evaluators match the native `gcd`.

**What the generated C shows:**
- **No fuel-like structures in designs 1, 2 and 3.** All proofs become `lean_box(0)`. For these three designs, `gcd_term` compiles to the same static object: just the syntax tree, with `R`, the well-foundedness proof and the condition erased.
  - `Guarded` works by building and running small closures.
  - `GuardedAcc` is identical, and the compiled function has no `Acc` argument at all.
  - `FreeCall` builds the call tree and walks it in a loop.
- **Design 4 does runtime termination work.** At every recursive call it runs a closure that decides `R y x` (for `gcd`, `lean_nat_dec_lt` on the second argument, i.e. the measure). It also keeps a default-value branch that is never taken.
- **Remaining costs in 1–3 compared with native code:**
  - the interpreter overhead;
  - one dummy field in a pair in design 1;
  - the variable-type list is passed at runtime;
  - recursion is real recursion, whereas native `gcd` compiles to a `goto` loop.

**Limitations:**
- The macro handles `Nat`/`Bool` arguments, if-then-else forms, comparisons, boolean operators, arithmetic and direct self-calls. It does not handle `match`-based definitions (e.g. Ackermann written by pattern matching); fixed parameters are not supported either.
- Every design's condition must hold for any results of earlier recursive calls. So nested recursion whose decrease depends on an inner call's result cannot be certified.