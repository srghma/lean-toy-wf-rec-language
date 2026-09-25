# Summary of changes for run f70d706a-08ba-4ca8-9107-758881c43445
I wrote `UNSUPPORTED.md`, an assessment of what the language and `#lean_wf_func_to_term` still can't do. I also added a test file, `RequestProject/WFLang/Tests/Unsupported.lean`, that pins each new rejection with `#guard_msgs`: if the capture starts accepting one of those functions, `lake build` fails. The full `lake build` passes and the new test file has no `sorry`. Entries I didn't re-test are marked "[documented]" in the file, meaning they are taken from the earlier notes.

**Unsupported, with tests pinning the rejection:**
- **Types:** only `Nat`, `Bool`, `Int`, pairs, lists and subtypes of them are allowed. `Option`, `String`, user structures and `Array` are rejected, even when they only appear as intermediate values. A `match` on the constructors of `Int` is also rejected.
- **Library code:** `List.map`, `foldl`, `contains`, `getD`, `l[i]!` and `decide` on a bounded `∀` are rejected, as is a recursive call under a `fun` passed to a library function (`underLambda`).
- **`do` notation:** rejected are `for x in l` over a list, `break`, early `return`, and ranges with a step. By contrast, `for` over a plain range, `let mut` with `if`, and `let rec` are accepted.
- **Recursion:**
  - Lean's own `while`, `partial` and `partial_fixpoint` are rejected.
  - Mutually recursive functions must share the same signature.
  - Calls inside a `wf_while` loop body are rejected.
- **A termination proof the capture can't redo:** `nestMin (n+1) = nestMin (min n (nestMin n)) + 1`. Lean proves it terminates, but the capture fails on a goal that is true, because it turns `min` into an `if` and Lean's proof no longer fits. This is a new finding and a gap in the capture's automation, not in the language.

**Other limits, taken from the earlier notes:**
- The capture itself has no correctness theorem; each captured function is only trusted once its own agreement theorem is proved.
- The evaluator uses one stack frame per recursive call, tail calls included. Under `#eval` it aborts at around 2–3k nested calls.
- A value bound by `let` and used twice is computed twice.
- Each call of an `@[inlinable]` recursive helper makes a separate copy of it.
- Some tooling rough edges, e.g. `wf_agree` can mix up two functions with the same body, and error messages are vague.

The file ends with a suggested order for further work, starting with `Option`/sum types and list loops. `README.md` now links to it.

# Summary of changes for run 447b61cb-6dda-4e6d-b775-1eef326acb48
I wrote the assessment in `CONTEXTS_ASSESSMENT.md`. It is based on reading the code only: I didn't change the language or the capture, and none of the claims has a new Lean proof behind it. In the code, "fnCtx" is the `fns` index of `Expr`, "jpCtx" is `js : JScope`, and "globalCtx" is the `GL` parameter.

**1. Removing fnCtx: there is no semantic or soundness reason to keep it.**
- **Local functions are already closed.** A `fix` body sees only its own parameters and an empty join-point scope, and its `R`/`pre`/`post` mention only those parameters. Its value depends only on the globals and on earlier local functions, so each one is a global in disguise.
- **Callers learn the same thing either way.** `fnCall` and `gCall` have identical premises (precondition in, postcondition out), so moving a function to the globals loses no decrease-proof information.
- **The ordering rules match.** Both contexts only allow calls to functions defined earlier, so lifting a `fix` into the global list is always possible.
- **The capture never really uses the context.** Every local call it emits is a fresh `fix` followed by `fnCall FnVar.here`, so a callee called k times is copied k times. `Tests/Globals.lean` pins this: 3 `fix` copies for 3 calls, and program size 19 versus 11 with globals.
- **`wf_agree` already treats local and global callees the same way.**

The reasons to keep it are all costs, not limitations of the language:
- The capture would need an up-front pass to collect and deduplicate `@[inlinable]` recursive callees, mutual groups, self-calling higher-order functions and specialised copies.
- A recursive `@[inlinable]` function would become global unless recursive join points exist, so the attribute would do nothing for it.
- Many pinned test counts (`fixes`, `nglobals`, `size`) would change.
- Programs would be slightly less self-contained to read.

**2. Should jpCtx take `R`? Yes, if it is done together with removing fnCtx.**
- **Shape of `R`:** it should depend on the environment where the join point is defined, like `whileLoop`'s relation, with `wf : ∀ e, WellFounded (R e)`. Only jumps from inside the join point's own body (back edges) need a decrease proof; the entry jump does not.
- **What it buys:**
  - It subsumes `whileLoop`.
  - Loops could exit early and call the enclosing recursive function, which neither `whileLoop` nor `fix` allows today.
  - Loops keep their captured variables instead of taking them as extra parameters, and decrease proofs get the full path condition.
  - Every tail-recursive helper, called anywhere, can become a join point; only functions with non-tail recursion need to be globals.
  - It is a step towards evaluating tail calls without growing the stack (see `STACK_OVERFLOW.md`), though it does not fix that in the current evaluator.
- **What it costs:** the join-point context must track the current argument to check decreases, `jump` needs a decrease field, and new equation and uniqueness lemmas are needed. The largest change is in `PCL/Termination.lean`, where finding the first recursive call must now iterate through recursive join points. The capture also needs a tail-recursion check, rewriting of the helper's returns, and an agreement proof per join point.

The file recommends doing both changes: local functions split into recursive join points (tail recursion) and globals (everything else). If only one is done, removing fnCtx in favour of globals is the cheaper change. Adding `R` alone would leave three overlapping loop mechanisms: `fix`, `whileLoop` and recursive join points.

The file is committed; no Lean files changed.

# Summary of changes for run 54ed47dd-645a-4154-af63-da1724d3dabb
**1. `where` helpers: yes, the capture already matched Lean, and I didn't need to change anything.** Lean turns `def foo … where go …` into two top-level constants, `foo` and `foo.go`, and `#lean_wf_func_to_term` treats `foo.go` like any other user function. Capturing your `foo` gives 1 global function (`foo.go`) and 1 global call. If you write `where @[inlinable] go …`, `go` is inlined as a local recursive function (`fix`) instead, and an `@[inlinable]` function never ends up in the global context. `foo.go` can also be captured on its own, and a function outside `foo` can call it (`useGo`). The new file `Tests/WhereFold.lean` fixes these counts in place and proves each case agrees with its Lean definition.

**2. Calls where all arguments are known: they weren't evaluated before; now they are.** Before this change, `a + triple 3 + sumTo 4` kept both calls and put both functions in the global context.
- **What changed:** when every argument of a call is known (the call contains no variables), the capture computes its value and uses that instead. This applies whether or not the callee is `@[inlinable]`, recursive or not, including `where` helpers. A function that is only called this way doesn't appear in the program at all.
- **Example:** `allKnown a = a + triple 3 + sumTo 4 + foo.go 2 3 + fact 5 + gcd 12 18 + sumDigits 1234` becomes a single `ret (a + 9 + 10 + 5 + 120 + 6 + 10)`, with no global functions and no local `fix`.
- **Turning it off:** `set_option wfLang.foldCalls false` restores the old behaviour; the same function then has 6 global functions.
- **Proofs:** the value is computed by Lean's kernel, and `wf_agree` proves each `g args = value` step with the same kernel computation, so the agreement proofs stay automatic. `#print axioms allKnown_agree` shows only `propext` and `Quot.sound`.
- **Not evaluated:** recursive calls of the function being captured, callees with a subtype result, preconditions or function parameters, and calls inside proofs.
- **Where:** the code is in `Capture/Meta.lean` (`foldCall?`, `foldCalls`, `wfFoldCalls`), and `Capture/Elab.lean` adds it to the proof steps.

**Status:** the full `lake build` passes, including all existing tests (none of their pinned counts changed) and the new file; `lake build wfbench` also passes, and there is no `sorry`. The new tests cover mixed known and unknown calls, nested calls, a known call in an `if` test, known calls inside a recursive function and inside a global function's body, `Bool`/`Int`/pair/list results, and runtime comparisons. I updated `README.md`, `GRAMMAR.md` and the header comments, and added two entries to the Properties table. All work is committed.

**Limitations:**
- **Same-body clash (existed before this change):** if one program contains both a global function and an `@[inlinable]` function with the same body and signature (e.g. `sumTo a + sumToI a`), `wf_agree` can mix the two up and fail. I worked around it in the tests by using a different inlinable function (`fact`); the tactic itself is unchanged.
- **Constant grouping:** known values are not regrouped across `+`, so `a + 9 + 10` is not simplified to `a + 19`.
- **Kernel speed:** evaluation happens at capture time with no cost limit, so a known call that is very slow to compute (e.g. a large Ackermann value) will make the capture slow.

# Summary of changes for run 69845e56-0d4c-4643-8303-6b7b9aa8907d
`PCL` now has a well-founded `while` loop, and `#lean_wf_func_to_term` captures Lean functions that use one. Lean's own `while` in `do` notation still can't be captured, so loops have to be written with the new `wf_while` notation (or `WFLang.whileWF`). The full `lake build` passes, including all the existing tests and `wfbench`, and there is no `sorry`. `#print axioms` on the new theorems I sampled shows only `propext`, `Classical.choice` and `Quot.sound`.

**The loop in the language (`PCL/Lang.lean`)**
- New statement `Expr.whileLoop`: `let v := while c do x := body from init in k`. The loop state `x` is one value, a tuple if there are several loop variables.
- Like `fix`, it carries a relation on the states with its well-foundedness proof, plus an invariant. The body's postcondition is "the new state satisfies the invariant and is below the old one", so each iteration provably goes down.
- The rest of the program (`k`) knows that the result satisfies the invariant and that the test is false.
- The evaluator runs the loop with `WellFounded.fix`, so it stays total: no fuel, no `Option`.
- The loop test only has to be in normal form and not a literal; unlike an `if` test it may be a negation (new check `isLoopCond`). The body can't call the enclosing recursive function or jump to a join point.
- Proved: the loop equation (`whileFn_eq`), that it has only one solution (`whileFn_unique`), and that the result satisfies the invariant and exit condition (`whileFn_spec`).
- In `PCL/Termination.lean`: every loop exits (`while_exits`), and a loop whose test stays true can't be written (`while_nonterminating_unbuildable`).
- `PCL/Size.lean` has a new count `whiles`.

**Writing loops in Lean (`Core/While.lean`)**
- Lean's `while` is built on a `partial` function, with no termination proof, and proofs can't look inside it. So I added a well-founded replacement:
  - `whileWF R wf inv c body step init hinit`: a relation, an invariant and a proof that each iteration keeps the invariant and goes down.
  - `whileMeasure`, for a `Nat` measure, with the notation `wf_while (x, y) := init while c do body termination_by μ`. `decreasing_by tac` is optional; otherwise the decrease is tried with `omega`.
- Proved there: the loop equation, uniqueness, partial correctness, a Hoare-style induction rule, and `whileWF_eq_loopVal`, which says a loop's value doesn't depend on its termination argument.

**Capture (`Capture/`)**
- Each `wf_while` / `whileWF` loop becomes one `whileLoop` node, reusing the Lean relation, invariant and proofs.
- `wf_agree` proves agreement by rewriting both sides to the same loop value.
- **Limitation:** the loop's test and body must be call-free (the initial state may contain calls). A loop with a call in its body is rejected with a clear error.

**Tests (`Tests/WhileFunctions.lean`, `Tests/While.lean`)**
- 12 functions are captured, each with an agreement theorem proved by `wf_agree`:
  - `isqrt`, `isqrtNewton`, `gcdLoop`, `sumDown`, `mc91While`, `diagonalWhile`, `collatzSteps`;
  - `roundSum` (a loop after a recursive call), `evenDown` (with an invariant), `twoLoops`;
  - `isqrtSum` (a loop inside a global function) and `evenSqrt` (the loop's initial state calls a global function).
- A hand-written program, `divOut`, has its specification in its type (for `d > 1` and `n > 0` the result is positive and not divisible by `d`). `divOut_spec` gets it from the loop's invariant and exit condition.
- The number of `while` and `fix` nodes per program is pinned, and runtime results are checked.
- Your uploaded `diagonalWhile`, `mc91While` and Newton `isqrt` are rewritten with explicit measures. They match the originals on sample inputs only; that's not a proof, because the originals use Lean's `while`.
- Two rejections are pinned: a call inside a loop body, and Lean's own `while` (`Tco.mc91While`).
- I did not rewrite `ackWhile` or `ackNoDataStructure`: they would need a termination measure on the stack.

`README.md`, `GRAMMAR.md` (a new section on `while`) and `GAPS.md` are updated.

# Summary of changes for run 7b1b1f57-889e-4feb-9509-6ecefccf7783
Mathlib was already installed: `lakefile.toml` requires it at tag `v4.28.0`, the same version as the Lean toolchain, and its compiled files were present. Before this run it was only used in two places (`Relation.ReflTransGen` and the `casesm` tactic). I refactored the parts where Mathlib replaces hand-written code. The full `lake build` passes, including every test, and so does `lake build wfbench`. There is no `sorry` in the project, and no statement of any user-facing theorem changed.

**Changes**
- **Well-founded relations (`Core/Types.lean`)**
  - I added one general lemma, `fibreRel_wf`: a relation that keeps some values `f x` fixed and relates the rest `g x` by `r (f x)` is well-founded if every `r k` is.
  - It is proved with Mathlib's `WellFounded.psigma_lex`, `InvImage.wf` and `Subrelation.wf` (a lexicographic order with the empty relation on the fixed part), instead of a hand-written induction.
  - `fixedRel_wf` and `fixedAtRel_wf` are now one-line instances of it. `preRel_wf` uses it on the environments that satisfy the precondition.
  - The definitions and signatures are unchanged, so the capture elaborator that builds these terms needed no changes.
- **Empty relation (`PCL/Lang.lean`, `Capture/Elab.lean`)**: I removed the project's own `emptyRel` / `emptyRel_wf`. Non-recursive global functions now use the library's `emptyRelation` / `emptyWf.wf`.
- **Iteration (`Tests/SourceProofs.lean`)**
  - I added `iter_eq_iterate` and `hyperLoop_eq_iterate`, which show that the uploaded helpers `iter` and `hyperLoop` are Mathlib's `Function.iterate` (`f^[n]`).
  - `hyperLoop_step` and `mc91Loop_eq` are now proved with Mathlib's iterate lemmas. `mc91Loop_eq` no longer needs `grind`.
  - The uploaded function definitions themselves are untouched, and the file header records the change.
- **Documentation**: `README.md` has a new "Use of Mathlib" section, and `GRAMMAR.md` and the docstrings now name `emptyRelation`.

**Considered but not changed**
- **Environments on Mathlib's `List.TProd`**: I tried this, but because `List.TProd` is defined with `List.foldr`, Lean can no longer work out the context from a pair `(v, env)`. That breaks the elaboration of the captured programs, so environments stay a right-nested tuple `Env`.
- **`hoRel_wf`** (recursion through a function argument): its relation is neither a lexicographic nor an inverse-image order, so it keeps its own proof.

The docstring of `Globals` in `PCL/Lang.lean` now names `emptyRelation`. I did not update the matching entry in the Properties table, so its code snippet may still show the old wording; the claim itself is unaffected.

# Summary of changes for run 212c9355-bb93-4d38-9b3a-d56ec45ff3fd
Both parts of the request are done. The full `lake build` passes, including the whole test suite, and so does `lake build wfbench`. There is no `sorry` in the project. The agreement theorems for the new tests use only the standard axioms (`propext`, `Quot.sound`).

**1. Optimised ("B-normal") form, enforced by the grammar**
- `Core/Normal.lean` defines `PExpr.isNF` and `PExpr.isCond`. An expression fails `isNF` if it still has any of these:
  - an operator applied only to literals (a constant that could be folded);
  - an algebraic identity (`x + 0`, `x * 1`, `x * 0`, `x ^ 1`, `b && true`, `xor b false`, `l ++ []`, …, and the same on `Int`);
  - `!!b`, `- - i` or `(a, b).1`;
  - an `if` on a literal or a negation, an `if` between two equal literals, or `if c then true else false`.
- Every `PCL.Expr` constructor that holds a call-free expression now also holds a proof that it is in normal form, checked by `decide` and erased at runtime. Every `if` test must also be a condition. So a program that could still be simplified does not type-check.
- The capture simplifies while it translates (`Capture/Optimize.lean`: constant folding, identities, dead branches, swapping negated tests), so what it produces always satisfies these checks. The agreement proofs are about the simplified programs.
- `Tests/Normal.lean` has three functions full of simplifiable subterms (`optEx`, `listEx`, `boolEx`). Their captures agree with the Lean functions, and their sizes are pinned (9, 1 and 1 nodes). The file also checks `isNF` on examples and shows that hand-written unsimplified programs are rejected.

**2. `@[inlinable]` and the global context**
- A program (`PTerm`) is now a global context plus a main statement. The global context (`Globals`) is an ordered list of closed well-founded functions, each of which may call the ones before it. `Expr` takes the globals' signatures as a parameter, and the new statement `gCall` calls a global function.
- `#lean_wf_func_to_term` inlines functions marked `@[inlinable]`. A recursive one becomes a local `fix` at each call site.
- Any other called user function is captured once, as an entry of the global context, and each call becomes a `gCall`.
- Exceptions: functions with function parameters, members of a mutual group, and functions calling themselves inside a function argument are still captured at the call site.
- A caller only knows a global function's postcondition, not its definition. So if a termination proof needs a helper's value, the helper must be `@[inlinable]`. `logHalfG` in `Tests/Globals.lean` shows this: with its helper not marked, the capture reports a termination error.
- Soundness (`fixFn_eq`, `fixFn_unique`, `PTerm.run_post`) and the termination theorems were re-proved for the new grammar.
- `Tests/Globals.lean` covers 7 functions: global vs inlined callees, a global calling a global, a global with a subtype postcondition, an `@[inlinable]` helper needed for termination, and the uploaded `gcd` used as a global. All agree with their Lean definitions. The number of globals, global calls, local `fix` nodes and sizes are pinned; for example, sharing `sumTo` as a global gives 11 nodes against 19 when it is inlined.
- The existing tests all still build. Callees in them that aren't marked `@[inlinable]` are now globals; for example, `Tco.mc91TR` calls the global `mc91Loop`.

**Documentation:** `README.md` (grammar, global context, `@[inlinable]`, file layout), `GRAMMAR.md` (new sections on the normal form and the global context), and the header comments of `PCL/Lang.lean`, `Capture/Meta.lean` and `Capture/Elab.lean` are updated. The Properties table has new entries for the normal form, the global context and programs, and the new agreement results, and outdated entries were refreshed. All work is committed.

# Summary of changes for run e0d7981d-2640-45c3-a9ec-504fc1733e02
Join points were worth adding, so I added them. A separate `Atom` layer was not, so I left it out. The full reasoning is in the new `GRAMMAR.md`. `lake build` passes (the test suite is part of it), `lake build wfbench` passes, and there is no new `sorry` or axiom. `#print axioms` on the new agreement theorems and on `fixFn_unique` / `fix_body_reaches_base` shows only `propext` and `Quot.sound`.

**Why join points.** A non-tail `if` with a call, like `(if c then f a else f b) + rest`, used to be handled by copying `rest` into both branches, so `k` such `if`s in a row made `2^k` copies. Now the capture writes:
`join j (v) := rest in if c then (…; jump j a) else (…; jump j b)`

- With join points, 2, 3 and 4 `if`s in a row (`seq2`/`seq3`/`seq4`) give 16, 21 and 26 nodes.
- With copying, `seq2`/`seq3` give 15 and 27. `seq4` did not finish elaborating within 4,000,000 heartbeats when I tried it; that run is not in the build.
- When `rest` is tiny, copying is smaller: `nested` has 17 nodes with join points and 13 with copies.

**Grammar changes** (`PCL/Lang.lean`)
- `Expr` has two new statements, `join` and `jump`, and a new index `js : JScope Γ t` listing the join points in scope.
- A join point has a precondition on its parameter (each jump proves it) and keeps the postcondition of the place where it is defined.
- It is not a function: not recursive, only jumped to in tail position, and not visible inside `fix` bodies.
- The evaluator is still total structural recursion with no fuel: `join` passes a closure of its body, and `jump` calls it.

**One design detail.** My first version tracked join points as a list that was re-mapped at every new variable. The build passed, but the agreement proofs timed out because `simp` could not reduce jumps through the re-mapping. `JScope` instead makes "one more variable in scope" its own constructor. That step is then free at runtime, and the lookup lemmas are definitional equalities that `simp` applies.

**Re-proved for the new grammar:** `fixFn_eq`, `fixFn_unique`, `PTerm.ofFix_run`, `Term.ofFix_eval(_post)`, `fix_body_reaches_base` (it now follows a `jump` into the join point's body), `fix_body_has_base_case` and `loop_unbuildable`. All existing agreement theorems and runtime checks build unchanged.

**Capture** (`Capture/Elab.lean`)
- Every non-tail `if`/`match` containing a call now uses a join point.
- It still copies when a call in scope returns a subtype, because the rest of the computation may need that result's property in its termination proofs.
- `set_option wfLang.joinPoints false` brings back copying everywhere.

**Tests:** new `Tests/Joins.lean`. It has agreement theorems for `alt`, `seq3`, `seq4`, `nested`, `viaMatch` and `mixed` (a call to `gcd` in one branch), plus `seq3` captured with copying. Join-point counts and node counts, with and without join points, are pinned by `#guard_msgs`, and there are runtime checks against the Lean functions.

**Why no `Atom` layer.** Restricting operators to atoms matters when evaluation order, effects or a machine model matter. Here `PExpr` is pure and total, and the only effect (calls) is already pulled out into `fixSelfCall`/`fnCall`. The one real benefit would be sharing: currently a Lean `let` with a call-free value is substituted, so a value used twice is computed twice. A pure `let v := p in k` statement would fix that more cheaply. `GRAMMAR.md` lists it as the next candidate, with three other options I did not implement.

README, GAPS.md and the Properties table (`Expr`, the soundness and base-case theorems, and a new join-point entry) are updated, and the work is committed.

# Summary of changes for run 5ff14f2e-5c6e-479b-9737-e934b0a09445
`#lean_wf_func_to_term` now captures every item in GAPS.md except calls under a `fun` inside library code like `List.map` (details below). The language is stricter too: as you asked, local recursive functions and loops now sit only in tail position. `lake build` passes and the tests are part of it. There is no `sorry` or new axiom. `#print axioms` on a sample of the agreement theorems (`hyperWhile_term_agree`, `boom_agree`, `gcdSum_agree`, `isEven_agree`) shows only `propext`, `Quot.sound` and `Classical.choice`.

**The stricter A-normal form** (`RequestProject/WFLang/PCL/Lang.lean`)
- The grammar now has five statements: `ret`, `ite`, `fixSelfCall`, `fnCall` and `fix`.
- `ite` (case) and `fix` may only appear in tail position. `fix` is now a `letrec f := fix … in rest`, and its scope is the rest of the computation. Loops and folds are `fix` nodes, so they are in tail position too.
- Local functions in scope are tracked in the type of an expression. A call to one is the new `let v := f args in k` (`fnCall`), which binds the result and its postcondition.
- A recursive function called in non-tail position is captured as `fix g := … in let v := g args in k`. A non-tail `if`/`match` containing a call still gets the rest of the computation copied into both branches.
- The evaluator is still total, with no fuel and no runtime checks. The soundness theorems (`fixFn_eq`, `fixFn_unique`) and the termination theorems (`fix_body_reaches_base`, `loop_unbuildable`) are restated for this grammar and proved again.
- To make the agreement proofs work with local functions, I added one simplification lemma for calls to the innermost local function.

**What is now captured**, each with an agreement theorem proved by `wf_agree`:
- **Control flow:** calls in non-tail `if` branches and on the right of `&&`/`||`, `match` on `Bool`, literal patterns, and `match h : e with`.
- **Operators:** all the listed ones.
- **Other types:** `Int`, pairs, lists, and subtype results (the postcondition is carried by `fix`).
- **Loops:** bounded `for` loops and `Nat.fold`.
- **Function parameters:** specialised to the function passed at each call site. This includes recursion through a function argument, e.g. `Tco.hyperWhile`, `Tco.hyperTCO` and `Tco.ack2`.
- **Mutual recursion:** one `fix` with a tag argument, reusing Lean's relation.
- **Proof preconditions:** `Tco.boom` is captured as a program that carries its precondition.

**Still rejected**
- `underLambda`, a call under `fun` inside `List.map`. Its rejection message is checked by the build.
- `while` loops, which Lean builds without a termination proof.
- Mutually recursive functions whose parameter or result types differ.
- A few restrictions on recursion through a function argument.

GAPS.md §6 lists these, with what each would need.

**Documentation:** README.md now describes the new grammar, what the capture supports, and the updated file layout. GAPS.md has a note on the stricter tail-position rule. The Properties table has updated signatures for the language and soundness theorems, plus new proved entries for the uploaded functions that are now captured directly, the GAPS.md examples, and mutual recursion. All work is committed.

# Summary of changes for run e2e72c9a-f076-4733-89dd-6aeab6e9131c
To answer this I ran about 25 well-founded, structural and plain Lean functions through `#lean_wf_func_to_term`, rather than guessing from the code. They're all in `RequestProject/WFLang/Tests/Gaps.lean`, and each one's current result is pinned with `#guard_msgs`, so the build fails if support changes. `GAPS.md` has the full classification and a fix plan for each gap. Three of the failures were bugs, which I fixed; the rest are listed below.

**Bugs found and fixed.** Each now has a `wf_agree` agreement theorem and runtime checks. The full project builds with no `sorry`, and all existing tests still pass.
- **Fixed parameter that isn't the first one** (e.g. `def f (n k : Nat)` where `k` never changes): the capture failed with a spurious "failed to prove termination". Lean 4.28 moves such parameters in front of the recursion even when they aren't a prefix, but the capture assumed they were the first ones. It now works out which parameters change. There's a new relation `fixedAtRel` with a proof that it's well-founded (`fixedAtRel_wf`, no axioms).
- **Non-recursive function with a recursive `where go` helper:** the capture worked, but `wf_agree` failed because it treated the function itself as recursive.
- **`if h : … else have … := (proof using h); f …`:** this was rejected; the `have` is now inlined first, so `h` is no longer in the way.

**Not supported, but the grammar already allows them (only the capture needs work):**
- A call inside a branch of an `if` that isn't in tail position, e.g. `1 + (if c then f a else f b)`.
- A call on the right of `&&` or `||` that isn't in tail position.
- `match` on a `Bool`.
- Literal patterns like `| 5 =>`.
- `match h : e with`.

For the last three I printed how Lean unfolds the `match` to confirm the fix plan.

**Missing operators:**
- **Translation only, no grammar change:** `Nat.pred`, `!=`/`bne`, `xor` on `Bool`, `min`/`max`, and `∣` (divides) in conditions.
- **Need new operators in the grammar:** `^`, bit shifts and bitwise ops, and library functions such as `Nat.gcd`. Alternatively, recursive library functions could be captured the same way user callees already are.

**Need a grammar extension:**
- **Other types:** `Int`, pairs (e.g. `Nat × Nat` results), `List`, and subtype results. The subtype case is the substantial one: when a termination proof uses a property of a recursive call's result, `fix` needs to carry a postcondition.
- **Higher-order code:** calls under a `fun`, bounded `for i in [a:b]` loops and `Nat.fold` could become a nested recursive definition when the loop body is known. The uploaded `iter`, `hyperLoop` and `ack2` could be handled by specialising them to the function passed at each call site.
- **Mutual recursion:** could be encoded as a single recursive definition with a tag argument, using the relation Lean already builds.
- **Proof preconditions** (like the uploaded `boom`): would need a program that carries a precondition.

**Can't be supported:** `while` loops, `partial def` and `partial_fixpoint`. Lean defines these with no termination proof, so there's nothing to reuse unless they're first rewritten as well-founded recursion, as was done for `hyperWhile`.

`README.md` now points to `GAPS.md` and the new test file.

# Summary of changes for run 535c967c-9505-4806-8c4b-938f73da789c
There is no `Tests/Functions.md` in the project, so I annotated `RequestProject/WFLang/Tests/Functions.lean`, which I took to be the file you meant. Every definition in it now has a `-- Recursion:` comment, and the file header has a new section explaining these comments. The file `Tests/MoreFunctions.lean` also exists; I didn't touch it.

I didn't classify the functions by reading their syntax. For each one I checked what Lean actually recorded when it compiled the definition: whether it went through well-founded recursion (`WellFounded.fix`) or structural recursion (`Nat.brecOn`), and, for structural recursion, which argument it recurses on.

**Well-founded:**
- `gcd`: measure `n` (1 of 2 args).
- `digitSum`: measure `n`, inferred by Lean since there's no `termination_by`.
- `isPow2`: measure `n`.
- `sumTo`: measure `i` (1 of 2 args).
- `Tco.ack`: lexicographic `(m, n)` (both args).
- `diagonal`: lexicographic `(m + n, m)` (both args).
- `diagonal_tr`: lexicographic `(m + n, m)` (2 of 3 args; `acc` isn't in the measure).
- `hyper`: lexicographic `(n, b)` (2 of 3 args).
- `mc91Loop`: `2 * (111 - n) + 21 * c` (both args).
- `boom`: measure `n` (1 of 2 args). The decrease proof only goes through because the `Safe n` hypothesis makes it vacuous.

**Structural:** Lean's structural recursion is always on exactly one argument.
- `ackInner`: on the `Nat` argument (`f` is fixed).
- `ack2`: on `m`.
- `hyperLoop`: on `b`.
- `hyperTCO`: on `n`.
- `hyperWhile`: on `n`, with the recursive call inside a `for` loop.
- `iter`: on the counter `c`.

**Non-recursive:**
- **Plain functions, no loop:** `ack999`, `pair`, `unpairLeft`, `unpairRight`, `hyperBase`, `mc91`, `mc91TR`, `Safe`.
- **`while` loops:** `ackWhile`, `isqrt`, `ackNoDataStructure`, `diagonalWhile`, `mc91While`. These use Lean's built-in loop combinator, which isn't checked for termination, so they are neither well-founded nor structural.

Where it's useful, the comments also say whether a function is tail recursive, has nested recursive calls, or is higher-order. I added comments only; no code changed. The project still builds successfully, and the change is committed.

# Summary of changes for run cddd1764-975b-48cb-a96b-b1cf1ba51385
There are two separate stack overflows, and only the second is the evaluator's fault. The full write-up with measurements is in `STACK_OVERFLOW.md`.

**1. The benchmark crashed before `main` ran, for any input, including native Lean (fixed).**
- **Cause:** `Tests/Functions.lean` has the uploaded line `def ack999 := ack 999 1 -- DONT TRY TO EVALUATE`. Lean computes a compiled `def` with no arguments once, when the module is loaded. So every executable that imports this file (`wfbench` does) computed native `ack 999 1` at startup. That overflowed an 8 MB stack, or segfaulted after about 25 s with an unlimited stack.
- **Fix:** I made `ack999` `noncomputable`. This doesn't change its meaning: `ack999_term` and `ack999_agree` still build. `wfbench native 1` now finishes in 1 ms.

**2. The PCL evaluator itself: stack depth grows with every recursive call, including tail calls.**
- **Which cases:** any run where the recursion goes deep, whether or not the calls are tail calls.
  - **Fine:** `gcd`, `isPow2`, `digitSum`, `mc91Loop`, small `ack` / `hyper`.
  - **Overflow:** `sumTo n` for large `n`, `diagonal_tr m 0 0` (about m²/2 nested calls), `diagonal`, and deep `ack` / `hyper`.
- **Measured thresholds** (single runs, not a Lean proof):
  - Compiled, 8 MB stack: works at about 45k nested calls, overflows at about 80k. That's roughly 100–130 bytes per call.
  - Compiled, 64 MB stack: works at about 320k, overflows at about 500k.
  - `#eval`: overflows after only about 2–3k calls (`sumTo 2000` works, `sumTo 2500` doesn't). It aborts the whole `lean` process with an uncaught "deep recursion" exception instead of reporting an error.
  - Native Lean runs the same `diagonal_tr` with 4.5M calls in 5 ms, because it compiles it to a loop.
- **Not non-termination:** with `lean --tstack=1000000`, `sumTo 20000` returns the correct result. The termination and soundness theorems are unaffected.
- **Why:** in `Expr.eval`, the recursive-call case is `k.eval (h (args.eval e) (dec e g), e) g h`. The call `h …` is an argument to the rest of the program `k`, so it is never the last thing the evaluator does, even when the source function is tail-recursive. The capture turns `sumTo (i-1) (acc+i)` into `fixSelfCall args dec (ret (var here))`, i.e. "call, then return the result" (I checked this with `#print`). In the generated C, each call nests `Expr.eval` → closure call → `WellFounded.fixC` → `Expr.eval` on the body, and then has to come back to run `k`. The other cases (`ret`, `ite`, and the continuation of `fix`) already compile to loops. `WellFounded.fix` itself isn't the problem: Lean compiles it to a plain recursive function.

**Possible fixes (not implemented):**
- A larger stack only moves the limit.
- A special case for tail calls wouldn't reliably give constant stack.
- The real fix is an evaluator that keeps its own stack of pending work on the heap. It would need a new termination measure and a new proof that it agrees with `Expr.eval`, which is a substantial change to `Lang.lean`.

`lake build` and `lake build wfbench` both succeed with no `sorry`, and the changes are committed.

# Summary of changes for run 3089c052-44b7-4ff3-b615-6a2da11cb642
I renamed the recursive-call constructor of the PCL language from `Expr.call` to `Expr.fixSelfCall`. `lake build` and `lake build wfbench` both succeed, and there is no `sorry` in the project.

**Changes**
- **`PCL/Lang.lean`:** the constructor is now `| fixSelfCall args dec k`. Its type and meaning are unchanged: `let v := self args in k`, carrying a proof `dec` that the arguments go down. I updated the evaluator case and the grammar in the header comment. The simp lemma for this case is renamed from `eval_call` to `eval_fixSelfCall`.
- **`PCL/Termination.lean`:** updated the pattern in `firstCall`, the program in `loop_unbuildable`, and the comments.
- **`Capture/Elab.lean`:** `#lean_wf_func_to_term` now produces `WFLang.PCL.Expr.fixSelfCall …` nodes.
- **`WFLang.lean` and `README.md`:** updated the references to the constructor.
- **Properties table:** updated the definition of `Expr` and the two entries that mention the constructor.

Every captured program and every agreement theorem (e.g. `gcd_agree`) still checks unchanged.

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