# When the PCL evaluator overflows the stack, and why

There are two separate problems. Only the second one is caused by the evaluator.

## 1. `wfbench` crashed before it evaluated anything (fixed)

`lake exe wfbench native 1` and `wfbench pcl 1` both crashed: "Stack overflow detected" with an
8 MB stack, or a segfault after about 25 s with an unlimited stack. That happened for every
input, including the native Lean function.

**Cause:** `Tests/Functions.lean` contains the uploaded line

```lean
def ack999 := ack 999 1 -- XXX: DONT TRY TO EVALUATE!!! only build Term
```

The compiler treats a `def` with no arguments as a global constant and computes it once, when
the module is initialised. The generated C (`_init_lp_RequestProject_Tco_ack999___closed__0`)
calls `Tco.ack 999 1` during initialisation. So every executable that imports
`Tests/Functions.lean` (and `Bench.lean` does, through `Tests/Basic.lean`) runs native
Ackermann(999, 1) before `main` starts. The PCL evaluator is never involved.

**Fix:** `ack999` is now `noncomputable def`. This changes nothing logically:
`ack999_term` and `ack999_agree` still build. After this change, `wfbench native 1` finishes
in about 1 ms.

## 2. Loops and tail calls: fixed by the jump machine

**Before.** The evaluator `Expr.eval` (`PCL/Lang/Eval.lean`) used stack for every loop iteration
and every recursive call, tail calls included:

* a recursive call `fixSelfCall args dec k` is evaluated as `k.eval (h args …)`: the call is an
  argument of the continuation, so it is never in tail position, even when `k` is just `ret v`;
* a loop (`joinrec`) is run by `WellFounded.fix`, and each back edge `jump L x` calls the closure
  of the loop body stored in the join-point environment, so each iteration nests a few more
  frames.

So `#eval` aborted the whole `lean` process with `deep recursion was detected at 'interpreter'`
at about 2–3k nested calls or loop iterations (`sumTo 2500 0`, `diagonalWhile m n` for
`n ≥ 40`–`60`), and compiled code (`wfbench`, 8 MB stack) overflowed on `diagonal_tr 3000 0 0`
(4.5 M nested calls; an earlier run had overflowed at about 80k).  The test in
`Tests/While.lean` was restricted to `n < 40` for this reason.

**Now.** Compiled code (and `#eval`) runs a different evaluator, proved equal to `Expr.eval`:

* `PCL/Lang/Machine.lean`: the **jump machine** `Expr.evalS`.  It keeps no join-point closures:
  a statement returns a `Step`, which is a value, a pending jump `jmp i v` to a join point in
  scope, or a pending tail call `call y` (the statement `let v := self y in ret v`, recognised
  by `Expr.retHere?`).  `join` handles the jumps to its join point by running the body; `joinrec`
  runs its loop with `runLoop`, a tail-recursive function that the compiler turns into a
  `goto` loop.  Other jumps and tail calls are passed outwards.
* `PCL/Lang/Fix.lean`: `fixS` runs a global function with the machine; a pending tail call is a
  tail call of `fixS` itself, which is also compiled to a `goto` (checked in the generated C,
  `.lake/build/ir/RequestProject/WFLang/PCL/Lang/Fix.c`).  Non-tail recursive calls go through
  the handler closure as before.
* `Expr.eval_val_eq_evalS` proves `(x.eval ge e g h je).1 = (x.evalS ge e g h).run h je` for
  every statement, and `fixS` carries the proof that its value is the value of `fixFn`.  The
  `@[csimp]` lemmas `Expr.eval_eq_evalImpl` and `fixFn_eq_fixFnImpl` then replace `Expr.eval`
  and `fixFn` by the machine in compiled code.  No `@[implemented_by]` and no new axiom: the
  replacement is checked by Lean, so the agreement theorems (`gcd_agree`, …) are about exactly
  the code that runs.

The stack depth is now the nesting depth of the syntax plus the depth of the **non-tail**
recursive calls; loop iterations and tail calls use none.  Non-tail recursion (`ack`, `hyper`,
`diagonal`) still uses one stack segment per nested call, which is inherent in those programs.

Measured on this machine (single runs of the compiled `wfbench` and of `#eval` under
`lake env lean`; timings, not proofs):

| run | before | now |
|---|---|---|
| `#eval` `diagonalWhile 0 n` (loop, `n(n+1)/2` iterations) | aborts for `n` ≈ 60 | `n = 1000` (500 500 iterations) in 3.0 s; `n = 3000` (4.5 M) works |
| `#eval` `sumTo n 0` (tail calls) | aborts at `n = 2500` | `n = 100 000` in 0.24 s |
| `#eval` `diagonal_tr 1000 0 0` (tail calls, 501 500) | aborts | 1.5 s (native Lean in the interpreter: 0.1 s) |
| `wfbench pcl m` = `diagonal_tr m 0 0`, compiled, 8 MB stack | `m = 1000` in 408 ms; overflows at `m = 3000` | `m = 1000` in 90 ms; `m = 3000` (4.5 M calls) in 0.78 s; `m = 6000` (18 M) in 3.2 s (native: 18 ms) |

The test suite now checks `diagonalWhile m n` for all `n < 60`, `m < 8`, and `diagonalWhile 0
400` (80 200 iterations) in `Tests/While.lean`, and `sumTo 50000 0` and `diagonal_tr 300 0 0`
in `Tests/BasicChecks.lean`.  `Tests/EvalChecks.lean` states these as theorems:
`WhilePCL.diagonalWhile_term_eq` proves the `diagonalWhile` check for **all** `m n` (no sampling),
and `native_decide` theorems record runs of the compiled machine (`diagonalWhile 0 1000`,
`sumTo 100000 0`, `diagonal_tr 1000 0 0`).  Stack usage and timings themselves are not
statements of Lean's logic and are not formalized.

**What is left.** The machine is still an interpreter over the syntax: each iteration of
`diagonalWhile` evaluates about 30 nodes of call-free expressions, so it is about 20 times
slower than the native Lean function under `#eval`, and far slower than native compiled code.
Making it faster would mean compiling programs (for example into Lean closures once, before
running them), which is not done.
