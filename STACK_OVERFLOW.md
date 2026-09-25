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

## 2. The evaluator uses one stack segment per recursive call, including tail calls

**Which programs:** any run in which the chain of recursive calls gets too long. "Too long"
means how many calls deep the recursion goes, not how many calls are made in total. **Tail
calls count too.** These inputs are fine: `gcd` (logarithmic depth), `mc91Loop`, `isPow2`,
`digitSum`, and small `ack` / `hyper`. These overflow: `sumTo i 0` for large `i`,
`diagonal_tr m 0 0` (depth about m²/2), `diagonal`, and `ack` / `hyper` once their recursion
gets deep. Native Lean compiles `sumTo`, `diagonal_tr` and `mc91Loop` to loops, so it has no
such limit for them.

Measured on `diagonal_tr m 0 0`. These are single runs of the compiled `wfbench`, plus `#eval`
under `lake env lean`; they are not a Lean proof:

| setting | works | overflows |
|---|---|---|
| compiled, 8 MB stack (`ulimit -s 8192`) | m = 300 (≈45k nested calls) | m = 400 (≈80k) |
| compiled, 64 MB stack | m = 800 (≈320k) | m = 1000 (≈500k) |
| `#eval` (interpreter, default thread stack) | m = 60 (≈1.8k) | m = 80 (≈3.2k) |
| `#eval` of `Term.eval sumTo_term n 0` | n = 2000 | n = 2500 |
| same, with `lean --tstack=1000000` | n = 20000 | – |
| native `Tco.diagonal_tr`, compiled | m = 3000 (4.5M calls, 5 ms) | – |
| native `Tco.diagonal_tr`, `#eval` | m = 2000 (2M calls) | – |

That works out to about 100–130 bytes of C stack per recursive call in compiled code. In the
interpreter it is far more: it fails at about 2–3k calls. There, the failure is an uncaught
`deep recursion was detected at 'interpreter'` exception, and it aborts the whole `lean`
process rather than reporting an error on the `#eval`. With a larger stack (`--tstack`) the
same programs finish with the correct result. So this is a resource limit, not
non-termination: the termination and soundness theorems are unaffected.

**Why.** Look at the case of `Expr.eval` (in `PCL/Lang.lean`) for a recursive call:

```lean
| .fixSelfCall args dec k, e, g, h => k.eval (h (args.eval e) (dec e g), e) g h
```

The recursive call `h (...)` is an *argument* of the continuation `k.eval`. Its result is
needed before `k` can run, so it is never in tail position, even when the object program is
tail-recursive. The capture writes `sumTo (i-1) (acc+i)` as
`fixSelfCall args dec (ret (var here))`: "call, bind the result to `v`, return `v`". The
evaluator does not see that the continuation just returns `v`. In the generated C
(`.lake/build/ir/RequestProject/WFLang/PCL/Lang.c`), each object-level call is this chain of
C calls:

```
Expr.eval (case fixSelfCall)
  └─ lean_apply_2(h, args, _)                  -- h is a closure, a non-tail call
       └─ fixC…lam_0 → WellFounded.fixC…        -- the compiled WellFounded.fix (csimp → fixC)
            └─ Expr.eval body                   -- evaluates the body for the new arguments
```

Only then does it return and `goto` into `k`. The other cases (`ret`, `ite`, and the
continuation of `fix`) already compile to `goto _start` loops and use no stack. So the stack
depth of the evaluator equals the depth of the object program's call tree, counting tail
calls. That explains the table above: `sumTo n` needs n nested frames, and
`diagonal_tr m 0 0` needs about m²/2.

`WellFounded.fix` itself is not the cause. The compiler replaces it by `WellFounded.fixC`,
which is `F x (fun y _ => fixC hwf F y)`: a plain recursive function with no `Acc` or fuel.
The cost comes from the evaluator having to return into `k` after every call.

## What could remove the limit (not implemented)

* **Larger stack** (no code change): `ulimit -s` for executables, `lean --tstack=…` for `#eval`.
  This only moves the limit.
* **Tail-call case in the evaluator:** when `k` is `ret (var here)`, evaluate the call as the
  last action. That still does not give constant stack, because the recursive step goes through
  the `h` closure and `fixC`, and the C compiler is not required to turn that into a jump.
* **An evaluator with an explicit stack.** Run a small machine over `(expr, env, continuation
  stack)` as a loop, where tail calls push nothing. That gives constant C stack for tail calls
  and heap-allocated frames for real nesting (`ack`). Termination would have to be proved with
  a measure built from `R` and the continuation stack, and it would need a new proof that the
  machine agrees with `Expr.eval`. That is a substantial change to `Lang.lean`.
