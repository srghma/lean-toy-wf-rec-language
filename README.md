This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# PCL — a typed toy language capturing well-founded Lean functions

```lean
def gcd (m n : Nat) : Nat :=
  if n = 0 then m else gcd n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

open WFLang PCL
def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree
```

## The language (`RequestProject/WFLang/PCL/Lang.lean`)

* Types `nat`, `bool`; typed de Bruijn variables; operators `+ - * / %`, `<`, `≤`, `bool_eq`
  (`==` at every type), `&&`, `||`, `!`, and `if-then-else`.
* Well-founded recursion is part of the grammar:
  * `fix params r R wf body args k` is a local recursive function whose relation `R` is proved
    well-founded by `wf`;
  * `fixSelfCall args dec k` is a recursive call carrying its own proof `dec` that the arguments are
    `R`-smaller. The proof may use the enclosing `if` tests, which are recorded in the type of
    the expression (the path condition).
* `Expr.eval` is total: structural recursion on the syntax, and `WellFounded.fix` at `fix` nodes.
  It returns a plain value, with no fuel, no `Option` and no runtime checks.
* Soundness: `fixFn_eq`, meaning a `fix` node satisfies its recursive equation, and `fixFn_unique`,
  meaning it is the only solution.
* `PCL/Termination.lean`: every `fix` body reaches a base case (`fix_body_reaches_base`,
  `fix_body_has_base_case`), and a looping program cannot be built (`loop_unbuildable`).

## Capture (`RequestProject/WFLang/Capture/`)

`#lean_wf_func_to_term f` reads `f.eq_def` and the `WellFounded.fix` that Lean built for `f`.
It then writes a `PCL` program that reuses Lean's relation and the decreasing proofs, including the
user's `decreasing_by`. `wf_agree` proves `Term.eval f_term = f` from the uniqueness of the fixpoint.
The capture supports:

* `if` / `match` on `Nat` / `cond` / `&&` / `||`;
* non-tail and nested calls;
* fixed parameters and structural recursion;
* calls to other functions: non-recursive functions are inlined, and recursive functions become
  nested `fix` nodes.

It rejects the following with an error message:

* mutual recursion;
* higher-order functions;
* `while`/`for` loops, which Lean builds without a termination proof.

## Layout

```
RequestProject/WFLang.lean          imports everything
RequestProject/WFLang/
├── Core/Types.lean                 Ty, Env, Var, Sig, FnType, curryEnv, BinOp, fixedRel
├── Core/PExpr.lean                 call-free expressions PExpr / PExprs
├── PCL/Lang.lean                   Expr (fix, fixSelfCall, ite, ret), eval, Term, soundness
├── PCL/Termination.lean            base-case existence, unbuildable loop
├── Capture/Meta.lean               reading a Lean function; tactics wf_dec, wf_close
├── Capture/Translate.lean          Lean term → PExpr syntax, branch recognition
├── Capture/Elab.lean               #lean_wf_func_to_term, wf_agree
└── Tests/                          the PCL test suite
    ├── Functions.lean              gcd, digitSum, isPow2, sumTo; namespace Tco (all functions
    │                               of the uploaded Tco*.lean files, verbatim)
    ├── Basic.lean                  their captures + agreement theorems
    ├── BasicChecks.lean            runtime checks (#guard_msgs)
    ├── MoreFunctions.lean          fixed parameters, structural recursion, calls, mutual recursion
    ├── More.lean                   their captures + agreement theorems
    ├── MoreChecks.lean             runtime checks, #expect_reject, rejections
    ├── SourceProofs.lean           the theorems of the uploaded files (+ hyperWhile = hyper)
    ├── Sources.lean                every uploaded function: captured or rejected (table),
                                    derived agreement theorems, runtime checks
    └── Gaps.lean                   coverage gaps: well-founded functions still rejected
                                    (pinned by #guard_msgs), see GAPS.md
GAPS.md                             which rejected functions could be supported, and how
Bench.lean                          `lake exe wfbench <native|pcl> <m>`
```

Build with `lake build`. The test suite is part of the default target, so a failing
`#guard_msgs` or agreement proof fails the build.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
