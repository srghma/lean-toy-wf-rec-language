# Project layout

All Lean code is under `RequestProject/WFLang/`; `RequestProject/WFLang.lean` imports every module.

```
RequestProject/WFLang/
├── Common/                 shared by every grammar
│   ├── Types.lean          Ty, Env, Var, Sig, FnType, curryEnv/uncurryEnv (+ curryEnv_eq), BinOp
│   ├── WFBox.lean          WFBox: `termination_by` on a relation stored in a program
│   ├── PExpr.lean          call-free expressions PExpr/PExprs, PExprs.ids (used by PCL, Tail, Meas)
│   ├── Meta.lean           `#lean_wf_func_to_term` / `wf_agree` syntax; reading a Lean function
│   │                       (signatureOf, withEqnRhs, findFix?, callSiteProofs, pullBackRel);
│   │                       tactics wf_dec, wf_close; agreement skeleton (agreeTarget, agreeRec)
│   └── Translate.lean      Lean term → object-language surface syntax (pexpr, pprop, branch?,
│                           directCall, decStx), parametric in the target constructors
├── Wrapper/                grammar 1: one self-recursive body, certificate in a wrapper structure
│   ├── Expr.lean           Expr/Exprs with `call`, reference semantics evalWith, IsFix
│   ├── Guarded.lean        design 1 (guard/value semantics + termination_by)
│   ├── GuardedAcc.lean     design 3 (Acc.rec on Prop-valued Acc)
│   ├── FreeCall.lean       design 2 (call trees + WellFounded.fix)
│   ├── Checked.lean        design 4 (runtime-checked relation, for contrast)
│   ├── Bridge.lean         FreeCall certificate ⇒ Guarded certificate
│   └── Elab.lean           capture + agreement for the four designs
├── PCL/   Lang.lean, Elab.lean     grammar 2: `fix` + proof-carrying `call`
├── Tail/  Lang.lean, Elab.lean     grammar 3: well-founded `loop` (tail recursion only)
├── Meas/  Lang.lean, Elab.lean     grammar 4: `fix` with an in-language measure, checked at runtime
├── Capture.lean            `#lean_wf_func_to_term f` / `wf_agree`: picks the grammar from the type
└── Examples/
    ├── Functions.lean      the captured Lean functions (user's gcd, digitSum, isPow2, sumTo;
    │                       namespace Tco: the functions of the uploaded Tco*.lean files)
    ├── Wrapper.lean        captures + agreement theorems for the four wrapper designs
    ├── WrapperChecks.lean  runtime checks for the wrapper designs
    ├── Langs.lean          captures + agreement theorems for PCL, Tail, Meas
    ├── LangChecks.lean     runtime checks, and the functions that are rejected
    ├── MoreFunctions.lean  functions with fixed parameters, structural recursion, calls of
    │                       other functions (and a mutually recursive pair, rejected)
    ├── More.lean           their captures + agreement theorems (PCL, Tail, Meas, wrappers)
    └── MoreChecks.lean     runtime checks, `#expect_reject`, rejections (while loops, higher
                            order, mutual recursion, calls in a Tail loop body)
```

`Bench.lean` (executable `wfbench`) benchmarks the evaluators of PCL, Tail and Meas.

The C files in `c_output/` are snapshots taken before this reorganisation, so their file names
(`Syntax.c`, `Examples.c`, `TcoExamples.c`, `LangExamples.c`, …) follow the earlier module
names.

Each grammar-specific `Elab.lean` only contains what is specific to its grammar (how a Lean term
becomes a statement / loop body / direct-style expression, and which evaluation lemmas the
agreement proof unfolds); everything else is in `Common/`.

## Alternative designs (`RequestProject/WFLang/Designs/`)

```
Designs/
├── VC.lean        PCL-VC: PCL without per-call proofs; one verification condition `Expr.VC`,
│                  `Certified` programs, erasure from PCL (`erase`, `erase_vc`, `erase_eval`)
├── Ext.lean       PCL-Ext: no termination info in the program; the measure is supplied by the
│                  caller; certified `eval`, checked `runChecked` (errors), `runFuel`
└── Examples.lean  gcd / ack in both designs, wrong measures (errors, non-certifiability),
                   and the silent default value of `Meas` with a wrong measure
```

See `DESIGNS.md` for the comparison and pros/cons.
