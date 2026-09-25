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

* Types `nat`, `int`, `bool`, pairs `prod s t` and lists `list t`; typed de Bruijn variables.
* Call-free expressions (`PExpr`, `Core/PExpr.lean`): `+ - * / % ^`, shifts and bitwise
  operators, `Nat.gcd`/`Nat.lcm`/`Nat.log2`, `<`, `≤`, `bool_eq` (`==` at every type), `&&`,
  `||`, `!`, `xor`, pairing and projections, `[]`, `::`, `++`, `head`, `tail`, `isNil`,
  `length`, casts between `Nat` and `Int`.
* Statements (`Expr`), in **strict A-normal form** and **optimised normal form**:

  ```
  | ret p hp                               -- return a call-free value
  | ite c hc a b                           -- if-then-else, tail position only
  | fixSelfCall args ha dec hpre k         -- let v := self args in k   (recursive call)
  | fnCall f args ha hpre k                -- let v := f args in k      (local function f)
  | gCall g args ha hpre k                 -- let v := g args in k      (global function g)
  | fix params r R wf pre post body rest   -- letrec f := fix … in rest, tail position only
  | join s P body m                        -- join j (v : s) := body in m, tail position only
  | jump j p hp hpre hpost                 -- jump j p                  (tail position)
  ```

  `hp`, `ha` are proofs that the call-free expressions are in optimised normal form
  (`PExpr.isNF`, `Core/Normal.lean`), `hc` that the test is a condition (`PExpr.isCond`): no
  constant left to fold, no algebraic identity left to apply (`x + 0`, `x * 1`, `b && true`,
  `l ++ []`, …), no `!!b`, `(a, b).1`, no `if` on a literal or a negation, no
  `if c then true else false`. A program that could still be simplified is ill-typed; the
  capture simplifies while it translates (`Capture/Optimize.lean`).

  The compound statements, `ite` (case), `fix` (local recursive functions, which also
  encode loops and folds) and `join`, occur only in tail position; the result of every call is
  bound to a fresh variable. Local functions and join points in scope are indices of `Expr`
  (typed de Bruijn indices `FnVar` and `JVar`; the join-point scope `JScope` has weakening as a
  constructor, so moving under a binder costs nothing). A join point names the rest of the
  computation after a non-tail `if`/`match`; it is not a function (not recursive, only jumped to
  in tail position, invisible in `fix` bodies). See `GRAMMAR.md` for the design discussion.
* Programs (`PTerm`, `Term`): a **global context** (`Globals`: closed well-founded recursive
  functions, each of which may call the earlier ones) and a main statement. `Expr` is
  parameterised by the signatures `GL` of the globals, and `gCall` calls one of them.
* A `fix` carries its relation `R`, the proof `wf : WellFounded R`, a precondition `pre` and a
  postcondition `post`. Every recursive call carries its own proof `dec` that the arguments are
  `R`-smaller. That proof may use the enclosing `if` tests, the precondition and the
  postconditions of earlier calls, which are recorded in the type of the statement (the path
  condition).
* `Expr.eval` is total: structural recursion on the syntax, and `WellFounded.fix` at `fix` nodes.
  It returns a plain value, with no fuel, no `Option` and no runtime checks.
* Soundness: `fixFn_eq`, meaning a `fix` node satisfies its recursive equation, and `fixFn_unique`,
  meaning it is the only solution. `PTerm.run_post`: every result satisfies the postcondition.
* `PCL/Termination.lean`: every `fix` body reaches a base case (`fix_body_reaches_base`,
  `fix_body_has_base_case`), and a looping program cannot be built (`loop_unbuildable`).

## Capture (`RequestProject/WFLang/Capture/`)

`#lean_wf_func_to_term f` reads `f.eq_def` and the `WellFounded.fix` that Lean built for `f`.
It then writes a `PCL` program that reuses Lean's relation and the decreasing proofs, including the
user's `decreasing_by`. `wf_agree` proves `Term.eval f_term = f` from the uniqueness of the fixpoint.
The capture supports:

* `if` / `match` on `Nat`, `Bool`, pairs and lists, literal patterns, `match h : e with`,
  `cond`, `&&` / `||`;
* calls in any position (a non-tail `if`/`match` containing a call becomes
  `join j (v) := rest in if c then (…; jump j a) else (…; jump j b)`; the rest is copied into
  both branches instead only when a call in scope has a postcondition, or with
  `set_option wfLang.joinPoints false`);
* fixed parameters and structural recursion;
* calls to other functions, according to the attribute `@[inlinable]`:
  * `@[inlinable]` functions are inlined: a non-recursive one is replaced by its body, a
    recursive one becomes a local `fix` node at the call site
    (`fix g := … in let v := g args in …`);
  * any other function is captured once as an entry of the global context of the program, and
    each call becomes `gCall i args` (only its postcondition is known at the call site, so a
    helper whose value a termination proof needs must be `@[inlinable]`);
  * functions with function parameters, members of a mutual group and functions calling
    themselves in a function argument are always captured at the call site;
* subtype results (postconditions) and proof parameters (preconditions);
* mutual recursion (one `fix` with a tag parameter);
* bounded `for` loops and `Nat.fold`, and function parameters specialised to the function
  passed at each call site, including recursion through a function argument
  (`Tco.hyperWhile`, `Tco.hyperTCO`, `Tco.ack2`).

`GAPS.md` lists what is still rejected (e.g. calls under a `fun` in library code such as
`List.map`, and `while` loops, which Lean builds without a termination proof).

## Use of Mathlib

The project depends on Mathlib (`lakefile.toml`, pinned to the `v4.28.0` tag, matching the
Lean toolchain). It is used where it replaces hand-written material:

* **Well-founded relations** (`Core/Types.lean`): `fibreRel_wf` (a relation that keeps some
  fixed values `f x` and relates the remaining data `g x` by `r (f x)`) is derived from
  `WellFounded.psigma_lex`, `InvImage.wf` and `Subrelation.wf` instead of a hand-written
  `Acc` induction. `fixedRel_wf`, `fixedAtRel_wf` and `preRel_wf` (the relations of captured
  functions with fixed parameters or preconditions) are instances of it.
* **Non-recursive global functions** use the library's `emptyRelation` / `emptyWf.wf`
  instead of a project-specific empty relation.
* **Termination** (`PCL/Termination.lean`): the chain of recursive calls reaching a base case
  is stated with `Relation.ReflTransGen`.
* **Iteration** (`Tests/SourceProofs.lean`): the helpers `iter` and `hyperLoop` of the uploaded
  files are identified with `Function.iterate` (`f^[n]`), and the proofs about them
  (`hyperLoop_step`, `mc91Loop_eq`) use Mathlib's iterate lemmas.
* **Tactics**: the generated termination proofs use `casesm`.

Places that were considered but left alone: environments stay a project-specific
right-nested tuple `Env` rather than Mathlib's `List.TProd` (which gives the same type for every concrete
context, but is defined with `List.foldr`, so Lean could no longer infer the context from a
pair `(v, env)`, which breaks the elaboration of the captured programs); `hoRel_wf` (recursion
through a function argument) is not a lexicographic or inverse-image order, so it keeps its own
proof.

## Layout

```
RequestProject/WFLang.lean          imports everything
RequestProject/WFLang/
├── Core/Types.lean                 Ty, Env, Var, Sig, FnType, curryEnv, BinOp, fixedRel, hoRel
├── Core/Loops.lean                 rangeLoop: first-order form of `for` loops and `Nat.fold`
├── Core/PExpr.lean                 call-free expressions PExpr / PExprs
├── Core/Normal.lean                optimised normal form: PExpr.isNF, PExpr.isCond
├── PCL/Lang.lean                   Expr (ret, ite, fixSelfCall, fnCall, gCall, fix, join, jump),
│                                   eval, Globals, PTerm/Term, soundness
├── PCL/Size.lean                   size measures (nodes, joins, fixes, global calls, globals)
├── PCL/Termination.lean            base-case existence, unbuildable loop
├── Capture/Meta.lean               reading a Lean function; @[inlinable]; inlining, globals;
│                                   tactics wf_dec, wf_close
├── Capture/Optimize.lean           simplifying IR (constant folding, identities, dead branches)
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
    ├── GapFunctions.lean           the functions of GAPS.md
    ├── Gaps.lean                   their captures + agreement theorems, and the functions
    │                               still rejected (pinned by #guard_msgs)
    ├── Joins.lean                  non-tail if/match captured with join points; sizes with
    │                               and without join points
    ├── Normal.lean                 optimised normal form: captures of simplifiable functions,
    │                               the isNF checks, unsimplified programs rejected
    └── Globals.lean                global functions vs @[inlinable]; shapes and sizes
GAPS.md                             what is supported, how, and what is left
GRAMMAR.md                          grammar layers: why join points, why no Atom layer
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
