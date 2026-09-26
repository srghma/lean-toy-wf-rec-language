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

## The language (`RequestProject/WFLang/PCL/Lang/`)

* Types `nat`, `int`, `bool`, pairs `prod s t` and lists `list t`; typed de Bruijn variables.
* Call-free expressions (`PExpr`, `Core/PExpr.lean`): `+ - * / % ^`, shifts and bitwise
  operators, `Nat.gcd`/`Nat.lcm`/`Nat.log2`, `<`, `≤`, `bool_eq` (`==` at every type), `&&`,
  `||`, `!`, `xor`, pairing and projections, `[]`, `::`, `++`, `head`, `tail`, `isNil`,
  `length`, `List.range`, `List.sum` (on `Nat`), casts between `Nat` and `Int`.
* Statements (`Expr`), in **strict A-normal form** and **optimised normal form**:

  ```
  | ret p hp                               -- return a call-free value
  | ite c hc a b                           -- if-then-else, tail position only
  | fixSelfCall args ha dec hpre k         -- let v := self args in k   (recursive call)
  | gCall g args ha hpre k                 -- let v := g args in k      (global function g)
  | map s u l hl body k                    -- let v := List.map (fun x => body) l in k
  | join s P body m                        -- join j (v : s) := body in m, tail position only
  | joinrec s P R wf body m                -- joinrec j (x : s) [R] := body in m  (a loop)
  | jump j p hp hpre hpost                 -- jump j p                  (tail position)
  ```

  There is no local-function context: a function is either a **global function** (closed,
  captured once, called with `gCall`) or, if it is only a loop, a **recursive join point**
  inside the statement that uses it. `whileLoop` is a derived form (a `join` for the exit and a
  `joinrec` for the loop, `Expr.whileLoop`, with `eval_whileLoop`).

  `hp`, `ha` are proofs that the call-free expressions are in optimised normal form
  (`PExpr.isNF`, `Core/Normal.lean`), `hc` that the test is a condition (`PExpr.isCond`): no
  constant left to fold, no algebraic identity left to apply (`x + 0`, `x * 1`, `b && true`,
  `l ++ []`, …), no `!!b`, `(a, b).1`, no `if` on a literal or a negation, no
  `if c then true else false`. A program that could still be simplified is ill-typed; the
  capture simplifies while it translates (`Capture/Optimize.lean`).

  The compound statements, `ite` (case), `join` and `joinrec`, occur only in tail position;
  the result of every call is bound to a fresh variable. Join points in scope are an index of
  `Expr` (typed de Bruijn indices `JVar`; the join-point scope `JScope` has weakening as a
  constructor, so moving under a binder costs nothing). A join point names the rest of the
  computation after a non-tail `if`/`match` or after a loop; it is only jumped to in tail
  position. See `GRAMMAR.md` for the design discussion.
* Programs (`PTerm`, `Term`): a **global context** (`Globals`: closed well-founded recursive
  functions, each of which may call the earlier ones) and a main statement. `Expr` is
  parameterised by the signatures `GL` of the globals, and `gCall` calls one of them. A
  recursive program is its function as the last global plus a main statement calling it
  (`PTerm.ofFix`, `PTerm.ofFix_run`, `Term.ofFix_eval`).
* A global function carries its relation `R`, the proof `wf : WellFounded R`, a precondition
  `pre` and a postcondition `post`. Every recursive call carries its own proof `dec` that the
  arguments are `R`-smaller. That proof may use the enclosing `if` tests, the precondition and
  the postconditions of earlier calls, which are recorded in the type of the statement (the path
  condition).
* **`map`** (`Expr.map`): `let v := List.map (fun x => body) l in k`. The body is a statement
  over one more variable `x`; it may make calls, recursive calls included, and its path condition
  contains `x ∈ l`, which its decrease proofs may use. The evaluator supplies the membership
  proofs itself (it maps over `l.attach`); the program contains none.
* **No proofs in programs except for termination.** The only proofs a program contains are the
  ones that justify termination (and the facts they rely on): the decrease proofs of recursive
  calls and back edges, the path conditions, pre- and postconditions they use, and the
  well-foundedness proofs. The `hp`/`hc`/`ha` normal-form proofs are Boolean checks of the
  optimisation, closed by `decide`. The capture erases the proofs of the Lean function: proof
  arguments and proof components become facts of the path condition. For example,
  `l.attach.map (fun ⟨x, h⟩ => f x)` is captured as `map (fun x => f x) l`, with no `attach`
  and no proof `h` (`Tests/Map.lean`). This is how the current capture works, not a rule of
  the language: programs may carry other proofs where a future extension needs them.
* **Recursive join points** (`joinrec`, loops): the body runs in the enclosing context (it
  reads the enclosing variables, stays inside the enclosing function, and may jump to the join
  points defined before it, e.g. to exit). Its relation `R : Env Γ → s → s → Prop` may depend
  on the enclosing variables, with `wf : ∀ e, WellFounded (R e)`; inside the body the
  precondition of the join point itself includes the decrease, so every back edge carries the
  proof that the new parameter is `R`-below the current one.
* **`while` loops** (`Expr.whileLoop`, derived): a well-founded loop on a state `x : s` (a
  tuple for several loop variables) with a relation, its well-foundedness proof and an invariant.
  Each iteration proves that the new state satisfies the invariant and is below the old one. The
  rest of the program knows that the result satisfies the invariant and not the test (partial
  correctness for free, e.g. `WhileHand.divOut_spec` in `Tests/While.lean`). `eval_whileLoop`:
  the loop computes the Lean loop `whileWF`.
* `Expr.eval` is total: structural recursion on the syntax, and `WellFounded.fix` for global
  functions and at `joinrec` nodes. It returns a plain value, with no fuel, no `Option` and no
  runtime checks.
* Soundness: `fixFn_eq`, meaning a global function satisfies its recursive equation, and
  `fixFn_unique`, meaning it is the only solution; `joinFn_eq` / `joinFn_unique`, the same for
  a recursive join point. `PTerm.run_post`: every result satisfies the postcondition.
* `PCL/Termination.lean`: every function body reaches a base case (`fix_body_reaches_base`,
  `fix_body_has_base_case`, also through recursive join points), a looping function cannot be
  built (`loop_unbuildable`), and neither can a looping join point
  (`joinrec_loop_unbuildable`).

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
    **tail-recursive** one becomes a **loop inside the caller**
    (`join K (v) := rest in joinrec L (x) := body of g in jump L args`, where the tail calls
    of `g` are back edges `jump L …` and its results are exits `jump K …`; see
    `Tests/Loops.lean`), and a recursive one with non-tail self calls becomes a global
    function;
  * any other function is captured once as an entry of the global context of the program, and
    each call becomes `gCall i args` (only its postcondition is known at the call site, so a
    helper whose value a termination proof needs must be `@[inlinable]`);
  * functions with function parameters are specialised to the function passed at each call
    (a loop if the specialised copy is tail-recursive, otherwise a global function), a mutual
    group is one global function with a tag parameter, and a function calling itself in a
    function argument is one global function together with the specialised argument;
  * helpers declared in a `where` clause are, as in Lean, ordinary top-level functions
    (`foo.go`), treated like any other function: global unless marked `@[inlinable]`
    (`where @[inlinable] go …`);
  * a call whose arguments are all known (a closed term) is evaluated when the function is
    captured and replaced by its value, whatever the callee's attribute, so a function only
    called that way does not appear in the program; `wf_agree` proves the equation by kernel
    evaluation (turn off with `set_option wfLang.foldCalls false`);
* subtype results (postconditions) and proof parameters (preconditions);
* mutual recursion (one global function with a tag parameter);
* **well-founded `while` loops** written with `wf_while x := init while c do body termination_by μ`
  (optionally `decreasing_by tac`) or `WFLang.whileWF` (relation + invariant), from
  `Core/While.lean`. Each loop becomes one `whileLoop` (a `join` and a `joinrec`); the test and
  the body must be call-free. `Tests/WhileFunctions.lean` transcribes the uploaded
  `diagonalWhile`, `mc91While` and Newton `isqrt` loops with their measures:

  ```lean
  def isqrtNewton (n : Nat) : Nat :=
    (wf_while (x, y) := (n, (n + 1) / 2) while y < x do (y, (y + n / y) / 2)
      termination_by x).1
  def isqrtNewton_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term isqrtNewton
  theorem isqrtNewton_agree : ∀ n, Term.eval isqrtNewton_term n = isqrtNewton n := by wf_agree
  ```
* **Lean's own `while` in `do` notation** (`Capture/LeanWhile.lean`, `Tests/LeanWhile.lean`).
  Since Lean v4.34, `while` (`Lean.Loop.forIn`) is defined in the logic and has an unfolding
  theorem. `WFLang.loopLaw : LoopLaw` (`Core/LeanWhile.lean`) is that law, proved from Lean's
  `Lean.Loop.forIn_eq_of_monadTail`: `forIn Loop.mk init body` runs `body` once, then continues
  or stops. The command `lean_while_to_wf f termination_by μ₁ … termination_by μₖ` (one optional
  measure and `decreasing_by` per loop, in source order; Lean guesses a measure when none is
  given) generates a well-founded version: each loop becomes a tail-recursive well-founded
  function `f.loop_i` on its mutable variables, `f.wf` is `f` with its loops replaced by them, and
  `f.eq_wf : ∀ xs, f xs = f.wf xs` is proved with `loopLaw`. There is no hypothesis left:
  `#lean_wf_func_to_term f` captures `f.wf` (running `lean_while_to_wf f` first if needed) and
  `wf_agree` proves agreement with `f` itself:

  ```lean
  def gcdW (a b : Nat) : Nat := Id.run do
    let mut a := a
    let mut b := b
    while b != 0 do
      let t := b
      b := a % b
      a := t
    return a
  lean_while_to_wf gcdW
    termination_by b
    decreasing_by all_goals exact Nat.mod_lt _ (by simp_all; omega)
  def gcdW_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdW
  theorem gcdW_agree : ∀ a b, Term.eval gcdW_term a b = gcdW a b := by wf_agree
  ```

  Supported: `break`, several loops in a row, nested loops, `match`/`if` in the body, loops
  reading earlier values, callers of functions with loops. The uploaded `isqrt` (and
  `unpairLeft`/`unpairRight`), `diagonalWhile` and `mc91While` are captured this way, and
  `diagonalWhile_eq` (omitted before) is proved. Not supported: `return` inside a
  loop, recursive functions containing a loop, and loops without a provable measure
  (`ackWhile`, `ackNoDataStructure`, whose stack needs a multiset order).
* `List.map`, including `List.attach.map` with recursive calls in the body, e.g.
  `((List.range n).attach.map fun ⟨i, _⟩ => underLambda i).sum` (`Tests/Map.lean`);
* bounded `for` loops and `Nat.fold`, and function parameters specialised to the function
  passed at each call site, including recursion through a function argument
  (`Tco.hyperWhile`, `Tco.hyperTCO`, `Tco.ack2`).

`GAPS.md` lists what is still rejected (e.g. calls under a `fun` in library code other than
`List.map`, such as `List.foldl`, Lean `while` loops with an early `return` or without a provable measure, and calls
inside the body of a `wf_while`).
`UNSUPPORTED.md` is the current assessment of everything still unsupported (types, library
combinators, `do` features, termination arguments, evaluator limits); its rejections are pinned in
`Tests/Unsupported.lean`.

## Use of Mathlib

The project depends on Mathlib (`lakefile.toml`, pinned to the `v4.34.0` tag, matching the
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

## Instances of the grammar datatypes

| datatype | instances |
|---|---|
| `Ty` | `DecidableEq`, `Repr`, `Hashable`, `Ord`, `Inhabited` |
| `Ty.denote t` (values) | `DecidableEq`, `Repr`, `Hashable` (by recursion on `t`) |
| `Sig` | `DecidableEq`, `Repr`, `Hashable`, `Inhabited` |
| `Var Γ t` | `DecidableEq`, `Repr`, `Hashable`; `IsEmpty (Var [] t)` |
| `BinOp a b c`, `UnOp a b` | `DecidableEq`, `Repr`, `Hashable` |
| `PExpr Γ t`, `PExprs Γ ts` | `DecidableEq`, `Repr`, `Hashable`, `Inhabited` (literals) |
| `FnVar fs f`, `JVar js` | `DecidableEq`, `Repr`; `IsEmpty (FnVar [] f)` |
| `JScope Γ t` | `Inhabited` |

Every `DecidableEq` instance also gives `BEq` with `ReflBEq` and `LawfulBEq` (so `==` agrees
with `=`), and together with `Hashable` it gives `LawfulHashable`. A separate `deriving BEq`
is not added, because it would give a second `==`, different from the lawful one.

`Fn`, `Self`, `JScope`, `Expr`, `Globals` and `PTerm` cannot have `DecidableEq` or `Repr`:
their fields contain predicates (`pre`, `post`, `P`, `Q`, the path condition `G`),
relations (`R`) and proofs. Equality of such fields cannot be decided.

**Functor / Traversable.** Lean's `Functor`, `LawfulFunctor`, `Traversable` and
`LawfulTraversable` apply only to type constructors `Type u → Type v`. None of the grammar
datatypes has that shape: they are families indexed by object types and contexts. The only
thing an expression "contains" is its variables. `Core/PExprMap.lean` therefore gives
the same structure over the variables, with the same laws, proved:

* `PExpr.rename f` / `PExprs.rename f` map a renaming `f : ∀ {t}, Var Γ t → Var Δ t`
  (the `map` analogue). They satisfy the functor laws `rename_id` and `rename_rename`, weakening
  is a renaming (`wk_eq_rename`), and renaming commutes with evaluation (`eval_rename`).
* `PExpr.traverseVars f` / `PExprs.traverseVars f` do an effectful renaming in any
  applicative functor (the `traverse` analogue). They satisfy the `LawfulTraversable` laws:
  identity (`traverseVars_id`), composition through `Functor.Comp` (`traverseVars_comp`),
  pure traversal equals map (`traverseVars_pure`), and naturality for applicative
  transformations (`traverseVars_naturality`).

`Tests/Instances.lean` checks that each instance is found, that equality is decided both by
`decide` and by `#eval`, and that the printing, hashing, renaming and traversal functions run.

## Layout

```
RequestProject/WFLang.lean          imports everything
RequestProject/WFLang/
├── Core/Types.lean                 Ty, Env, Var, Sig, FnType, curryEnv, BinOp, fixedRel, hoRel
├── Core/Loops.lean                 rangeLoop: first-order form of `for` loops and `Nat.fold`
├── Core/While.lean                 well-founded `while` in Lean: whileWF, whileMeasure, `wf_while`,
│                                   loop equation, loopVal
├── Core/LeanWhile.lean             LoopLaw: the unfolding law of Lean's `while` (Loop.forIn),
│                                   proved (loopLaw), and its consequences
├── Core/EvalSimpAttr.lean          the simp set `wflang_eval` (equations of the evaluator)
├── Core/PExpr.lean                 call-free expressions PExpr / PExprs
├── Core/PExprMap.lean              renaming (functor laws) and traversal (traversable laws) of
│                                   PExpr / PExprs; Inhabited / IsEmpty instances
├── Core/Normal.lean                optimised normal form: PExpr.isNF, PExpr.isCond
├── PCL/Lang.lean                   the language (imports PCL/Lang/*):
│   ├── Lang/Syntax.lean            global functions, join points, Expr (ret, ite, fixSelfCall,
│   │                               gCall, map, join, joinrec, jump)
│   ├── Lang/Eval.lean              eval (reference semantics), soundness of loops (joinFn)
│   ├── Lang/Machine.lean           the jump machine evalS (loops, tail calls in constant stack),
│   │                               its proof of agreement with eval, csimp
│   ├── Lang/Fix.lean               global functions (fixFn), soundness, fixS (machine), csimp
│   ├── Lang/While.lean             whileLoop (derived form) and eval_whileLoop
│   ├── Lang/Program.lean           Globals, PTerm/Term, Term.ofFix, tuples
│   └── Lang/Simp.lean              simp lemmas used by the capture tactics
├── PCL/Size.lean                   size measures (nodes, joins, loops, global calls, maps, globals)
├── PCL/Termination.lean            base-case existence, unbuildable loops
├── Capture/Meta.lean               reading a Lean function (imports Capture/Meta/*):
│   ├── Meta/Signature.lean         object types, signatures, specialised references (FnRef)
│   ├── Meta/Fix.lean               the WellFounded.fix of a Lean function
│   ├── Meta/Calls.lean             @[inlinable], calls with known arguments, inlining, loops
│   ├── Meta/Callees.lean           classifying callees, global functions, withEqnRhs
│   ├── Meta/WFRel.lean             decrease proofs, well-founded relations on environments
│   ├── Meta/Mutual.lean            mutual recursion, recursion through a function argument
│   ├── Meta/Tactics.lean           tactics wf_dec, wf_close, …
│   └── Meta/Agree.lean             skeleton of the agreement tactic
├── Capture/Optimize.lean           simplifying IR (constant folding, identities, dead branches)
├── Capture/Translate/Context.lean  the capture context (callees: loops or globals)
├── Capture/Translate.lean          Lean term → PExpr syntax, branch recognition
├── Capture/Stmt/Basic.lean         helpers: control-flow tests, callee kinds, join-point
│                                   indices, loop-state tuples
├── Capture/Stmt.lean               Lean term → statements: A-normal form, join points, loops
│                                   for tail-recursive inlinable callees, global calls, `while`,
│                                   `List.map` (with `List.attach` and its proofs erased)
├── Capture/LeanWhile/Loops.lean    recognising Lean's `while` loops, tuples of mutable
│                                   variables, the loop as a tail-recursive function
├── Capture/LeanWhile.lean          `lean_while_to_wf f`: well-founded versions f.loop_i, f.wf of
│                                   a function using Lean's `while`, and f.eq_wf
├── Capture/Elab.lean               the capture commands (imports Capture/Elab/*):
│   ├── Elab/Term.lean              the lazily collected global context, #lean_wf_func_to_term
│   └── Elab/Agree.lean             the agreement tactic wf_agree
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
    ├── Globals.lean                global functions vs @[inlinable]; shapes and sizes
    ├── WhereFold.lean              `where` helpers as global functions; calls with known
    │                               arguments evaluated at capture time
    ├── WhileFunctions.lean         Lean functions written with well-founded `while` loops
    ├── While.lean                  a hand-written `while` program with its specification;
    │                               captures of the loops + agreement theorems, shapes,
    │                               runtime checks, rejections
    ├── Loops.lean                  tail-recursive @[inlinable] functions inlined as loops
    │                               (recursive join points) inside the caller
    ├── LeanWhile.lean              Lean's own `while`: the uploaded loops and others captured,
    │                               agreement theorems, diagonalWhile_eq, runtime checks,
    │                               rejections
    └── Map.lean                    `List.map` and `List.attach.map` (proofs erased), with
                                    recursive calls in the body; underLambda
GAPS.md                             what is supported, how, and what is left
GRAMMAR.md                          grammar layers: why join points, why no Atom layer
CONTEXTS_ASSESSMENT.md              the design note behind removing local functions and adding
                                    recursive join points
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
