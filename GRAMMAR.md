# Grammar layers: what was refined and what was left alone

The question was whether the grammar should be split further than `PExpr` / `Expr`, for example
into `Atom` / `Comp` / `Expr`, or given join points. Short answer:

* **Join points: yes, added.** They fix a real problem: continuations were being copied, and
  the copies could grow exponentially.
* **An `Atom` layer under `PExpr`: no.** In this language it adds proof work and buys nothing.
  Details below.

## The layers now

```
PExpr  ::= x | lit | op PExpr PExpr | !PExpr | if PExpr then PExpr else PExpr
             -- pure, total, call-free values                          (Core/PExpr.lean)
NF     ::= PExpr  with  isNF = true              -- optimised normal form (Core/Normal.lean)
Cond   ::= PExpr  with  isCond = true            -- NF, not a literal, not a negation
LCond  ::= PExpr  with  isLoopCond = true        -- NF, not a literal (a loop test)

Expr   ::= ret NF                                     -- return
         | if Cond then Expr else Expr                -- case          (tail only)
         | let v := self NF* in Expr                  -- fixSelfCall   (carries `dec`)
         | let v := f NF* in Expr                     -- fnCall        (local function)
         | let v := g NF* in Expr                     -- gCall         (global function)
         | let v := while LCond do x := Expr from NF in Expr
                                                      -- whileLoop     (carries R, wf, inv)
         | letrec f := fix self xs. Expr in Expr      -- fix           (tail only)
         | join j (v : s) := Expr in Expr             -- join          (tail only)
         | jump j NF                                  -- jump          (tail)

Program ::= global g₁ := fix self xs. Expr  …  global gₙ := fix self xs. Expr ;  Expr
             -- `PTerm`: global context (`Globals`) + main statement
```

This is the usual A-normal form with join points. `PExpr` already plays the role of the
"value / primitive computation" layer, and `Expr` is the statement layer. Every call result is
bound to a variable, and every compound statement is in tail position. On top of that, the
grammar enforces an **optimised normal form** and a **global context** (sections below).

## Optimised normal form (`Core/Normal.lean`)

Every call-free expression occurring in a statement (`ret`, the arguments of the three kinds
of calls, `jump`) carries a proof `p.isNF = true`, and every `if` test a proof `c.isCond = true`.
`isNF` is a Boolean function, so these proofs are `by decide` and are erased at runtime.
`isNF` rejects every expression that the capture would still simplify:

* **constant folding**: an operator (binary, unary, `!`) applied to literals only;
* **algebraic identities**: `x + 0`, `0 + x`, `x - 0`, `x * 1`, `x * 0`, `x / 1`, `x % 1`,
  `x ^ 0`, `x ^ 1`, `1 ^ x`, `b && lit`, `b || lit`, `xor b lit`, `l ++ []`, `[] ++ l`, … (and
  the same on `Int`) — the full list is `BinOp.simplifies`;
* **redundant unary operators**: `!!b`, `- - i`, `(a, b).1`, `(a, b).2` (`UnOp.simplifies`);
* **branches**: an `if` whose test is a literal (dead branch) or a negation `!c` (the branches
  are swapped instead), an `if` between two equal literals, and `if c then true else false`.

`isCond` adds that a statement-level test is neither a literal nor a negation, so the dead
branch of an `Expr.ite` is removed and `if !c then a else b` becomes `if c then b else a`.

The capture meets these requirements by construction: it translates Lean terms into an
intermediate representation (`Capture/Optimize.lean`) whose smart constructors `mkBin`,
`mkNot`, `mkUn`, `mkIte` fold constants, apply the identities, drop dead branches and swap
negated tests, and only then renders the `PCL` syntax. `Capture/Translate.lean` does the same
for statement-level `if`s (`iteStx`). A hand-written program that is not simplified fails to
type-check (`Tests/Normal.lean`).

Every rewrite preserves `PExpr.eval`, and the agreement theorems (`wf_agree`) are proved about
the simplified programs, so each capture is checked against the Lean function end to end.

## `while` loops (`PCL/Lang.lean`, `Core/While.lean`)

`whileLoop s init c R wf inv hinit body k` is `let v := (while c do x := body from x := init) in
k`. The loop state `x : s` is one value (a tuple for several loop variables). The node carries:

* a relation `R e` on the states, for each value `e` of the enclosing variables, with
  `wf : ∀ e, WellFounded (R e)`;
* an invariant `inv e x`, with the proof `hinit` that the initial state satisfies it;
* a body, which is a statement over `x` and the enclosing variables. Its path condition includes
  the invariant and the test (`c = true`). Its postcondition is that the new state satisfies the
  invariant and is `R`-below the old one. The `ret`s of the body prove it, like the `dec` proof
  of a recursive call.

The continuation `k` knows that `v` satisfies the invariant and that the test is false. So a
loop gives Hoare-style partial correctness for free: `Tests/While.lean` shows this with a
hand-written program whose postcondition follows from the loop's exit condition. The evaluator
runs the loop with `WellFounded.fix` on the states. `whileFn_eq` is the loop equation and
`whileFn_unique` says it has only one solution. `while_exits` and
`while_nonterminating_unbuildable` (`PCL/Termination.lean`) say that every loop exits and that a
loop whose test stays true cannot be written.

A loop binds its result, like a call, so it can occur in non-tail position. It does not need to
be a `fix` in tail position. The test is a `PExpr` with `isLoopCond`: in normal form and not a
literal. Unlike the test of an `if`, it may be a negation, since the body and the exit of a loop
cannot be swapped. The body may call the local and global functions in scope. It may not call
the enclosing recursive function, and it may not jump to a join point: a loop is a complete
computation, like a call.

**Lean side.** Lean's `while` (in `do` notation) is built on `Loop.forIn`, a `partial def`. It
has no termination proof and cannot be unfolded in proofs, so the capture cannot reuse it. The
well-founded replacement is `WFLang.whileWF R wf inv c body step init hinit` (`Core/While.lean`).
There is also its measure form `whileMeasure μ c body dec init`, with the notation

```lean
wf_while (x, y) := init while c do body termination_by μ   -- (decreasing_by tac)?
```

`#lean_wf_func_to_term` turns each such loop into one `whileLoop` node. It reuses the Lean
relation, invariant and proofs (as functions of the environment), requires the test and the body
to be call-free (the initial state may call), and proves agreement by rewriting both sides to
`loopVal c body init`, the first iterate of `body` on which `c` is false (`whileWF_eq_loopVal`).

## Global context (`PCL/Lang.lean`, `Capture/Elab.lean`)

A program is `PTerm.mk globals main`: a list of global functions (`Globals`, each a closed
well-founded recursive function `defn gs f R wf body`, a non-recursive one using the empty relation `emptyRelation`)
and the main statement. `Expr` has the list of global signatures `GL` as a parameter, and
`gCall i args` calls the global function at index `i`. A global body may call the globals
defined before it, so the context is ordered callees first. `Globals.env` evaluates each
definition once with `fixFn`, and `Expr.eval` takes that environment.

The capture decides what goes in the global context from the attribute `@[inlinable]`:

* a function marked `@[inlinable]` is inlined: a non-recursive one is replaced by its body, a
  recursive one becomes a local `fix` at each call site;
* any other user-defined function is captured **once**, as an entry of the global context, and
  every call of it becomes a `gCall`;
* functions with function parameters (specialised per call site), members of a mutual group,
  and functions calling themselves inside a function argument are always captured at the call
  site.

A `gCall` only knows the postcondition of its callee. When the termination proof of a caller
needs the value computed by a helper (`logHalf n` calls itself on `half n`), the helper must be
`@[inlinable]`; see `Tests/Globals.lean`, which also shows that sharing a recursive function in
the global context gives a smaller program than inlining it at each call site
(11 vs 19 nodes).

## Join points (`PCL/Lang.lean`)

**The problem.** A non-tail `if` containing a call, such as `(if c then f a else f b) + rest`, had
to become `if c then (let v := f a; rest v) else (let v := f b; rest v)`, because `ite` must stay
in tail position. `k` such `if`s in a row give `2^k` copies of the rest, and each copy has its
own decrease proofs to elaborate. In `Tests/Joins.lean`, `seq2` and `seq3` have 15 and 27 nodes
with copies. The capture of `seq4` with copies did not finish elaborating within 4 000 000
heartbeats when I tried it; that run is not part of the build.

**The construct.** The rest of the computation now becomes a named join point:

```
join j (v : s) := ⟦rest⟧ in
if c then (let v₁ := f a in jump j v₁) else (let v₂ := f b in jump j v₂)
```

`seq2`, `seq3` and `seq4` have 16, 21 and 26 nodes with join points, 5 more per `if`. This is
pinned in `Tests/Joins.lean`.

**Typing.**
* The join points in scope are a new index `js : JScope Γ t` of `Expr`, and jumps use typed
  de Bruijn indices `JVar js`.
* A join point has a precondition `P` on its parameter, which every jump must prove and its body
  may use. It also has the postcondition `Q` of its definition site, and a jump proves that `Q`
  implies the current postcondition.
* The body runs under the path condition of the definition site plus `P`.
* A join point is **not a function**:
  * it is not recursive, so it needs no `dec` proof;
  * it can only be jumped to in tail position;
  * it is invisible inside `fix` bodies, because the body of a `fix` starts with
    `JScope.nil`, so a join point cannot escape into another function.

**Why `JScope` has a weakening constructor.** My first version used `List (Join Γ t)` and
`js.map (·.push s)` under binders. That type-checks, but the jumps then stay stuck behind
`List.map` in the agreement proofs, and `simp` never reduces them: the proof timed out.
`JScope` has `wk js s` as a constructor instead, and `JEnv (.wk js s) e` unfolds to
`JEnv js e.2`. This has two consequences:
* moving under a binder is the identity at runtime;
* the lookup lemmas `JVar.get_here`, `JVar.get_there` and `JVar.get_wk` are `rfl` lemmas that
  `simp` applies.

**Semantics.**
* `Expr.eval` takes the values of the join points as an extra argument `JEnv js e`.
* `join` passes the closure of its body to its scope, and `jump` calls that closure.
* The evaluator is still structural recursion with no fuel. `#print axioms Expr.eval` still
  reports only `propext`, as before, and this is checked by `#guard_msgs` in
  `PCL/Termination.lean`.

**Re-proved for the new grammar.**
* `fixFn_eq` and `fixFn_unique`: a `fix` body now runs with no join points in scope.
* `PTerm.ofFix_run`, and `Term.ofFix_eval` / `Term.ofFix_eval_post`.
* `fix_body_reaches_base`, `fix_body_has_base_case` and `loop_unbuildable`. Here `firstCall`
  follows a `jump` into the join point's body; the information it needs is in `JFirst`.
* All earlier agreement theorems in the test suite build unchanged: every `wf_agree` proof and
  every runtime check.

**Capture.**
* Every non-tail `if`/`match` containing a call becomes a join point.
* **When the capture still copies.** If a call in scope has a postcondition (a function with a
  subtype result), the capture falls back to copying. The rest of the computation may need that
  postcondition in its decrease proofs, and the parameter of a join point does not record which
  call produced it. Copying keeps it.
* `set_option wfLang.joinPoints false` brings back the old behaviour everywhere; the comparison
  in `Tests/Joins.lean` uses it.
* When the rest of the computation is tiny, copying is smaller: `nested` has 17 nodes with a
  join point and 13 with copies.

## Why no `Atom` layer (`Atom ::= x | lit`, operators only on atoms)

Full ANF restricts operator arguments to atoms and names every intermediate result
(`let x := a + b in …`). That matters when:

1. **evaluation order or effects** must be explicit. Here `PExpr` is pure and total; the only
   effect, calling a function, is already pulled out into `fixSelfCall` / `fnCall` / `gCall`;
2. **there is a cost model or a machine to compile to**, such as registers or stack slots. There
   is neither here: the evaluator is denotational;
3. **sharing**: a pure subexpression that is written twice is computed twice.

Only point 3 applies. Atoms everywhere would be a heavy way to address it:
* every operator would need its own `let` statement;
* the path conditions would grow with those `let`s;
* every agreement proof would need more `simp` steps.

Adding the layer would cost proof and capture work in every file and would not strengthen
soundness or termination.

## Possible next refinements (not implemented)

* **A pure `let v := p in k` statement**, with the path condition extended by `v = p`. At present
  the capture substitutes a Lean `let` whose value is call-free, so a value used twice is computed
  twice. This `let` would add sharing without atoms. It is also where a separate `Comp` layer
  would actually pay off.
* **Join points in functions with postconditions**: give the join parameter a precondition
  recording the relevant postcondition (e.g. `∃ args, post args v`) instead of copying.
* **Merging `fixSelfCall` into `fnCall`**, with `self` as a local function whose calls carry an
  extra `dec` obligation. This would give a smaller grammar, but a local function and the
  function being defined have different runtime meanings: the local function is total, while
  `self` is only defined below the current arguments (the `Handler`). Keeping two constructors
  keeps that difference visible in the types.
* **Folding `PExpr.not` into `UnOp`**: cosmetic.
