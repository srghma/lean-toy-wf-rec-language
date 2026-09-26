# Grammar layers: what was refined and what was left alone

The question was whether the grammar should be split further than `PExpr` / `Expr`, for example
into `Atom` / `Comp` / `Expr`, or given join points. Short answer:

* **Join points: yes, added.** They fix a real problem: continuations were being copied, and
  the copies could grow exponentially.
* **Recursive join points and no local functions: done** (following `CONTEXTS_ASSESSMENT.md`).
  The local-function context is gone: a function is either global or, if it is a loop, a
  recursive join point inside the statement that uses it. `while` is a derived form.
* **An `Atom` layer under `PExpr`: no.** In this language it adds proof work and buys nothing.
  Details below.

## The layers now

```
PExpr  ::= x | lit | op PExpr PExpr | !PExpr | if PExpr then PExpr else PExpr
             -- pure, total, call-free values                          (Core/PExpr.lean)
NF     ::= PExpr  with  isNF = true              -- optimised normal form (Core/Normal.lean)
Cond   ::= PExpr  with  isCond = true            -- NF, not a literal, not a negation
LCond  ::= PExpr  with  isLoopCond = true        -- NF, not a literal (a loop test)
Share  ::= PExpr  with  isShareable = true       -- NF, not a variable or a literal

Expr   ::= ret NF                                     -- return
         | if Cond then Expr else Expr                -- case          (tail only)
         | let v := self NF* in Expr                  -- fixSelfCall   (carries `dec`)
         | let v := g NF* in Expr                     -- gCall         (global function)
         | let v := Share in Expr                     -- plet          (pure let: sharing;
                                                      --  the rest knows v = the value)
         | let v := map (fun x => Expr) NF in Expr    -- map           (the body knows x ∈ l)
         | let v := foldl (fun acc x => Expr) NF NF in Expr
                                                      -- foldl         (the body knows x ∈ l)
         | join j (v : s) := Expr in Expr             -- join          (tail only)
         | joinrec j (x : s) [R, wf] := Expr in Expr  -- joinrec       (tail only; a loop)
         | jump j NF                                  -- jump          (tail; a back edge
                                                      --  carries the decrease)

derived: let v := while LCond do x := NF from NF in Expr
           = join k (v) := Expr in joinrec L (x) := (if c then jump L body else jump k x)
             in jump L init                           -- Expr.whileLoop

Program ::= global g₁ := fix self xs. Expr  …  global gₙ := fix self xs. Expr ;  Expr
             -- `PTerm`: global context (`Globals`) + main statement
```

This is the usual A-normal form with join points. `PExpr` already plays the role of the
"value / primitive computation" layer, and `Expr` is the statement layer. Every call result is
bound to a variable, and every compound statement is in tail position. On top of that, the
grammar enforces an **optimised normal form** and a **global context** (sections below).

## Optimised normal form (`Core/Normal.lean`)

Every call-free expression occurring in a statement (`ret`, the arguments of the two kinds
of calls, `jump`) carries a proof `p.isNF = true`, the value of a pure `let` a proof
`p.isShareable = true` (normal form, and not a variable or a literal), and every `if` test a
proof `c.isCond = true`.
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

## Pure `let`: sharing (`PCL/Lang/Syntax.lean`, `Capture/Stmt.lean`)

```
let v := p in k            -- Expr.plet s p hp k
```

* `p` is a call-free expression, computed once; `k` runs in the context extended by `v`.
* The path condition of `k` is the current one plus the equation `v = p`, so the proofs in `k`
  (decrease of recursive calls and back edges, preconditions, postconditions) know the value of
  `v`. Example: in `gcdL` (`Tests/Sharing.lean`), `let r := m % n; … gcdL n r` needs `r < n`,
  which follows from `r = m % n` and `n ≠ 0`.
* `hp : p.isShareable = true` (`Core/Normal.lean`): `p` is in normal form and is not a
  variable or a literal. Binding an atom would only rename it, so the normal form requires it
  to be substituted instead; a hand-written `let x := y in …` is ill-typed.
* Semantics: `Expr.eval` evaluates `p` once and passes its value to `k` (`eval_plet`); the jump
  machine does the same (`evalS`), and `eval_val_eq_evalS` covers the new case. Soundness and
  the termination results (`fix_body_reaches_base`, …) extend to it: `firstCall` continues into
  `k` with the value of `p`.
* Capture: a Lean `let x := v; b` becomes `plet` when `v` is call-free, of an object type, not
  atomic once simplified (so `let y := 2 + 3` is folded and substituted), and `x` occurs at
  least twice in `b` (counted syntactically, `bvarUses`). This works in tail and non-tail
  position (`stmt`, `lift`), inside loop bodies and in `do` notation. Other call-free `let`s are
  substituted as before; `set_option wfLang.shareLets false` substitutes all of them.
* Proofs: `wf_dec` rewrites each program variable bound by a `plet` into its value
  (`wf_subst_lets`) before the usual closing tactics, so decrease obligations have the same form
  as in the Lean function. `wf_agree` needs no change: `eval_plet` is a simplification lemma,
  and the Lean `let` is unfolded by `simp`.
* Measures: `PTerm.lets` counts the `plet` nodes, and `PTerm.exprNodes` counts the nodes of
  the call-free expressions of a program (each shared value counted once). For
  `pow4 a b c := let x := a * b + c; x * x * x * x`, `exprNodes` is 12 with sharing and 23
  without (`Tests/Sharing.lean`).

## `while` loops (`PCL/Lang/While.lean`, `Core/While.lean`)

`Expr.whileLoop s init hi c hc R wf inv hinit p hp step k` is
`let v := (while c do x := p from x := init) in k`. It is a derived form (a definition, not a
constructor): a join point `k` for the exit and a recursive join point for the loop, whose body
is `if c then jump L p else jump k x` (`Expr.whileBody`). The loop state `x : s` is one value (a
tuple for several loop variables). It carries:

* a relation `R e` on the states, for each value `e` of the enclosing variables, with
  `wf : ∀ e, WellFounded (R e)`;
* an invariant `inv e x`, with the proof `hinit` that the initial state satisfies it;
* the next state `p`, a call-free expression over `x` and the enclosing variables, with the
  proof `step` that, under the invariant and the test, it satisfies the invariant and is
  `R`-below the old state (the back edge `jump L p` needs exactly this).

The continuation `k` knows that `v` satisfies the invariant and that the test is false. So a
loop gives Hoare-style partial correctness for free: `Tests/While.lean` shows this with a
hand-written program whose postcondition follows from the loop's exit condition.
`eval_whileLoop` shows that the loop computes the Lean loop `whileWF` (`Core/While.lean`), and
is proved from `joinFn_unique`.

The test is a `PExpr` with `isLoopCond`: in normal form and not a literal. Unlike the test of an
`if`, it may be a negation (`Expr.whileBody` swaps the branches itself).

**Lean side.** Lean's `while` (in `do` notation) is built on `Loop.forIn`. Since Lean v4.34 it
is defined in the logic and unfolds by `Lean.Loop.forIn_eq_of_monadTail`; it still has no
termination proof to reuse. `lean_while_to_wf f` (with one `termination_by`/`decreasing_by` per
loop) builds a well-founded version `f.wf` of `f`, whose loops are tail-recursive well-founded
functions `f.loop_i` on the mutable variables, and proves `f.eq_wf : ∀ xs, f xs = f.wf xs` from
`WFLang.loopLaw : LoopLaw` (`Core/LeanWhile.lean`, the unfolding law of `Loop.forIn`, proved);
`#lean_wf_func_to_term f` captures `f.wf` (each `f.loop_i` becomes a recursive join point), and
`wf_agree` proves agreement with `f` itself, with no hypothesis. Another
well-founded replacement is `WFLang.whileWF R wf inv c body step init hinit` (`Core/While.lean`).
There is also its measure form `whileMeasure μ c body dec init`, with the notation

```lean
wf_while (x, y) := init while c do body termination_by μ   -- (decreasing_by tac)?
```

`#lean_wf_func_to_term` turns each such loop into one `whileLoop`. It reuses the Lean
relation, invariant and proofs (as functions of the environment), requires the test and the body
to be call-free (the initial state may call), and proves agreement by rewriting both sides to
`loopVal c body init`, the first iterate of `body` on which `c` is false (`whileWF_eq_loopVal`).

## `map`, and why programs hold no proofs except for termination

`let v := map (fun x => body) l in k` (`Expr.map s u l hl body k`) maps a statement `body`, over
one more variable `x : s`, over the list `l`. The body may make calls, recursive calls of the
enclosing function included. It has no join point in scope (`JScope.nil`: a jump cannot leave
the body) and no postcondition. Its path condition is the current one plus `x ∈ l`, so the
decrease proof of a recursive call inside the body may use the membership. The evaluator maps
over `l.attach` to supply that fact (`eval_map`); the program itself contains no membership
proof.

The current capture follows this convention (a design choice, not a restriction: the grammar may
carry other proofs through a program if a future extension needs to): **a program contains only
the proofs that justify termination**: the decrease
proofs `dec` of recursive calls and of back edges, the well-foundedness proofs `wf`, and the
facts they use (path conditions, pre- and postconditions). The normal-form proofs `hp`/`hc`/`ha`
are Boolean checks (`decide`) of the optimisation. Nothing else a Lean function computes with
proofs appears in the program: the capture erases proof arguments and proof components, and
turns the facts they carry into facts of the path condition. `List.attach` is the standard
example: Lean code writes `l.attach.map (fun ⟨x, h⟩ => f x)` only to have `h : x ∈ l` for the
termination proof of `f x`, and the capture produces `map (fun x => f x) l`, where `x ∈ l` is in
the path condition. The agreement proofs relate the two forms with `List.attach_map_val`.
`PTerm.maps` counts the `map` nodes; `Tests/Map.lean` has the examples, including
`underLambda`.

`let v := foldl (fun acc x => body) init l in k` (`Expr.foldl s u l hl init hi body k`) is the
same idea for a left fold: `body` is a statement over two more variables, the accumulator
`acc : u` and the element `x : s`, whose path condition is the current one plus `x ∈ l`
(`eval_foldl`: the evaluator folds over `l.attach`). A Lean `l.attach.foldl (fun acc ⟨x, h⟩ => …)
init`, and the forms rewritten into it (`l.attach.any p`, `l.attach.all p`, and a `for` loop that
uses its membership proof, `for h : x in l` or `for ⟨x, h⟩ in l.attach`, whose body always
continues), is captured as `foldl`; `Tests/AttachCombinators.lean` has the examples
(`depthSum`, `forMem`).

## Global context (`PCL/Lang/Program.lean`, `Capture/Elab/Term.lean`)

A program is `PTerm.mk globals main`: a list of global functions (`Globals`, each a closed
well-founded recursive function `defn gs f R wf body`, a non-recursive one using the empty relation `emptyRelation`)
and the main statement. `Expr` has the list of global signatures `GL` as a parameter, and
`gCall i args` calls the global function at index `i`. A global body may call the globals
defined before it, so the context is ordered callees first. `Globals.env` evaluates each
definition once with `fixFn`, and `Expr.eval` takes that environment. A recursive program is its
function as the last global and a main statement that calls it (`PTerm.ofFix`).

The capture collects the global context lazily: while it translates, the first call of a
function that must be global registers it (after its own callees, so the context stays ordered
callees first); a function called several times is captured once.

The capture decides what goes in the global context from the attribute `@[inlinable]`:

* a function marked `@[inlinable]` is inlined: a non-recursive one is replaced by its body, a
  tail-recursive one becomes a loop (recursive join point) at each call site (next section), and
  a recursive one with non-tail self calls is a global function;
* any other user-defined function is captured **once**, as an entry of the global context, and
  every call of it becomes a `gCall`;
* functions with function parameters are specialised per call site (a loop if the copy is
  tail-recursive, otherwise one global per specialisation), a mutual group is one global
  function with a tag parameter, and a function calling itself inside a function argument is
  one global function together with the specialised argument.

A `gCall` only knows the postcondition of its callee. When the termination proof of a caller
needs the value computed by a helper (`logHalf n` calls itself on `half n`), the helper must be
`@[inlinable]`; see `Tests/Globals.lean`.

`where` helpers: Lean compiles `def foo … where go …` into two top-level constants, `foo` and
`foo.go`, and `foo.go` can be called from anywhere. The capture follows Lean: `foo.go` is a
user function like any other, so it is an entry of the global context unless it is marked
`@[inlinable]` (`where @[inlinable] go …`). An `@[inlinable]` function never appears in the
global context.

Calls with known arguments: a call `g a₁ … aₙ` of a user function whose arguments are all known
(the call is a closed term) is evaluated when the function is captured and replaced by its
value (`foldCall?` in `Capture/Meta/Calls.lean`; the kernel computes the value). This holds for
global functions and `@[inlinable]` ones alike, recursive or not. The function is then not
needed for that call, so a function only called with known arguments is neither in the global
context nor a loop. `wf_agree` proves each equation `g a₁ … aₙ = v` with the same kernel
evaluation (the simplification procedure `wfFoldCalls`). Not evaluated: calls of the function
being captured itself, of functions with a subtype result, proof parameters or function
parameters, and calls inside proofs. `set_option wfLang.foldCalls false` turns it off.
See `Tests/WhereFold.lean`.

## Recursive join points (`PCL/Lang/Syntax.lean`, `Capture/Stmt.lean`)

```
joinrec j (x : s) [R, wf] := body in m
```

* `body` runs in `s :: Γ`, under the path condition of the definition site and the
  precondition `P e x`. It **keeps** the enclosing function (so it may make recursive calls of
  it), the enclosing variables and the outer join points.
* In `m` (the entry), `jump j p` needs only `P`.
* Inside `body`, `j` is in scope with the precondition `P e v ∧ R e v x`: every back edge
  `jump j v` proves that `v` is below the current parameter `x` along `R e`. No new `JScope`
  constructor is needed: the decrease is part of the precondition of the entry seen from inside.
* `R e` may depend on the enclosing variables `e`, with `wf : ∀ e, WellFounded (R e)`.
* `Expr.eval` runs it with `(wf e).fix` (`joinFn`); `joinFn_eq` is its equation and
  `joinFn_unique` says that it is the only solution. `joinrec_loop_unbuildable`
  (`PCL/Termination.lean`): `joinrec j (x) := jump j x` cannot be written.

**Tail-recursive `@[inlinable]` functions are inlined as loops.** A call `g args` followed by
the rest of the computation `k` becomes

```
join K (v) := ⟦k v⟧ in
joinrec L (x) [R] := ⟦body of g: tail calls g a ↦ jump L a, results r ↦ jump K r⟧ in
jump L args
```

The parameter of `L` is the tuple of `g`'s parameters (`PCL.tupleTy`, read with `PCL.toEnv`),
and `R` is Lean's well-founded relation for `g`. The decrease proofs of the back edges are found
by the same tactic as for recursive calls. The loop is part of the caller's statement: it sees
the caller's variables, its exit `jump K r` continues the caller, and `K` may call the
enclosing recursive function. If the body of `g` turns out not to be translatable as a loop,
`g` becomes a global function instead. `wf_agree` identifies each loop with
`joinFn_unique`: the value of `L` on `x` is `K (g x)`, proved by unfolding `g` once, for every
value of the join points in scope. `Tests/Loops.lean` pins the shapes (`loops`, `nglobals`):
two calls give two loops, a loop can contain a loop, a loop body can call a global function, and
bounded `for` loops (through the tail-recursive `rangeLoop`) are loops too.

## Join points (`PCL/Lang/Syntax.lean`)

**The problem.** A non-tail `if` containing a call, such as `(if c then f a else f b) + rest`, had
to become `if c then (let v := f a; rest v) else (let v := f b; rest v)`, because `ite` must stay
in tail position. `k` such `if`s in a row give `2^k` copies of the rest, and each copy has its
own decrease proofs to elaborate. In `Tests/Joins.lean`, `seq2` and `seq3` have 14 and 26 nodes
with copies. The capture of `seq4` with copies did not finish elaborating within 4 000 000
heartbeats when I tried it; that run is not part of the build.

**The construct.** The rest of the computation now becomes a named join point:

```
join j (v : s) := ⟦rest⟧ in
if c then (let v₁ := f a in jump j v₁) else (let v₂ := f b in jump j v₂)
```

`seq2`, `seq3` and `seq4` have 15, 20 and 25 nodes with join points, 5 more per `if`. This is
pinned in `Tests/Joins.lean`.

**Typing.**
* The join points in scope are a new index `js : JScope Γ t` of `Expr`, and jumps use typed
  de Bruijn indices `JVar js`.
* A join point has a precondition `P` on its parameter, which every jump must prove and its body
  may use. It also has the postcondition `Q` of its definition site, and a jump proves that `Q`
  implies the current postcondition.
* The body runs under the path condition of the definition site plus `P`.
* A (non-recursive) join point is **not a function**:
  * it is not recursive, so it needs no `dec` proof;
  * it can only be jumped to in tail position;
  * it is invisible inside global function bodies, which start with `JScope.nil`, so a join
    point cannot escape into another function.

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
* The evaluator is still structural recursion with no fuel. `#print axioms Expr.eval` reports
  only standard axioms (`propext`, and, since `String` was added to the types, `Classical.choice`
  and `Quot.sound`, which come from Lean's `String` library), and this is checked by
  `#guard_msgs` in `PCL/Termination.lean`.

**Re-proved for the new grammar.**
* `fixFn_eq` and `fixFn_unique`: a function body runs with no join points in scope.
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
* When the rest of the computation is tiny, copying is smaller: `nested` has 16 nodes with a
  join point and 12 with copies.

## Why no `Atom` layer (`Atom ::= x | lit`, operators only on atoms)

Full ANF restricts operator arguments to atoms and names every intermediate result
(`let x := a + b in …`). That matters when:

1. **evaluation order or effects** must be explicit. Here `PExpr` is pure and total; the only
   effect, calling a function, is already pulled out into `fixSelfCall` / `gCall`;
2. **there is a cost model or a machine to compile to**, such as registers or stack slots. There
   is neither here: the evaluator is denotational;
3. **sharing**: a pure subexpression that is written twice is computed twice. This is now
   addressed by the pure `let` statement (`plet`, section above), without atoms.

Only point 3 applies, and the pure `let` handles it. Atoms everywhere would have been a heavy
way to address it:
* every operator would need its own `let` statement;
* the path conditions would grow with those `let`s;
* every agreement proof would need more `simp` steps.

Adding the layer would cost proof and capture work in every file and would not strengthen
soundness or termination.

## Possible next refinements (not implemented)

* **Sharing beyond Lean `let`s** (common subexpression elimination): the capture only shares
  what the Lean function names with a `let`; a subexpression written twice without a `let` is
  still computed twice.
* **Join points in functions with postconditions**: give the join parameter a precondition
  recording the relevant postcondition (e.g. `∃ args, post args v`) instead of copying.
* **Merging `fixSelfCall` into `gCall`**, with `self` as a global function whose calls carry
  an extra `dec` obligation. This would give a smaller grammar, but a global function and the
  function being defined have different runtime meanings: the global function is total, while
  `self` is only defined below the current arguments (the `Handler`). Keeping two constructors
  keeps that difference visible in the types.
* **Loops with calls in the `while` test or body**: a `wf_while` loop whose body calls a
  function could be a general recursive join point too; the capture still requires the test and
  the body of a `wf_while` to be call-free.
* **Folding `PExpr.not` into `UnOp`**: cosmetic.
