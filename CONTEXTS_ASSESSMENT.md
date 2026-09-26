# Assessment: removing the local-function context, and recursive join points

> **Status: implemented.** Both changes were made after this note was written, so the
> "nothing was changed" remark below describes the code at the time of the assessment.
> * `fns`, `fix` and `fnCall` are gone from `PCL.Expr`; recursive programs are a global function
>   plus a main statement calling it (`PTerm.ofFix`).
> * Recursive join points are a separate constructor `joinrec s P R wf body m` (the "separate
>   constructor" option of part 2). Instead of a new `JScope` entry, the body sees `j` through
>   the ordinary `bind` entry whose precondition is `P e v ∧ R e v x`, so every back edge
>   proves the decrease (`joinFn`, `joinFn_eq`, `joinFn_unique`, `joinrec_loop_unbuildable`).
> * `whileLoop` is a derived form (`Expr.whileLoop`, `eval_whileLoop`).
> * Tail-recursive `@[inlinable]` functions are inlined as loops inside the caller; recursive
>   ones with non-tail calls are global functions (`Tests/Loops.lean`, `Tests/Globals.lean`).

This note answers two design questions about `PCL.Expr` (`RequestProject/WFLang/PCL/Lang.lean`):

1. Is there a reason **not** to remove the local-function context ("fnCtx") and split what it
   does between the join-point context ("jpCtx") and the global context ("globalCtx")?
2. Should join points take a well-founded relation `R` as well?

Names used in the code:

| informal name | index of `Expr` | lookup / values | constructors that use it |
|---|---|---|---|
| fnCtx     | `fns : List Fn`   | `FnVar fns f`, `FEnv fns` (argument `fe` of `eval`) | `fix`, `fnCall` |
| jpCtx     | `js : JScope Γ t` | `JVar js`, `JEnv js e` (argument `je`)             | `join`, `jump` |
| globalCtx | `GL : List Fn` (a parameter) | `FnVar GL f`, `FEnv GL` (argument `ge`) | `Globals.defn`, `gCall` |

This is an assessment only. Nothing in the language or the capture was changed, and none of the
claims below is backed by a new Lean proof. They come from reading the current code, and the
places they rely on are cited.

---

## 1. Removing fnCtx

### Short answer

There is **no semantic or soundness reason** to keep `fns`. Everything it holds could be a
global function. The remaining reasons are about engineering and presentation: the capture
would need restructuring, `@[inlinable]` would mean something different to users, and several
pinned test counts would change. None of them is a limitation of the language.

### Why `fns` is redundant

1. **Local functions are already closed.** A `fix` body has type
   `Expr GL params pre fns (some (Self.top …)) r post .nil`: its variable context is `params`
   only, not the enclosing `Γ`. `R`, `wf`, `pre` and `post` of `Fn`/`fix` mention only
   `Env params`, and its join-point scope is `.nil`. So a local function never captures a
   variable, a path condition or a join point from where it is defined. Its value
   `fixFn ge wf body fe` depends only on the globals `ge` and on the earlier local functions
   `fe`, which are closed too. Semantically it is a global function that happens to be written
   in the middle of a statement.

2. **Information available to callers is the same.** `fnCall` and `gCall` have identical
   premises and continuations: the precondition `hpre`, the postcondition `f.post` added to the
   path condition of `k`, and the same `Handler.push`. A caller learns nothing more from a local
   callee than from a global one, so moving a function from local to global loses no
   decrease-proof information.

3. **The ordering discipline is the same.** A `fix` body may call the local functions defined
   before it and the globals. A `Globals.defn` body may call the globals before it. Lambda
   lifting a `fix` means inserting it into the global list just before the first global (or the
   main statement) that contains it. Its references to earlier local functions become
   references to earlier globals. There is no mutual recursion to break, because neither
   context allows it: mutual groups are already encoded as one function with a tag.

4. **The capture uses `fns` only as "define it, then call it once".** Every local call the
   capture emits is `$head (Expr.fnCall FnVar.here …)`: a fresh `fix` node immediately
   followed by a call of the innermost local function (`Capture/Elab.lean`, the `calleeCall?`
   and `specCall?` cases of the translation, `captureStx`; `Expr.ofFix` in `PCL/Lang/`).
   `FnVar.there` is generated only for global indices (`gvarStx` in `Capture/Translate/Context.lean`).
   So the de Bruijn structure of `fns` is never really used, and a callee called `k` times is
   **copied `k` times**. `Tests/Globals.lean` pins this: `useInlined` has 3 `fix` nodes for 3
   calls of `sumToI`, and size 19 against 11 for the version using globals. Nested
   `@[inlinable]` recursive callees multiply these copies.

5. **Proofs already treat both the same way.** `wf_agree` identifies a local callee and a
   global one in the same way: it finds `fixFn …` occurrences and rewrites them with
   `fixFn_unique` (`rewriteCallees`, `rewriteCalleesWith`, `rewriteHOCallees` in
   `Capture/Elab.lean`). `Globals.env_defn` unfolds a global to exactly such a `fixFn` term.

### What removing it would simplify

* `Expr` loses one index. `fix` and `fnCall` disappear, or `fnCall` merges into `gCall`.
  `Expr.eval` loses the `fe : FEnv fns` argument, and `fixFn`, `fixFn_eq`, `fixFn_unique`
  and `eval_fix` lose their `fe`.
* `PCL/Termination.lean` (`firstCall`, `fix_body_reaches_base`, …) and `PCL/Size.lean` lose a
  case and a parameter.
* A recursive program becomes "globals + a main statement that is one `gCall`" instead of
  `Expr.ofFix`, which is a local `fix` followed by `fnCall .here`. `PTerm.ofFix_run` and
  `Term.ofFix_eval` would be restated for that shape.
* Duplicate code (point 4) disappears, because each function is captured once.

### Reasons to keep it (the costs)

These are the reasons against removing `fns`. None of them is a soundness issue.

1. **The capture would need a collection pass.** `GL` is a *parameter* of `Expr`, fixed
   before the main statement is elaborated. Today the list of globals is computed up front
   (`globalsOf`/`collectGlobals`), but local nodes are created lazily at the call site
   (`calleeHeads`, `fixHead`, `specHead`). All of the following would have to be discovered
   first, given signatures, deduplicated and ordered:
   * the `@[inlinable]` recursive callees;
   * the mutual groups, as one tagged function each;
   * the functions that call themselves inside a function argument (`hoParts`, with tag and
     padding);
   * the **specialised copies** of higher-order functions. Each of these depends on the
     function argument at its call site, so the deduplication key is (callee, function
     argument up to α-equivalence), and the signature includes the lifted variables `ys`.

   Some errors that exist today would have to be revisited too, because they may be capture
   restrictions rather than language ones:
   * "`… calls itself inside a function argument; it cannot be a global function`"
     (`globalDefStx`);
   * "`calling such a function from another function is not supported`" (`fixHead`).

2. **`@[inlinable]` would mean something different to users.** Right now "`@[inlinable]`
   functions never end up in the global context". Many tests pin `fixes`, `nglobals`, `gcalls`
   and `size` (`Tests/Globals.lean`, `Tests/WhereFold.lean`, `Tests/While.lean`, …).
   * Without `fns`, a *non-recursive* `@[inlinable]` function is still inlined, as it is now.
   * A *recursive* `@[inlinable]` function has to go somewhere. If it is not tail-recursive,
     the only place is `GL`, and then `@[inlinable]` does nothing for it.
   * With recursive join points (part 2), a tail-recursive `@[inlinable]` function could be
     inlined *for real*, as a loop inside the caller that captures the caller's variables.
     That fits the word better than a closed copy does.

3. **Programs are less self-contained to read.** A local `fix` keeps a helper next to its use.
   This only affects how programs look.

4. **The index lists get longer.** Every call of a lifted function becomes an
   `FnVar.there^k .here` into a longer `GL`. This matters only for very large programs.

### Verdict on part 1

Removing `fns` is sound and simplifies both the metatheory and the output. It is worth doing
**if** the capture is restructured to collect local functions globally. Splitting "local
functions" between jpCtx and globalCtx, as the question proposes, is the natural target:

* **tail-recursive helpers / loops → recursive join points.** These capture the environment and
  need no lambda lifting. They require part 2.
* **general recursion (non-tail calls: `fib`, `ack`, tree recursion) → globals.**

Without part 2, *everything* goes to globals. That is still correct, but tail-recursive
inlinables lose any claim to being "inlined".

---

## 2. Should jpCtx take `R`?

### Short answer

**Yes, if** join points are meant to take over the loop-like uses of local functions (and of
`whileLoop`). A non-recursive join point is then just the case `R = emptyRelation`, as
non-recursive globals already are (`Globals` uses `emptyRelation` and `emptyWf.wf`). If join
points stay non-recursive, `R` adds nothing.

### What a recursive join point is

```
joinrec j (x : s) [R : Env Γ → s → s → Prop, wf : ∀ e, WellFounded (R e), P] := body in m
```

* `body` runs in `s :: Γ`, under `G e.2 ∧ P e.2 e.1`. It **keeps** the enclosing
  function `sf`, the outer join points `js`, and the enclosing variables. The current
  `whileLoop` body gets `sf = none` and `.nil`, and a `fix` body gets a fresh context.
* In `m` (the entry), `jump j p` needs only `P`.
* **Inside `body`**, and inside join points nested in it, `jump j p` is a back edge. It also
  needs `dec : ∀ e, G e → R e p cur`, where `cur` is the current value of `j`'s parameter.
  This is the same pattern as `fixSelfCall.dec`, with `Self.cur`.
* `R` should be indexed by the environment at the definition (`Env Γ → …`, with
  `wf : ∀ e, WellFounded (R e)`), as `whileLoop` already does. A closed `R`, as `fix` has,
  would force captured variables to be passed as parameters again.

### What changes in the definitions

* `JScope` needs an entry for "`j` seen from inside its own body", which knows how to read
  `cur`. For example, a constructor `self js s P Q R : JScope (s :: Γ) t` with `cur = e.1`;
  `wk` shifts it as usual. `bind` keeps its meaning as the entry seen from `m`.
* `JVar` gets a decrease predicate `JVar.dec : Env Γ → arg → Prop`: `True` for entries seen
  from outside, `R e.2 v e.1` for `self`, shifted by `wk`. `jump` gets a `dec` field.
* `JEnv` stores, for a `self` entry, a handler that requires the decrease proof, like
  `Handler`. `eval` at `joinrec` uses `(wf e).fix`, exactly as `whileLoop` does now.
  Evaluation stays total and structural apart from that `WellFounded.fix`.
* New lemmas `joinFn_eq` and `joinFn_unique`, analogous to `fixFn_eq`/`fixFn_unique` and
  `whileFn_eq`/`whileFn_unique`.
* `PCL/Termination.lean`: `JFirst` (the first recursive call through a join point) currently
  needs no recursion. Through a recursive join point it must iterate, by well-founded
  recursion on `R e`, until the body makes a self call or exits. This is the largest proof
  change.

### What it buys

1. **It subsumes `whileLoop`.** The loop
   `let v := while c do x := body from init in k` becomes

   ```
   join k (v) := K in
   joinrec L (x) := if c then body[ret p ↦ jump L p] else jump k x in
   jump L init
   ```

   `whileLoop` could then be removed or kept as a derived form. `whileFn_*` would follow from
   `joinFn_*`.

2. **Loops can do more.** They can exit early (`return`/`break`, by jumping to an outer join
   point), and they can call the enclosing recursive function (`fixSelfCall`, with the
   decrease measured against the unchanged `sf.cur`). Neither `whileLoop` nor `fix` allows
   either today.

3. **No lambda lifting for loops.** Captured variables stay variables, and the relation can
   mention them (for example `n - i` with `n` captured). Decrease proofs see the full path
   condition at the jump, including the facts known where the loop is defined. That gives
   `wf_dec` more context than a closed `fix` body gets.

4. **Any tail-recursive helper, in any call position, can be a join point.** Use a
   continuation join point for the rest (`join k … in joinrec …`), and replace `ret p` in the
   helper with `jump k p`. The helper's postcondition becomes `k`'s `P`. Only helpers with
   non-tail self calls need to be globals.

5. **A step towards constant stack.** `STACK_OVERFLOW.md` explains that the evaluator uses
   stack for every recursive call, tail calls included. Recursive join points do **not** fix
   this in the current closure-based evaluator: a jump still goes through `WellFounded.fix`.
   But they make tail recursion explicit in the syntax, which is what the explicit-stack
   evaluator sketched there needs in order to run jumps as a loop.

### What it costs

* The more complex `JScope`/`JVar`/`JEnv` described above, and the `Termination.lean` change.
* Capture work:
  * decide which helpers are tail-recursive in every self call;
  * rewrite the helper's `ret`s into jumps to the continuation;
  * get `R` and `wf` from Lean's relation for the helper, instantiated at the captured
    arguments;
  * prove agreement per recursive join point with `joinFn_unique`, as is done today for
    `whileLoop` via `whileFn_unique`.
* Choosing between "every join point carries `R`" (uniform, with `emptyRelation` for
  non-recursive ones, which makes proof terms slightly larger) and a separate `joinrec`
  constructor that shares `JScope` (smaller terms, one more case everywhere). The uniform
  version mirrors `Globals` and is the simpler invariant.

### Verdict on part 2

Give jpCtx `R` (environment-indexed, with `wf : ∀ e, WellFounded (R e)`, and a decrease proof
only on back edges) **together with** removing fnCtx. The two changes support each other:

* local functions split into *recursive join points* (tail recursion; they capture the
  environment and can reach outer join points and the enclosing function) and *globals*
  (everything else, closed, shared once);
* `whileLoop` and local `fix` become redundant.

If only one change is made, removing fnCtx in favour of globals is the cheaper one. It is
purely a restructuring of the capture, and the metatheory only gets smaller. Adding `R` to
join points without removing fnCtx would leave three overlapping loop mechanisms: `fix`,
`whileLoop` and `joinrec`.
