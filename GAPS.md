# Well-founded functions and `#lean_wf_func_to_term`: what is supported, and what is left

Every example below is a real Lean definition in the test suite (`RequestProject/WFLang/Tests/`).
Each captured function has an agreement theorem proved by `wf_agree` and a runtime check
(`#guard_msgs`); each function that is still rejected has its error message pinned by
`#guard_msgs`. The test files are part of the default build, so if any of this changes,
`lake build` fails.

The soundness argument is the same for every construct. The agreement proof (`wf_agree`) relies
only on the uniqueness of the solution of each recursive equation (`fixFn_unique` for global
functions, `joinFn_unique` for loops) and on `f.eq_def`. The
well-founded relation and the decreasing proofs are still the ones Lean built, pulled back to
the program's parameters (or combined from Lean's relations, for the two new encodings below:
mutual recursion and recursion through a function argument).

The language stays in **strict A-normal form**: arithmetic, comparisons, `bool_eq`, `&&`, `||`,
`!`, pairs and list operations are call-free `PExpr`s; the result of every call is bound to a
new variable (`fixSelfCall` for a recursive call, `gCall` for a call of a global function); and
the compound statements occur only in tail position: `ite` (case), `join` and `joinrec` (a
loop). A Lean `if`/`match` with a call in non-tail position is captured with a join point
(`join j (v) := rest in if c then (…; jump j a) else (…; jump j b)`, see `GRAMMAR.md`; the rest
of the computation is copied into both branches instead when a call in scope has a
postcondition). A call of a tail-recursive `@[inlinable]` function (and of a specialised
tail-recursive function, such as the loop of a `for`) in any position becomes a loop:
`join K (v) := k in joinrec L (x) := body in jump L args`; other recursive functions are global
functions, called with `gCall`.

## 1. Capture-only gaps (the grammar could already express them): all closed

| example (`Tests/GapFunctions.lean`) | shape | how it is captured |
|---|---|---|
| `callInInnerIf` | `1 + (if c then f a else f b)` | the continuation becomes a join point, and both branches of the `ite` jump to it |
| `callInAnd` | `!(c && f n)` in non-tail position | `a && b` becomes `if a then b else false` (`\|\|` likewise), then as above |
| `boolMatch` | `match b with \| true => … \| false => …` | `Bool.casesOn` is the test `b`, branches swapped |
| `litPatterns` | `\| 1 => … \| 5 => … \| n+2 => …` | the casts (`▸`) of the unfolded matcher are erased; each literal is an `n = k` test |
| `matchEq` | `match h : n % 3 with …` | the matcher is beta-reduced, the `Eq.ndrec` erased |

## 2. Operators: all closed

* **By translation alone**: `Nat.pred n` ↦ `n - 1`, `a != b` / `bne` ↦ `!(a == b)`, `min`/`max`
  ↦ `if a ≤ b then … else …`, `a ∣ b` ↦ `b % a == 0` (`usesLibFns`, `usesBne`, `usesMin`,
  `usesDvd`).
* **New operators** (`BinOp`/`UnOp` in `Core/Types.lean`): `^`, `<<<`, `>>>`, `&&&`, `|||`, `^^^`,
  `xor` on `Bool`, `Nat.gcd`, `Nat.lcm`, `Nat.log2` (`usesPow`, `usesShift`, `usesXor`,
  `usesLibFns`).

## 3. Other types: all closed

| example | what was added |
|---|---|
| `intDown`, `intSteps` | `Ty.int`, with `+ - * / %`, `<`, `≤`, negation, `Int.toNat`, `Int.natAbs`, the cast `Nat → Int`; Lean's relation (`termination_by n.toNat`) is reused |
| `fibPair`, `swapSteps` | `Ty.prod s t`, pairing, projections, `match` on pairs; pairs as parameters and results |
| `listSum`, `listRev`, `listPairs`, `listHalve` | `Ty.list t`, `[]`, `::`, `++`, `head`, `tail`, `isNil`, `length`; `match` on lists (also nested patterns) becomes `isNil` tests; structural recursion on lists uses the length |
| `boundedRes`, `nestedBound` | **postconditions**: a subtype result `{r // Q r}` becomes the postcondition `Q` of the function. Each `ret` proves it, and after each recursive call it is added to the path condition, so a decrease proof may use it (`nestedBound`'s second call needs `r ≤ n - 1` from the first). `PTerm.run_post`: every run satisfies it |

## 4. Higher-order code

| example | status | how |
|---|---|---|
| `forRange`: `for i in [0:n] do s := s + i` | captured | the `for` loop (in `Id`, over a range, always continuing) is rewritten into `WFLang.rangeLoop` (`Core/Loops.lean`), a first-order tail-recursive well-founded function whose function parameter is then *specialised* to the loop body: a loop (recursive join point) with measure `stop - i` |
| `usesFold`: `Nat.fold n (fun i _ acc => …) init` | captured | rewritten into `rangeLoop` in the same way |
| `Tco.iter`, `Tco.hyperLoop` (function parameters) | captured when specialised | `#lean_wf_func_to_term (Tco.iter Tco.mc91)` captures the copy specialised to a closed function argument; a call with a function argument inside another function is specialised at the call site, the free variables of the argument becoming extra (fixed) parameters (`useIter`: `Tco.iter (fun x => x + k) n 0`) |
| `Tco.hyperWhile` (a `for` loop whose body calls `hyperWhile`), `Tco.hyperTCO` (`hyperLoop (hyperTCO n a) …`), `Tco.ack2` (`ackInner (ack2 m)`, a function result), `loopRec`, `foldRec`, `viaApplyN` | captured | **recursion through a function argument**, see below |
| `useHyperWhile`, `sumHyperTCO` | captured | functions calling the above: their node is called with tag `0` (and padding) |
| `underLambda`: a call under `fun` in `List.map` over `List.attach` | captured | `List.map` is the grammar statement `Expr.map`; the membership proofs of `attach` are erased and become facts of the path condition used only by the decrease proofs (`Tests/Map.lean`, `underLambda_agree`); see §6 |

**Recursion through a function argument.** When `f` calls a recursive function `g` with a
function argument that calls `f` again, `f` and the copy of `g` specialised to that argument are
captured as **one** global function. Its parameters are
`tag :: f's parameters ++ g's lifted variables ++ g's parameters` (the part not used by a call
is padded with default values); `tag = 0` runs `f`'s body and `tag = 1` runs `g`'s. Its relation
is `WFLang.hoRel` (`Core/Types.lean`, proved well-founded by `hoRel_wf`, no axioms), built from
Lean's relations `Rf` of `f` and `Rg` of `g`, and a predicate `Call x k`, read off the function
argument: "the function argument, at the lifted variables `k`, may call `f x`":

* `f x' < f x` if `Rf x' x`;
* `g y < f x` (entering `g`) if every call `f x'` that the function argument may make is
  `Rf`-below `x`. This is where the path condition of `f` is used: e.g. for `hyperWhile` it is
  `∀ r, (n - 1, a, r)` is below `(n, a, b)`, true because the `match` gave `n ≠ 0`;
* `g y' < g y` if they have the same lifted variables and `Rg y' y`;
* `f x' < g y` if the function argument of `g y` may call `f x'` (true at every call, by
  construction).

The agreement proof shows that the node computes
`F (t, xs, ys, zs) = if t = 0 then f xs else g (spec ys) zs`, by unfolding `f` or `g` once.

## 5. Other recursion schemes: closed

| example | how |
|---|---|
| mutual recursion: `More.Mutual.isEven`/`isOdd` (structural), `downA`/`downB` (well-founded, `termination_by`), `mod3a`/`mod3b`/`mod3c` (three functions) | one global function with a tag parameter selecting the member; a call of the `i`-th member is a recursive call with tag `i`; the relation is Lean's relation for the group (on the `PSum` domain of `f._mutual`), pulled back along `(i, xs) ↦ PSum.inl/inr xs` (for structural groups: the common recursive parameter decreases) |
| a proof precondition: `Tco.boom (n) (h : Safe n)` | a global function carries a precondition `pre`, which is part of the path condition of its body; every call proves it for its arguments. The program is a `PTerm` with precondition `Safe n`, run as `PTerm.run boom_term (n, ()) h` |

## 6. Lifted since the last assessment

These were listed as unsupported and are now captured, with agreement proofs
(`Tests/NewTypes.lean`, `Tests/ListCombinators.lean`, `Tests/MutualSignatures.lean`,
`Tests/LeanWhile.lean`):

| example | how |
|---|---|
| `Option`, `Sum`, `Except`, `String`, `Char`, `Array`, `Unit` (parameters, results, intermediate values) | new object types in `Ty`, with their constructors, tests and projections as `PExpr` operators; `match` on them is a test (`isSome`, `isLeft`, `isOk`) and projections (`getD`, `getLeft`, …) |
| `match` on `Int` (`.ofNat` / `.negSucc`) | the test `0 ≤ i` and the casts `toNat`, `(-i - 1).toNat` |
| `l.getD i d`, `l[i]!`, `l[i]?`, `take`, `drop` | `PExpr` operators (`getElem?`, `take`, `drop`) and simp lemmas relating `getD`/`get!` to `getElem?` |
| calls under a binder in `List.foldl`, `foldr`, `any`, `all`, `contains`, `elem`, `find?`, `filter`, `for x in l` | rewritten into the first-order recursive functions of `Core/ListLoops.lean` (`listFoldl`, …), which are specialised to their function argument like `rangeLoop`; a call of the captured function inside that argument is recursion through a function argument (`ListComb.fsum`, `anyRec`) |
| `decide (∀ i < n, P i)`, `if ∃ x ∈ l, P x then …` | `listAll` / `listAny` over `List.range n` or `l` |
| `for` with `break` or an early `return`; ranges with a step `[a:b:s]` | `rangeLoopN f size step start init` / `listLoopN`, whose body returns a `ForInStep`; the case split on the body is pushed into its branches, so no `ForInStep` remains in the program |
| `return` inside Lean's `while` (`findDiv`) | the loop state holds an `Option`, now an object type |
| mutual recursion with different parameter or result types (`mA : Nat → Nat` / `mB : Nat → Bool → Nat`; `rA : Nat → Nat` / `rB : Nat → Bool`) | the global function takes the tag, then the parameters of all members one after the other (padded with default values); different results are a tuple with one component per member; for structural groups the measure is the recursive parameter of the member selected by the tag |
| `nestMin` (a decrease that Lean's proof no longer closes after `min` becomes an `if`) | the decrease tactic splits the `if`s of the translated goal and calls `omega` |

## 7. Still not supported

* **User structures and inductive types, `Fin n`, `UInt8`…`UInt64`, `Float`, `BitVec`**: not in
  `Ty` (`Tests/Unsupported.lean`).
* **Loops that use their membership proof and may stop early** (`Unsupported.forMemRet`):
  recursive calls whose decrease needs `x ∈ l` are captured in `List.map`, and in `List.foldl`,
  `any`, `all` over `l.attach` and `for h : x in l` loops whose body always continues (the
  `foldl` statement, `Tests/AttachCombinators.lean`), but not in such a loop with `break` or
  `return`.
* **Function-valued parameters without a known argument**, e.g. `#lean_wf_func_to_term Tco.iter`
  on its own: the program would need function types in `Ty`. Capture a specialised copy instead.
* Restrictions of recursion through a function argument: one specialised function per captured
  function (a second, different loop whose body calls `f` is rejected); `f` and `g` must have
  the same result type; no proof parameters or subtype result; the calls of `f` inside the
  function argument may not be under a further binder.
* Mutually recursive functions with proof parameters or subtype results.
* **Lean's own `while` loops** are captured through `lean_while_to_wf`
  (`Capture/LeanWhile.lean`, `Tests/LeanWhile.lean`), including `return` inside a loop. Still
  rejected: recursive functions containing a loop (`LeanWhileRejected.recLoop`), and
  `ackWhile` / `ackNoDataStructure` (no measure: the stack needs a multiset order).
* **Not well-founded definitions**: `partial def`, and `partial_fixpoint` definitions for which
  none of the measures the capture tries decreases (`Unsupported.loopUp`); a `partial_fixpoint`
  definition with such a measure is captured (`Tests/PartialFixpoint.lean`). Lean
  builds them without any termination proof (opaque implementations), so
  there is no relation or decreasing proof to reuse, and the evaluator of `PCL` is total. They
  can be captured after being rewritten with the **well-founded `while`** (`wf_while … termination_by μ`, or
  `WFLang.whileWF` with an invariant, `Core/While.lean`), as well-founded recursion, or as a
  bounded `for` loop.
* **Calls inside a well-founded `while` loop**: the test and the body of a captured loop must be
  call-free (`WhileEx.callInBody` is rejected).
