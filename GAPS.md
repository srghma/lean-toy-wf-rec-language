# Well-founded functions that `PCL` / `#lean_wf_func_to_term` do not handle, and what it would take

Every example below is a real Lean definition in `RequestProject/WFLang/Tests/Gaps.lean`.
Next to each one, a `#guard_msgs` block records what the capture does with it today. The file is
part of the default build, so if any of these behaviours changes, `lake build` fails.

The gaps fall into two groups:

* Some limits come only from the **capture** (`Capture/*.lean`). The `PCL` grammar can already
  express these functions; the elaborator just does not recognise the Lean term shape.
* Others need a **grammar extension**: new operators, types or constructs in `Core/` and `PCL/`.

In either case the soundness argument stays the same. The agreement proof (`wf_agree`) only
relies on the uniqueness of the `fix` solution (`fixFn_unique`) and on `f.eq_def`. The well-founded
relation and the decreasing proofs are still the ones Lean built.

## 0. Fixed in this session (they were bugs, not design limits)

| example | before | cause | fix |
|---|---|---|---|
| `fixedMid (n k)`, `fixedMid3 (n k acc)`: a fixed parameter that is not the first one | capture failed with a spurious "failed to prove termination" | Lean 4.28 moves fixed parameters in front of the `WellFounded.fix` even when they are not a prefix, but the capture assumed they were the first ones | the capture now reads which parameters are packed into the fixpoint argument. For a non-prefix layout it uses the new relation `WFLang.fixedAtRel` and its well-foundedness proof `fixedAtRel_wf` (`Core/Types.lean`) |
| `whereHelper` (non-recursive, calls its recursive `where go`) | capture fine, but `wf_agree` failed | `go` is named `whereHelper.go`, and the "auxiliary definition of `fn`" test was a plain prefix test, so the function was taken to be recursive itself | only internal auxiliaries (`fn._unary`, …) are followed now |
| `haveProof`: `if h : n = 0 … else have : n/2 < n := … h …; f (n/2)` | rejected | the `dite` branch mentions `h`, but only inside the `have`'s proof | `let`/`have` are inlined before the "does the branch use `h`?" check |

All of these now have agreement theorems and runtime checks in `Tests/Gaps.lean`.

## 1. Capture-only gaps: `PCL` can express them, the elaborator must learn the shape

| example | error today | how to support it | effort |
|---|---|---|---|
| `callInInnerIf`: `1 + (if c then f a else f b)`, a call inside a branch of a **non-tail** `if`/`match` | recursive call in an unsupported position | in `lift`, when a control node contains a call, emit `Expr.ite` and put the continuation `k` into both branches (or bind the `if` result in a small join `fix`). The path conditions then give the decrease proofs exactly as for tail `if`s | small |
| `callInAnd`: `!(c && f n)` in non-tail position | same | desugar `a && b` to `if a then b else false` (and `a \|\| b` likewise), then use the item above. Tail `&&`/`\|\|` already work this way | small |
| `boolMatch`: `match b with \| true => … \| false => …` | same | the matcher unfolds to `Bool.casesOn b (false-branch) (true-branch)`. Recognise it in `branch?` as the test `.bool b`, with the branches swapped | small |
| `litPatterns`: patterns `\| 1 => … \| 5 => … \| n+2 => …` | same | the matcher unfolds to `Nat.casesOn x … (Nat.casesOn n … (if h : n = 3 then h ▸ … else …))`. The `dite` branch uses `h` only in a cast (`▸`) of the motive. Erase that cast, since the motive is constant here, and then it is an ordinary `n = 3` test | small–medium |
| `matchEq`: `match h : n % 3 with …` | same | the matcher unfolds to `(fun x₁ => if h : x₁ = 0 then Eq.ndrec … else …) (n % 3) rfl`, i.e. a `dite` plus an `Eq.ndrec` that transports the named equation. Beta-reduce, then erase the `Eq.ndrec` as above | small–medium |

(Checked by printing the unfolded matchers of these three functions.)

## 2. Operators missing from the grammar

Some can be handled **by translation alone**, with no grammar change:

| Lean | translation |
|---|---|
| `Nat.pred n` (`usesLibFns`) | `n - 1` |
| `a != b`, `bne` (`usesBne`) | `!(a == b)` |
| `xor a b` on `Bool` (`usesXor`) | `!(a == b)` |
| `min a b` / `max a b` (`usesMin`) | `if a ≤ b then a else b` / `if a ≤ b then b else a` (`PExpr.ite`) |
| `a ∣ b` as a condition (`usesDvd`) | `b % a == 0` (true also for `a = 0` since `b % 0 = b`) |

Others need **new `BinOp` constructors**: an evaluation clause, one line in `natBin?`, and a
`simp` lemma for `wf_agree`.

* `a ^ b` (`usesPow`), and `>>>`, `<<<` (`usesShift`), `&&&`, `|||`, `^^^`.
* Library functions such as `Nat.gcd` (`usesLibFns`), `Nat.log2`, `Nat.sqrt`. You can add each
  one as an operator. The general route is to treat recursive library functions as callees, the
  way user functions are handled already (a nested `fix` built from their `eq_def` and Lean's
  well-founded relation). Right now library constants are deliberately never inlined or captured.

## 3. Types other than `Nat` and `Bool` (grammar extension)

| example | what is needed |
|---|---|
| `intDown : Int → Int` | a `Ty.int` with its operators and comparisons. Lean's relation (`termination_by n.toNat`) is reused unchanged |
| `fibPair : Nat → Nat × Nat` | a product type `Ty.prod s t` with a pair constructor and projections in `PExpr`. This also allows returning several results, e.g. the state of a loop |
| `listSum : List Nat → Nat` | `Ty.list t` with `nil`, `cons`, and a `match` on lists turned into a branch (`isNil`, `head`, `tail`). The relation is Lean's `sizeOf`-based one, pulled back as now |
| `boundedRes : Nat → {r // r ≤ n}` | the case where a termination proof needs a *property of a recursive result*. A plain `.val` is easy, but using `r.2` in a decrease proof needs a `fix` that carries a postcondition `post : Env params → ret → Prop`, proved at every `ret` and assumed for each `fixSelfCall` result in its continuation's path condition. That is a real extension of the grammar and of the evaluator's typing. Soundness still follows from `WellFounded.fix` |

## 4. Higher-order code

| example | how it could be supported |
|---|---|
| `forRange`: `for i in [0:n] do s := s + i` | unlike `while`, a range `for` terminates. Desugar it into a nested `fix` over `(i, state…)` with measure `n - i`. With several mutable variables this needs products (§3) or one parameter per variable |
| `usesFold`: `Nat.fold n (fun i _ acc => …) init` | same technique: when the lambda argument is known, specialise the combinator to a nested `fix` |
| `underLambda`: recursive call under `fun` in `List.map` over `attach` | needs lists (§3) plus `map`/`sum`, or lambda lifting into a nested `fix` that iterates over the list |
| uploaded `Tco.iter`, `Tco.hyperLoop`, `Tco.ack2` (function-valued parameters; rejected in `Tests/Sources.lean`) | *specialisation / defunctionalisation*: when every call site passes a known function, e.g. `iter mc91`, capture a copy of `iter` with that function inlined. Fully general function-valued parameters would need function types in `Ty` (a higher-order `PCL`) |

## 5. Other recursion schemes

| example | how it could be supported |
|---|---|
| mutual recursion (`More.Mutual.isEven`/`isOdd`, rejected in `Tests/MoreChecks.lean`) | Lean defines the pair as one `WellFounded.fix` on a `PSum` domain. Encode it as a single `fix` with an extra tag parameter selecting the function, with Lean's relation pulled back along `tag, args ↦ PSum.inl/inr args`. Alternatively add a `mutual fix` node with an index. If the functions have different signatures, this needs products or padding |
| functions with a proof precondition, e.g. uploaded `Tco.boom (n) (h : Safe n)` | let a `Term` carry a precondition `pre` as the path condition of the top-level `fix` body, instead of `True`. `Term.eval` then takes a proof of `pre x`, and the decrease proofs may use it |

## 6. Not supportable: these are not well-founded definitions

* `while` loops (`Tco.ackWhile`, `Tco.diagonalWhile`, `Tco.mc91While`, `isqrt`, …), `partial def`,
  `partial_fixpoint`. Lean builds them without any termination proof (`Lean.Loop.forIn` / opaque
  implementations), so there is no relation or decreasing proof to reuse. They can only be
  captured after being rewritten as well-founded recursion, as was done for `hyperWhile` in
  `Tests/SourceProofs.lean`.
