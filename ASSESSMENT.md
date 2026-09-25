# A toy language for capturing well-founded Lean functions: proposals and C-output assessment

All code is under `RequestProject/WFLang/`, and `RequestProject/WFLang.lean` imports all of it. The designs described here live in `RequestProject/WFLang/Wrapper/` (see `STRUCTURE.md` for the directory layout).
It builds without `sorry`. The theorems depend only on the standard axioms
(`propext`, `Quot.sound`).

## 1. The language (shared by every proposal) — `Common/Types.lean`, `Wrapper/Expr.lean`

* Types: `Ty := nat | bool`, interpreted as `Nat` / `Bool`.
* Intrinsically typed expressions `Expr s Γ τ`:
  * de Bruijn variables
  * literals
  * `+ - * / %`, `<`, `≤`
  * **`bool_eq`** (`BinOp.beq t`, at every type)
  * `&&`, `||`, `!`
  * **`if-then-else`**
  * `call`, the recursive self call, whose arguments are typed by the signature `s`.

  A body is `Expr s s.args s.ret`.
* Reference semantics `Expr.evalWith o`. This is plain structural recursion, with the recursive
  call answered by an oracle `o`.
* Soundness specification `IsFix body f := ∀ x, f x = body.evalWith f x`. In words: `f`
  satisfies the recursive defining equation.

**No fuel, no measure and no `AccT` appear in `Expr`, in any `Term`, or in any evaluator.**
Every program carries a relation `R`. Its well-foundedness `WellFounded R` and the
"recursive calls decrease" certificate are ordinary `Prop`s.

Every proposal provides `Term s`, `Term.run`, the curried `Term.eval`, and three proved theorems:

| theorem | meaning |
|---|---|
| `Term.run_isFix` | the evaluator satisfies the defining equation (sound) |
| `Term.isFix_unique` | any `f` satisfying the equation equals the evaluator (unique ⇒ it is *the* function) |
| `Term.eval_eq` | the curried form: `IsFix body (uncurry f) → Term.eval t = f` |

Termination needs no separate theorem. Every evaluator is a total Lean `def`: no `partial` or
`unsafe`, and no fuel. The kernel accepts it only because of the `Prop`-level well-foundedness
proof stored in the term.

## 2. `#lean_wf_func_to_term` — `Wrapper/Elab.lean`

```lean
def gcd (m n : Nat) : Nat :=
  if n = 0 then m else gcd n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

open WFLang Guarded       -- or GuardedAcc / FreeCall / Checked
def gcd_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, Term.eval gcd_term m n = gcd m n := by wf_agree
```

The term elaborator works in four steps:

1. It reifies the right-hand side of `gcd.eq_def` into an `Expr`.
2. It takes the well-founded relation and its `WellFounded` proof that **Lean itself** built for
   `gcd` (from `WellFounded.fix` / `WellFounded.Nat.fix`), and pulls them back along the
   argument packing.
3. It extracts the decreasing proofs at every recursive call site of `gcd`. This includes the
   user's `decreasing_by` proof, i.e. `Nat.mod_lt …`.
4. It uses those proofs to discharge the certificate of the proposal named by the expected type.

`wf_agree` proves agreement through `Term.eval_eq`: by uniqueness, it is enough that `gcd`
satisfies the equation of the reified body, and that follows from `gcd.eq_def`.

`Examples/Wrapper.lean` captures `gcd` with every proposal and proves `gcd_agree` for each of them. It
also captures `digitSum`, `isPow2` (Bool result, `&&`, `==`) and `sumTo`. It checks at runtime
that all evaluators agree with the native `gcd`, using `#guard_msgs` checks inside the build.

## 3. The proposals

The proposals differ in two ways: how the `Prop` certificate is phrased, and how the recursion
is driven.

| # | file | `Prop` certificate | recursion driver |
|---|---|---|---|
| 1 | `Wrapper/Guarded.lean` | `Guarded.Dec R body : ∀ x ih, (sem R x ih x body).1`: a guard/value semantics `sem : Expr → (G : Prop) ×' (G → τ)` (an induction-recursion encoding) says that every call *actually reached* is `R`-smaller | `termination_by` on `R` (through the `WFBox` wrapper) |
| 2 | `Wrapper/FreeCall.lean` | `FreeCall.Dec R body : ∀ x, (evalC x body).AllCalls (R · x)`: the body is first interpreted into a **call tree** (free monad `Comp`), and every `call y` node satisfies `R y x` | `WellFounded.fix` + a tree interpreter `Comp.interp` |
| 3 | `Wrapper/GuardedAcc.lean` | same as 1 | `Acc.rec` on the ordinary **`Prop`** `Acc R x` (obtained from `WellFounded`; *not* `AccT`) |
| 4 | `Wrapper/Checked.lean` | `Contracting R body`: the extensional property "the body only looks at `R`-smaller calls". Needs `DecidableRel R` | `termination_by`, but every call first **decides `R y x` at runtime** |

Proposal 4 is included as a contrast. Its certificate does not say *which* calls are made, so
the evaluator must check the relation at runtime.

## 4. Assessment of the generated C

The C files produced by `lake build` are copied to `c_output/`. Function names below are the
exported C symbols.

### Reference: native `gcd` (`c_output/Examples.c`, `lp_RequestProject_gcd`)

```c
x_4 = lean_nat_dec_eq(x_2, x_3);            // n == 0 ?
if (x_4 == 0) { x_5 = lean_nat_mod(x_1, x_2); x_1 = x_2; x_2 = x_5; goto _start; }
else { return x_1; }
```

### What the programs compile to

`gcd_term` for proposals 1, 2 and 3 compiles to **one and the same static object**:
`ExGuarded_gcd__term___closed__13`. It is just the syntax tree `ite (beq n 0) m (call n (m % n))`.
The `R`, `wf` and `dec` fields are erased completely, and the one-field structure is unboxed to
its `body`.

`ExChecked_gcd__term` is different. It is a pair `(body, decR)`, and `decR` is a real closure:

```c
uint8_t ExChecked_gcd__term___lam__0(x_1, x_2) {   // decides R y x
  x_5 = lean_ctor_get(lean_ctor_get(x_1,1),0);     // y.2.1
  x_6 = lean_ctor_get(lean_ctor_get(x_2,1),0);     // x.2.1
  return lean_nat_dec_lt(x_5, x_6);                // the measure comparison, at runtime
}
```

### Proposal 1 — Guarded (`c_output/Guarded.c`)

```c
Guarded_Term_run(s, t, x):
  ih  = closure(Term_run___lam__0, s, t)          // recursive call handle
  p   = Guarded_sem___redArg(s, x, ih, Γ, x, t)   // builds a tree of closures
  return lean_apply_1(lean_ctor_get(p,1), lean_box(0));   // run it; the proof is lean_box(0)
Guarded_sem: case call  -> closure(lam__5): ih(args(box(0)), box(0))
             case ite   -> closure(lam__4): if cond(box(0)) then a(box(0)) else b(box(0))
```

* There is no counter, no measure and no `Acc`. Every proof becomes `lean_box(0)`.
* This is the **"delayed"** style. `sem` returns the pair `⟨G, v⟩`. `G` is erased to
  `lean_box(0)`, and `v : G → τ` becomes a closure whose argument is the erased proof. So every
  step builds a small closure tree and then forces it.
* A small leftover artefact: the pair `(lean_box(0), closure)` is still allocated, with a dummy
  first field. It carries no information.

### Proposal 3 — GuardedAcc (`c_output/GuardedAcc.c`)

```c
Acc_recC___at___WFLang_GuardedAcc_Term_runAcc_spec__0___redArg(s, t, x)   // no Acc argument
  -> identical body to Guarded_Term_run
```

The code generator compiles `Acc.rec` through `Acc.recC` and drops the accessibility proof. The
specialised function has **no parameter for the `Acc` proof**. This is exactly why a `Prop`
`Acc` is not fuel, whereas `AccT` would be: `AccT` would be a runtime tree that gets
pattern-matched.

### Proposal 2 — FreeCall (`c_output/FreeCall.c`)

```c
WellFounded_fixC___at___FreeCall_Term_run_spec__0___redArg(s, t, x):
  ih = closure(...recursive...);
  c  = FreeCall_evalC___redArg(s, Γ, x, t);       // builds the call tree (free monad)
  return FreeCall_Comp_interp___redArg(ih, c);
Comp_interp(ih, c):                               // a loop (goto _start)
  pure v     -> return v
  call y k   -> v = ih(y, lean_box(0)); c = k(v); goto _start;
```

* There is no counter or measure. The `AllCalls` proof becomes `lean_box(0)`.
* `WellFounded.fix` is compiled as the native recursive `WellFounded.fixC`.
* This is the **"free data structure"** style. At runtime the body is materialised as
  `Comp.pure` / `Comp.call y k` nodes, with continuations as closures. The interpreter then
  consumes them.

### Proposal 4 — Checked (`c_output/Checked.c`)

```c
Checked_Term_run___lam__0(decR, x, retTy, s, t, y):
  if (!unbox(lean_apply_2(decR, y, x)))  return Ty_default(retTy);   // dead branch
  else                                   return Checked_Term_run(s, t, y);
```

At **every** recursive call, the evaluator calls the decision procedure for `R y x`. For `gcd`
that is `y.2 < x.2`, i.e. it re-evaluates the termination measure. It also keeps a dead
"default value" branch. This is a fuel-like runtime artefact: it is not a counter, but it is
termination bookkeeping that runs at runtime. It also needs `DecidableRel R`, which the other
proposals do not.

### Verdict

| proposal | fuel / counter | `Acc`/proof objects at runtime | measure evaluated at runtime | runtime shape |
|---|---|---|---|---|
| 1 Guarded | **none** | none (`lean_box(0)`) | **no** | delayed closures (`G → τ`) |
| 2 FreeCall | **none** | none (`lean_box(0)`) | **no** | free-monad call tree + interpreter loop |
| 3 GuardedAcc | **none** | none (no `Acc` parameter at all) | **no** | same as 1 |
| 4 Checked | none | none | **yes** (`decR` closure: `lean_nat_dec_lt` each call) + dead default branch | direct interpreter + runtime guard |

**Proposals 1, 2 and 3 generate no fuel-like data structures.** Their C code is a plain
recursive interpreter, and the recursive call is a direct call:

* 1 and 3 add only delayed closures;
* 2 adds only the free-monad nodes.

Proposal 4 is the only one that does runtime termination bookkeeping.

Differences from native code that remain in 1–3, observed in the C above:

* **Interpretive overhead.** The code walks the syntax tree and allocates closures or
  call-tree nodes per step.
* **The context list `Γ` is passed at runtime.** It is a type-index list used by `Var.get`.
  It is ordinary data, not fuel.
* **No tail-call loop across recursive calls.** Native `gcd` compiles to a `goto` loop. The
  interpreters perform real recursion, with stack depth proportional to recursion depth, like a
  non-tail-recursive native function. `Comp.interp` in proposal 2 is itself a loop, but the call
  to `ih` inside it is a genuine recursive call.

## 5. Limitations

* The reifier handles `Nat`/`Bool` arguments and results, and `if`/`ite`/`dite`/`cond` whose
  branches do not use the hypothesis. It handles `=`, `≠`, `<`, `≤`, `>`, `≥`, `∧`, `∨`, `¬`,
  `==`, `&&`, `||`, `!`, `+ - * / %`, literals, and direct self-calls. *(Update: definitions by
  pattern matching on `Nat`, functions with fixed parameters, structurally recursive functions
  and calls of non-recursive helper functions are now supported, see `LANGUAGES.md`, section
  "Features added later". Calls of other recursive functions are supported by the grammars
  `PCL`, `Tail` and `Meas`, not by these wrapper designs.)*
* The certificate tactic has to close the goals "the arguments of this call are `R`-smaller".
  It uses the extracted call-site proofs, then falls back to `simp_all`, `omega` and
  `decreasing_tactic`.
* All the certificates quantify over *all* answers of earlier recursive calls. So
  nested recursion whose decrease depends on the value returned by an inner call cannot be
  certified.
* Proposal 4 additionally needs `R` to be decidable, which the tactic establishes with `dsimp`
  followed by `infer_instance`.
