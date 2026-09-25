# Other ways to design PCL, and what happens when a measure is wrong

## 1. The question about `Meas`: error or default value?

The current `Meas` evaluator (`RequestProject/WFLang/Meas/Lang.lean`, `measFix`) **returns the
default value** of the result type (`0` for `nat`, `false` for `bool`) when a recursive call does
not decrease the measure. It reports nothing, and the computation carries on with that made-up
value. This is now proved on an example
(`ExMeasWrong.gcdWrong_4_6` in `RequestProject/WFLang/Designs/Examples.lean`): `gcd` written in
`Meas` with the wrong measure `(m, 0)` evaluates `gcd 4 6` to `0`, while `gcd 4 6 = 2`.

For captured functions this never happens. The capture copies the measure from `termination_by`,
and the agreement proof shows that the check always succeeds. But the check lives in the evaluator,
not in the language, so nothing prevents a hand-written program with a bad measure. So your
criticism is correct:

* the measure is part of the program, not chosen by the person running it;
* the syntax contains no proof that the measure is correct;
* a wrong measure is only noticed at run time, and then it is hidden behind a default value.

The designs below fix this in three different ways. Each uses one of three answers to *"what
happens if the measure is exhausted / wrong?"*:

| answer | where | what the user sees |
|---|---|---|
| it cannot happen: an evaluator without a proof cannot be called | `PCL`, `PCL-VC`, `PCL-Ext` `eval` | the program cannot be run until you supply a proof, and for a wrong measure no proof exists (`gcd_wrong_not_certified`) |
| an **error** that says which call failed | `PCL-Ext` `runChecked` | `Except.error (.notDecreasing callee caller)`, e.g. `.notDecreasing (6,0) (4,0)` for `gcd 4 6` with the wrong measure (`gcd_wrong_error`) |
| an **error** "out of fuel" | `PCL-Ext` `runFuel` | `Except.error .outOfFuel`; the fuel is computed from a proved-correct measure, so it never runs out (`runFuel_measure`) |
| a silent default value | `Meas` (old) | a wrong result |

We recommend errors or proofs, never default values.

## 2. The design space

A language with well-founded recursion has to decide three things:

1. **Who chooses the termination argument** (relation or measure): the program (in the
   syntax), or whoever runs it (from outside).
2. **Where the proof that it is correct lives**: on every call, once per program, or nowhere
   (checked at run time).
3. **What the evaluator does when the proof is missing or wrong**: this cannot happen, error, or
   default value.

| design | file | termination argument chosen by | proof lives | wrong argument ⇒ |
|---|---|---|---|---|
| `PCL` (existing) | `PCL/Lang.lean` | the program (`fix … R wf …`) | on every `call` (`dec`), using the path condition `G` | cannot be written (type error) |
| **`PCL-VC`** (new) | `Designs/VC.lean` | the program (`fix … R wf …`) | once per program: `Expr.VC`, one `Prop` | `VC` is false, so the program cannot be `Certified` |
| **`PCL-Ext`** (new) | `Designs/Ext.lean` | **outside**: a measure `μ` passed to the evaluator | once per (program, measure): `Program.Decreases p μ` | certified `eval` cannot be called; `runChecked` returns an **error**; `runFuel` returns `outOfFuel` |
| `Meas` (existing) | `Meas/Lang.lean` | the program (in-language measure) | nowhere; checked at run time | **silent default value** |
| `Tail` (existing) | `Tail/Lang.lean` | the program | on every `next` | cannot be written |
| Wrapper designs (existing) | `Wrapper/*.lean` | the wrapper structure | outside the grammar | cannot be written (`Checked`: default value) |

### 2.1 `PCL-VC`: proof-free syntax, one verification condition (implemented)

`RequestProject/WFLang/Designs/VC.lean`, namespace `WFLang.VC`.

* The syntax is `PCL` without the path-condition index `G` and without the `dec` field on
  `call`. It keeps `fix params r R wf body args k`.
* `Expr.VC p e : Prop` is a *verification-condition generator*. It walks the syntax, uses the
  outcome of each `if` test, and requires `R args cur` at every call.
* `Expr.eval p e (hv : p.VC e) h` uses `hv` only to justify recursive calls. The proof is erased
  by code generation, so there is no runtime check and no fuel.
* `Certified s` bundles a program with `∀ x, term.VC x`, and `Certified.eval` is the curried
  evaluator.
* Proved: `fixFn_eq` and `fixFn_unique` (the fixpoint equation and uniqueness of its solution).
* Proved: `erase_vc` and `erase_eval`. Erasing the proofs of any `PCL` program gives a
  `PCL-VC` program whose `VC` holds and which computes the same value. So `Certified.ofPCL`
  reuses the existing `#lean_wf_func_to_term` capture. Examples: `ExVC.gcd_agree` and
  `ExVC.ack_agree`.
* Proved: `ExVC.gcdWrong_not_certified`. `gcd` written with the wrong relation "first argument
  decreases" is valid syntax, but its `VC` is false, so it cannot be evaluated.

Pros
* Programs are plain data: no proofs inside `call`, no path-condition index. They are easier to
  write by hand, to generate, to print and to transform.
* Separation of concerns: write the program first, prove termination afterwards, in one
  goal that one tactic can often close (`simp [Expr.VC, …]; omega`).
* No runtime cost, same as `PCL`.

Cons
* The evaluator takes an extra proof argument, so it can only be used through `Certified`.
* After any program transformation the `VC` must be proved again. In `PCL` the proofs travel
  with the calls, and a type-correct transformation keeps them.
* The relation is still inside the syntax (`fix … R wf`), so it is still chosen by the program.
* Like `PCL`, the `VC` must hold for *every* result of earlier calls, so nested recursion whose
  decrease depends on an inner result cannot be certified.

### 2.2 `PCL-Ext`: no termination information in the program; the measure is chosen outside (implemented)

`RequestProject/WFLang/Designs/Ext.lean`, namespace `WFLang.Ext`. This design answers the
criticism of `Meas` directly.

* A `Program s` is one recursive function whose body has only `ret`, `ite` and
  `let v := self args in k`. It contains **no** relation, measure or proof.
* The measure `μ : Env ps → ℕ × ℕ` (lexicographic; one `ℕ` is `fun x => (f x, 0)`) is an ordinary
  Lean function. Whoever runs the program supplies it.
* Three evaluators:
  * `Program.eval p μ (hμ : p.Decreases μ)`: **certified**. `Decreases` is the verification
    condition "every reached call lowers `μ`". There is no runtime check. It cannot be called with
    a wrong measure, because `hμ` does not exist.
  * `Program.runChecked p μ`: **checked**, needs no proof. It compares measures at every call and
    returns `Except.error (.notDecreasing callee caller)` when a call does not decrease. **It never
    returns a default value.**
  * `Program.runFuel p n`: **fuel**. It is structural recursion on `n`, returns
    `Except.error .outOfFuel` when the fuel runs out, and reduces in the kernel (`rfl` checks
    concrete runs).
* Proved properties:
  * `fn_eq` and `fn_unique`: the certified evaluator solves the program's recursive equation
    `Body.evalT`, which mentions no measure, and is its unique solution.
  * `eval_measure_irrelevant`: two different correct measures give the same function. So the
    measure only justifies termination and never changes a value.
  * `runChecked_eq_ok`: with a certified measure the checked run never fails and gives the
    certified value.
  * `not_decreases_of_error`: an error from `runChecked` is a proof that the measure is wrong.
  * `runFuel_eq_ok` and `runFuel_measure`: for a certified `ℕ`-valued measure `f`, fuel `f x + 1`
    is always enough. So the fuel is *computed from a proved-correct measure* and provably never
    runs out.
* Examples in `Designs/Examples.lean`, namespace `ExExt`:
  * `gcd` with the user measure `n`: `gcdμ_ok`, `gcd_agree`, and `gcd_fuel`
    (`runFuel (n+1) (m,n) = .ok (gcd m n)`).
  * `ack` with the lexicographic measure `(m, n)`: `ackμ_ok`, `ack_agree`. A *different* correct
    measure `(2m, n)` gives the same function (`ackμ'_ok` and an `example` using
    `eval_measure_irrelevant`).
  * Wrong measures: `gcd_wrong_error` (`runChecked` returns
    `.error (.notDecreasing (6,0) (4,0))` on `gcd 4 6`), `gcd_wrong_not_certified`,
    `ack_wrong_error` and `ack_wrong_not_certified`. `gcd_wrong_ok` shows that the checked run
    still succeeds on inputs where the wrong measure happens to decrease. That is why an error
    can only be reported at run time, and why the proof-based evaluator is the one that rules
    errors out for all inputs.
  * `#guard_msgs` runtime checks compare all three evaluators with `gcd` and `Tco.ack`.

Pros
* Termination is chosen from outside and is not part of the program. The same program can be
  run with different measures, and it is proved that the choice cannot change the result.
* Wrong measures are never hidden: the certified evaluator rejects them statically, and the
  checked evaluator reports them as errors naming the offending measures.
* The user decides the trade-off per run: proof and no checks (`eval`), no proof and checks
  (`runChecked`), or a kernel-reducible run (`runFuel`).
* Programs are the simplest of all designs: typed ANF with no annotations at all.

Cons
* One recursive function per program: there is no nested `fix` (the `PCL` / `PCL-VC` capture
  handles helper functions; this one does not).
* The measure is limited to `ℕ × ℕ` lexicographic. More general orders need a different measure
  type, or a relation plus a decision procedure for the checked evaluator.
* `runChecked` pays a comparison per call. `runFuel` pays a counter and needs an `ℕ`-valued
  measure to compute the fuel; with a lexicographic measure such as Ackermann's, the recursion
  depth is not bounded by the measure.
* There is no capture command yet. The examples are written by hand, although turning a
  `termination_by` measure into `μ` is straightforward.

### 2.3 Comparison with the existing designs

| | `PCL` | `PCL-VC` | `PCL-Ext` | `Meas` |
|---|---|---|---|---|
| proofs in the syntax | per call | none (only `wf` on `fix`) | none | none |
| termination argument chosen by | program | program | caller (outside) | program |
| correctness of the argument | typed, per call | one `VC` proof | `Decreases` proof, or runtime check | runtime check only |
| wrong argument ⇒ | cannot be written | cannot be certified | cannot be certified / **error** | **default value** |
| runtime checks | none | none | none (`eval`) / per call (`runChecked`) | per call |
| nested local recursive functions | yes | yes | no | yes |
| capture from Lean | yes | yes (via `Certified.ofPCL`) | not yet | yes |

## 3. Further designs (described, not implemented)

These are not in the project. They are listed only to complete the picture.

* **Bove–Capretta domain predicate.** The program is general recursive. Its "domain" is an
  inductive predicate `Dom x` generated from the syntax, and `eval x (h : Dom x)` recurses on `h`.
  Pro: it expresses partial functions and nested recursion whose decrease depends on inner
  results. Con: `Dom` must be proved per input, or once for all inputs, and generating it needs
  induction–recursion for nested calls.
* **Partiality / delay monad.** `eval : … → Delay r`, with no termination argument at all, plus a
  separate theorem "terminates for all inputs". Pro: any program can be written. Con: the
  evaluator is not a total function to `r` until termination is proved; this is the pure
  "semantics first" approach.
* **Sized types / structural recursion only** (System T `natrec`). Termination is guaranteed by the
  grammar and there are no proofs. Con: `gcd`, `mc91` etc. need an encoding with an explicit bound,
  which is then a fuel argument again.
* **Accessibility argument in the syntax** (`call` carries `Acc R y`). This is essentially
  `GuardedAcc` from the Wrapper designs, moved into the grammar. It offers no advantage over
  per-call `R y x` proofs, because `Acc` for the callee follows from `R` and the caller's `Acc`.
