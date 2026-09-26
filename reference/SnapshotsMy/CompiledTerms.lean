/-!
# (retired) The functions of the snapshots, compiled into terms

This file was written against an earlier iteration of this project, whose modules
`LeanScript.Term.Compile` and `LeanScript.Term.Run`, command `#leanjs_compile_term_for`
and tactics `eval_term` / `run_term` are not part of this tree.  Nothing in it can be
elaborated here, so the whole of it is preserved below inside a block comment rather
than deleted.

What replaces it in this tree:

* `LeanScript.Expr` is the typed term language (`Term Γ τ`), and `LeanScript.Eval` is
  its evaluator, `Term.evalClosed`, which is a total Lean function — so a term is *run*
  by `rfl`/`decide` on `Term.evalClosed`, and there is no separate small-step relation,
  no `eval_term` tactic and no `MultiStep`/`Total`/`GuardStuck` obligations to discharge.
* `SnapshotsMy.LeanScriptModels` holds the terms themselves: a `Term` for several of the
  functions of these snapshots, each checked against the Lean function it models.
* `LeanScript.Term.Elab` provides `#leanjs_generate_term_and_ctx_for`, the report on
  what a Lean definition would compile to; it is applied to the public functions of the
  snapshot files.
-/

/-
import LeanScript.Term.Compile
import LeanScript.Term.Run
import SnapshotsMy.TcoAck
import SnapshotsMy.TcoBoom
import SnapshotsMy.TcoDiagonal
import SnapshotsMy.TcoHyper
import SnapshotsMy.TcoMc91
import SnapshotsMy.GcdEntry

/ -!
# The functions of the snapshots, compiled into terms

`#leanjs_generate_term_and_ctx_for` (in each snapshot file) *reports* what a definition
compiles to.  This file does the compilation: for every public function of the
`SnapshotsMy/Tco*.lean` files that the language can hold, it adds

```
<f>.leanTerm : Term [] <the Ty of f>
```

to the environment, and then **runs** several of the generated terms with `eval_term`,
comparing the answer of the small-step relation with the one Lean itself computes.

## What is compiled, and what is not

Of the twenty-four functions the snapshots report on, seventeen are compiled here.  The
other seven are the imperative versions, written as `Id.run do … while …`: a `while` loop
in a `do` block is `ForIn.forIn` at `Lean.Loop`, whose instance is `repeatM` — Lean's
**partial fixpoint** combinator, the third of the six kinds of recursion.  There is no
constructor of the term language that could hold one, which is exactly the design: the
report of each of them now says `partial fixpoint  NOT REPRESENTABLE in Term`, and
`unpairLeft`, `unpairRight` and `ackNoDataStructure`, which call `isqrt`, are rejected
with it.  (`hyperWhile` is left out for a different reason: its body is a `do` block, and
the generator translates ordinary terms, not monadic ones.)
- /

open LeanScript LeanScript.Term
open scoped LeanScript.Term

/ -! ## Ackermann and its staged variants - /

#leanjs_compile_term_for ack
#leanjs_compile_term_for ack999
#leanjs_compile_term_for ack2
#leanjs_compile_term_for AckWithoutStackButUsingCantorPairing.pair

/ -! ## McCarthy 91 - /

#leanjs_compile_term_for mc91
#leanjs_compile_term_for mc91Loop
#leanjs_compile_term_for mc91TR
#leanjs_compile_term_for iter

/ -! ## The hyperoperation tower - /

#leanjs_compile_term_for hyper
#leanjs_compile_term_for hyperBase
#leanjs_compile_term_for hyperLoop
#leanjs_compile_term_for hyperTCO

/ -! ## The diagonal enumeration, `boom`, and `gcd` - /

#leanjs_compile_term_for diagonal
#leanjs_compile_term_for diagonal_tr
#leanjs_compile_term_for boom
#leanjs_compile_term_for gcd2

/ -! ## Checked runs

Each theorem is a complete derivation of the small-step relation: the generated term
really does run to the value Lean computes. - /

/ -- `ack 1 1 = 3`, run in the language.  The loop `ack` compiles to seals the
    lexicographic order on its two arguments, so the inner call `ack (m+1) n` — which
    leaves the first argument alone — is accepted by the guard. - /
theorem ack_at_1_1 : (Term.app (Term.app ack.leanTerm (natLit 1)) (natLit 1)) ⇓ natLit 3 := by
  unfold ack.leanTerm
  eval_term

/ -- `mc91 120 = 110`. - /
theorem mc91_at_120 : (Term.app mc91.leanTerm (natLit 120)) ⇓ natLit 110 := by
  unfold mc91.leanTerm
  eval_term

/ -- `hyperBase 1 7 = 7`. - /
theorem hyperBase_at_1_7 :
    (Term.app (Term.app hyperBase.leanTerm (natLit 1)) (natLit 7)) ⇓ natLit 7 := by
  unfold hyperBase.leanTerm
  eval_term

/ -- `gcd2 12 8 = 4`. - /
theorem gcd2_at_12_8 :
    (Term.app (Term.app gcd2.leanTerm (natLit 12)) (natLit 8)) ⇓ natLit 4 := by
  unfold gcd2.leanTerm
  eval_term

/ -- `boom 1 = 0`: the one input at which `boom` terminates. - /
theorem boom_at_1 : (Term.app boom.leanTerm (natLit 1)) ⇓ natLit 0 := by
  unfold boom.leanTerm
  eval_term

/ -- The successor function, as a term. - /
private def succT : Term [] (Ty.nat ⇒ Ty.nat) :=
  .lam (natOp2 (fun x y => x + y) (.var .zero) (natLit 1))

/ -- `hyperLoop (· + 1) 3 0 = 3`: a loop whose function argument is a **fixed
    parameter**, bound outside the loop and read from inside it. - /
theorem hyperLoop_run :
    (Term.app (Term.app (Term.app hyperLoop.leanTerm succT) (natLit 3)) (natLit 0)) ⇓
      natLit 3 := by
  unfold hyperLoop.leanTerm succT
  eval_term

/ -- `iter (· + 1) 2 5 = 7`: the same, with the recursion carrying an accumulator. - /
theorem iter_run :
    (Term.app (Term.app (Term.app iter.leanTerm succT) (natLit 2)) (natLit 5)) ⇓
      natLit 7 := by
  unfold iter.leanTerm succT
  eval_term

/ -! ## Stopping early is not divergence: `boom` at an unsafe input

In Lean, `boom` is total only because of its erased argument `h : Safe n`, which says
`n = 1` and so makes the recursive call `boom (3 * n)` dead code.  A term of the language
carries no erased proofs, so the compiled `boom` really does reach that call at every
other input — and there it *stops*, because `3 * n` does not descend along the measure
the loop sealed.

The three theorems below say exactly what happens at the input `2`, and they are the
worked answer to "could a term of this language run forever?":

* the run **reaches** the call `boom 6` made from `boom 2` (`boom_at_2_runs_to_stuck`),
* that state is a normal form, so the run **stops** there (`boom_stuck_nf`) — the
  evaluator never takes another step, let alone infinitely many, and
  `LeanScript.Term.terminates` already guaranteed as much for every closed term;
* what it is *not* is an answer: the state is `GuardStuck`, so the term is not `Total`
  (`boom_at_2_not_total`).

Divergence is unwritable; giving up is what an unproved recursive call costs.  The
contrast is `LeanScript.Term.Examples.gcdTerm`, whose calls do descend and which is
therefore proved `Total` at every input. - /

/ -- The body of the compiled `boom`: variable `0` is the argument, variable `1` the
    recursive call. - /
private def boomBody : Term [Ty.nat, Ty.nat ⇒ Ty.nat] Ty.nat :=
  .cond (natRel2 (fun x y => x == y) (.var .zero) (natLit 1)) (natLit 0)
    (.app (.var (.succ .zero)) (natOp2 (fun x y => x * y) (natLit 3) (.var .zero)))

/ -- …and that really is the body the generator produced. - /
theorem boom_leanTerm_eq :
    boom.leanTerm =
      Tm.loop (measureRel (PVal.natAt [])) (measureRel_wf _) boomBody := rfl

/ -- The compiled `boom`, in progress at the argument `n`. - /
private def boomSelf (n : Nat) : Term [] (Ty.nat ⇒ Ty.nat) :=
  .wfFix (measureRel (PVal.natAt [])) (measureRel_wf _) (by decide)
    (some (.prim (.nat n))) boomBody

/ -- `6` does not descend below `2` along the measure the loop sealed. - /
private theorem boom_no_descent :
    ¬ measureRel (PVal.natAt []) (.prim (.nat 6)) (.prim (.nat 2)) := by
  intro h
  exact absurd (show (6 : Nat) < 2 from h) (by omega)

/ -- Applied to `2`, the compiled `boom` runs as far as the recursive call on `6`. - /
theorem boom_at_2_runs_to_stuck :
    MultiStep (Term.app boom.leanTerm (natLit 2)) (Term.app (boomSelf 2) (natLit 6)) := by
  unfold boom.leanTerm boomSelf boomBody
  run_term

/ -- And there it stops: no rule applies. - /
theorem boom_stuck_nf : Nf (Term.app (boomSelf 2) (natLit 6)) := by
  intro t' hs
  cases hs with
  | appL h => cases h
  | appR _ h => cases h
  | fixStep _ he hr =>
      cases he
      exact absurd hr boom_no_descent

/ -- The state it stops at is a recursive call that does not descend. - /
theorem boom_stuck_state : GuardStuck (Term.app (boomSelf 2) (natLit 6)) := by
  refine GuardStuck.here (Value.lit _) ?_
  rintro ⟨u', hu, hr⟩
  cases hu
  exact absurd hr boom_no_descent

/ -- So the compiled `boom` is not total at `2` — it gives up rather than answering. - /
theorem boom_at_2_not_total : ¬ Total (Term.app boom.leanTerm (natLit 2)) :=
  fun h => h _ boom_at_2_runs_to_stuck boom_stuck_state

/ -- Its run stops all the same: this is `LeanScript.Term.terminates`, which holds of
    every closed term, `Term.wfFix` included. - /
theorem boom_at_2_terminates :
    ∃ w, MultiStep (Term.app boom.leanTerm (natLit 2)) w ∧ Nf w :=
  terminates _

-/
