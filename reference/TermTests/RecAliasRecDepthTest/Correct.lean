module

public import TermTests.RecAliasRecDepthTest
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive newtype: correct on **every** chain

§7 of `TermTests.RecAliasRecDepthTest` runs the terms on a few chains.  This file proves,
for **every** chain `c` built by the introduction form (`chainVal c`), that the term answers
exactly what its Lean reference does:

* `fibTerm_correct` — the depth-one fold computes `Chain.fib`;
* `contTerm_correct` — the depth-one fold that also reads the label computes `Chain.cont`;
* `fibTRTerm_correct` — the depth-zero fold at a function type computes `Chain.fibTR`;
* `fibPairTerm_correct` — the depth-zero fold at a record type computes `Chain.fib`.

Each proof follows the recursion of the reference: the evaluator's memoised fold of a
chain one or two links longer unfolds, **by `rfl`**, to the branch applied to the answers
stored at the chains below — which are the folds of those chains.  The fold's branch is
evaluated in the context the term stands in, so each statement about the fold is proved
for an arbitrary such environment `e`, and the runs instantiate it.
-/

namespace TermTests.RecAliasRecDepth

open LeanScript

/-! ## The branches of the folds

The terms are translations of the Lean programs; a statement about the fold's step names
its branch, which is read back out of the translated term. -/

/-- The branch of `fibTerm`. -/
def fibBranch : Term sigAdd (branchCtx natT 1) natT := #leanscript_fold_branch fibTerm

/-- The branch of `contTerm`. -/
def contBranch : Term sigAdd (branchCtx natT 1) natT := #leanscript_fold_branch contTerm

/-- The branch of `fibTRTerm`. -/
def fibTRBranch : Term sigAdd (branchCtx loopTy 0) loopTy := #leanscript_fold_branch fibTRTerm

/-- The branch of `fibPairTerm`. -/
def fibPairBranch : Term sigAdd (branchCtx pairTy 0) pairTy :=
  #leanscript_fold_branch fibPairTerm

/-! ## `fib` -/

/-- The step of the evaluator's fold in `fibTerm`, in the environment `e`. -/
abbrev fibStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctor chainBodyW.toTy).A)
      (kids : (Ty.toPFunctor chainBodyW.toTy).B node → AliasMemo chainBodyW natT) =>
    Term.eval envAdd fibBranch (Env.append (aliasRecEnv chainBodyW (by ty_wf) natT 1 node kids) e)
     

set_option maxHeartbeats 4000000 in
/-- Two links down, the fold adds the answers at the two chains below. -/
theorem fibStep_cons_cons (e : Env CCtx) (l l' : Nat) (g : Chain) :
    WType.memoFold (fibStep e) (chainVal (.cons l (.cons l' g))) =
      WType.memoFold (fibStep e) (chainVal (.cons l' g)) +
        WType.memoFold (fibStep e) (chainVal g) := rfl

/-- The fold of `fibTerm` is `Chain.fib`, in every environment. -/
theorem fib_memoFold (e : Env CCtx) : ∀ c : Chain,
    WType.memoFold (fibStep e) (chainVal c) = Chain.fib c
  | .nil => by rw [Chain.fib]; rfl
  | .cons l .nil => by rw [Chain.fib]; rfl
  | .cons l (.cons l' g) => by
      rw [fibStep_cons_cons, fib_memoFold e (.cons l' g), fib_memoFold e g, Chain.fib]

/-- **`fibTerm` computes `Chain.fib`** on every chain. -/
theorem fibTerm_correct (c : Chain) : runP fibTerm (chainVal c) = Chain.fib c :=
  fib_memoFold _ c

/-! ## The continuant -/

/-- The step of the evaluator's fold in `contTerm`, in the environment `e`. -/
abbrev contStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctor chainBodyW.toTy).A)
      (kids : (Ty.toPFunctor chainBodyW.toTy).B node → AliasMemo chainBodyW natT) =>
    Term.eval envAdd contBranch (Env.append (aliasRecEnv chainBodyW (by ty_wf) natT 1 node kids) e)
     

set_option maxHeartbeats 4000000 in
/-- Two links down, the continuant multiplies the label by the answer one link down and
    adds the answer two links down. -/
theorem contStep_cons_cons (e : Env CCtx) (a b : Nat) (g : Chain) :
    WType.memoFold (contStep e) (chainVal (.cons a (.cons b g))) =
      a * WType.memoFold (contStep e) (chainVal (.cons b g)) +
        WType.memoFold (contStep e) (chainVal g) := rfl

/-- The fold of `contTerm` is `Chain.cont`, in every environment. -/
theorem cont_memoFold (e : Env CCtx) : ∀ c : Chain,
    WType.memoFold (contStep e) (chainVal c) = Chain.cont c
  | .nil => by rw [Chain.cont]; rfl
  | .cons a .nil => by rw [Chain.cont]; rfl
  | .cons a (.cons b g) => by
      rw [contStep_cons_cons, cont_memoFold e (.cons b g), cont_memoFold e g, Chain.cont]

/-- **`contTerm` computes `Chain.cont`** on every chain. -/
theorem contTerm_correct (c : Chain) : runP contTerm (chainVal c) = Chain.cont c :=
  cont_memoFold _ c

/-! ## The tail-recursive loop -/

/-- The step of the evaluator's fold in `fibTRTerm`, in the environment `e`. -/
abbrev fibTRStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctor chainBodyW.toTy).A)
      (kids : (Ty.toPFunctor chainBodyW.toTy).B node → AliasMemo chainBodyW loopTy) =>
    Term.eval envAdd fibTRBranch
      (Env.append (aliasRecEnv chainBodyW (by ty_wf) loopTy 0 node kids) e)

/-- The fold of `fibTRTerm` is the loop `Chain.fibLoopTR`, in every environment. -/
theorem fibTR_memoFold (e : Env CCtx) : ∀ (c : Chain) (a b : Nat),
    WType.memoFold (fibTRStep e) (chainVal c) a b = Chain.fibLoopTR c a b
  | .nil, _, _ => rfl
  | .cons _ c, a, b => by
      rw [Chain.fibLoopTR, ← fibTR_memoFold e c b (a + b)]
      rfl

/-- **`fibTRTerm` computes `Chain.fibTR`** on every chain. -/
theorem fibTRTerm_correct (c : Chain) : runP fibTRTerm (chainVal c) = Chain.fibTR c :=
  fibTR_memoFold _ c 0 1

/-! ## The pair recursion -/

/-- The step of the evaluator's fold in `fibPairTerm`, in the environment `e`. -/
abbrev fibPairStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctor chainBodyW.toTy).A)
      (kids : (Ty.toPFunctor chainBodyW.toTy).B node → AliasMemo chainBodyW pairTy) =>
    Term.eval envAdd fibPairBranch
      (Env.append (aliasRecEnv chainBodyW (by ty_wf) pairTy 0 node kids) e)

/-- The fold of `fibPairTerm` carries the pair `Chain.fibPair`, in every environment. -/
theorem fibPair_memoFold (e : Env CCtx) : ∀ c : Chain,
    ((WType.memoFold (fibPairStep e) (chainVal c)).1,
      (WType.memoFold (fibPairStep e) (chainVal c)).2.1) = Chain.fibPair c
  | .nil => rfl
  | .cons _ c => by
      have ih := fibPair_memoFold e c
      rw [Chain.fibPair, ← ih]
      rfl

/-- **`fibPairTerm` computes `Chain.fib`** on every chain: it is the first component of the
    pair recursion, which is `fib` (`Chain.fibPair_fst_eq_fib`). -/
theorem fibPairTerm_correct (c : Chain) : runP fibPairTerm (chainVal c) = Chain.fib c := by
  rw [← Chain.fibPair_fst_eq_fib, ← fibPair_memoFold (chainVal c, PUnit.unit) c]
  rfl

end TermTests.RecAliasRecDepth

end
