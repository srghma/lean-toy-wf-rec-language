module

public import TermTests.RecObjectRecDepthTest
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive record: correct on **every** chain

§7 of `TermTests.RecObjectRecDepthTest` runs the terms on a few chains.  This file proves,
for **every** chain `c` built by the introduction form (`cellVal c`), that the term answers
exactly what its Lean reference does:

* `fibTerm_correct` — the depth-one fold computes `Cell.fib`;
* `contTerm_correct` — the depth-one fold that also reads the label computes `Cell.cont`;
* `fibTRTerm_correct` — the depth-zero fold at a function type computes `Cell.fibTR`;
* `fibPairTerm_correct` — the depth-zero fold at a record type computes `Cell.fib`.

Each proof follows the recursion of the reference: the evaluator's memoised fold of a
chain one or two cells longer unfolds, **by `rfl`** (checked by the kernel alone,
`kernel_rfl`), to the branch applied to the answers
stored at the cells below — which are the folds of those cells.  The fold's branch is
evaluated in the context the term stands in, so each statement about the fold is proved
for an arbitrary such environment `e`, and the runs instantiate it.
-/

namespace TermTests.RecObjectRecDepth

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
  fun (node : (Ty.toPFunctorRecord (objF cellSchema)).A)
      (kids : (Ty.toPFunctorRecord (objF cellSchema)).B node → ObjMemo cellSchema natT) =>
    Term.eval envAdd fibBranch (Env.append (objRecEnv cellSchema (by ty_wf) natT 1 node kids) e)
     

/-- Two cells down, the fold adds the answers at the two cells below. -/
theorem fibStep_cons_cons (e : Env CCtx) (l l' : Nat) (g : Cell) :
    WType.memoFold (fibStep e) (cellVal (.mk l (some (.mk l' (some g))))) =
      WType.memoFold (fibStep e) (cellVal (.mk l' (some g))) +
        WType.memoFold (fibStep e) (cellVal g) := by kernel_rfl

/-- The fold of `fibTerm` is `Cell.fib`, in every environment. -/
theorem fib_memoFold (e : Env CCtx) : ∀ c : Cell,
    WType.memoFold (fibStep e) (cellVal c) = Cell.fib c
  | .mk l none => by rw [Cell.fib]; rfl
  | .mk l (some (.mk l' none)) => by rw [Cell.fib]; rfl
  | .mk l (some (.mk l' (some g))) => by
      rw [fibStep_cons_cons, fib_memoFold e (.mk l' (some g)), fib_memoFold e g, Cell.fib]
termination_by c => sizeOf c
decreasing_by all_goals (simp_wf; omega)

/-- **`fibTerm` computes `Cell.fib`** on every chain. -/
theorem fibTerm_correct (c : Cell) : runP fibTerm (cellVal c) = Cell.fib c :=
  fib_memoFold _ c

/-! ## The continuant -/

/-- The step of the evaluator's fold in `contTerm`, in the environment `e`. -/
abbrev contStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctorRecord (objF cellSchema)).A)
      (kids : (Ty.toPFunctorRecord (objF cellSchema)).B node → ObjMemo cellSchema natT) =>
    Term.eval envAdd contBranch (Env.append (objRecEnv cellSchema (by ty_wf) natT 1 node kids) e)
     

/-- Two cells down, the continuant multiplies the label by the answer one cell down and
    adds the answer two cells down. -/
theorem contStep_cons_cons (e : Env CCtx) (a b : Nat) (g : Cell) :
    WType.memoFold (contStep e) (cellVal (.mk a (some (.mk b (some g))))) =
      a * WType.memoFold (contStep e) (cellVal (.mk b (some g))) +
        WType.memoFold (contStep e) (cellVal g) := by kernel_rfl

/-- The fold of `contTerm` is `Cell.cont`, in every environment. -/
theorem cont_memoFold (e : Env CCtx) : ∀ c : Cell,
    WType.memoFold (contStep e) (cellVal c) = Cell.cont c
  | .mk a none => by rw [Cell.cont]; kernel_rfl
  | .mk a (some (.mk b none)) => by rw [Cell.cont, Cell.cont]; kernel_rfl
  | .mk a (some (.mk b (some g))) => by
      rw [contStep_cons_cons, cont_memoFold e (.mk b (some g)), cont_memoFold e g, Cell.cont]
termination_by c => sizeOf c
decreasing_by all_goals (simp_wf; omega)

/-- **`contTerm` computes `Cell.cont`** on every chain. -/
theorem contTerm_correct (c : Cell) : runP contTerm (cellVal c) = Cell.cont c :=
  cont_memoFold _ c

/-! ## The tail-recursive loop -/

/-- The step of the evaluator's fold in `fibTRTerm`, in the environment `e`. -/
abbrev fibTRStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctorRecord (objF cellSchema)).A)
      (kids : (Ty.toPFunctorRecord (objF cellSchema)).B node → ObjMemo cellSchema loopTy) =>
    Term.eval envAdd fibTRBranch
      (Env.append (objRecEnv cellSchema (by ty_wf) loopTy 0 node kids) e)

/-- The fold of `fibTRTerm` is the loop `Cell.fibLoopTR`, in every environment. -/
theorem fibTR_memoFold (e : Env CCtx) : ∀ (c : Cell) (a b : Nat),
    WType.memoFold (fibTRStep e) (cellVal c) a b = Cell.fibLoopTR c a b
  | .mk _ none, _, _ => rfl
  | .mk _ (some c), a, b => by
      rw [Cell.fibLoopTR, ← fibTR_memoFold e c b (a + b)]
      rfl

/-- **`fibTRTerm` computes `Cell.fibTR`** on every chain. -/
theorem fibTRTerm_correct (c : Cell) : runP fibTRTerm (cellVal c) = Cell.fibTR c :=
  fibTR_memoFold _ c 0 1

/-! ## The pair recursion -/

/-- The step of the evaluator's fold in `fibPairTerm`, in the environment `e`. -/
abbrev fibPairStep (e : Env CCtx) :=
  fun (node : (Ty.toPFunctorRecord (objF cellSchema)).A)
      (kids : (Ty.toPFunctorRecord (objF cellSchema)).B node → ObjMemo cellSchema pairTy) =>
    Term.eval envAdd fibPairBranch
      (Env.append (objRecEnv cellSchema (by ty_wf) pairTy 0 node kids) e)

/-- The fold of `fibPairTerm` carries the pair `Cell.fibPair`, in every environment. -/
theorem fibPair_memoFold (e : Env CCtx) : ∀ c : Cell,
    ((WType.memoFold (fibPairStep e) (cellVal c)).1,
      (WType.memoFold (fibPairStep e) (cellVal c)).2.1) = Cell.fibPair c
  | .mk _ none => rfl
  | .mk _ (some c) => by
      have ih := fibPair_memoFold e c
      rw [Cell.fibPair, ← ih]
      rfl

/-- **`fibPairTerm` computes `Cell.fib`** on every chain: it is the first component of the
    pair recursion, which is `fib` (`Cell.fibPair_fst_eq_fib`). -/
theorem fibPairTerm_correct (c : Cell) : runP fibPairTerm (cellVal c) = Cell.fib c := by
  rw [← Cell.fibPair_fst_eq_fib, ← fibPair_memoFold (cellVal c, PUnit.unit) c]
  rfl

end TermTests.RecObjectRecDepth

end
