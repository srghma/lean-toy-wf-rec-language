module

public import LeanScript.Expr.Build
public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Function and delayed fields in a fold deeper than `0`

The fold of a recursive record or newtype at depth `k` (`Term.recObject_rec k`,
`Term.recAlias_rec k`) gives its branch a window in which each subvalue is replaced by
its **answer tree** of depth `k`. At a field that is a function into the type
(`node (f : Nat → T)`), the window holds the function of the answer trees at `f a`. At a
delayed field (`Thunk T`), it holds the delayed answer tree.

`#leanscript_to_term` reads such a field the same way at every depth. Beside the window
it binds the function of the answers, `fnTreeAnswer`, or the delayed answer,
`thunkTreeAnswer`, and reads the answer at `f a` as that function applied to `a`. This
file proves that this is right, for every signature, context, environment and depth:

* `aliasAnswerTree_zero` and `objAnswerTree_zero`: the answer tree of depth `0` at a
  node is the answer stored there. `aliasAnswerTree_succ_fst` and
  `objAnswerTree_succ_fst`: the first field of an answer tree of any depth is that same
  answer.
* `Term.eval_fnTreeAnswer`: the term the translation binds at a function field evaluates
  to `fun a => (w a).1`, the function of the first fields of the answer trees.
* `Term.eval_thunkTreeAnswer`: the term it binds at a delayed field evaluates to the
  first field of the delayed answer tree.
* `eval_fnTreeAnswer_aliasAnswerTree` and `eval_fnTreeAnswer_objAnswerTree`: put
  together, when the window at a function field is the function of the answer trees of
  depth `j + 1` at the subvalues (as the evaluator builds it), the bound function is the
  function of the **answers** at the subvalues. That is exactly what the depth-`0` window
  holds there, and what the Lean branch reads as `(f a).foo`. The `thunk` versions say
  the same for a delay.
-/

namespace LeanScript

variable {Sg : Sig}

/-! ## The answer inside an answer tree -/

/-- The answer tree of depth `0` at a node of the memo of a recursive newtype is the
    answer stored there. -/
theorem aliasAnswerTree_zero (b : TyWfIn 1) (τ : TyWf) (m : AliasMemo b τ) :
    aliasAnswerTree b τ 0 m = m.answer := rfl

/-- **The first field of an answer tree of a recursive newtype, at any depth, is the answer
    at its node.** -/
theorem aliasAnswerTree_succ_fst (b : TyWfIn 1) (τ : TyWf) (j : Nat) (m : AliasMemo b τ) :
    (show TyWf.Den τ × TyWf.Den (TyWf.recAliasMap b (TyWf.recAliasAnswerTree b τ j)) × PUnit
      from aliasAnswerTree b τ (j + 1) m).1 = m.answer := by
  obtain ⟨⟨s, a⟩, kids⟩ := m
  rfl

/-- The answer tree of depth `0` at a node of the memo of a recursive record is the answer
    stored there. -/
theorem objAnswerTree_zero (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) (m : ObjMemo fs τ) :
    objAnswerTree fs τ 0 m = m.answer := rfl

/-- **The first field of an answer tree of a recursive record, at any depth, is the answer
    at its node.** -/
theorem objAnswerTree_succ_fst (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) (j : Nat)
    (m : ObjMemo fs τ) :
    (show TyWf.Den τ × TyWf.Den (TyWf.recObjectMap fs (TyWf.recObjectAnswerTree fs τ j)) ×
        PUnit from objAnswerTree fs τ (j + 1) m).1 = m.answer := by
  obtain ⟨⟨s, a⟩, kids⟩ := m
  rfl

/-! ## The terms the translation binds beside the window

`Term.fnTreeAnswer` and `Term.thunkTreeAnswer` are defined in `LeanScript.Expr.Build`, with
the other builders the translation writes, so that every file that uses the translation
can read them. -/

/-- **The function the translation binds at a function field is the function of the
    first fields of the window.** -/
theorem Term.eval_fnTreeAnswer (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ τ W : TyWf}
    (w : Γ ∋ (σ ⇒ .record ⟨τ, W, []⟩))
    (env : Env Γ) :
    Term.eval G (Term.fnTreeAnswer w) env =
      fun a => (show TyWf.Den τ × TyWf.Den W × PUnit from Env.get w env a).1 := rfl

/-- **The delayed answer the translation binds at a delayed field is the first field of
    the delayed answer tree.** (A delay denotes the value it stands for.) -/
theorem Term.eval_thunkTreeAnswer (G : GlobalEnv Sg.decls) {Γ : Ctx} {τ W : TyWf}
    (w : Γ ∋ .thunk (.record ⟨τ, W, []⟩))
    (env : Env Γ) :
    Term.eval (τ := .thunk τ) G (Term.thunkTreeAnswer w) env =
      (show TyWf.Den τ × TyWf.Den W × PUnit from Env.get w env).1 := rfl

/-! ## Put together: the bound function is the depth-`0` window -/

/-- **At a function field of a recursive newtype, at any depth `j + 1`**: if the window
    holds the function of the answer trees at the subvalues `m a`, the function the
    translation binds beside it is the function of the answers at them. That is the
    depth-`0` window, `fun a => aliasAnswerTree b τ 0 (m a)`. -/
theorem eval_fnTreeAnswer_aliasAnswerTree (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ : TyWf}
    (b : TyWfIn 1) (τ : TyWf) (j : Nat) (m : TyWf.Den σ → AliasMemo b τ)
    (w : Γ ∋ (σ ⇒ .record ⟨τ, TyWf.recAliasMap b (TyWf.recAliasAnswerTree b τ j), []⟩))
    (env : Env Γ)
    (hw : Env.get w env = fun a => aliasAnswerTree b τ (j + 1) (m a)) :
    Term.eval G (Term.fnTreeAnswer w) env = fun a => aliasAnswerTree b τ 0 (m a) := by
  refine (Term.eval_fnTreeAnswer G w env).trans ?_
  funext a
  rw [hw]
  exact aliasAnswerTree_succ_fst b τ j (m a)

/-- **At a function field of a recursive record, at any depth `j + 1`**: the function the
    translation binds is the function of the answers at the subvalues, the depth-`0`
    window. -/
theorem eval_fnTreeAnswer_objAnswerTree (G : GlobalEnv Sg.decls) {Γ : Ctx} {σ : TyWf}
    (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) (j : Nat) (m : TyWf.Den σ → ObjMemo fs τ)
    (w : Γ ∋ (σ ⇒ .record ⟨τ, TyWf.recObjectMap fs (TyWf.recObjectAnswerTree fs τ j), []⟩))
    (env : Env Γ)
    (hw : Env.get w env = fun a => objAnswerTree fs τ (j + 1) (m a)) :
    Term.eval G (Term.fnTreeAnswer w) env = fun a => objAnswerTree fs τ 0 (m a) := by
  refine (Term.eval_fnTreeAnswer G w env).trans ?_
  funext a
  rw [hw]
  exact objAnswerTree_succ_fst fs τ j (m a)

/-- **At a delayed field of a recursive newtype, at any depth `j + 1`**: the delayed answer
    the translation binds is the answer at the delayed subvalue, the depth-`0` window. -/
theorem eval_thunkTreeAnswer_aliasAnswerTree (G : GlobalEnv Sg.decls) {Γ : Ctx}
    (b : TyWfIn 1) (τ : TyWf) (j : Nat) (m : AliasMemo b τ)
    (w : Γ ∋ .thunk (.record ⟨τ, TyWf.recAliasMap b (TyWf.recAliasAnswerTree b τ j), []⟩))
    (env : Env Γ)
    (hw : Env.get w env = aliasAnswerTree b τ (j + 1) m) :
    Term.eval (τ := .thunk τ) G (Term.thunkTreeAnswer w) env =
      aliasAnswerTree b τ 0 m := by
  refine (Term.eval_thunkTreeAnswer G w env).trans ?_
  rw [hw]
  exact aliasAnswerTree_succ_fst b τ j m

/-- **At a delayed field of a recursive record, at any depth `j + 1`**: the delayed answer
    the translation binds is the answer at the delayed subvalue. -/
theorem eval_thunkTreeAnswer_objAnswerTree (G : GlobalEnv Sg.decls) {Γ : Ctx}
    (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) (j : Nat) (m : ObjMemo fs τ)
    (w : Γ ∋ .thunk (.record ⟨τ, TyWf.recObjectMap fs (TyWf.recObjectAnswerTree fs τ j), []⟩))
    (env : Env Γ)
    (hw : Env.get w env = objAnswerTree fs τ (j + 1) m) :
    Term.eval (τ := .thunk τ) G (Term.thunkTreeAnswer w) env =
      objAnswerTree fs τ 0 m := by
  refine (Term.eval_thunkTreeAnswer G w env).trans ?_
  rw [hw]
  exact objAnswerTree_succ_fst fs τ j m

end LeanScript

end
