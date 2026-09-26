module

public import LeanScript.Expr.Build
public import LeanScript.RecObjectRecFacts

@[expose] public section

set_option autoImplicit false

/-!
# What the fold of a recursive newtype binds, and why it needs an answer window

`LeanScript.Term.recAlias_rec` is, beside `LeanScript.Term.recObject_rec`, the other fold
whose branch cannot be written with `LeanScript.TyWf.recBinders`.  `recBinders` puts the
value of the fold after a field that is **literally** an occurrence of the type being
folded over, and the body of a recursive newtype is never such a field: a body written
`Ty.self` states the equation `T = T`, which no value satisfies, so the tree is not a type
(`Ty.not_wf_recAlias_self`).

`recBinders_recAlias` below is that statement: at a recursive newtype the binders of the
old fold are *exactly* the binder of `Term.recAlias_casesOn`, so the plain fold handed its
branch no answer whatsoever.  What the depth-`k` fold hands it instead is one **lookback
window** binder — the newtype's own body with each subvalue replaced by its answer tree of
depth `k` (`TyWf.recAliasAnswerTree`) — and `recAliasRecBinders_zero` says that the
default depth is the old branch context with the one answer the old one was missing
appended to it.
-/

namespace LeanScript

namespace Ty

/-- **The body of a recursive newtype is never the newtype itself.**  The body has to have
    a value without the newtype being assumed to have one, and `Ty.self` alone has
    none. -/
theorem ne_self_of_wf_recAlias {b : Ty} (h : Wf (.recAlias b)) : b ≠ .self := by
  intro hb
  exact not_habIn_nil_self (hb ▸ habIn_of_wfIn_recAlias h)

end Ty

namespace TyWf

/-- **The plain fold of a recursive newtype gave its branch no answer**: its binders are
    the body of the newtype, unfolded, which is what `Term.recAlias_casesOn` binds. -/
theorem recBinders_recAlias (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b)) (motive : TyWf) :
    recBinders (recAlias b hwf) motive [b] = [recAliasUnfold b hwf] :=
  recBinders_eq_map _ _ fun a hm => by
    cases List.mem_singleton.mp hm
    exact Ty.ne_self_of_wf_recAlias hwf

/-- The branch of a depth-zero fold of a recursive newtype is the branch of the plain fold
    with the answers at the immediate subvalues — the one thing it was missing — bound
    after the body. -/
theorem recAliasRecBinders_zero (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (motive : TyWf) :
    recAliasRecBinders b hwf motive 0 =
      recBinders (recAlias b hwf) motive [b] ++ [recAliasMap b motive] := by
  rw [recAliasRecBinders, recBinders_recAlias]
  rfl

/-- One more depth is one more level inside the window: the answer tree of depth `k + 1`
    at a subvalue is the answer at it beside the depth-`k` trees of *its* subvalues. -/
theorem recAliasAnswerTree_succ (b : TyWfIn 1) (motive : TyWf) (k : Nat) :
    recAliasAnswerTree b motive (k + 1) =
      .record ⟨motive, recAliasMap b (recAliasAnswerTree b motive k), []⟩ := rfl

/-- The branch of a depth-`k` fold binds the newtype's body and one answer window. -/
theorem length_recAliasRecBinders (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (motive : TyWf) (k : Nat) : (recAliasRecBinders b hwf motive k).length = 2 := rfl

end TyWf

end LeanScript

end
