import Mathlib.Order.RelClasses
import RequestProject.WFLang.Core.EvalSimpAttr

/-!
# Library equations used by the agreement proofs

The capture translates some library functions into operators of the grammar (e.g. `a[i]!` into
`a[i]?.getD default`); these are the equations the
agreement proofs use to identify both sides.
-/

namespace WFLang

theorem array_getElem!_eq {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = a[i]?.getD default := by
  rcases a with ⟨l⟩
  simp [List.getElem!_eq_getElem?_getD]

@[simp, wflang_eval] theorem except_toBool_ok {ε α : Type} (a : α) :
    (Except.ok a : Except ε α).toBool = true := rfl

@[simp, wflang_eval] theorem except_toBool_error {ε α : Type} (e : ε) :
    (Except.error e : Except ε α).toBool = false := rfl

end WFLang
