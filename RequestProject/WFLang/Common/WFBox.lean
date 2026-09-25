/-!
# `WFBox`: recursion on an arbitrary well-founded relation with `termination_by`

`termination_by` expects a `WellFoundedRelation` instance.  `WFBox R h` is a type synonym of
`α` whose instance is the relation `R` stored in a program, so an evaluator can write
`termination_by (WFBox.mk x : WFBox t.R t.wf)`.
-/

namespace WFLang

/-- Type synonym carrying a well-founded relation as instance. -/
def WFBox {α : Type} (R : α → α → Prop) (_ : WellFounded R) : Type := α

/-- Injection into `WFBox` (the identity). -/
def WFBox.mk {α : Type} {R : α → α → Prop} {h : WellFounded R} (a : α) : WFBox R h := a

instance {α : Type} (R : α → α → Prop) (h : WellFounded R) :
    WellFoundedRelation (WFBox R h) := ⟨R, h⟩

end WFLang
