module
import Init.Data.Array.Lemmas
public import NonEmpty.ArrayCorrectByConstruction.Instances
meta import NonEmpty.ArrayCorrectByConstruction.Basic

@[expose] public section

/-!
The literal notation for `NonEmptyArray` and its coercions to the underlying array.
-/

namespace NonEmpty.ArrayCorrectByConstruction

section

-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![])                           => Lean.Macro.throwError "#! literal must contain at least one element"
  | `(#![ $head:term ])               => ``(NonEmptyArray.mk $head #[])
  | `(#![ $head:term, $tail:term,* ]) => ``(NonEmptyArray.mk $head #[$tail,*])

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard #![1, 2, 3].head = 1
#guard #![1, 2, 3].tail = #[2, 3]
#guard #![1, 2, 3].size = 3
#guard #![1, 2, 3][0] = 1
#guard #![1, 2, 3][1] = 2
#guard #![1, 2, 3][2] = 3

end

-- ============================================================
-- Coercions (downgraders)
-- ============================================================

/-- Automatically coerce `NonEmptyArray` (CorrectByConstruction) to its underlying `Array`. -/
@[inline]
instance : CoeOut (NonEmpty.ArrayCorrectByConstruction.NonEmptyArray α) (Array α) where
  coe xs := xs.toArr

end NonEmpty.ArrayCorrectByConstruction
