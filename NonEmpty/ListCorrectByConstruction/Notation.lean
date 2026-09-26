module
import Init.Data.List.Lemmas
public import NonEmpty.ListCorrectByConstruction.Instances
meta import NonEmpty.ListCorrectByConstruction.Basic

@[expose] public section

/-!
The literal notation for `NonEmptyList` and its coercions to the underlying list.
-/

namespace NonEmpty.ListCorrectByConstruction

section

-- Macro for creating non-empty list literals
syntax "![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(![])                           => Lean.Macro.throwError "! literal must contain at least one element"
  | `(![ $head:term ])               => ``(NonEmptyList.mk $head [])
  | `(![ $head:term, $tail:term,* ]) => ``(NonEmptyList.mk $head [$tail,*])

example : NonEmptyList Nat := ![1, 2, 3]
example : NonEmptyList String := !["hello", "world"]
example : NonEmptyList Nat := ![10]

#guard ![1, 2, 3].head = 1
#guard ![1, 2, 3].tail = [2, 3]
#guard ![1, 2, 3].length = 3
#guard ![1, 2, 3][0] = 1
#guard ![1, 2, 3][1] = 2
#guard ![1, 2, 3][2] = 3

end

-- ============================================================
-- Coercions (downgraders)
-- ============================================================

/-- Automatically coerce `NonEmptyList` (CorrectByConstruction) to its underlying `List`. -/
@[inline]
instance : CoeOut (NonEmpty.ListCorrectByConstruction.NonEmptyList α) (List α) where
  coe xs := xs.toList

end NonEmpty.ListCorrectByConstruction
