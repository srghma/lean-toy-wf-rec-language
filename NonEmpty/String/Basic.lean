module

public import Init.Data.String.Lemmas
public import Init.Data.String.Lemmas.Basic

@[expose] public section
namespace NonEmpty.String

structure NonEmptyString where
  toString : String
  isNonEmpty : toString ≠ "" := by decide
  deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- instance : CoeOut NonEmptyString String where
--   coe s := s.toString

instance : ToString NonEmptyString where
  toString s := s.toString

namespace NonEmptyString

abbrev fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none

abbrev fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨String.ofList cs, by simp_all only [ne_eq, String.ofList_eq_empty_iff, not_false_eq_true]⟩

abbrev fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.ofList cs)

@[simp] theorem toString_ne_empty (s : NonEmptyString) : s.toString ≠ "" := s.isNonEmpty

instance : Append NonEmptyString where
  append s1 s2 := ⟨s1.toString ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_self, not_false_eq_true]⟩

instance : HAppend String NonEmptyString NonEmptyString where
  hAppend s1 s2 := ⟨s1 ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_false, not_false_eq_true]⟩

instance : HAppend NonEmptyString String NonEmptyString where
  hAppend s1 s2 := ⟨s1.toString ++ s2, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, false_and, not_false_eq_true]⟩

instance : LT NonEmptyString where
  lt a b := a.toString < b.toString

instance : LE NonEmptyString where
  le a b := a.toString ≤ b.toString

instance (a b : NonEmptyString) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toString < b.toString))

instance (a b : NonEmptyString) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toString ≤ b.toString))

instance : Min NonEmptyString where
  min a b := if a ≤ b then a else b

instance : Max NonEmptyString where
  max a b := if a ≤ b then b else a

instance {m : Type u → Type v} [Monad m] : ForIn m NonEmptyString Char where
  forIn s init f := forIn s.toString.toList init f

end NonEmptyString

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (by decide) : NonEmptyString) )

#guard (nes!"world").toString == "world"
#guard (nes!"11" < nes!"112")
#guard if (nes!"112" < nes!"11") then true else true

#guard nes!"11" ≤ nes!"112"
#guard nes!"11" ≤ nes!"11"
#guard nes!"112" > nes!"11"
#guard nes!"112" ≥ nes!"11"
#guard nes!"11" == nes!"11"
#guard nes!"11" != nes!"12"

end NonEmpty.String
