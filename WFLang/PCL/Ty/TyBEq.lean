module

public import LeanScript.Ty.Ty

@[expose] public section

namespace LeanScript

/-!
# `Ty.beq` is equality

`LeanScript.Ty.beq` (`LeanScript.Ty.Ty`) compares two trees node by node.  This module
proves that the comparison is the equality of the trees — `Ty.eq_of_beq` and
`Ty.beq_refl` — and that is what the `LawfulBEq` and `DecidableEq` instances below are.

`Ty` is a **nested** inductive: its children sit inside `TyShape`, the schemas and `List`,
so neither `DecidableEq` nor `LawfulBEq` can be derived for it.  What takes their place is
the functional induction principle of `Ty.beq` itself, `Ty.beq.induct`, which has one
motive per function of the `mutual` block the comparison is written as; each proof below
gives those twelve motives and then closes every case by unfolding one step.
-/

namespace Ty

attribute [local simp] beq beqShape beqCov beqList beqCtors beqA2 beqNE beqTU beqCP beqFam
  beqFamList beqFamily

open NonEmpty.ListCorrectByConstruction (NonEmptyList) in
/-- The case a walk of two trees reaches when neither matches a pattern of the comparison:
    take the one tree the case has apart, whichever of the twelve languages it is in. -/
local macro "ty_beq_cases" : tactic =>
  `(tactic|
    first
      | cases (‹Ty›)
      | cases (‹TyShape Ty›)
      | cases (‹LeanPrimTyCovariant Ty›)
      | cases (‹List Ty›)
      | cases (‹List (List Ty)›)
      | cases (‹LeanRecordSchema Ty›)
      | cases (‹NonEmptyList Ty›)
      | cases (‹LeanTaggedUnionSchema Ty›)
      | cases (‹CtorsWithPayload Ty›)
      | cases (‹LeanFamMemberSchema Ty›)
      | cases (‹List (LeanFamMemberSchema Ty)›)
      | cases (‹LeanMutualRecFamily Ty›))

/-- **The comparison is sound**: two trees it accepts are the same tree. -/
theorem eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b := by
  intro a b
  induction a, b using Ty.beq.induct
    (motive2 := fun x y => Ty.beqFamily x y = true → x = y)
    (motive3 := fun x y => Ty.beqFam x y = true → x = y)
    (motive4 := fun x y => Ty.beqA2 x y = true → x = y)
    (motive5 := fun x y => Ty.beqList x y = true → x = y)
    (motive6 := fun x y => Ty.beqTU x y = true → x = y)
    (motive7 := fun x y => Ty.beqCP x y = true → x = y)
    (motive8 := fun x y => Ty.beqCtors x y = true → x = y)
    (motive9 := fun x y => Ty.beqNE x y = true → x = y)
    (motive10 := fun x y => Ty.beqFamList x y = true → x = y)
    (motive11 := fun x y => Ty.beqShape x y = true → x = y)
    (motive12 := fun x y => Ty.beqCov x y = true → x = y) <;>
  intros <;> simp_all

/-- **The comparison is complete**: it accepts a tree against itself.  It is stated with
    the two trees apart, and `rfl` between them, because that is the shape the induction
    principle of a two-argument function has. -/
theorem beq_of_eq : ∀ {a b : Ty}, a = b → Ty.beq a b = true := by
  intro a b
  induction a, b using Ty.beq.induct
    (motive2 := fun x y => x = y → Ty.beqFamily x y = true)
    (motive3 := fun x y => x = y → Ty.beqFam x y = true)
    (motive4 := fun x y => x = y → Ty.beqA2 x y = true)
    (motive5 := fun x y => x = y → Ty.beqList x y = true)
    (motive6 := fun x y => x = y → Ty.beqTU x y = true)
    (motive7 := fun x y => x = y → Ty.beqCP x y = true)
    (motive8 := fun x y => x = y → Ty.beqCtors x y = true)
    (motive9 := fun x y => x = y → Ty.beqNE x y = true)
    (motive10 := fun x y => x = y → Ty.beqFamList x y = true)
    (motive11 := fun x y => x = y → Ty.beqShape x y = true)
    (motive12 := fun x y => x = y → Ty.beqCov x y = true) <;>
  intros <;> subst_eqs <;> (try simp_all) <;> ty_beq_cases <;> (try simp_all) <;>
  (apply_assumption <;> rfl)

/-- A tree compares equal to itself. -/
theorem beq_refl (a : Ty) : Ty.beq a a = true := beq_of_eq rfl

end Ty

instance : LawfulBEq Ty where
  eq_of_beq h := Ty.eq_of_beq h
  rfl := Ty.beq_refl _

instance : DecidableEq Ty := fun a b =>
  if h : Ty.beq a b then .isTrue (Ty.eq_of_beq h) else .isFalse fun he => h (Ty.beq_of_eq he)

end LeanScript

end
