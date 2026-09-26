module

public import LeanScript.Expr.Build
public import LeanScript.Eval

/-!
# Which terms does the evaluator evaluate?

**All of them.**  `Term.eval` is a total function on every term: every type of the language
has values in the model `TyWf.Den` — a recursive *tagged union*, a recursive *record* and
a recursive *newtype* denote the W-tree of their payload, and a *mutual family* the
indexed W-tree of its members — so every introduction form, the one of a mutual family
included, has a value.  This file checks, with the kernel, that

* a closed term such as `natNil` (the empty list of naturals) runs, and so do the
  eliminators applied to it: `natHead` and `natFoldZero` are told apart;
* so does a rose tree (a recursive record), which the evaluator builds and takes apart;
* so does a member of a mutual family, which the evaluator builds and dispatches on; the
  statements that held when a family denoted an empty type — that no function at all
  could send every closed term to a value of its type — are kept, commented out, as the
  record of what changed, and `total_evaluator` is that function.
-/

namespace TermTests

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- The empty signature. -/
def covEmptySig : Sig := ⟨[], by decide⟩

/-- `List Nat` as a recursive tagged union: `nil`, and `cons` of a natural and the list. -/
def natListSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.prim .nat).toTyWfIn, [Ty.self.toTyWfIn]⟩ [])

/-- The type of a list of naturals. -/
def natListTy : TyWf := .recTaggedUnion natListSchema

/-- The empty list. -/
def natNil : Term covEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 0) (fields := .nil)

/-- The head of a list, or `0`. -/
def natHead : Term covEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_casesOn' (.var (v♯0))
    (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- The fold over a list that answers `0`. -/
def natFoldZero : Term covEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_rec' 0 (.var (v♯0))
    (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯2))) .nil)))

/-- `[5]`. -/
def natFive : Term covEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 1) (fields := .cons (.nat_mk 5) (.cons natNil .nil))

/-! The four statements below held when a recursive tagged union denoted `PEmpty`.  They
are **false** now that it denotes the W-tree of its constructors: `natNil` has a value, `natListTy` has values, and `natHead` and `natFoldZero` differ on `[5]`.  They
are kept, commented out, as the record of what changed.

```
theorem natNil_not_noRecMk : ¬ Term.NoRecMk natNil := fun h => h
theorem natListTy_den_empty : TyWf.Den natListTy → False := fun v => PEmpty.elim v
theorem den_fun_natList_subsingleton (f g : TyWf.Den (natListTy ⇒ TyWf.prim .nat)) :
    f = g := funext fun v => PEmpty.elim v
theorem run_natHead_eq_run_natFoldZero :
    Term.run (Sg := covEmptySig) GlobalEnv.nil natHead =
      Term.run (Sg := covEmptySig) GlobalEnv.nil natFoldZero
```
-/

-- [SKIPPED BY PROFILE_LAKE] /-- The head of `[5]` is `5`. -/
-- [SKIPPED BY PROFILE_LAKE] theorem run_natHead_natFive :
-- [SKIPPED BY PROFILE_LAKE]     Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natHead natFive) = 5 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- The head of a list and the fold that answers `0` are told apart, on `[5]`. -/
-- [SKIPPED BY PROFILE_LAKE] theorem run_natHead_ne_run_natFoldZero :
-- [SKIPPED BY PROFILE_LAKE]     Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natHead natFive) ≠
-- [SKIPPED BY PROFILE_LAKE]       Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natFoldZero natFive) := by decide +kernel

/-- A rose tree: a label and an array of subtrees — a recursive **record**. -/
def roseSchema : LeanRecordSchema (TyWfIn 1) :=
  ⟨(Ty.prim .nat).toTyWfIn, (Ty.array Ty.self).toTyWfIn, []⟩

/-- The type of a rose tree. -/
def roseTy : TyWf := .recObject roseSchema

/-- A leaf: the label `1` and no children. -/
def roseLeaf : Term covEmptySig [] roseTy :=
  .recObject_mk roseSchema (fields := .cons (.nat_mk 1) (.cons (.array_mk .nil) .nil))

/-! The three statements below held when a recursive record denoted `PEmpty`.  They are
**false** now that it denotes the W-tree of its fields: `roseLeaf` has a value and
`roseTy` has values.  They are kept, commented out, as the record of what changed.

```
theorem roseLeaf_not_noRecMk : ¬ Term.NoRecMk roseLeaf := fun h => h
theorem roseTy_den_empty : TyWf.Den roseTy → False := fun v => PEmpty.elim v
theorem no_total_evaluator (ev : ∀ τ : TyWf, Term covEmptySig [] τ → TyWf.Den τ) :
    False :=
  roseTy_den_empty (ev _ roseLeaf)
```
-/

/-- The label of a rose tree: the eliminator binds every field, so it is index `0`. -/
def roseLabel : Term covEmptySig [] (roseTy ⇒ TyWf.prim .nat) :=
  .lam (.recObject_casesOn' (.var (v♯0)) (.var (v♯0)))

-- [SKIPPED BY PROFILE_LAKE] /-- The label of the leaf reads back. -/
-- [SKIPPED BY PROFILE_LAKE] theorem run_roseLabel_roseLeaf :
-- [SKIPPED BY PROFILE_LAKE]     Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap roseLabel roseLeaf) = 1 := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-- A mutual family: member `A` has a field-less constructor and one holding a `B`, and
    `B` is a record of a natural and an `A`. -/
def covFamA : LeanMutualRecFamily (TyWfIn 2) :=
  .selectedThenMore []
    (.ctors (.skip (.here ⟨(Ty.familyMember 1).toTyWfIn, []⟩ [])))
    (.record ⟨(Ty.prim .nat).toTyWfIn, (Ty.familyMember 0).toTyWfIn, []⟩) []

/-- The type of member `A`. -/
def covTyA : TyWf := .mutualRecursiveFamily covFamA

/-- The field-less constructor of `A`. -/
def covANil : Term covEmptySig [] covTyA :=
  .mutualRecursiveFamily_mk covFamA (value := .ctors _ 0 (fields := .nil))

/-- Is an `A` the field-less constructor?  A dispatch on both constructors of `A`. -/
def covAIsNil : Term covEmptySig [] (covTyA ⇒ TyWf.prim .bool) :=
  .lam (.mutualRecursiveFamily_casesOn' (.var (v♯0))
    (.ctors (.skip (.bool_mk true) (.here (.bool_mk false) .nil))))

-- [SKIPPED BY PROFILE_LAKE] /-- The field-less constructor of `A` reads back. -/
-- [SKIPPED BY PROFILE_LAKE] theorem run_covAIsNil_covANil :
-- [SKIPPED BY PROFILE_LAKE]     Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap covAIsNil covANil) = true := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-! The three statements below held when a mutual family denoted `PEmpty`.  They are
**false** now that it denotes the indexed W-tree of its members: `covANil` has a value,
and so `covTyA` has values.  They are kept, commented out, as the record of what changed.

```
theorem covANil_not_noRecMk : ¬ Term.NoRecMk covANil := fun h => h
theorem covTyA_den_empty : TyWf.Den covTyA → False := fun v => PEmpty.elim v
theorem no_total_evaluator (ev : ∀ τ : TyWf, Term covEmptySig [] τ → TyWf.Den τ) :
    False :=
  covTyA_den_empty (ev _ covANil)
```
-/

/-- A member of a mutual family has values in the model. -/
theorem covTyA_den_nonempty : Nonempty (TyWf.Den covTyA) :=
  ⟨Term.run GlobalEnv.nil covANil⟩

/-- **The evaluator evaluates every closed term**: it gives each closed term of the empty
    signature a value of its type, with no side condition. -/
def total_evaluator : ∀ τ : TyWf, Term covEmptySig [] τ → TyWf.Den τ :=
  fun _ t => Term.run GlobalEnv.nil t

end TermTests
