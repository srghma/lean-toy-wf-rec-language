module

public import LeanScript.Ty.Ty
public import LeanScript.Ty.TyBEq
public import LeanScript.Ty.Wf
public import LeanScript.Ty.TyWf
public meta import LeanScript.Ty.TyWf
public import LeanScript.Ty.TyWfIn
public meta import LeanScript.Ty.WfTactic
public import LeanScript.ExprCtx
public meta import LeanScript.ExprCtx
public import LeanScript.DeBruijn
public import LeanScript.Expr.SelfField
public import LeanScript.Ty.Traversable

@[expose] public section

/-!
# Printing, mapping and the remaining coercions

Pins the `Repr` instances of the trees and the schemas, the `Functor`/`LawfulFunctor`
instances of the schemas and shapes (whose `<$>` is their `map`), and the coercions
between the schemas.
-/

open LeanScript

namespace InstancesTest

/-! ## Floats have decidable equality

`Float`, `Float32` and their models have `DecidableEq` (equality of the bits), so a type
holding them is not kept from having one.  Note that `==` on `Float` is IEEE equality,
which is not `LawfulBEq` (`NaN != NaN`, `0.0 == -0.0`), so it is not the `BEq` that
comes from `DecidableEq`. -/

example : DecidableEq Float := inferInstance
example : DecidableEq Float32 := inferInstance
example : DecidableEq Float.Model := inferInstance
example : DecidableEq Float32.Model := inferInstance

/-! ## `Repr` -/

-- [SKIPPED BY PROFILE_LAKE] /--
-- [SKIPPED BY PROFILE_LAKE] info: LeanScript.Ty.shape
-- [SKIPPED BY PROFILE_LAKE]   (LeanScript.TyShape.record
-- [SKIPPED BY PROFILE_LAKE]     { fst := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.nat)),
-- [SKIPPED BY PROFILE_LAKE]       snd := LeanScript.Ty.self,
-- [SKIPPED BY PROFILE_LAKE]       rest := [] })
-- [SKIPPED BY PROFILE_LAKE] -/
-- [SKIPPED BY PROFILE_LAKE] #guard_msgs in
-- [SKIPPED BY PROFILE_LAKE] #eval (Ty.record ⟨.prim .nat, .self, []⟩ : Ty)

-- [SKIPPED BY PROFILE_LAKE] /-- info: { toTy := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.bool)), isWf := _ } -/
-- [SKIPPED BY PROFILE_LAKE] #guard_msgs in
-- [SKIPPED BY PROFILE_LAKE] #eval (⟨.prim .bool, by ty_wf⟩ : TyWf)

-- [SKIPPED BY PROFILE_LAKE] /-- info: LeanScript.LeanFamMemberSchema.alias 3 -/
-- [SKIPPED BY PROFILE_LAKE] #guard_msgs in
-- [SKIPPED BY PROFILE_LAKE] #eval (LeanFamMemberSchema.alias 3 : LeanFamMemberSchema Nat)

-- [SKIPPED BY PROFILE_LAKE] /-- info: { name := "x", ty := { toTy := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.nat)), isWf := _ } } -/
-- [SKIPPED BY PROFILE_LAKE] #guard_msgs in
-- [SKIPPED BY PROFILE_LAKE] #eval (⟨"x", ⟨.prim .nat, by ty_wf⟩⟩ : GlobalDecl)

example : Repr (LeanTaggedUnionSchema Nat) := inferInstance
example : Repr (CtorsWithPayload Nat) := inferInstance
example : Repr (LeanMutualRecFamily Nat) := inferInstance
example : Repr (TyShape Nat) := inferInstance
example : Repr (TyWfIn 1) := inferInstance
example : Repr Sig := inferInstance
example : Repr (DeBruijnProj id [Ty.self] Ty.self) := inferInstance
example : Repr (SelfField []) := inferInstance

/-! ## Equality of the indexed pointers comes from their decidable equality -/

example : LawfulBEq (SelfField []) := inferInstance
example : LawfulBEq (FamilyMemberField (n := 0) 0 []) := inferInstance

/-! ## `Functor` and `LawfulFunctor` -/

example : LawfulFunctor LeanRecordSchema := inferInstance
example : LawfulFunctor CtorsWithPayload := inferInstance
example : LawfulFunctor LeanTaggedUnionSchema := inferInstance
example : LawfulFunctor LeanFamMemberSchema := inferInstance
example : LawfulFunctor LeanMutualRecFamily := inferInstance
example : LawfulFunctor LeanPrimTyCovariant := inferInstance
example : LawfulFunctor TyShape := inferInstance

-- [SKIPPED BY PROFILE_LAKE] example : ((· + 1) <$> (⟨1, 2, [3]⟩ : LeanRecordSchema Nat)) = ⟨2, 3, [4]⟩ := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ((· * 2) <$> (TyShape.fn 1 2 : TyShape Nat)) = .fn 2 4 := rfl
example (s : LeanTaggedUnionSchema Nat) : id <$> s = s := id_map s

/-! ## Coercions -/

example (s : LeanRecordSchema Ty) : Ty := s
example (s : LeanTaggedUnionSchema Ty) : Ty := s
example (e : LeanEnumSchema) : Ty := e
example (c : CtorsWithPayload Nat) : LeanTaggedUnionSchema Nat := c
example (s : LeanRecordSchema Nat) : LeanFamMemberSchema Nat := s
example (s : LeanTaggedUnionSchema Nat) : LeanFamMemberSchema Nat := s
example (t : TyWf) : TyWfIn 1 := t
-- [SKIPPED BY PROFILE_LAKE] example (t : TyWf) : ((t : TyWfIn 1) : Ty) = t.toTy := rfl

end InstancesTest
