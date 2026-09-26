module

public import LeanScript.Ty.Ty
public import LeanScript.Ty.TyBEq
public import LeanScript.Ty.Wf
public import LeanScript.Ty.TyWf
public import LeanScript.Ty.Class
public meta import LeanScript.Ty.WfTactic
public import LeanScript.Ty.Instances

@[expose] public section

/-!
# Equality of trees, and the coercions between them

`Ty.beq` is the equality of trees (`LeanScript.Ty.TyBEq`), so `==` on a `Ty` is lawful and
a `Ty` has a decidable equality; the same holds of a bundled `TyWf`, whose second field is
a proof.  This file pins both, together with the coercions that let a leaf, a node or a
bundled tree stand where a tree is wanted.
-/

open LeanScript

namespace EqTest

/-! ## `==` on a tree is its equality -/

example : (Ty.prim .nat == Ty.prim .nat) = true := beq_self_eq_true _
example : ¬ (Ty.prim .nat = Ty.prim .bool) := by
  intro h
  have : Ty.beq (.prim .nat) (.prim .bool) = true := Ty.beq_of_eq h
  simp [Ty.beq, Ty.beqShape] at this

example (a b : Ty) (h : a == b) : a = b := eq_of_beq h
example (a : Ty) : (a == a) = true := beq_self_eq_true a

/-- A decidable equality of trees, used as one. -/
example (a b : Ty) : Bool := if a = b then true else false

/-! ## A bundled tree

Two bundles are equal when their trees are: the second field is a proof. -/

example (s t : TyWf) (h : s.toTy = t.toTy) : s = t := TyWf.ext h
example (s : TyWf) : (s == s) = true := beq_self_eq_true s
example (s t : TyWf) (h : s == t) : s = t := eq_of_beq h

/-! ## The coercions

A terminal type, a node and a bundled tree each stand where a tree is wanted. -/

example : Ty := (LeanPrimTy.nat : Ty)
example : Ty := ((.array (Ty.prim .nat) : LeanPrimTyCovariant Ty) : Ty)
example : Ty := ((.fn (Ty.prim .nat) (Ty.prim .bool) : TyShape Ty) : Ty)
example : Ty := tyWfOf Nat

-- [SKIPPED BY PROFILE_LAKE] example : (tyWfOf Nat : Ty) = Ty.prim .nat := rfl

-- and back: a tree becomes a bundle, with `ty_wf` writing the proof
example : TyWf := (Ty.prim .nat).toTyWf
-- [SKIPPED BY PROFILE_LAKE] example : ((Ty.array (.prim .nat)).toTyWf).toTy = .array (.prim .nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (List Nat) = .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])) := rfl

/-! ## The schemas and the shapes compare too -/

example : (Ty.record ⟨.prim .nat, .prim .bool, []⟩ == Ty.record ⟨.prim .nat, .prim .bool, []⟩)
    = true := beq_self_eq_true _
example : ((⟨.prim .nat, .prim .bool, []⟩ : LeanRecordSchema Ty)
    == ⟨.prim .nat, .prim .bool, []⟩) = true := beq_self_eq_true _
example : (LeanEnumSchema.mk 0 (-1) == ⟨0, -1⟩) = true := beq_self_eq_true _

end EqTest
