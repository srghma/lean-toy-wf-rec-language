module

public import LeanScript.Ty.TyWf
public meta import LeanScript.Ty.WfTactic

@[expose] public section

namespace LeanScript

/-!
# `LeanScriptTyWf`: the Lean types the language models

The class that gives a Lean type its bundled tree, with the accessors `tyWfOf` (the
bundle), `tyOf` (its tree) and `tyWf` (its proof).  The instances the language comes with
are in `LeanScript.Ty.Instances`; `deriving LeanScriptTyWf` is in `LeanScript.Ty.Deriving`.
-/

/-- The Lean types the language models: `α` has a tree, and the tree is a type of the
    language.  Both are one field, the bundle `LeanScript.TyWf`. -/
class LeanScriptTyWf (α : Type u) where
  /-- The tree of the language that models `α`, with its proof. -/
  tyWfOf : TyWf

/-- The bundled tree of the language that models `α`. -/
abbrev tyWfOf (α : Type u) [inst : LeanScriptTyWf α] : TyWf := inst.tyWfOf

/-- The tree of the language that models `α`: `tyOf Nat` is `Ty.prim .nat`. -/
abbrev tyOf (α : Type u) [inst : LeanScriptTyWf α] : Ty := inst.tyWfOf.toTy

/-- The proof that the tree of `α` is a type of the language: the instance's own, never
    recomputed. -/
abbrev tyWf (α : Type u) [inst : LeanScriptTyWf α] : Ty.Wf (tyOf α) := inst.tyWfOf.isWf

/-- And back: a bundled model is an instance for whatever type it is chosen to model. -/
@[instance_reducible] def TyWf.asModelOf (t : TyWf) (α : Type u) : LeanScriptTyWf α := ⟨t⟩

end LeanScript

end
