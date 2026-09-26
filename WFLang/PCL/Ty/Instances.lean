module

public import LeanScript.Ty.Class
meta import LeanScript.Ty.WfTactic

@[expose] public section

namespace LeanScript

/-!
# The instances the language comes with

The Lean types the language knows about have their model written here, once: the terminal
types, the type formers it has a shape for (`Array`, `Thunk`, `→`), and the handful of
library types whose model is a *decision* rather than a mechanical translation.

Everything else gets its instance from `deriving LeanScriptTyWf`
(`LeanScript.Ty.Deriving`), which builds a type's tree out of the trees of these.

## Why some of these are written by hand

`Ordering` is the example.  Mechanically it is a field-less sum of three constructors, so
a translation would give it `Ty.enum ⟨0, 0⟩` — the constructors numbered `0`, `1`, `2`.
What it should be is the enum numbered from `-1`, so that `lt`, `eq` and `gt` are `-1`,
`0` and `1` and comparison is a subtraction.  Because the answer lives in an instance,
that decision is made **once** and everything that mentions an `Ordering` — every record
with an `Ordering` field, in any module — uses it; there is no second model of `Ordering`
anywhere, and nothing has to know that the model is unusual.
-/

/-! ## Terminal types -/

instance : LeanScriptTyWf Nat := ⟨.prim .nat, by ty_wf⟩
instance : LeanScriptTyWf Int := ⟨.prim .int, by ty_wf⟩
instance : LeanScriptTyWf Bool := ⟨.prim .bool, by ty_wf⟩
instance : LeanScriptTyWf Char := ⟨.prim .char, by ty_wf⟩
instance : LeanScriptTyWf String := ⟨.prim .string, by ty_wf⟩
instance : LeanScriptTyWf UInt8 := ⟨.prim .uint8, by ty_wf⟩
instance : LeanScriptTyWf UInt16 := ⟨.prim .uint16, by ty_wf⟩
instance : LeanScriptTyWf UInt32 := ⟨.prim .uint32, by ty_wf⟩
instance : LeanScriptTyWf UInt64 := ⟨.prim .uint64, by ty_wf⟩
instance : LeanScriptTyWf Int8 := ⟨.prim .int8, by ty_wf⟩
instance : LeanScriptTyWf Int16 := ⟨.prim .int16, by ty_wf⟩
instance : LeanScriptTyWf Int32 := ⟨.prim .int32, by ty_wf⟩
instance : LeanScriptTyWf Int64 := ⟨.prim .int64, by ty_wf⟩
instance : LeanScriptTyWf Float := ⟨.prim .float, by ty_wf⟩
instance : LeanScriptTyWf Float32 := ⟨.prim .float32, by ty_wf⟩
instance : LeanScriptTyWf String.Pos.Raw := ⟨.prim .stringPosRaw, by ty_wf⟩
instance : LeanScriptTyWf Substring.Raw := ⟨.prim .substringRaw, by ty_wf⟩
instance : LeanScriptTyWf String.Slice := ⟨.prim .stringSlice, by ty_wf⟩

/-- `BitVec 0` has one value, so it carries no information and the language erases it;
    the instance is therefore stated at `n + 1`, which is also where the positivity
    condition of `LeanPrimTy.bitvec` is discharged. -/
instance (n : Nat) : LeanScriptTyWf (BitVec (n + 1)) :=
  ⟨.prim (.bitvec (n + 1) (Nat.succ_pos n)), by ty_wf⟩

/-! ## The type formers the language has a shape for -/

instance [LeanScriptTyWf α] : LeanScriptTyWf (Array α) := ⟨.array (tyWfOf α), by ty_wf⟩
instance [LeanScriptTyWf α] : LeanScriptTyWf (Thunk α) := ⟨.thunk (tyWfOf α), by ty_wf⟩

/-- Every function of the language is curried, so `α → β` is one parameter and one
    result. -/
instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α → β) :=
  ⟨.fn (tyWfOf α) (tyWfOf β), by ty_wf⟩

/-! ## Library types

Each of these is the tree `deriving LeanScriptTyWf` would give it, written out here because
the declaration belongs to the core library and cannot carry a `deriving` clause — except
`Ordering`, whose model is a decision (see the header).

The trees are stated once, as type formers of the language (`TyWf.option`, `TyWf.prod`,
`TyWf.sum`, `TyWf.list`, `TyWf.ordering`), and the instances are these formers applied to
the models of the arguments.  Everything else that needs the model of one of these types —
the externs of `Init` (`LeanScript.Expr.Extern`), the reading back of a list value
(`LeanScript.Den.Rec`), `#leanscript_to_term` — uses the same formers, so there is one
model of each. -/

namespace TyWf

/-- `Option α`: constructor `0` (`none`) carries nothing; constructor `1` (`some`) carries
    the value. -/
@[reducible] def option (α : TyWf) : TyWf :=
  ⟨.taggedUnion (.skip (.here ⟨α, []⟩ [])), by ty_wf⟩

/-- `α × β`: one constructor with two fields, in that order. -/
@[reducible] def prod (α β : TyWf) : TyWf := ⟨.record ⟨α, β, []⟩, by ty_wf⟩

/-- `α ⊕ β`: two constructors, each with one field. -/
@[reducible] def sum (α β : TyWf) : TyWf :=
  ⟨.taggedUnion (.payloadFirst ⟨α, []⟩ [β] []), by ty_wf⟩

/-- `List α`: the recursive sum `nil | cons (_ : α) (_ : self)`. -/
@[reducible] def list (α : TyWf) : TyWf := ⟨.recTaggedUnion (Ty.listSchema α), by ty_wf⟩

/-- `Ordering`: `lt`, `eq` and `gt` are `-1`, `0` and `1` — the enum is shifted, which a
    mechanical translation of the declaration would not have done.  Its values are still
    the constructor numbers `0`, `1`, `2`, in the order of the constructors of
    `Ordering`. -/
@[reducible] def ordering : TyWf := ⟨.enum ⟨0, -1⟩, by ty_wf⟩

/-- `Lean.Name`: the recursive tagged union `anonymous | str self String | num self Nat`,
    the tree `deriving LeanScriptTyWf` gives the declaration. -/
@[reducible] def leanName : TyWf :=
  ⟨.recTaggedUnion (.skip (.here ⟨.self, [.prim .string]⟩ [[.self, .prim .nat]])), by ty_wf⟩

end TyWf

instance [LeanScriptTyWf α] : LeanScriptTyWf (Option α) := ⟨TyWf.option (tyWfOf α)⟩

instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α × β) :=
  ⟨TyWf.prod (tyWfOf α) (tyWfOf β)⟩

/-- A pair one component of which is `Unit` is the other component: the language erases
    `Unit`, and a structure with one field the language keeps is that field (as for a
    structure declared with `deriving LeanScriptTyWf`).  This is the state `do` gives a
    `for` loop that can `return` from inside and has no `let mut` variable,
    `Option ρ × Unit`. -/
instance (priority := high) [LeanScriptTyWf α] : LeanScriptTyWf (α × Unit) := ⟨tyWfOf α⟩

/-- See the instance for `α × Unit`. -/
instance (priority := high) [LeanScriptTyWf β] : LeanScriptTyWf (Unit × β) := ⟨tyWfOf β⟩

/-- `PProd` at `Type`, the pair Lean uses for the answers of the functions of a `mutual`
    block that recurse on the same type: the same record as `α × β`. -/
instance {α β : Type} [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (PProd α β) :=
  ⟨TyWf.prod (tyWfOf α) (tyWfOf β)⟩

instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α ⊕ β) :=
  ⟨TyWf.sum (tyWfOf α) (tyWfOf β)⟩

instance [LeanScriptTyWf α] : LeanScriptTyWf (List α) := ⟨TyWf.list (tyWfOf α)⟩

/-- `ForInStep α`, the answer of one iteration of a `for` loop: constructor `0` (`done`,
    leave the loop) and constructor `1` (`yield`, go on), each carrying the state — the
    same tagged union as `α ⊕ α`.  A loop that can `break` carries it as its state (see
    `LeanScript.ToTerm.ForIn`). -/
instance [LeanScriptTyWf α] : LeanScriptTyWf (ForInStep α) :=
  ⟨TyWf.sum (tyWfOf α) (tyWfOf α)⟩

/-- A subtype `{x // p x}` is modelled by the tree of `α`: its proof is erased, as every
    proof is, and a structure with one field the language keeps is that field.  So
    `List.attach l` has the tree of `l`. -/
instance {α : Type u} {p : α → Prop} [LeanScriptTyWf α] : LeanScriptTyWf (Subtype p) :=
  ⟨tyWfOf α⟩

instance : LeanScriptTyWf Ordering := ⟨TyWf.ordering⟩

instance : LeanScriptTyWf Lean.Name := ⟨TyWf.leanName⟩

end LeanScript

end
