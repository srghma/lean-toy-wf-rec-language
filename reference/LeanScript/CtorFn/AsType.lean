module

public import LeanScript.Ty.Class

@[expose] public section

/-!
# The type-level helpers of `#leanscript_ctor`

`TyWf.AsType`, a Lean type standing for a bundled tree, `TyWf.Hidden`, a Lean type standing
for a hidden type, and `TyWf.oneOf`, the tagged union
`#leanscript_to_term` builds where values of different types meet.
-/

namespace LeanScript

/-- A Lean type that stands for the bundle `t`: its values are irrelevant (it is `PUnit`), and
    its `LeanScriptTyWf` instance is `t`.  So `tyWfOf (F t.AsType)` is the tree `F`'s own
    instance gives `F α` when `α` is modelled by `t`.  This is how `#leanscript_ctor` writes
    the tree of a field of type `F S`, for a type argument `S`, when the tree of `F`'s instance
    is one the bundled smart constructors cannot rebuild — a recursive one, such as
    `List S`'s: it is `tyWfOf (List S.AsType)`. -/
def TyWf.AsType.{u} (_t : TyWf) : Type u := PUnit

instance TyWf.instLeanScriptTyWfAsType.{u} (t : TyWf) : LeanScriptTyWf (TyWf.AsType.{u} t) := ⟨t⟩

/-- A Lean type standing for a **hidden type** whose tree is `t`: the type field of a
    structure with an existential (`Unfold.State`), in a function that is translated for every
    choice of it (`LeanScript.ToTerm.ExistentialArgs`).  Its `LeanScriptTyWf` instance is `t`.

    Unlike `TyWf.AsType`, it is not `PUnit`: a value of it is a value of the hidden type, which
    the language keeps (a `PUnit` would be erased as a one-value type). -/
structure TyWf.Hidden.{u} (_t : TyWf) : Type u where
  /-- The only way to build one; a translated function never does. -/
  private mk ::

instance TyWf.instLeanScriptTyWfHidden.{u} (t : TyWf) : LeanScriptTyWf (TyWf.Hidden.{u} t) :=
  ⟨t⟩

/-- **One of** the types `a`, `b`, `cs…`: the tagged union with one constructor per type,
    whose one field is a value of that type.

    `#leanscript_to_term` builds it where values of *different* types meet — the branches of
    an `if` that build a datatype with existentials with different choices of the hidden
    types — and injects each value with the constructor of its own type. -/
@[reducible] def TyWf.oneOf (a b : TyWf) (cs : List TyWf) : TyWf :=
  TyWf.taggedUnion (.payloadFirst ⟨a, []⟩ [b] (cs.map fun c => [c]))

end LeanScript

end
