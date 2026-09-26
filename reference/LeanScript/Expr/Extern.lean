module

public import LeanScript.Den.Rec
public import LeanScript.Ty.Instances
public import LeanScript.LeanInitPureExterns
public import LeanScript.LeanInitPureExternShorthands

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The externs of `Init`

`LeanScript.LeanInitPureExtern` is written against an abstract type language `MyTy` with a
denotation `denote : MyTy → Type`.  This module instantiates it at the types of the
language, `LeanScript.TyWf`, with the evaluator's denotation `LeanScript.TyWf.Den`; the result,
`LeanScript.Extern`, is an extern *applied to values*, with the proofs the Lean function
takes: `Extern.lean_array_fget αt a i h`.  Its value is `LeanScript.Extern.eval`
(`LeanScript.Eval.Extern`), which calls the Lean function itself, handing it those proofs.
`LeanScript.Term.extern` holds one.  The catalogue is in two levels (a family of entries per
section of `Init`, and one constructor of `LeanInitPureExtern` per family); an entry is
written through its shorthand (`.lean_nat_add a b`, which is
`.preludeExtern (.lean_nat_add a b)`; `LeanScript.LeanInitPureExternShorthands`).

The catalogue asks for a few type formers the language does not have as primitives.  Each
is the model of the corresponding Lean type — the very former its `LeanScriptTyWf`
instance is built from (`LeanScript.Ty.Instances`), so a value an extern answers with has
the type any other part of the language gives that Lean type:

| catalogue      | here                                                                  |
| :------------- | :-------------------------------------------------------------------- |
| `list α`       | the recursive tagged union `nil \| cons α self` (`TyWf.list`)          |
| `option α`     | the tagged union `none \| some α` (`TyWf.option`)                      |
| `prod α β`     | the record with the two fields `α`, `β` (`TyWf.prod`)                  |
| `leanName`     | the recursive tagged union `anonymous \| str self String \| num self Nat` (`TyWf.leanName`) |
| `ordering`     | the enum `lt \| eq \| gt`, numbered from `-1` (`TyWf.ordering`)        |

The three coercions the catalogue expects (from `LeanPrimTy`, from a covariant wrapper of a
`LeanPrimTy`, and from a covariant wrapper of a type of the language) are instances below.
-/

namespace TyWf

/-- A covariant wrapper (array, thunk or lazy value) of a type of the language. -/
@[reducible] def primCovariant : LeanPrimTyCovariant TyWf → TyWf
  | .array a => TyWf.array a
  | .thunk a => TyWf.thunk a
  | .lazy a => TyWf.lazy a

end TyWf

instance instCoeLeanPrimTyTyWf : Coe LeanPrimTy TyWf := ⟨TyWf.prim⟩

instance instCoePrimCovariantLeanPrimTyTyWf : Coe (LeanPrimTyCovariant LeanPrimTy) TyWf :=
  ⟨fun c => TyWf.primCovariant (c.map TyWf.prim)⟩

instance instCoePrimCovariantTyWf : Coe (LeanPrimTyCovariant TyWf) TyWf :=
  ⟨TyWf.primCovariant⟩

/-- A pure extern of `Init`, applied to all of its arguments (and to the proofs it takes),
    whose result has type `τ`: `LeanScript.LeanInitPureExtern` at the types of the language
    and their values. -/
def Extern : TyWf → Type :=
  LeanInitPureExtern TyWf.Den TyWf.option TyWf.list TyWf.prod TyWf.leanName TyWf.ordering

/-! ## Values of the derived type formers

`TyWf.list`, `TyWf.option`, `TyWf.prod`, `TyWf.leanName` and `TyWf.ordering` are shapes of the language, so
their values are the values of those shapes; these functions build them from the Lean
values. -/

/-- The value of `TyWf.list α` a Lean list stands for. -/
def TyWf.Den.ofList {α : TyWf} : List α.Den → (TyWf.list α).Den :=
  Ty.DenRec.ofList α.toTy


/-- A value of `TyWf.list α`, read back as a Lean list: how an extern that takes a Lean
    list is handed a value of the language. -/
def TyWf.Den.toList {α : TyWf} : (TyWf.list α).Den → List α.Den :=
  Ty.DenRec.toList α.toTy

/-- The first of the values of a list of types. -/
def TyWf.DenList.head {σ : TyWf} {σs : List TyWf} (vs : TyWf.DenList (σ :: σs)) : σ.Den :=
  vs.1

/-- The values of a list of types, but the first. -/
def TyWf.DenList.tail {σ : TyWf} {σs : List TyWf} (vs : TyWf.DenList (σ :: σs)) :
    TyWf.DenList σs :=
  vs.2

/-- The value of `TyWf.option α` a Lean `Option` stands for. -/
def TyWf.Den.ofOption {α : TyWf} : Option α.Den → (TyWf.option α).Den
  | none => ⟨⟨0, Nat.zero_lt_succ 1⟩, PUnit.unit⟩
  | some a => ⟨⟨1, Nat.lt_succ_self 1⟩, (a, PUnit.unit)⟩

/-- The value of `TyWf.prod α β` a Lean pair stands for. -/
def TyWf.Den.ofProd {α β : TyWf} : α.Den × β.Den → (TyWf.prod α β).Den
  | (a, b) => (a, b, PUnit.unit)

/-- The value of `TyWf.ordering` a Lean `Ordering` stands for: its constructor number (the
    shift of the enum only changes how the constructors print). -/
def TyWf.Den.ofOrdering : Ordering → TyWf.ordering.Den
  | .lt => ⟨0, by decide⟩
  | .eq => ⟨1, by decide⟩
  | .gt => ⟨2, by decide⟩

/-- The value of `TyWf.leanName` a `Lean.Name` stands for: `anonymous` is the node without
    a subtree, and `str p s` / `num p n` hold `s` / `n` and have `p` as their one
    subtree. -/
def TyWf.Den.ofName : Lean.Name → TyWf.leanName.Den
  | .anonymous => WType.mk ⟨⟨0, by decide⟩, PUnit.unit⟩ (fun h => nomatch h)
  | .str p s => WType.mk ⟨⟨1, by decide⟩, (PUnit.unit, s, PUnit.unit)⟩ (fun _ => TyWf.Den.ofName p)
  | .num p n => WType.mk ⟨⟨2, by decide⟩, (PUnit.unit, n, PUnit.unit)⟩ (fun _ => TyWf.Den.ofName p)

/-- A value of `TyWf.leanName`, read back as a `Lean.Name`. -/
def TyWf.Den.toName : TyWf.leanName.Den → Lean.Name :=
  WType.elim _ fun
    | ⟨⟨⟨0, _⟩, _⟩, _⟩ => .anonymous
    | ⟨⟨⟨1, _⟩, (_, s, _)⟩, ih⟩ => .str (ih (.inl PUnit.unit)) s
    | ⟨⟨⟨2, _⟩, (_, n, _)⟩, ih⟩ => .num (ih (.inl PUnit.unit)) n

/-- Reading back a name built from a `Lean.Name` gives that name. -/
theorem TyWf.Den.toName_ofName (n : Lean.Name) : TyWf.Den.toName (TyWf.Den.ofName n) = n := by
  induction n with
  | anonymous => rfl
  | str p s ih => exact congrArg (Lean.Name.str · s) ih
  | num p k ih => exact congrArg (Lean.Name.num · k) ih

end LeanScript

end
