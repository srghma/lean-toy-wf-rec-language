module

@[expose] public section

set_option autoImplicit false

/-!
# One de Bruijn family, up to a projection

Every scope of the language — the variables, the labels, the recursions and the module
signature — is an instance of the single inductive family defined here.  Three of them
index an entry *by itself* (`DeBruijn`, the case `f := id`); the fourth, a reference into
the module signature, indexes a declaration by its **type**, and that projection is
exactly what the parameter `f` supplies.

This file used to be the first section of `LeanScript.Expr`.  It is separate so that
`LeanScript.Env` — the runtime environments, which a `Term` now mentions, because
the recursion schemes carry a subject of their arguments — can be defined before the
grammar
without dragging the grammar in.
-/

namespace LeanScript

/-- **A typed de Bruijn index, up to a projection**: constructive evidence that some
    entry of `xs` occurs in it *whose image under `f` is `b`*, together with *where*.

    Every scope of the language is an instance of this one family.  The three scopes
    whose index *is* the entry — variables, labels and recursions — take `f := id`, and
    are packaged as `DeBruijn`.  The signature of the module takes `f := GlobalDecl.ty`:
    its entries are declarations, but a reference to one is indexed by the declaration's
    **type**, and that projection is exactly what `f` supplies. -/
inductive DeBruijnProj {α β : Type} (f : α → β) : List α → β → Type
  /-- The entry just bound. -/
  | head : ∀ {x : α} {xs : List α}, DeBruijnProj f (x :: xs) (f x)
  /-- An entry bound further out. -/
  | tail : ∀ {x : α} {xs : List α} {b : β},
      DeBruijnProj f xs b → DeBruijnProj f (x :: xs) b
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- How many binders out an index is. -/
def DeBruijnProj.index {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β}, DeBruijnProj f xs b → Nat
  | _, _, .head => 0
  | _, _, .tail v => DeBruijnProj.index v + 1

/-- The entry of `xs` an index points at. -/
def DeBruijnProj.entry {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β}, DeBruijnProj f xs b → α
  | x :: _, _, .head => x
  | _ :: _, _, .tail v => DeBruijnProj.entry v

/-- The entry an index points at is one of the entries. -/
theorem DeBruijnProj.entry_mem {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β} (v : DeBruijnProj f xs b), v.entry ∈ xs
  | _ :: _, _, .head => by simp [DeBruijnProj.entry]
  | _ :: _, _, .tail v => by
      have := DeBruijnProj.entry_mem v
      simp [DeBruijnProj.entry]
      exact Or.inr this

/-- The index of an entry is an index at that entry's image. -/
theorem DeBruijnProj.f_entry {α β : Type} {f : α → β} :
    ∀ {xs : List α} {b : β} (v : DeBruijnProj f xs b), f v.entry = b
  | _ :: _, _, .head => rfl
  | _ :: _, _, .tail v => DeBruijnProj.f_entry v

/-- **A typed de Bruijn index**: constructive evidence that `x` occurs in `xs`, together
    with *where* — the special case of `DeBruijnProj` whose projection is the identity. -/
abbrev DeBruijn {α : Type} (xs : List α) (x : α) : Type := DeBruijnProj id xs x

/-- The entry just bound. -/
@[match_pattern] abbrev DeBruijn.head {α : Type} {x : α} {xs : List α} :
    DeBruijn (x :: xs) x := DeBruijnProj.head

/-- An entry bound further out. -/
@[match_pattern] abbrev DeBruijn.tail {α : Type} {x y : α} {xs : List α}
    (v : DeBruijn xs x) : DeBruijn (y :: xs) x := DeBruijnProj.tail v

/-- How many binders out an index is. -/
abbrev DeBruijn.index {α : Type} {xs : List α} {x : α} (v : DeBruijn xs x) : Nat :=
  DeBruijnProj.index v

end LeanScript

end
