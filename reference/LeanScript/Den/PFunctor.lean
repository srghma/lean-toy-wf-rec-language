module

public import Mathlib.Data.PFunctor.Univariate.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Polynomial functors and their W-types

What `LeanScript.Ty.Den` needs to give a **recursive** tagged union its values: the least
fixpoint of the functor the union's payload describes.  Every former of a payload is a
*container* — a type of shapes and, for each shape, a type of holes where an occurrence
of the binder sits — which is exactly Mathlib's polynomial functor `PFunctor` (shapes
`P.A`, holes `P.B`), and the least fixpoint of a polynomial functor is Mathlib's
**W-type** `WType P.B` (which is also `PFunctor.W P`): a tree whose nodes are shapes and
whose children are indexed by the holes.

Nothing here is specific to the language: these are the formers of polynomial functors
the denotation is built from (`PFunctor.const`, `PFunctor.prod`, `PFunctor.sigma`,
`PFunctor.pi`, `PFunctor.list`, `PFunctor.array`, `PFunctor.mu`), a few operations on
Mathlib's `PFunctor.Obj` (the extension of a polynomial functor at a type), and a
memoising fold of a `WType`.
-/

namespace PFunctor

/-- A constant: every value is a shape, and no shape has a hole. -/
@[reducible] def const (A : Type) : PFunctor.{0, 0} := ⟨A, fun _ => PEmpty⟩

/-- A product: a shape of each, and the holes of both. -/
@[reducible] def prod (c d : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  ⟨c.A × d.A, fun p => c.B p.1 ⊕ d.B p.2⟩

/-- A sum over `I`: an index and a shape of that summand, with its holes. -/
@[reducible] def sigma (I : Type) (c : I → PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  ⟨(i : I) × (c i).A, fun p => (c p.1).B p.2⟩

/-- An exponent: a function from `A` to shapes; a hole is an argument and a hole of the
    shape at it. -/
@[reducible] def pi (A : Type) (c : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  ⟨A → c.A, fun f => (a : A) × c.B (f a)⟩

/-- The holes of a list of shapes: the holes of each element, in order. -/
@[reducible] def ListPos {S : Type} (P : S → Type) : List S → Type
  | [] => PEmpty
  | s :: ss => P s ⊕ ListPos P ss

/-- A list: a list of shapes, with the holes of each.  No type of the language denotes
    it — `Ty.array` denotes `PFunctor.array` — but it is what `PFunctor.array` is built
    from, and the list-level functions below work on it. -/
@[reducible] def list (c : PFunctor.{0, 0}) : PFunctor.{0, 0} := ⟨List c.A, ListPos c.B⟩

/-- An array: an array of shapes, with the holes of each, in order — the holes of the
    list of its elements. -/
@[reducible] def array (c : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  ⟨Array c.A, fun a => ListPos c.B a.toList⟩

/-- The least fixpoint, which has no holes left: it is closed.  Its shapes are the
    W-type of `c` (Mathlib's `WType c.B`, which is `PFunctor.W c`). -/
@[reducible] def mu (c : PFunctor.{0, 0}) : PFunctor.{0, 0} := const (WType c.B)

namespace Obj

/-- Pair two extensions. -/
def pair {c d : PFunctor.{0, 0}} {Y : Type} (x : c.Obj Y) (y : d.Obj Y) : (prod c d).Obj Y :=
  ⟨(x.1, y.1), fun | .inl p => x.2 p | .inr q => y.2 q⟩

/-- The first component of an extension of a product. -/
def prodFst {c d : PFunctor.{0, 0}} {Y : Type} (x : (prod c d).Obj Y) : c.Obj Y :=
  ⟨x.1.1, fun p => x.2 (.inl p)⟩

/-- The second component of an extension of a product. -/
def prodSnd {c d : PFunctor.{0, 0}} {Y : Type} (x : (prod c d).Obj Y) : d.Obj Y :=
  ⟨x.1.2, fun p => x.2 (.inr p)⟩

/-- Put an extension in front of an extension of a list. -/
def cons {c : PFunctor.{0, 0}} {Y : Type} (h : c.Obj Y) (t : (list c).Obj Y) :
    (list c).Obj Y :=
  ⟨h.1 :: t.1, fun | .inl p => h.2 p | .inr q => t.2 q⟩

/-- A list of extensions, from a list of values and a way to turn each into one. -/
def ofList {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y) :
    List α → (list c).Obj Y
  | [] => ⟨[], fun p => PEmpty.elim p⟩
  | x :: xs => cons (f x) (ofList f xs)

/-- The other direction of `PFunctor.Obj.ofList`. -/
def toList {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (h : c.Obj Y → α) :
    (xs : List c.A) → (ListPos c.B xs → Y) → List α
  | [], _ => []
  | s :: ss, g => h ⟨s, fun p => g (.inl p)⟩ :: toList h ss (fun q => g (.inr q))

/-- An array of extensions, from an array of values and a way to turn each into one. -/
def ofArray {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y) (xs : Array α) :
    (array c).Obj Y :=
  ⟨⟨(ofList f xs.toList).1⟩, (ofList f xs.toList).2⟩

/-- The other direction of `PFunctor.Obj.ofArray`. -/
def toArray {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (h : c.Obj Y → α) (xs : Array c.A)
    (g : ListPos c.B xs.toList → Y) : Array α :=
  ⟨toList h xs.toList g⟩

/-- An extension of an exponent, pointwise. -/
def ofPi {c : PFunctor.{0, 0}} {Y : Type} {A : Type} (g : A → c.Obj Y) : (pi A c).Obj Y :=
  ⟨fun y => (g y).1, fun q => (g q.1).2 q.2⟩

theorem pair_prodFst_prodSnd {c d : PFunctor.{0, 0}} {Y : Type} (x : (prod c d).Obj Y) :
    pair (prodFst x) (prodSnd x) = x := by
  obtain ⟨⟨s, t⟩, f⟩ := x
  exact congrArg (Sigma.mk (s, t)) (funext fun | .inl _ => rfl | .inr _ => rfl)

theorem const_eta {Y : Type} {A : Type} (s : A) (f : (const A).B s → Y) :
    (⟨s, fun p => PEmpty.elim p⟩ : (const A).Obj Y) = ⟨s, f⟩ :=
  congrArg (Sigma.mk s) (funext fun p => PEmpty.elim p)

theorem toList_ofList {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y)
    (h : c.Obj Y → α) (hr : ∀ x, h (f x) = x) : ∀ xs : List α,
    toList h (ofList f xs).1 (ofList f xs).2 = xs
  | [] => rfl
  | x :: xs => by
      show h ⟨(f x).1, fun p => (f x).2 p⟩ :: _ = x :: xs
      rw [List.cons.injEq]
      exact ⟨hr x, toList_ofList f h hr xs⟩

theorem ofList_toList {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y)
    (h : c.Obj Y → α) (hr : ∀ e, f (h e) = e) : ∀ (ss : List c.A) (g : ListPos c.B ss → Y),
    ofList f (toList h ss g) = ⟨ss, g⟩
  | [], g => congrArg (Sigma.mk []) (funext fun p => PEmpty.elim p)
  | s :: ss, g => by
      have ih := ofList_toList f h hr ss (fun q => g (.inr q))
      have hx := hr ⟨s, fun p => g (.inl p)⟩
      show (⟨_, _⟩ : (list c).Obj Y) = _
      generalize f (h ⟨s, fun p => g (.inl p)⟩) = A at hx ⊢
      generalize ofList f (toList h ss fun q => g (.inr q)) = B at ih ⊢
      subst hx ih
      exact congrArg (Sigma.mk (s :: ss)) (funext fun | .inl _ => rfl | .inr _ => rfl)

theorem toArray_ofArray {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y)
    (h : c.Obj Y → α) (hr : ∀ x, h (f x) = x) (xs : Array α) :
    toArray h (ofArray f xs).1 (ofArray f xs).2 = xs := by
  cases xs with
  | mk l => exact congrArg Array.mk (toList_ofList f h hr l)

theorem ofArray_toArray {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (f : α → c.Obj Y)
    (h : c.Obj Y → α) (hr : ∀ e, f (h e) = e) (ss : Array c.A)
    (g : ListPos c.B ss.toList → Y) :
    ofArray f (toArray h ss g) = ⟨ss, g⟩ := by
  cases ss with
  | mk l =>
      have e := ofList_toList f h hr l g
      show (⟨⟨(ofList f (toList h l g)).1⟩,
        (ofList f (toList h l g)).2⟩ : (array c).Obj Y) = _
      generalize ofList f (toList h l g) = B at e ⊢
      subst e
      rfl

/-- A list of values is an extension of the list container, when each value is an
    extension of the element container: `ofList` and `toList` as a Mathlib `Equiv`. -/
def listEquiv {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (e : α ≃ c.Obj Y) :
    List α ≃ (list c).Obj Y where
  toFun := ofList e
  invFun x := toList e.symm x.1 x.2
  left_inv := toList_ofList e e.symm e.symm_apply_apply
  right_inv x := ofList_toList e e.symm e.apply_symm_apply x.1 x.2

/-- The same for arrays: `ofArray` and `toArray` as a Mathlib `Equiv`. -/
def arrayEquiv {c : PFunctor.{0, 0}} {Y : Type} {α : Type} (e : α ≃ c.Obj Y) :
    Array α ≃ (array c).Obj Y where
  toFun := ofArray e
  invFun x := toArray e.symm x.1 x.2
  left_inv := toArray_ofArray e e.symm e.symm_apply_apply
  right_inv x := ofArray_toArray e e.symm e.apply_symm_apply x.1 x.2

end Obj

end PFunctor

/-! ## Folding a W-tree, remembering every answer

A depth-`k` fold looks at the answers of the fold at subtrees up to `k` levels down.
Rather than recomputing them, the fold stores its answer at every node: `WType.memo`
turns a tree into the same tree with the answer at each node beside its shape, bottom-up,
so a branch that looks further down reads answers that are already there. -/

namespace WType

/-- A tree with the fold's answer stored at every node. -/
abbrev Memo (S : Type) (P : S → Type) (β : Type) := WType (fun p : S × β => P p.1)

/-- The answer stored at the root. -/
def Memo.answer {S : Type} {P : S → Type} {β : Type} : Memo S P β → β
  | .mk (_, b) _ => b

/-- The tree with the answer at every node: first the children's memos, then the answer
    at this node, from its shape and its children's memos (which hold every answer
    below it). -/
def memo {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) : WType P → Memo S P β
  | .mk s f =>
      let kids := fun p => memo step (f p)
      .mk (s, step s kids) kids

/-- The answer of the memoised fold at the root. -/
def memoFold {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (v : WType P) : β :=
  (memo step v).answer

/-- The plain fold of a W-tree: the answer at a node from its shape, its subtrees and the
    answers at them. -/
def fold {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → WType P) → (P s → β) → β) : WType P → β
  | .mk s f => step s f (fun p => fold step (f p))

/-- Forgetting the answers of a memo gives back the tree: Mathlib's `WType.elim`, rebuilding
    every node without its answer. -/
def Memo.tree {S : Type} {P : S → Type} {β : Type} : Memo S P β → WType P :=
  WType.elim _ fun x => .mk x.1.1 x.2

theorem memo_mk {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (s : S) (f : P s → WType P) :
    memo step (.mk s f) =
      .mk (s, step s (fun p => memo step (f p))) (fun p => memo step (f p)) :=
  rfl

theorem memoFold_mk {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (s : S) (f : P s → WType P) :
    memoFold step (.mk s f) = step s (fun p => memo step (f p)) :=
  rfl

/-- The memo of a tree is that tree, with answers. -/
theorem memo_tree {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) : ∀ v : WType P,
    (memo step v).tree = v
  | .mk s f => by
      show WType.mk s (fun p => (memo step (f p)).tree) = _
      exact congrArg (WType.mk s) (funext fun p => memo_tree step (f p))

end WType

end
