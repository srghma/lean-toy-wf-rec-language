module

public import LeanScript.Den.PFunctor

@[expose] public section

set_option autoImplicit false

/-!
# Indexed polynomial functors and their W-types

What `LeanScript.Ty.Den` needs to give a **mutual recursive family** its values.  A lone
recursive binder is the least fixpoint of one polynomial functor (`LeanScript.Den.PFunctor`),
and every hole of a shape holds a value of that one binder.  A family has one functor
per member, and a hole of a shape of one member holds a value of *some* member — the one
the occurrence `Ty.familyMember j` names.  So a container of a family records, beside the
shapes and the holes, the **target** of every hole: `IPFunctor.tgt`, a member number.

The least fixpoint of a list of such containers is the *indexed* W-type `IWType`: a tree
whose root is a node of member `i`, and whose child at a hole is a tree rooted at the
hole's target.  `FamW Fs i` is that tree for the list of containers `Fs` of a family, at
member `i`; a target the family does not have is read as member `0` (`selIdx`), which
`LeanScript.LeanMutualRecFamily.select` agrees with, so the value of an occurrence is the
value of a family selecting that member *definitionally* up to the members list.

As for `LeanScript.WType.memo`, `IWType.memo` stores the answer of a fold at every node,
bottom-up, so that a branch that looks further down reads answers that are already there.
-/

/-- An **indexed polynomial functor**: shapes, the holes of each shape, and for every
    hole the index (a member number) of what it holds. -/
structure IPFunctor : Type 1 where
  /-- The shapes. -/
  A : Type
  /-- The holes of a shape. -/
  B : A → Type
  /-- The member number a hole holds a value of. -/
  tgt : (a : A) → B a → Nat

namespace IPFunctor

/-- The extension of an indexed polynomial functor at a family of types: a shape, with a
    value of the right member in each hole. -/
def Obj (P : IPFunctor) (X : Nat → Type) : Type := (a : P.A) × ((b : P.B a) → X (P.tgt a b))

/-- A constant: every value is a shape, and no shape has a hole. -/
@[reducible] def const (A : Type) : IPFunctor := ⟨A, fun _ => PEmpty, fun _ p => PEmpty.elim p⟩

/-- An occurrence of member `j`: one shape, with one hole, which holds member `j`. -/
@[reducible] def hole (j : Nat) : IPFunctor := ⟨PUnit, fun _ => PUnit, fun _ _ => j⟩

/-- A product: a shape of each, and the holes of both. -/
@[reducible] def prod (c d : IPFunctor) : IPFunctor :=
  ⟨c.A × d.A, fun p => c.B p.1 ⊕ d.B p.2, fun p => Sum.elim (c.tgt p.1) (d.tgt p.2)⟩

/-- A sum over `I`: an index and a shape of that summand, with its holes. -/
@[reducible] def sigma (I : Type) (c : I → IPFunctor) : IPFunctor :=
  ⟨(i : I) × (c i).A, fun p => (c p.1).B p.2, fun p b => (c p.1).tgt p.2 b⟩

/-- An exponent: a function from `A` to shapes; a hole is an argument and a hole of the
    shape at it. -/
@[reducible] def pi (A : Type) (c : IPFunctor) : IPFunctor :=
  ⟨A → c.A, fun f => (a : A) × c.B (f a), fun f q => c.tgt (f q.1) q.2⟩

/-- The target of a hole of a list of shapes. -/
def listTgt (c : IPFunctor) : (xs : List c.A) → PFunctor.ListPos c.B xs → Nat
  | [], p => PEmpty.elim p
  | s :: _, .inl p => c.tgt s p
  | _ :: ss, .inr q => listTgt c ss q

/-- An array: an array of shapes, with the holes of each, in order. -/
@[reducible] def array (c : IPFunctor) : IPFunctor :=
  ⟨Array c.A, fun a => PFunctor.ListPos c.B a.toList, fun a => listTgt c a.toList⟩

/-- Entry `i` of a list of containers; past the end, the empty one — the library's
    `List.getD` with the empty container as the default. -/
@[reducible] def «at» (cs : List IPFunctor) (n : Nat) : IPFunctor := cs.getD n (const PEmpty)

namespace Obj

variable {X Y : Nat → Type}

/-- Change the value in every hole. -/
def map {P : IPFunctor} (g : ∀ j, X j → Y j) (x : P.Obj X) : P.Obj Y :=
  ⟨x.1, fun b => g _ (x.2 b)⟩

/-- Pair two extensions. -/
def pair {c d : IPFunctor} (x : c.Obj X) (y : d.Obj X) : (prod c d).Obj X :=
  ⟨(x.1, y.1), fun | .inl p => x.2 p | .inr q => y.2 q⟩

/-- The first component of an extension of a product. -/
def prodFst {c d : IPFunctor} (x : (prod c d).Obj X) : c.Obj X :=
  ⟨x.1.1, fun p => x.2 (.inl p)⟩

/-- The second component of an extension of a product. -/
def prodSnd {c d : IPFunctor} (x : (prod c d).Obj X) : d.Obj X :=
  ⟨x.1.2, fun p => x.2 (.inr p)⟩

/-- An extension of an exponent, pointwise. -/
def ofPi {c : IPFunctor} {A : Type} (g : A → c.Obj X) : (pi A c).Obj X :=
  ⟨fun y => (g y).1, fun q => (g q.1).2 q.2⟩

/-- The extension of a list of shapes: the shapes, with a value in each of their holes. -/
abbrev ListObj (c : IPFunctor) (X : Nat → Type) : Type :=
  (xs : List c.A) × ((p : PFunctor.ListPos c.B xs) → X (listTgt c xs p))

/-- Put an extension in front of an extension of a list. -/
def cons {c : IPFunctor} (h : c.Obj X) (t : ListObj c X) : ListObj c X :=
  ⟨h.1 :: t.1, fun | .inl p => h.2 p | .inr q => t.2 q⟩

/-- A list of extensions, from a list of values and a way to turn each into one. -/
def ofList {c : IPFunctor} {α : Type} (f : α → c.Obj X) : List α → ListObj c X
  | [] => ⟨[], fun p => PEmpty.elim p⟩
  | x :: xs => cons (f x) (ofList f xs)

/-- The other direction of `IPFunctor.Obj.ofList`. -/
def toList {c : IPFunctor} {α : Type} (h : c.Obj X → α) :
    (xs : List c.A) → ((p : PFunctor.ListPos c.B xs) → X (listTgt c xs p)) → List α
  | [], _ => []
  | s :: ss, g => h ⟨s, fun p => g (.inl p)⟩ :: toList h ss (fun q => g (.inr q))

/-- An array of extensions, from an array of values. -/
def ofArray {c : IPFunctor} {α : Type} (f : α → c.Obj X) (xs : Array α) : (array c).Obj X :=
  ⟨⟨(ofList f xs.toList).1⟩, (ofList f xs.toList).2⟩

/-- The other direction of `IPFunctor.Obj.ofArray`. -/
def toArray {c : IPFunctor} {α : Type} (h : c.Obj X → α) (x : (array c).Obj X) : Array α :=
  ⟨toList h x.1.toList x.2⟩

end Obj

end IPFunctor

/-! ## The indexed W-type -/

/-- **The indexed W-type**: a tree whose root is a node of index `i` — a shape `a : A i` —
    and whose child at a hole `b` is a tree rooted at the hole's target `tgt i a b`. -/
inductive IWType (A : Nat → Type) (B : (i : Nat) → A i → Type)
    (tgt : (i : Nat) → (a : A i) → B i a → Nat) : Nat → Type where
  /-- A node of index `i`: a shape, and a subtree at every hole. -/
  | mk (i : Nat) (a : A i) (f : (b : B i a) → IWType A B tgt (tgt i a b)) : IWType A B tgt i

namespace IWType

variable {A : Nat → Type} {B : (i : Nat) → A i → Type} {tgt : (i : Nat) → (a : A i) → B i a → Nat}

/-- The root of a tree: its shape and its subtrees. -/
def node {i : Nat} : IWType A B tgt i → (a : A i) × ((b : B i a) → IWType A B tgt (tgt i a b))
  | .mk _ a f => ⟨a, f⟩

/-- A tree with the answer of a fold stored at every node. -/
abbrev Memo (A : Nat → Type) (B : (i : Nat) → A i → Type)
    (tgt : (i : Nat) → (a : A i) → B i a → Nat) (β : Type) : Nat → Type :=
  IWType (fun i => A i × β) (fun i p => B i p.1) (fun i p b => tgt i p.1 b)

/-- The answer stored at the root. -/
def Memo.answer {β : Type} {i : Nat} : Memo A B tgt β i → β
  | .mk _ (_, x) _ => x

/-- Forgetting the answers gives back the tree. -/
def Memo.tree {β : Type} {i : Nat} : Memo A B tgt β i → IWType A B tgt i
  | .mk _ (a, _) f => .mk _ a (fun b => Memo.tree (f b))

/-- The tree with the answer at every node: first the children's memos, then the answer
    at this node, from its index, its shape and its children's memos. -/
def memo {β : Type}
    (step : (i : Nat) → (a : A i) → ((b : B i a) → Memo A B tgt β (tgt i a b)) → β) :
    {i : Nat} → IWType A B tgt i → Memo A B tgt β i
  | _, .mk i a f =>
      let kids := fun b => memo step (f b)
      .mk i (a, step i a kids) kids

/-- The answer of the memoised fold at the root. -/
def memoFold {β : Type}
    (step : (i : Nat) → (a : A i) → ((b : B i a) → Memo A B tgt β (tgt i a b)) → β)
    {i : Nat} (v : IWType A B tgt i) : β :=
  (memo step v).answer

theorem memoFold_mk {β : Type}
    (step : (i : Nat) → (a : A i) → ((b : B i a) → Memo A B tgt β (tgt i a b)) → β)
    (i : Nat) (a : A i) (f : (b : B i a) → IWType A B tgt (tgt i a b)) :
    memoFold step (.mk i a f) = step i a (fun b => memo step (f b)) :=
  rfl

/-- The memo of a tree is that tree, with answers. -/
theorem memo_tree {β : Type}
    (step : (i : Nat) → (a : A i) → ((b : B i a) → Memo A B tgt β (tgt i a b)) → β) :
    ∀ {i : Nat} (v : IWType A B tgt i), (memo step v).tree = v
  | _, .mk i a f => by
      show IWType.mk i a (fun b => (memo step (f b)).tree) = _
      exact congrArg (IWType.mk i a) (funext fun b => memo_tree step (f b))

end IWType

/-! ## The values of a family -/

/-- A member number of a family of `L` members: itself if the family has it, and member
    `0` otherwise — which is what `LeanScript.LeanMutualRecFamily.select` selects for a
    number out of range. -/
def selIdx (L i : Nat) : Nat := if i < L then i else 0

/-- **The values of a family** whose members have the containers `Fs`, at member `i`: the
    indexed W-type of the containers, a hole's target read by `selIdx`. -/
abbrev FamW (Fs : List IPFunctor) : Nat → Type :=
  IWType (fun i => (IPFunctor.at Fs i).A) (fun i a => (IPFunctor.at Fs i).B a)
    (fun i a b => selIdx Fs.length ((IPFunctor.at Fs i).tgt a b))

/-- A value of a family, with the answer of a fold of answers `β` at every node. -/
abbrev FamMemo (Fs : List IPFunctor) (β : Type) : Nat → Type :=
  IWType.Memo (fun i => (IPFunctor.at Fs i).A) (fun i a => (IPFunctor.at Fs i).B a)
    (fun i a b => selIdx Fs.length ((IPFunctor.at Fs i).tgt a b)) β

/-- The answer stored at the root of a memo of a family. -/
def FamMemo.answer {Fs : List IPFunctor} {β : Type} {i : Nat} (m : FamMemo Fs β i) : β :=
  IWType.Memo.answer m

/-- The value a memo of a family is a memo of. -/
def FamMemo.tree {Fs : List IPFunctor} {β : Type} {i : Nat} (m : FamMemo Fs β i) : FamW Fs i :=
  IWType.Memo.tree m

namespace FamW

variable {Fs : List IPFunctor}

/-- Build a node of member `i` from a shape of a container `P` that *is* the container of
    member `i`. -/
def mkAt (i : Nat) (P : IPFunctor) (h : IPFunctor.at Fs i = P)
    (x : P.Obj (fun j => FamW Fs (selIdx Fs.length j))) : FamW Fs i := by
  subst h
  exact IWType.mk i x.1 x.2

/-- The root of a value of member `i`, as a shape of a container `P` that *is* the
    container of member `i`, with its subtrees. -/
def nodeAt (i : Nat) (P : IPFunctor) (h : IPFunctor.at Fs i = P) (v : FamW Fs i) :
    P.Obj (fun j => FamW Fs (selIdx Fs.length j)) := by
  subst h
  exact ⟨v.node.1, v.node.2⟩

/-- The root of a memo of member `i`, as a shape of a container `P` that *is* the
    container of member `i`: the shape, the answer stored there, and the memos of its
    subtrees. -/
def memoNodeAt {β : Type} (i : Nat) (P : IPFunctor) (h : IPFunctor.at Fs i = P)
    (v : FamMemo Fs β i) :
    β × P.Obj (fun j => FamMemo Fs β (selIdx Fs.length j)) := by
  subst h
  exact (v.node.1.2, ⟨v.node.1.1, v.node.2⟩)

end FamW

end
