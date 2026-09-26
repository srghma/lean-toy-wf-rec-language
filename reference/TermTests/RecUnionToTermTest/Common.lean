module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `recTaggedUnion_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci`, `pentanacci`, … ; `TermTests/ArrayRecToTermTest/` does the same
for `LeanScript.Term.array_rec k` and `TermTests/RecObjectToTermTest/` for
`LeanScript.Term.recObject_rec k`.  These files do it for
`LeanScript.Term.recTaggedUnion_rec k`, the fold of a **recursive tagged union** whose
branches may look `k` times further down, into one subvalue or into several.

**Which Lean program is a `recTaggedUnion_rec k`.**  Any structural recursion on an
inductive type whose tree is `Ty.recTaggedUnion` — several constructors, each field
either the type itself or a value that does not mention it.  Lean compiles it into
`X.brecOn`, and the translation (`LeanScript.ToTerm.TransRecUnion`) reads it as
`recTaggedUnion_rec k`, where `k` is the smallest depth at which every branch is served
by the constructor's fields, the answers at its subvalues, and at most `k` looks — each
into a subvalue of the node the branch stands at (`LeanScript.FoldKBranch.deep`) or of a
node above it (`LeanScript.FoldKBranch.deepOuter`).  The programs are written as ordinary
Lean, with no annotation and nothing added for the translation.

`BothSubtrees.lean` has programs that read below several subvalues at once (the sum of
the labels at even levels, which reads the grandchildren below both children), and
`Refused.lean` one the translation refuses.

One file per depth, `K0.lean` … `K4.lean`, each with programs on three datatypes (the
datatypes, and the inputs built for them, are defined here):

* `List Nat`, one recursive point: the depth-`k` programs are the
  Fibonacci-like recursions of `TermTests/NatRecDepthTest/` on the length of the list.
* `Tree` (`leaf | node left val right`), two recursive points: the
  deeper looks go down the left spine or the right spine.
* `Tree3` (`leaf val | node a b c`), three recursive points: the deeper
  looks go down the first, the middle or the last child.

Each program is checked three ways:

* the translated term **is** a `recTaggedUnion_rec` of the expected depth;
* the term computes the expected numbers;
* the term computes what the Lean definition computes.

The inputs are built by translated Lean programs too (e.g. `Tree.full n`, a `nat_rec`
whose branch builds nodes with `recTaggedUnion_mk`).

The equations are checked by `kernel_rfl` rather than `rfl`: the elaborator's own check of
such an equation fails or runs out of heartbeats, while the kernel checks it quickly (see
`LeanScript/KernelRfl.lean`).  `kernel_rfl` is still a proof by `Eq.refl`, checked by the
kernel.
-/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

mutual
/-- The depth of the `recTaggedUnion_rec` a translated function is: the fold under the
    `fun`s of its arguments, applied to the arguments that Lean put in the motive.  `none`
    if the translation is not of that shape. -/
def recUnionRecDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .recTaggedUnion_rec k _ _ _ => some k
  | .letE c body => (recUnionRecDepth?.comp c).orElse fun _ => recUnionRecDepth? body
  | .letJ jp body => (recUnionRecDepth? body).orElse fun _ => recUnionRecDepth? jp
  | _ => none

/-- `recUnionRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recUnionRecDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => recUnionRecDepth? b
  | _ => none
end

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## `List Nat` (one recursive point)

`List Nat` is the recursive tagged union `nil | cons nat self`.  A program that matches
`k + 1` conses deep is `recTaggedUnion_rec k`: each deeper look goes into the tail. -/

/-- A list of the language, from a Lean list. -/
abbrev natList (l : List Nat) : TyWf.Den (tyWfOf (List Nat)) := Ty.DenRec.ofList (.prim .nat) l

/-! ## `Tree`, a binary tree (two recursive points)

`Tree` is the recursive tagged union `leaf | node self nat self`.  A branch of
`recTaggedUnion_rec k` is given a node's subtrees, its label, and the answers at both
subtrees; a deeper look goes into **one** subtree — the programs at `k ≥ 1` read
`k + 1` levels down the left spine (`.here`) or the right spine (`.there (.there .here)`),
while still using the answers at the other subtrees. -/

/-- A binary tree with a label at each node. -/
inductive Tree where
  | leaf
  | node (left : Tree) (val : Nat) (right : Tree)
  deriving LeanScriptTyWf

/-- The type of a tree, in the language. -/
abbrev treeT : TyWf := tyWfOf Tree

-- The derived tree is a recursive tagged union with two occurrences of itself.
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Tree = .recTaggedUnion (.skip (.here ⟨.self, [.prim .nat, .self]⟩ [])) := rfl

namespace Tree

/-- The complete tree of height `n`, the root labelled `n`. -/
def full : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (full n) (n + 1) (full n)

/-- A left spine of `n` nodes labelled `n, …, 1`, each with a leaf on the right. -/
def leftSpine : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (leftSpine n) (n + 1) .leaf

/-- A right spine of `n` nodes labelled `n, …, 1`, each with a one-node tree on the left
    labelled like it. -/
def rightSpine : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (.node .leaf (n + 1) .leaf) (n + 1) (rightSpine n)

end Tree

/-- `Tree.full`, as a term: a `nat_rec` whose branch builds a node with
    `recTaggedUnion_mk`. -/
def full_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.full

/-- `Tree.leftSpine`, as a term. -/
def leftSpine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.leftSpine

/-- `Tree.rightSpine`, as a term. -/
def rightSpine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.rightSpine

/-- A tree written out. -/
def tree7 : Tree :=
  .node (.node (.node .leaf 4 .leaf) 2 (.node .leaf 5 .leaf)) 1
    (.node (.node .leaf 6 .leaf) 3 (.node (.node .leaf 8 .leaf) 7 .leaf))

/-- `tree7`, as a term: nested `recTaggedUnion_mk`s. -/
def tree7_term : Term sigAdd [] treeT := #leanscript_to_term tree7

/-! ## `Tree3`, a ternary tree (three recursive points)

`Tree3` is the recursive tagged union `leaf nat | node self self self` — its first
constructor carries a field, so its schema starts with `payloadFirst`, unlike `List` and
`Tree`.  A branch of `recTaggedUnion_rec k` is given a node's three subtrees and the
answers at all three; a deeper look goes into **one** of them — the programs at `k ≥ 1`
descend the first child (`.here`), the middle child (`.there .here`) or the last
child (`.there (.there .here)`). -/

/-- A ternary tree with a label at each leaf. -/
inductive Tree3 where
  | leaf (val : Nat)
  | node (a b c : Tree3)
  deriving LeanScriptTyWf

/-- The type of a ternary tree, in the language. -/
abbrev tree3T : TyWf := tyWfOf Tree3

-- The derived tree is a recursive tagged union with three occurrences of itself.
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Tree3 = .recTaggedUnion (.payloadFirst ⟨.prim .nat, []⟩ [.self, .self, .self] []) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

namespace Tree3

/-- The complete ternary tree of height `n`, with leaves labelled `1`. -/
def full : Nat → Tree3
  | 0 => .leaf 1
  | n + 1 => .node (full n) (full n) (full n)

/-- A spine of `n` nodes down the first child, the other children leaves labelled by the
    level. -/
def firstSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (firstSpine n) (.leaf (n + 1)) (.leaf (n + 1))

/-- A spine of `n` nodes down the middle child. -/
def midSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (.leaf (n + 1)) (midSpine n) (.leaf (n + 1))

/-- A spine of `n` nodes down the last child. -/
def lastSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (.leaf (n + 1)) (.leaf (n + 1)) (lastSpine n)

end Tree3

/-- `Tree3.full`, as a term: a `nat_rec` whose branch builds a node with
    `recTaggedUnion_mk`. -/
def full3_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.full

/-- `Tree3.firstSpine`, as a term. -/
def firstSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.firstSpine

/-- `Tree3.midSpine`, as a term. -/
def midSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.midSpine

/-- `Tree3.lastSpine`, as a term. -/
def lastSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.lastSpine

/-- A ternary tree written out. -/
def tree3a : Tree3 :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3) (.node (.leaf 4) (.leaf 5) (.leaf 6))) (.leaf 7)

/-- `tree3a`, as a term: nested `recTaggedUnion_mk`s. -/
def tree3a_term : Term sigAdd [] tree3T := #leanscript_to_term tree3a

end TermTests.RecUnionToTerm

end
