module

public import TermTests.RecObjectToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `recObject_rec k` on a **binary** recursive record

`TermTests/RecObjectToTermTest/` folds `Cell`, a record that holds *one* `Option` of
itself.  These files fold a record that holds *two*:

```lean
inductive BNode where
  | mk (label : Nat) (left right : Option BNode)
```

— a binary tree whose every node carries a label and has zero, one or two children.  Its
tree is `Ty.recObject ⟨nat, Option self, Option self⟩` (checked below), so each branch of
`recObject_rec k` receives the answers at *both* children, and the window of depth `k`
reaches `k + 1` levels down along every path.

One file per depth, `K0.lean` … `K2.lean`, checked as in
`TermTests/RecObjectToTermTest/Common.lean`: the translated term is a `recObject_rec` of
the expected depth, computes the expected numbers, and computes what the Lean definition
computes.
-/

namespace TermTests.RecObjectToTerm.BinTree

open LeanScript TermTests.RecObjectToTerm

/-- A binary tree: a label and at most two children. -/
inductive BNode where
  /-- A label, and perhaps a left and a right child. -/
  | mk (label : Nat) (left right : Option BNode)
  deriving LeanScriptTyWf

/-- The type of a binary tree, in the language. -/
abbrev bnodeT : TyWf := tyWfOf BNode

-- the derived tree: a recursive record with two `Option`s of itself
-- [SKIPPED BY PROFILE_LAKE] example : tyOf BNode = .recObject ⟨.prim .nat,
-- [SKIPPED BY PROFILE_LAKE]     .taggedUnion (.skip (.here ⟨.self, []⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]     [.taggedUnion (.skip (.here ⟨.self, []⟩ []))]⟩ := rfl

/-- The complete binary tree of height `n` (`2 ^ (n + 1) - 1` nodes), labelled by the
    height of each node. -/
def BNode.full : Nat → BNode
  | 0 => .mk 0 none none
  | n + 1 => .mk (n + 1) (some (BNode.full n)) (some (BNode.full n))

/-- The left comb of height `n`: a left spine of `n + 1` nodes labelled `n, …, 0`, each
    inner node with a right leaf labelled `1`. -/
def BNode.comb : Nat → BNode
  | 0 => .mk 0 none none
  | n + 1 => .mk (n + 1) (some (BNode.comb n)) (some (.mk 1 none none))

/-- `BNode.full`, as a term: a `nat_rec` whose branch builds a node with `recObject_mk`. -/
def full_term : Term sig0 [] (natT ⇒ bnodeT) := #leanscript_to_term BNode.full
/-- `BNode.comb`, as a term. -/
def comb_term : Term sig0 [] (natT ⇒ bnodeT) := #leanscript_to_term BNode.comb

/-- `BNode.full n`, as a value of the language. -/
def fullOf (n : Nat) : TyWf.Den bnodeT := run full_term n
/-- `BNode.comb n`, as a value of the language. -/
def combOf (n : Nat) : TyWf.Den bnodeT := run comb_term n

/-- A lopsided tree written out. -/
def t1 : BNode :=
  .mk 5 (some (.mk 3 none (some (.mk 7 (some (.mk 2 none none)) none))))
    (some (.mk 4 (some (.mk 1 none none)) (some (.mk 6 none none))))

/-- `t1`, as a term: nested `recObject_mk`s. -/
def t1_term : Term sig0 [] bnodeT := #leanscript_to_term t1

end TermTests.RecObjectToTerm.BinTree

end
