module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `mutualRecursiveFamily_rec k` on **mutual trees**: a tree and its forest

The classic mutual pair: a tree is a label and a forest of children, a forest is a list
of trees.

```lean
mutual
  inductive Tree where
    | node (label : Nat) (kids : Forest)
  inductive Forest where
    | nil
    | cons (t : Tree) (rest : Forest)
end
```

Unlike the chains of `TermTests/MutualFamilyToTermTest/Common.lean`, a member has a
constructor with **two** occurrences (`Forest.cons` holds a `Tree` and a `Forest`), and a
member (`Tree`) has a single constructor, so it is a *record* member of the family.  A
depth-`k` program looks `k` times, along one path, alternately into forests and trees:
the first child of a node is two looks down (into the forest, then into its first tree).

One file per depth, `K0.lean` … `K3.lean`; each program is checked as in
`TermTests/MutualFamilyToTermTest/Common.lean`: the depth of the translated fold, some
numbers, and agreement with the Lean definition on trees built by translated programs
(`Tree.full`, `Tree.spine`, `Forest.leaves`) and on a written-out tree.
-/

namespace TermTests.MutualFamilyToTerm.TreeForest

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

mutual
  /-- A tree: a label and its children. -/
  inductive Tree where
    /-- A node: its label and the forest of its children. -/
    | node (label : Nat) (kids : Forest)
  /-- A forest: a list of trees. -/
  inductive Forest where
    /-- No trees. -/
    | nil
    /-- A tree, and the rest of the forest. -/
    | cons (t : Tree) (rest : Forest)
end

deriving instance LeanScriptTyWf for Tree
deriving instance LeanScriptTyWf for Forest

/-- The type of a tree, in the language. -/
abbrev treeT : TyWf := tyWfOf Tree
/-- The type of a forest, in the language. -/
abbrev forestT : TyWf := tyWfOf Forest

-- the derived trees: `Tree` is a record member, `Forest` a member with constructors, one
-- of which holds two occurrences
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Tree = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.prim .nat, .familyMember 1, []⟩)
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ []))) []) := rfl

/-- The complete binary tree of height `n`: every node at height `h + 1` has two
    children of height `h`, and is labelled by its height. -/
def Tree.full : Nat → Tree
  | 0 => .node 0 .nil
  | n + 1 => .node (n + 1) (.cons (Tree.full n) (.cons (Tree.full n) .nil))

/-- The spine of `n + 1` nodes: every node but the last has one child, labelled
    `n, n - 1, …, 0` from the top. -/
def Tree.spine : Nat → Tree
  | 0 => .node 0 .nil
  | n + 1 => .node (n + 1) (.cons (Tree.spine n) .nil)

/-- The forest of `n` childless trees, labelled `n - 1, …, 0`. -/
def Forest.leaves : Nat → Forest
  | 0 => .nil
  | n + 1 => .cons (.node n .nil) (Forest.leaves n)

/-- `Tree.full`, as a term: a `nat_rec` building nodes with `mutualRecursiveFamily_mk`. -/
def full_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.full

/-- `Tree.spine`, as a term. -/
def spine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.spine

/-- `Forest.leaves`, as a term: a `nat_rec` building a forest. -/
def leaves_term : Term sigAdd [] (natT ⇒ forestT) := #leanscript_to_term Forest.leaves

/-- The complete binary tree of height `n`, as a value of the language. -/
def fullOf (n : Nat) : TyWf.Den treeT := runAdd full_term n

/-- The spine of `n + 1` nodes, as a value of the language. -/
def spineOf (n : Nat) : TyWf.Den treeT := runAdd spine_term n

/-- The forest of `n` childless trees, as a value of the language. -/
def leavesOf (n : Nat) : TyWf.Den forestT := runAdd leaves_term n

/-- A tree written out: a root with three children, the second of which has children of
    its own, one of them a spine of three. -/
def tree1 : Tree :=
  .node 1 (.cons (.node 2 .nil)
    (.cons (.node 3 (.cons (.node 4 (.cons (.node 5 (.cons (.node 6 .nil) .nil)) .nil))
      (.cons (.node 7 .nil) .nil)))
    (.cons (.node 8 .nil) .nil)))

/-- `tree1`, as a term: nested `mutualRecursiveFamily_mk`s of both members. -/
def tree1_term : Term sigAdd [] treeT := #leanscript_to_term tree1

/-- A forest written out: two trees, the first with two children. -/
def forest1 : Forest :=
  .cons (.node 9 (.cons (.node 4 .nil) (.cons (.node 6 .nil) .nil)))
    (.cons (.node 2 .nil) .nil)

/-- `forest1`, as a term. -/
def forest1_term : Term sigAdd [] forestT := #leanscript_to_term forest1

end TermTests.MutualFamilyToTerm.TreeForest

end
