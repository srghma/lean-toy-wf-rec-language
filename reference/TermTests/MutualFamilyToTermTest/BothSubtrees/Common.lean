module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `mutualRecursiveFamily_rec k`: looks into several subvalues

The programs of `TermTests/MutualFamilyToTermTest/` (`K0.lean` … `K4.lean` and the
subdirectories) read below one subvalue at a time.  The programs of this directory read
below **several**: after a deeper look into one field of a node, a branch looks into
another field of that node, or of a node further up the path it came down
(`LeanScript.FamilyFoldKBranch.deepOuter`).  Each look costs one unit of depth, so reading
the grandchildren below both children of a binary node is depth `2`, as for
`recTaggedUnion_rec` (`TermTests/RecUnionToTermTest/BothSubtrees.lean`).

The family used here is a binary tree whose levels alternate between two members, so that
every look goes into the *other* member:

```lean
mutual
  inductive ETree where
    | leaf
    | node (l : OTree) (v : Nat) (r : OTree)
  inductive OTree where
    | leaf
    | node (l : ETree) (v : Nat) (r : ETree)
end
```

`TreeForest.lean` does the same on the tree-and-forest family of
`TermTests/MutualFamilyToTermTest/TreeForest/`.

Each program is checked as in `TermTests/MutualFamilyToTermTest/Common.lean`: the depth of
the translated fold, some numbers, and agreement with the Lean definition on trees built
by translated programs and on a written-out tree.
-/

namespace TermTests.MutualFamilyToTerm.BothSubtrees

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

mutual
  /-- A binary tree at an even level. -/
  inductive ETree where
    /-- No node. -/
    | leaf
    /-- A node: two children at the next (odd) level, and a label. -/
    | node (l : OTree) (v : Nat) (r : OTree)
  /-- A binary tree at an odd level. -/
  inductive OTree where
    /-- No node. -/
    | leaf
    /-- A node: two children at the next (even) level, and a label. -/
    | node (l : ETree) (v : Nat) (r : ETree)
end

deriving instance LeanScriptTyWf for ETree
deriving instance LeanScriptTyWf for OTree

/-- The type of an even-level tree, in the language. -/
abbrev etreeT : TyWf := tyWfOf ETree
/-- The type of an odd-level tree, in the language. -/
abbrev otreeT : TyWf := tyWfOf OTree

-- the derived tree: two members with constructors, each node holding two occurrences of
-- the other member
-- [SKIPPED BY PROFILE_LAKE] example : tyOf ETree = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 1, [.prim .nat, .familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 0, [.prim .nat, .familyMember 0]⟩ []))) []) := rfl

/-- The complete even-level tree of height `n`, every node labelled by its height: a fold
    of the height into a pair of trees, one of each member, of which it is the first. -/
def ETree.full (n : Nat) : ETree :=
  (Nat.rec (motive := fun _ => ETree × OTree) (.leaf, .leaf)
    (fun n p => (.node p.2 (n + 1) p.2, .node p.1 (n + 1) p.1)) n).1

/-- The right spine of `n` nodes, labelled `n, …, 1` from the top, as an even-level
    tree. -/
def ETree.spine (n : Nat) : ETree :=
  (Nat.rec (motive := fun _ => ETree × OTree) (.leaf, .leaf)
    (fun n p => (.node .leaf (n + 1) p.2, .node .leaf (n + 1) p.1)) n).1

/-- `ETree.full`, as a term. -/
def full_term : Term sigAdd [] (natT ⇒ etreeT) := #leanscript_to_term ETree.full
/-- `ETree.spine`, as a term. -/
def spine_term : Term sigAdd [] (natT ⇒ etreeT) := #leanscript_to_term ETree.spine

/-- The complete tree of height `n`, as a value of the language. -/
def fullOf (n : Nat) : TyWf.Den etreeT := runAdd full_term n
/-- The right spine of `n` nodes, as a value of the language. -/
def spineOf (n : Nat) : TyWf.Den etreeT := runAdd spine_term n

/-- A lopsided tree written out, five levels deep. -/
def et1 : ETree :=
  .node (.node (.node (.node .leaf 8 .leaf) 4 .leaf) 2 (.node .leaf 5 (.node .leaf 9 .leaf)))
    1
    (.node (.node .leaf 6 .leaf) 3 (.node (.node .leaf 10 (.node .leaf 11 .leaf)) 7 .leaf))

/-- `et1`, as a term: nested `mutualRecursiveFamily_mk`s of both members. -/
def et1_term : Term sigAdd [] etreeT := #leanscript_to_term et1

end TermTests.MutualFamilyToTerm.BothSubtrees

end
