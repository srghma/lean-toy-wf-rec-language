module

public import TermTests.RecAliasToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec k` on a binary recursive newtype: below both children

Part of the `recAlias_rec k` translation tests; see
`TermTests/RecAliasToTermTest/Common.lean` for what is checked.

`Chain` has one occurrence of itself per link.  The newtype here has **two**:

```lean
inductive Fork (α : Type) where
  | tip
  | fork (l : α) (v : Nat) (r : α)

inductive BTree where
  | mk (node : Fork BTree)
```

a binary tree, whose tree is `Ty.recAlias (tip | fork self nat self)` (checked below).  The
programs read below **both** children of a node, like `evenLevelSum` in
`TermTests/RecUnionToTermTest/BothSubtrees.lean`.  A fold of a recursive newtype needs
nothing more for them: its window (`LeanScript.TyWf.recAliasRecBinders`) is given in the
shape of the newtype's body, so at depth `k` it holds the answers at *every* subvalue
`k + 1` levels down, below all the children at once, and the fields of a child are read off
the child itself.  So the answers at the grandchildren below both children are a
`recAlias_rec 1`. -/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

/-- One node of a binary tree: nothing, or two children and a label.  A non-recursive
    wrapper of its own, so that `BTree` below is a newtype whose body is a union. -/
inductive Fork (α : Type) where
  /-- No node. -/
  | tip
  /-- Two children and a label. -/
  | fork (l : α) (v : Nat) (r : α)
  deriving LeanScriptTyWf

/-- A binary tree: the recursive newtype the programs fold over. -/
inductive BTree where
  /-- The one constructor, of one field: the wrapper is erased. -/
  | mk (node : Fork BTree)
  deriving LeanScriptTyWf

/-- The type of a binary tree, in the language. -/
abbrev btreeT : TyWf := tyWfOf BTree

-- The derived tree is a recursive newtype whose body is `tip | fork self nat self`.
-- [SKIPPED BY PROFILE_LAKE] example : tyOf BTree =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.taggedUnion (.skip (.here ⟨.self, [.prim .nat, .self]⟩ []))) := rfl

/-- The complete binary tree of height `n`, every node labelled by its height. -/
def BTree.full : Nat → BTree
  | 0 => .mk .tip
  | n + 1 => .mk (.fork (BTree.full n) (n + 1) (BTree.full n))

/-- `BTree.full`, as a term: a `nat_rec` whose branch builds a node with `recAlias_mk`. -/
def btFull_term : Term sigAdd [] (natT ⇒ btreeT) := #leanscript_to_term BTree.full

/-- The complete binary tree of height `n`, as a value of the language. -/
def btFullOf (n : Nat) : TyWf.Den btreeT := runAdd btFull_term n

/-- A lopsided tree written out. -/
def bt1 : BTree :=
  .mk (.fork (.mk (.fork (.mk (.fork (.mk .tip) 4 (.mk .tip))) 2 (.mk .tip))) 1
    (.mk (.fork (.mk (.fork (.mk .tip) 5 (.mk .tip))) 3
      (.mk (.fork (.mk (.fork (.mk .tip) 7 (.mk .tip))) 6 (.mk .tip))))))

/-- `bt1`, as a term: nested `recAlias_mk`s. -/
def bt1_term : Term sigAdd [] btreeT := #leanscript_to_term bt1

/-! ## The sum of the labels at even levels -/

def btEvenLevelSum : BTree → Nat
  | .mk .tip => 0
  | .mk (.fork (.mk .tip) v (.mk .tip)) => v
  | .mk (.fork (.mk .tip) v (.mk (.fork rl _ rr))) => v + btEvenLevelSum rl + btEvenLevelSum rr
  | .mk (.fork (.mk (.fork ll _ lr)) v (.mk .tip)) => v + btEvenLevelSum ll + btEvenLevelSum lr
  | .mk (.fork (.mk (.fork ll _ lr)) v (.mk (.fork rl _ rr))) =>
      v + btEvenLevelSum ll + btEvenLevelSum lr + btEvenLevelSum rl + btEvenLevelSum rr

def btEvenLevelSum_term : Term sigAdd [] (btreeT ⇒ natT) :=
  #leanscript_to_term btEvenLevelSum

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? btEvenLevelSum_term = some 1 := by kernel_rfl
-- levels 0 and 2 of `bt1`: `1 + (4 + 5 + 6)`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenLevelSum_term (runAdd bt1_term) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenLevelSum_term (runAdd bt1_term) = btEvenLevelSum bt1 := by kernel_rfl
-- `full 4`: `4 + 4 * 2 + 16 * 0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenLevelSum_term (btFullOf 4) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenLevelSum_term (btFullOf 6) = btEvenLevelSum (BTree.full 6) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## Across: from the left child's right child to the right child's left child -/

def btZigzag : BTree → Nat
  | .mk .tip => 1
  | .mk (.fork (.mk (.fork _ _ lr)) v (.mk (.fork rl _ _))) => v + btZigzag lr * btZigzag rl
  | .mk (.fork l v r) => v + btZigzag l + btZigzag r

def btZigzag_term : Term sigAdd [] (btreeT ⇒ natT) := #leanscript_to_term btZigzag

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? btZigzag_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btZigzag_term (runAdd bt1_term) = btZigzag bt1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btZigzag_term (btFullOf 6) = btZigzag (BTree.full 6) := by kernel_rfl

/-! ## Two arguments: a weight per level -/

def btEvenWeighted : BTree → Nat → Nat
  | .mk (.fork (.mk (.fork ll _ lr)) v (.mk (.fork rl _ rr))), w =>
      v * w + btEvenWeighted ll (w + 2) + btEvenWeighted lr (w + 2) +
        btEvenWeighted rl (w + 2) + btEvenWeighted rr (w + 2)
  | .mk (.fork _ v _), w => v * w
  | .mk .tip, _ => 0

def btEvenWeighted_term : Term sigAdd [] (btreeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term btEvenWeighted

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? btEvenWeighted_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenWeighted_term (btFullOf 5) 1 = btEvenWeighted (BTree.full 5) 1 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd btEvenWeighted_term (runAdd bt1_term) 2 = btEvenWeighted bt1 2 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.RecAliasToTerm

end
