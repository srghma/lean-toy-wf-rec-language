module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Nested inductives through `Array`

```lean
inductive ATree where
  | node (v : Nat) (kids : Array ATree)
```

has the tree `Ty.recObject ⟨nat, array self⟩` (checked below): `Array`'s model is a shape of
the language, so the occurrence stands inside it.  Lean accepts a structural recursion on
it written as a `mutual` block over `ATree`, `Array ATree` and `List ATree`, which it
compiles into `ATree.brecOn` with three motives.

Such a recursion is now `recObject_rec k` (`LeanScript.ToTerm.TransRecObject`): the window
of the fold holds, at the field `kids`, the **array of the answers** at the children, and the
answer of the helper on `Array ATree` is computed from it — the helper on `List ATree` is the
fold of that array (`array_rec`), its branch given the answer at the head and the answer at
the rest, and the helper on `Array ATree` is then applied to the answer at its list.  Both
are bound with `letE` before the branch of `ATree.node` reads them.

The helpers may answer types other than the main function (`ATree.labels` answers a
`List Nat`), and a recursive newtype over an array (`Rose | mk (kids : Array Rose)`) is
folded the same way, as `recAlias_rec k`.  A helper that takes a child apart rather than
reading its answer has no term: the children themselves are not in the window.

Declarations of several constructors, arrays of arrays (or of options, or of pairs),
functions and delays are in `TermTests/StructRecTest/NestedOther.lean`. -/

namespace TermTests.StructRec.NestedArray

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- The depth of the outermost fold of a translated function, if it is a fold of a record
    or of a newtype. -/
def foldDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .recObject_rec k _ _ _ => some k
  | .recAlias_rec k _ _ _ => some k
  | .letE c body => (foldDepth?.comp c).orElse fun _ => foldDepth? body
  | .letJ jp body => (foldDepth? body).orElse fun _ => foldDepth? jp
  | _ => none

/-- `foldDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def foldDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => foldDepth? b
  | _ => none
end

/-- A rose tree holding its children in an array. -/
inductive ATree where
  | node (v : Nat) (kids : Array ATree)
  deriving LeanScriptTyWf

/-- The type of an `ATree`, in the language. -/
abbrev atreeT : TyWf := tyWfOf ATree

-- [SKIPPED BY PROFILE_LAKE] example : tyOf ATree = .recObject ⟨.prim .nat, .array .self, []⟩ := rfl

/-- A tree written out. -/
def at1 : ATree := .node 1 #[.node 2 #[], .node 3 #[.node 4 #[], .node 5 #[]], .node 6 #[]]

def at1_term : Term sigAdd [] atreeT := #leanscript_to_term at1

/-- A path of `n + 1` nodes, labelled `n, …, 0` from the top. -/
def ATree.path : Nat → ATree
  | 0 => .node 0 #[]
  | n + 1 => .node (n + 1) #[ATree.path n]

def path_term : Term sigAdd [] (natT ⇒ atreeT) := #leanscript_to_term ATree.path

/-! ## The sum of the labels -/

mutual
def ATree.sum : ATree → Nat
  | .node v kids => v + ATree.sumA kids
def ATree.sumA : Array ATree → Nat
  | ⟨l⟩ => ATree.sumL l
def ATree.sumL : List ATree → Nat
  | [] => 0
  | t :: ts => t.sum + ATree.sumL ts
end

def sum_term : Term sigAdd [] (atreeT ⇒ natT) := #leanscript_to_term ATree.sum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? sum_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd at1_term) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd at1_term) = at1.sum := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd path_term 6) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd path_term 9) = (ATree.path 9).sum := by kernel_rfl

/-! ## The number of nodes, and a weighted sum -/

mutual
def ATree.size : ATree → Nat
  | .node _ kids => ATree.sizeA kids + 1
def ATree.sizeA : Array ATree → Nat
  | ⟨l⟩ => ATree.sizeL l
def ATree.sizeL : List ATree → Nat
  | [] => 0
  | t :: ts => t.size + ATree.sizeL ts
end

def size_term : Term sigAdd [] (atreeT ⇒ natT) := #leanscript_to_term ATree.size

-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd at1_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd path_term 4) = 5 := by kernel_rfl

mutual
/-- The label, and the children's answers, each counted once more than the one after
    it. -/
def ATree.weighted : ATree → Nat
  | .node v kids => v + ATree.weightedA kids
def ATree.weightedA : Array ATree → Nat
  | ⟨l⟩ => ATree.weightedL l
def ATree.weightedL : List ATree → Nat
  | [] => 0
  | t :: ts => t.weighted + ATree.weightedL ts + ATree.weightedL ts
end

def weighted_term : Term sigAdd [] (atreeT ⇒ natT) := #leanscript_to_term ATree.weighted

-- [SKIPPED BY PROFILE_LAKE] example : runAdd weighted_term (runAdd at1_term) = at1.weighted := by kernel_rfl

/-! ## Helpers answering another type: the labels in preorder

The helper on `Array ATree` is left out: `ATree.labels` calls the one on `List ATree` on the
array's list directly, so the recursion has an answer for lists and none for arrays (its
motive there is `PUnit`). -/

mutual
/-- The labels, in preorder. -/
def ATree.labels : ATree → List Nat
  | .node v kids => v :: ATree.labelsL kids.toList
/-- The labels of a list of trees, in preorder. -/
def ATree.labelsL : List ATree → List Nat
  | [] => []
  | t :: ts => t.labels ++ ATree.labelsL ts
end

def labels_term : Term sigAdd [] (atreeT ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term ATree.labels

-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (runAdd labels_term (runAdd at1_term)) =
-- [SKIPPED BY PROFILE_LAKE]     [1, 2, 3, 4, 5, 6] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (runAdd labels_term (runAdd at1_term)) =
-- [SKIPPED BY PROFILE_LAKE]     at1.labels := by kernel_rfl

/-! ## Refused: a helper that takes a child apart

The window holds the answers at the children, not the children: a helper that matches on
a child has no term. -/

mutual
/-- The number of children that are leaves, summed over the tree. -/
def ATree.leafKids : ATree → Nat
  | .node _ kids => ATree.leafKidsL kids.toList
/-- `ATree.leafKids`, on a list of trees. -/
def ATree.leafKidsL : List ATree → Nat
  | [] => 0
  | .node _ ⟨[]⟩ :: ts => ATree.leafKidsL ts + 1
  | t :: ts => t.leafKids + ATree.leafKidsL ts
end

example : Term sigAdd [] (atreeT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term ATree.leafKids
  exact .lam (.nat_mk 0)

/-! ## An `Option` field beside the array -/

/-- A rose tree whose nodes may also carry a side tree. -/
inductive STree where
  | node (v : Nat) (side : Option STree) (kids : Array STree)
  deriving LeanScriptTyWf

/-- The type of an `STree`, in the language. -/
abbrev streeT : TyWf := tyWfOf STree

def st1 : STree :=
  .node 1 (some (.node 10 none #[])) #[.node 2 none #[.node 3 (some (.node 20 none #[])) #[]]]

def st1_term : Term sigAdd [] streeT := #leanscript_to_term st1

mutual
def STree.sum : STree → Nat
  | .node v none kids => v + STree.sumA kids
  | .node v (some s) kids => v + s.sum + STree.sumA kids
def STree.sumA : Array STree → Nat
  | ⟨l⟩ => STree.sumL l
def STree.sumL : List STree → Nat
  | [] => 0
  | t :: ts => t.sum + STree.sumL ts
end

def stSum_term : Term sigAdd [] (streeT ⇒ natT) := #leanscript_to_term STree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd stSum_term (runAdd st1_term) = 36 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd stSum_term (runAdd st1_term) = st1.sum := by kernel_rfl

/-! ## A recursive newtype over an array -/

/-- A rose tree with no labels: only its shape. -/
inductive Rose where
  | mk (kids : Array Rose)
  deriving LeanScriptTyWf

/-- The type of a `Rose`, in the language. -/
abbrev roseT : TyWf := tyWfOf Rose

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Rose = .recAlias (.array .self) := rfl

def rose1 : Rose := .mk #[.mk #[], .mk #[.mk #[], .mk #[.mk #[]]]]

def rose1_term : Term sigAdd [] roseT := #leanscript_to_term rose1

mutual
/-- The number of nodes. -/
def Rose.size : Rose → Nat
  | .mk kids => Rose.sizeA kids + 1
def Rose.sizeA : Array Rose → Nat
  | ⟨l⟩ => Rose.sizeL l
def Rose.sizeL : List Rose → Nat
  | [] => 0
  | t :: ts => t.size + Rose.sizeL ts
end

def roseSize_term : Term sigAdd [] (roseT ⇒ natT) := #leanscript_to_term Rose.size

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? roseSize_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd roseSize_term (runAdd rose1_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd roseSize_term (runAdd rose1_term) = rose1.size := by kernel_rfl

end TermTests.StructRec.NestedArray

end
