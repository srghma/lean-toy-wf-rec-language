module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # A structural recursion split across two top-level definitions

```lean
def go : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => go n (a + 2)

def callGo (n : Nat) : Nat := go n 0
```

`callGo` is not recursive itself: it calls `go`, a structural recursion defined on its own.
A call of a structural recursion — a definition Lean compiled through a `brecOn` — is
inlined even when it is neither `@[inline]` nor declared in the signature, so `callGo`
translates to the fold `go` compiles to (`LeanScript.ToTerm.isStructuralRecursion`).  So is
a wrapper whose body calls one (`callCallGo` below calls `callGo`), through any number of
wrappers of the program's own modules (`LeanScript.ToTerm.callsStructuralRecursion`).  Any
other call still has to be inlinable or declared (`TermTests/ToTermTest/Refused.lean`).
More shapes — longer chains, chains across files, `where` helpers, partial application,
recursions written with `Nat.rec`/`List.rec`, and `mutual` blocks Lean splits — are in
`TermTests/StructRecTest/SplitRecursionMore.lean`.

Covered below: helpers on `Nat`, on `List`, on a user-defined tree and on a recursive
newtype; a chain of wrappers; a helper called twice; a recursion whose branch calls another
separately defined recursion; and a helper that is itself a recursion of depth `2`. -/

namespace TermTests.StructRec.Split

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- Is there a fold anywhere in this term? -/
def hasFold {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Bool
  | .nat_rec .. | .recTaggedUnion_rec .. | .array_rec .. | .recObject_rec ..
  | .recAlias_rec .. | .mutualRecursiveFamily_rec .. => true
  | .letE c body => (hasFold.comp c) || hasFold body
  | .letJ jp body => (hasFold body) || hasFold jp
  | _ => false

/-- `hasFold`, in the computation a `let` binds: the body of a `fun`. -/
def hasFold.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Bool
  | .lam b => hasFold b
  | _ => false
end

/-! ## On `Nat`, with an accumulator -/

def go : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => go n (a + 2)

def callGo (n : Nat) : Nat := go n 0

def callGo_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term callGo

-- [SKIPPED BY PROFILE_LAKE] example : hasFold callGo_term = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd callGo_term 5 = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd callGo_term 13 = callGo 13 := by kernel_rfl

/-- Two wrappers deep. -/
def callCallGo (n : Nat) : Nat := callGo (n + 1)

def callCallGo_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term callCallGo

-- [SKIPPED BY PROFILE_LAKE] example : runAdd callCallGo_term 4 = 10 := by kernel_rfl

/-- The helper called twice, at different arguments. -/
def twice (n : Nat) : Nat := go n 1 + go (n + 3) 0

def twice_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term twice

-- [SKIPPED BY PROFILE_LAKE] example : runAdd twice_term 2 = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd twice_term 7 = twice 7 := by kernel_rfl

/-! ## A helper of depth `2` -/

def fibAux : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibAux n + fibAux (n + 1)

def fibPlusOne (n : Nat) : Nat := fibAux n + 1

def fibPlusOne_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term fibPlusOne

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibPlusOne_term 10 = 56 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibPlusOne_term 15 = fibPlusOne 15 := by kernel_rfl

/-! ## On lists -/

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

def total (l : List Nat) : Nat := sumList l + sumList (0 :: l)

def total_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) := #leanscript_to_term total

-- [SKIPPED BY PROFILE_LAKE] example : runAdd total_term (Ty.DenRec.ofList (.prim .nat) [1, 2, 3]) = 12 := by kernel_rfl

/-- The length of a list, defined on its own. -/
def lenList : List Nat → Nat
  | [] => 0
  | _ :: xs => lenList xs + 1

/-- A recursion whose branch calls another separately defined recursion. -/
def sumLens : List (List Nat) → Nat
  | [] => 0
  | l :: ls => lenList l + sumLens ls

def sumLens_term : Term sigAdd [] (tyWfOf (List (List Nat)) ⇒ natT) :=
  #leanscript_to_term sumLens

-- [SKIPPED BY PROFILE_LAKE] example : hasFold sumLens_term = true := by kernel_rfl

/-! ## On a user-defined tree -/

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)
  deriving LeanScriptTyWf

def Tree.sumAcc : Tree → Nat → Nat
  | .leaf, a => a
  | .node l v r, a => Tree.sumAcc l (Tree.sumAcc r (a + v))

def treeSum (t : Tree) : Nat := t.sumAcc 0

def treeSum_term : Term sigAdd [] (tyWfOf Tree ⇒ natT) := #leanscript_to_term treeSum

def tree1 : Tree := .node (.node .leaf 1 .leaf) 2 (.node (.node .leaf 3 .leaf) 4 .leaf)

def tree1_term : Term sigAdd [] (tyWfOf Tree) := #leanscript_to_term tree1

-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_term (runAdd tree1_term) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd treeSum_term (runAdd tree1_term) = treeSum tree1 := by kernel_rfl

/-! ## A call that is still refused

A non-recursive helper is not a structural recursion: it still has to be inlinable or
declared in the signature. -/

def plainHelper (n : Nat) : Nat := n + 1

def callsPlain (n : Nat) : Nat := plainHelper n

/-- error: `#leanscript_to_term`: `TermTests.StructRec.Split.plainHelper` is not declared in the signature and is not inlinable, so a term cannot call it.  Either add a `GlobalDecl` named "plainHelper" (or "TermTests.StructRec.Split.plainHelper") to the signature, or mark `TermTests.StructRec.Split.plainHelper` `@[inline]`.  (A structural recursion is inlined without either.) -/
#guard_msgs (error) in
example : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term callsPlain

end TermTests.StructRec.Split

end
