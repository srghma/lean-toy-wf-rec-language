module

public import TermTests.RecUnionToTermTest.Common
public import TermTests.RecObjectToTermTest.BinTree.Common
public import TermTests.RecObjectToTermTest.Common
public import TermTests.RecAliasToTermTest.Common
public import TermTests.MutualFamilyToTermTest.TreeForest.Common
public import TermTests.MutualFamilyToTermTest.BothSubtrees.Common
public import TermTests.ArrayRecToTermTest.Common
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Shapes of structural recursion on one type

Recursions on `Nat`, `List`, a recursive union (`Tree`) and a recursive record (`BNode`)
whose branches take values apart in any position — nested `match`es on children and
grandchildren, matches on another argument, `let`, `if`, a `match` on the result of a
recursive call, results passed as arguments of recursive calls — and read the answers
below **both** children at once.  Each is a fold at the depth it needs. -/

namespace TermTests.Shapes.Folds

open LeanScript TermTests.NatRecDepth TermTests.RecUnionToTerm


-- 1. nested match in the branch on a child
def p1 : Tree → Nat
  | .leaf => 0
  | .node l v r =>
    match l with
    | .leaf => v + p1 r
    | .node ll _ _ => v + p1 ll + p1 r

def p1_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term p1

-- 2. wildcard nested patterns on both children
def p2 : Tree → Nat
  | .node (.node _ a _) v (.node _ b _) => a + b + v
  | .node l v r => v + p2 l + p2 r
  | .leaf => 0

def p2_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term p2

-- 3. Tree → Tree
def p3 : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node (p3 r) v (p3 l)

def p3_term : Term sigAdd [] (treeT ⇒ treeT) := #leanscript_to_term p3



-- 6. list nested match in branch
def p6 : List Nat → Nat
  | [] => 0
  | x :: xs => match xs with
    | [] => x
    | y :: ys => x + y + p6 ys

def p6_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) := #leanscript_to_term p6

-- 7. two list args, structural on first
def p7 : List Nat → List Nat → Nat
  | [], _ => 7
  | _ :: _, [] => 0
  | x :: xs, y :: ys => x + y + p7 xs ys

def p7_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ tyWfOf (List Nat) ⇒ natT) := #leanscript_to_term p7

-- 8. nat, call on n and n+1 from n+3
def p8 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => p8 n + p8 (n + 1)

def p8_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term p8

-- 9. List of lists
def p9 : List (List Nat) → Nat
  | [] => 0
  | l :: ls => (match l with | [] => 0 | a :: _ => a) + p9 ls

def p9_term : Term sigAdd [] (tyWfOf (List (List Nat)) ⇒ natT) := #leanscript_to_term p9

-- 10. evenLevelSum written with nested matches instead of patterns
def p10 : Tree → Nat
  | .leaf => 0
  | .node l v r =>
    v + (match l with | .leaf => 0 | .node ll _ lr => p10 ll + p10 lr)
      + (match r with | .leaf => 0 | .node rl _ rr => p10 rl + p10 rr)

def p10_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term p10


-- [SKIPPED BY PROFILE_LAKE] example : runAdd p10_term (runAdd tree7_term) = p10 tree7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p8_term 9 = p8 9 := by kernel_rfl


def a1 : Tree → Nat
  | .leaf => 0
  | .node l v r =>
    v + (match l with | .leaf => 0 | .node ll _ lr => a1 ll + a1 lr) + a1 r

def a1_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term a1

def a2 : Tree → Nat
  | .leaf => 0
  | .node l v _ =>
    (match l with | .leaf => 0 | .node ll _ lr => a2 ll + a2 lr) + v

def a2_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term a2

def a3 : Tree → Nat
  | .leaf => 0
  | .node l _ _ =>
    (match l with | .leaf => 0 | .node ll _ lr => a3 ll + a3 lr)

def a3_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term a3


-- nested recursive calls: results as arguments
def q1 : Tree → Nat → Nat
  | .leaf, a => a
  | .node l v r, a => q1 l (q1 r (a + v))
def q1_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT) := #leanscript_to_term q1
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q1_term (runAdd tree7_term) 0 = q1 tree7 0 := by kernel_rfl

-- let and if in the branch
def q2 : Tree → Nat
  | .leaf => 0
  | .node l v r =>
    let a := q2 l
    let b := q2 r
    if a < b then b + v else a + v
def q2_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term q2
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q2_term (runAdd tree7_term) = q2 tree7 := by kernel_rfl

-- the recursion returns a function used later
def q3 : List Nat → (Nat → Nat)
  | [] => fun a => a
  | x :: xs => fun a => q3 xs (a * 2 + x)
def q3_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT ⇒ natT) := #leanscript_to_term q3

-- termination_by structural
def q4 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => q4 k + 2
termination_by structural n
def q4_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term q4
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q4_term 5 = 10 := by kernel_rfl

-- match on the result of a recursive call
def q5 : Tree → Nat
  | .leaf => 0
  | .node l v r => match q5 l with
    | 0 => v + q5 r
    | m + 1 => m + q5 r
def q5_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term q5
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q5_term (runAdd tree7_term) = q5 tree7 := by kernel_rfl

-- `if` on a child's shape via a Bool function
@[inline] def isLeaf : Tree → Bool | .leaf => true | _ => false
def q6 : Tree → Nat
  | .leaf => 0
  | .node l v r => if isLeaf l then v + q6 r else q6 l + q6 r
def q6_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term q6

-- nested match both subtrees non-head on BNode
section
open TermTests.RecObjectToTerm TermTests.RecObjectToTerm.BinTree
def q7 : BNode → Nat
  | .mk v l r =>
    v + (match l with
          | none => 0
          | some (.mk _ ll lr) =>
            (match ll with | none => 0 | some t => q7 t) +
              (match lr with | none => 0 | some t => q7 t)) +
      (match r with
        | none => 0
        | some (.mk _ rl rr) =>
          (match rl with | none => 0 | some t => q7 t) +
            (match rr with | none => 0 | some t => q7 t))
def q7_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term q7
-- [SKIPPED BY PROFILE_LAKE] example : run q7_term (run full_term 4) = q7 (BNode.full 4) := by kernel_rfl
end

-- two-list lexicographic (structural on first, match on both)
def q8 : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then q8 xs ys else (if x < y then true else false)
def q8_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ tyWfOf (List Nat) ⇒ .prim .bool) := #leanscript_to_term q8


def q9 (x y : Nat) : Bool := decide (x < y)
def q9_term : Term sigAdd [] (natT ⇒ natT ⇒ .prim .bool) := #leanscript_to_term q9
end TermTests.Shapes.Folds
