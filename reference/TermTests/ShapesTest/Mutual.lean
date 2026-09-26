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

/-! # Mutual recursions, and folds of every kind looking into their subvalues

Mutual functions over one type (`Nat`, `List`, `Tree`, `Cell`, `Chain`), three-way and
four-way mutual recursions, mutual functions over a mutual block, recursions whose
branches `match` on a subvalue of a record, a newtype, a family member or an array's
list. -/

namespace TermTests.Shapes.Mutual

open LeanScript TermTests.NatRecDepth

section
open TermTests.RecUnionToTerm


mutual
def isEv : Nat → Bool
  | 0 => true
  | n + 1 => isOd n
def isOd : Nat → Bool
  | 0 => false
  | n + 1 => isEv n
end

def isEv_term : Term sigAdd [] (natT ⇒ .prim .bool) := #leanscript_to_term isEv
def isOd_term : Term sigAdd [] (natT ⇒ .prim .bool) := #leanscript_to_term isOd
-- [SKIPPED BY PROFILE_LAKE] example : runAdd isEv_term 10 = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd isOd_term 7 = true := by kernel_rfl

mutual
def evS : Tree → Nat
  | .leaf => 0
  | .node l v r => v + odS l + odS r
def odS : Tree → Nat
  | .leaf => 0
  | .node l _ r => evS l + evS r
end

def evS_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term evS
-- [SKIPPED BY PROFILE_LAKE] example : runAdd evS_term (runAdd tree7_term) = evS tree7 := by kernel_rfl
def odS_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term odS
-- [SKIPPED BY PROFILE_LAKE] example : runAdd odS_term (runAdd tree7_term) = odS tree7 := by kernel_rfl

end


mutual
def n1a : Nat → Nat
  | 0 => 1
  | n + 1 => n1b n + 1
def n1b : Nat → Nat
  | 0 => 2
  | n + 1 => n1c n * 2
def n1c : Nat → Nat
  | 0 => 3
  | n + 1 => n1a n + n
end
def n1_term : Term sigAdd [] (.prim .nat ⇒ .prim .nat) := #leanscript_to_term n1a
-- [SKIPPED BY PROFILE_LAKE] example : runAdd n1_term 7 = n1a 7 := by kernel_rfl

def n2 : Nat → Nat
  | 0 => 0
  | n + 1 => (match n with | 0 => 1 | m + 1 => n2 m) + n2 n
def n2_term : Term sigAdd [] (.prim .nat ⇒ .prim .nat) := #leanscript_to_term n2
-- [SKIPPED BY PROFILE_LAKE] example : runAdd n2_term 9 = n2 9 := by kernel_rfl

mutual
def n3a : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => n3b n (a + 1)
def n3b : Nat → Nat → Nat
  | 0, a => a * 10
  | n + 1, a => n3a n (a * 2)
end
def n3_term : Term sigAdd [] (.prim .nat ⇒ .prim .nat ⇒ .prim .nat) := #leanscript_to_term n3a
-- [SKIPPED BY PROFILE_LAKE] example : runAdd n3_term 5 1 = n3a 5 1 := by kernel_rfl

mutual
def altP : List Nat → Nat
  | [] => 0
  | x :: xs => x + altM xs
def altM : List Nat → Nat
  | [] => 0
  | _ :: xs => altP xs
end
def altP_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ .prim .nat) := #leanscript_to_term altP

def sumFrom : Nat → List Nat → Nat
  | a, [] => a
  | a, x :: xs => sumFrom (a + x) xs
def sumFrom_term : Term sigAdd [] (.prim .nat ⇒ tyWfOf (List Nat) ⇒ .prim .nat) :=
  #leanscript_to_term sumFrom

section
open TermTests.RecObjectToTerm
def c1 : Cell → Nat
  | .mk v next => v + (match next with | none => 0 | some c => c1 c)
def c1_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term c1

mutual
def evC : Cell → Nat
  | .mk v none => v
  | .mk v (some c) => v + odC c
def odC : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some c) => evC c
end
def evC_term : Term sig0 [] (cellT ⇒ natT) := #leanscript_to_term evC
end

section
open TermTests.RecAliasToTerm
mutual
def evA : Chain → Nat
  | .mk .stop => 0
  | .mk (.step v r) => v + odA r
def odA : Chain → Nat
  | .mk .stop => 0
  | .mk (.step _ r) => evA r
end
def evA_term : Term sigAdd [] (chainT ⇒ natT) := #leanscript_to_term evA

def a2 : Chain → Nat
  | .mk l => 1 + (match l with | .stop => 0 | .step v r => v + a2 r)
def a2_term : Term sigAdd [] (chainT ⇒ natT) := #leanscript_to_term a2
end

section
open TermTests.MutualFamilyToTerm.TreeForest
mutual
def tsz : Tree → Nat
  | .node v ks => v + (match ks with | .nil => 0 | .cons t r => tsz t + fsz r)
def fsz : Forest → Nat
  | .nil => 0
  | .cons t r => tsz t + fsz r
end
def tsz_term : Term sigAdd [] (TermTests.MutualFamilyToTerm.TreeForest.treeT ⇒ .prim .nat) := #leanscript_to_term tsz
end

section
open TermTests.ArrayRecToTerm
def ar1 (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | x :: xs => x * (match xs with | [] => 1 | y :: _ => y) + go xs
def ar1_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) := #leanscript_to_term ar1
-- [SKIPPED BY PROFILE_LAKE] example : run ar1_term #[1, 2, 3, 4] = ar1 #[1, 2, 3, 4] := by kernel_rfl
end


section
open TermTests.MutualFamilyToTerm TermTests.MutualFamilyToTerm.BothSubtrees

-- even-level sum on ETree only (recursion skips OTree levels), and the OTree one just calls it
mutual
def eEven : ETree → Nat
  | .leaf => 0
  | .node l v r => v + oEven l + oEven r
def oEven : OTree → Nat
  | .leaf => 0
  | .node l _ r => eEven l + eEven r
end
def oEven_term : Term sigAdd [] (otreeT ⇒ .prim .nat) := #leanscript_to_term oEven

@[inline] def eSkip : ETree → Nat
  | .leaf => 0
  | .node .leaf v .leaf => v
  | .node (.node ll _ lr) v .leaf => v + eSkip ll + eSkip lr
  | .node .leaf v (.node rl _ rr) => v + eSkip rl + eSkip rr
  | .node (.node ll _ lr) v (.node rl _ rr) => v + eSkip ll + eSkip lr + eSkip rl + eSkip rr
def oSkip : OTree → Nat
  | .leaf => 0
  | .node l _ r => eSkip l + eSkip r
def oSkip_term : Term sigAdd [] (otreeT ⇒ .prim .nat) := #leanscript_to_term oSkip

-- four mutual functions over the family: two per member
mutual
def eA : ETree → Nat
  | .leaf => 0
  | .node l v r => v + oB l + oA r
def eB : ETree → Nat
  | .leaf => 1
  | .node l _ r => oA l * oB r
def oA : OTree → Nat
  | .leaf => 0
  | .node l v r => v + eB l + eA r
def oB : OTree → Nat
  | .leaf => 1
  | .node l _ r => eA l + eB r
end
def eA_term : Term sigAdd [] (etreeT ⇒ .prim .nat) := #leanscript_to_term eA
end

section
open TermTests.MutualFamilyToTerm.TreeForest
-- the members answer different types: the fold answers the tuple of both
mutual
def tHasBig : Tree → Bool
  | .node v ks => if 10 < v then true else if fCount ks = 0 then false else true
def fCount : Forest → Nat
  | .nil => 0
  | .cons t r => (if tHasBig t then 1 else 0) + fCount r
end
def tHasBig_term : Term sigAdd [] (TermTests.MutualFamilyToTerm.TreeForest.treeT ⇒ .prim .bool) :=
  #leanscript_to_term tHasBig
@[inline] def bigEx : Tree := .node 1 (.cons (.node 2 .nil) (.cons (.node 30 .nil) .nil))
def bigEx_term : Term sigAdd [] TermTests.MutualFamilyToTerm.TreeForest.treeT :=
  #leanscript_to_term bigEx
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tHasBig_term (runAdd bigEx_term) = true := by kernel_rfl
def fCount_term : Term sigAdd [] (TermTests.MutualFamilyToTerm.TreeForest.forestT ⇒ .prim .nat) :=
  #leanscript_to_term fCount
end

end TermTests.Shapes.Mutual
