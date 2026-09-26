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

/-! # A recursive record: looks through `Option` fields, one or both subtrees -/

namespace TermTests.Shapes.Objects

open LeanScript TermTests.RecObjectToTerm TermTests.RecObjectToTerm.BinTree

def r1 : BNode → Nat
  | .mk v l _ => v + (match l with | none => 0 | some t => r1 t)
def r1_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r1

def r2 : BNode → Nat
  | .mk v l _ => v + (match l with | none => 0 | some (.mk _ ll _) => (match ll with | none => 0 | some t => r2 t))
def r2_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r2

def r3 : BNode → Nat
  | .mk v l _ => match l with | none => v | some (.mk _ ll _) => (match ll with | none => 0 | some t => r3 t)
def r3_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r3

def r4 : BNode → Nat
  | .mk v (some (.mk _ (some t) _)) _ => v + r4 t
  | .mk v _ _ => v
def r4_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r4
def r5 : BNode → Nat
  | .mk v l r => v + (match l with | none => 0 | some t => r5 t) + (match r with | none => 0 | some t => r5 t)
def r5_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r5

def r6 : BNode → Nat
  | .mk v l _ =>
    v + (match l with
          | none => 0
          | some (.mk _ ll lr) =>
            (match ll with | none => 0 | some t => r6 t) +
              (match lr with | none => 0 | some t => r6 t))

def r6_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r6

def r7 : BNode → Nat
  | .mk v l _ =>
    v + (match l with
          | none => 0
          | some (.mk _ ll _) =>
            (match ll with | none => 0 | some t => r7 t) + 1)
def r7_term : Term sig0 [] (bnodeT ⇒ .prim .nat) := #leanscript_to_term r7

-- [SKIPPED BY PROFILE_LAKE] example : run r6_term (run full_term 4) = r6 (BNode.full 4) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run r4_term (run full_term 4) = r4 (BNode.full 4) := by kernel_rfl

end TermTests.Shapes.Objects
