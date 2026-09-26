module

public import LeanScript.Ty.Instances
public import LeanScript.Eval
public meta import LeanScript.KernelRfl
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab
@[expose] public section

/-! Nested inductives: a type recursing through `List` (rose trees).  Its structural
recursions — over the type and over the lists of it, mutual helpers over the lists, looks
two levels down — are folds of the family `Rose`, `List Rose`. -/


namespace TermTests.Shapes.Nested
open LeanScript
inductive Rose | node (v : Nat) (kids : List Rose)
  deriving LeanScriptTyWf
def sig0 : Sig := ⟨[], by decide⟩
scoped macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)
def Rose.sum : Rose → Nat
  | .node v ks => v + sumL ks
where sumL : List Rose → Nat
  | [] => 0
  | k :: ks => k.sum + sumL ks
def r_term : Term sig0 [] (tyWfOf Rose ⇒ .prim .nat) := #leanscript_to_term Rose.sum
def sumL_term : Term sig0 [] (tyWfOf (List Rose) ⇒ .prim .nat) := #leanscript_to_term Rose.sum.sumL
@[inline] def ex : Rose := .node 1 [.node 2 [], .node 3 [.node 4 []]]
def ex_term : Term sig0 [] (tyWfOf Rose) := #leanscript_to_term ex
-- [SKIPPED BY PROFILE_LAKE] example : run r_term (run ex_term) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run sumL_term (run (#leanscript_to_term [ex, ex] : Term sig0 [] (tyWfOf (List Rose)))) = 20 := by kernel_rfl

def Rose.build : Nat → Rose
  | 0 => .node 0 []
  | n + 1 => .node (n + 1) [Rose.build n, .node 7 []]
def build_term : Term sig0 [] (.prim .nat ⇒ tyWfOf Rose) := #leanscript_to_term Rose.build
-- [SKIPPED BY PROFILE_LAKE] example : run r_term (run build_term 5) = Rose.sum (Rose.build 5) := by kernel_rfl

-- number of children of the root (match on the list, no recursion)
def Rose.nkids : Rose → Nat
  | .node _ [] => 0
  | .node _ [_] => 1
  | .node _ _ => 2
def nkids_term : Term sig0 [] (tyWfOf Rose ⇒ .prim .nat) := #leanscript_to_term Rose.nkids
-- [SKIPPED BY PROFILE_LAKE] example : run nkids_term (run ex_term) = 2 := by kernel_rfl

-- depth
def Rose.depth : Rose → Nat
  | .node _ ks => depthL ks + 1
where depthL : List Rose → Nat
  | [] => 0
  | k :: ks => max k.depth (depthL ks)
def depth_term : Term sig0 [] (tyWfOf Rose ⇒ .prim .nat) := #leanscript_to_term Rose.depth
-- [SKIPPED BY PROFILE_LAKE] example : run depth_term (run build_term 4) = Rose.depth (Rose.build 4) := by kernel_rfl

-- grandchildren: sum of labels at even levels
def Rose.evenSum : Rose → Nat
  | .node v ks => v + gl ks
where
  gl : List Rose → Nat
    | [] => 0
    | .node _ gs :: ks => kl gs + gl ks
  kl : List Rose → Nat
    | [] => 0
    | k :: ks => k.evenSum + kl ks
def evenSum_term : Term sig0 [] (tyWfOf Rose ⇒ .prim .nat) := #leanscript_to_term Rose.evenSum

-- a parameter
inductive TreeL (α : Type) where
  | node : α → List (TreeL α) → TreeL α
  deriving LeanScriptTyWf
def TreeL.sum : TreeL Nat → Nat
  | .node v ks => v + sumL ks
where sumL : List (TreeL Nat) → Nat
  | [] => 0
  | k :: ks => k.sum + sumL ks
def tsum_term : Term sig0 [] (tyWfOf (TreeL Nat) ⇒ .prim .nat) := #leanscript_to_term TreeL.sum

-- a list of lists
inductive RLL where
  | node : List (List RLL) → RLL
  deriving LeanScriptTyWf
def RLL.count : RLL → Nat
  | .node xss => 1 + c2 xss
where
  c2 : List (List RLL) → Nat
    | [] => 0
    | xs :: xss => c1 xs + c2 xss
  c1 : List RLL → Nat
    | [] => 0
    | x :: xs => x.count + c1 xs
def rll_term : Term sig0 [] (tyWfOf RLL ⇒ .prim .nat) := #leanscript_to_term RLL.count
-- [SKIPPED BY PROFILE_LAKE] example : run evenSum_term (run build_term 3) = Rose.evenSum (Rose.build 3) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run depth_term (run ex_term) = 3 := by kernel_rfl

-- a `match` on the list of children, with list patterns and a wildcard
def f2 (ks : List Rose) : Nat := match ks with | [] => 0 | [_] => 1 | _ => 2
def f2_term : Term sig0 [] (tyWfOf (List Rose) ⇒ .prim .nat) := #leanscript_to_term f2

end TermTests.Shapes.Nested
