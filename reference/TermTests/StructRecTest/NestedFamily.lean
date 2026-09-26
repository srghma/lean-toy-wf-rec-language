module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Arrays, functions and delays inside a family

A member of a mutual family may hold members **inside** another type former that is not
itself a member: an `Array` of them (`List (Array T)`, `Array (List T)`, an array of another
member of a `mutual` block), a function into one (`Nat → H`), or a delay of one
(`Thunk TB`).  The fold of a family binds, beside such a field, the answers at the members
it holds, in the field's own shape (`LeanScript.TyWf.famAnswerBinders`): the array of the
answers at the elements, the function of the answers, the delayed answer.  The Lean
recursion's helpers on the auxiliary types (`Array Q`, and the `List Q` inside it) are
folded over that array (`array_rec`), as for a recursive newtype
(`TermTests/StructRecTest/NestedOther.lean`).

For each case the kernel checks with `kernel_rfl` that the translated term gives the same
value as the Lean function. -/

namespace TermTests.StructRec.NestedFamily

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## `Array (List T)`: the list is a member, the array is not -/

/-- A tree whose children are held in an array of lists. -/
inductive ALTree where
  | node (v : Nat) (kids : Array (List ALTree))
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] /-- The tree: a family whose first member holds an array of the second (`List ALTree`). -/
-- [SKIPPED BY PROFILE_LAKE] example : tyOf ALTree = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.prim .nat, .array (.familyMember 1), []⟩)
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ []))) []) := rfl

mutual
def ALTree.sum : ALTree → Nat
  | .node v kids => v + ALTree.sumAL kids
def ALTree.sumAL : Array (List ALTree) → Nat
  | ⟨l⟩ => ALTree.sumLL l
def ALTree.sumLL : List (List ALTree) → Nat
  | [] => 0
  | t :: ts => ALTree.sumL t + ALTree.sumLL ts
def ALTree.sumL : List ALTree → Nat
  | [] => 0
  | t :: ts => t.sum + ALTree.sumL ts
end

def al1 : ALTree := .node 1 #[[.node 2 #[], .node 3 #[[.node 4 #[]]]], [], [.node 5 #[]]]
def al1_term : Term sigAdd [] (tyWfOf ALTree) := #leanscript_to_term al1
def alSum_term : Term sigAdd [] (tyWfOf ALTree ⇒ natT) := #leanscript_to_term ALTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd alSum_term (runAdd al1_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd alSum_term (runAdd al1_term) = al1.sum := by kernel_rfl

/-! ## An array of another member of a `mutual` block -/

mutual
/-- A node holds an array of `Q`s. -/
inductive P where
  | leaf (n : Nat)
  | node (qs : Array Q)
/-- A `Q` holds a label and a `P`. -/
inductive Q where
  | mk (v : Nat) (p : P)
end
deriving instance LeanScriptTyWf for P, Q

mutual
def P.sum : P → Nat
  | .leaf n => n
  | .node qs => P.sumA qs
def P.sumA : Array Q → Nat
  | ⟨l⟩ => P.sumL l
def P.sumL : List Q → Nat
  | [] => 0
  | q :: qs => q.sum + P.sumL qs
def Q.sum : Q → Nat
  | .mk v p => v + p.sum
end

def p1 : P := .node #[.mk 1 (.leaf 2), .mk 3 (.node #[.mk 4 (.leaf 5)])]
def p1_term : Term sigAdd [] (tyWfOf P) := #leanscript_to_term p1
def q1 : Q := .mk 7 (.node #[.mk 1 (.leaf 2), .mk 3 (.node #[.mk 4 (.leaf 5)])])
def q1_term : Term sigAdd [] (tyWfOf Q) := #leanscript_to_term q1

/-- Started at either member. -/
def pSum_term : Term sigAdd [] (tyWfOf P ⇒ natT) := #leanscript_to_term P.sum
def qSum_term : Term sigAdd [] (tyWfOf Q ⇒ natT) := #leanscript_to_term Q.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd p1_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd p1_term) = p1.sum := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd qSum_term (runAdd q1_term) = 22 := by kernel_rfl

/-! Members that answer different types (`Nat` and `Bool`): the fold answers the tuple of
them, and the helpers on the array read the component of `Q`. -/

mutual
def P.depth : P → Nat
  | .leaf _ => 0
  | .node qs => P.depthA qs + 1
def P.depthA : Array Q → Nat
  | ⟨l⟩ => P.depthL l
def P.depthL : List Q → Nat
  | [] => 0
  | q :: qs => (if q.big then 1 else 0) + P.depthL qs
def Q.big : Q → Bool
  | .mk _ p => match p.depth with
    | 0 => false
    | _ + 1 => true
end

def pDepth_term : Term sigAdd [] (tyWfOf P ⇒ natT) := #leanscript_to_term P.depth

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pDepth_term (runAdd p1_term) = p1.depth := by kernel_rfl

/-! A deeper look: the branch of `Q` takes its `P` apart and reads the answer at the array
inside it, so the fold is of depth `1` and the array is one of the node below. -/

mutual
def P.w : P → Nat
  | .leaf n => n
  | .node qs => P.wA qs
def P.wA : Array Q → Nat
  | ⟨l⟩ => P.wL l
def P.wL : List Q → Nat
  | [] => 0
  | q :: qs => q.w + P.wL qs
def Q.w : Q → Nat
  | .mk v (.leaf n) => v + n + n
  | .mk v (.node qs) => v + P.wA qs
end

def qW_term : Term sigAdd [] (tyWfOf Q ⇒ natT) := #leanscript_to_term Q.w

-- [SKIPPED BY PROFILE_LAKE] example : runAdd qW_term (runAdd q1_term) = 29 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd qW_term (runAdd q1_term) = q1.w := by kernel_rfl

/-! ## A function into another member -/

mutual
/-- A node holds a function into `H`. -/
inductive G where
  | leaf (n : Nat)
  | node (f : Nat → H)
/-- An `H` wraps a `G`. -/
inductive H where
  | mk (g : G)
end
deriving instance LeanScriptTyWf for G, H

mutual
def G.at3 : G → Nat
  | .leaf n => n
  | .node f => (f 3).at3
def H.at3 : H → Nat
  | .mk g => g.at3 + 1
end

def g1 : G := .node (fun n => .mk (.leaf (n * 10)))
def g1_term : Term sigAdd [] (tyWfOf G) := #leanscript_to_term g1
def gAt_term : Term sigAdd [] (tyWfOf G ⇒ natT) := #leanscript_to_term G.at3

-- [SKIPPED BY PROFILE_LAKE] example : runAdd gAt_term (runAdd g1_term) = 31 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd gAt_term (runAdd g1_term) = g1.at3 := by kernel_rfl

/-! ## A delay of another member -/

mutual
/-- A node holds a delayed `TB`. -/
inductive TA where
  | leaf (n : Nat)
  | node (t : Thunk TB)
/-- A `TB` holds a label and a `TA`. -/
inductive TB where
  | mk (v : Nat) (a : TA)
end
deriving instance LeanScriptTyWf for TA, TB

mutual
def TA.sum : TA → Nat
  | .leaf n => n
  | .node ⟨f⟩ => (f ()).sum
def TB.sum : TB → Nat
  | .mk v a => v + a.sum
end

def ta1 : TA := .node (Thunk.mk fun _ => .mk 4 (.node (Thunk.mk fun _ => .mk 2 (.leaf 5))))
def ta1_term : Term sigAdd [] (tyWfOf TA) := #leanscript_to_term ta1
def taSum_term : Term sigAdd [] (tyWfOf TA ⇒ natT) := #leanscript_to_term TA.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd taSum_term (runAdd ta1_term) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd taSum_term (runAdd ta1_term) = ta1.sum := by kernel_rfl

end TermTests.StructRec.NestedFamily

end
