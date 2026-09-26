module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # More `mutual` blocks whose members also occur nested

Companion to `TermTests/StructRecTest/MutualNested.lean`, which has the basic case
(`Option Q` inside `P`).  This file covers further shapes of the same kind:

* occurrences in **both directions** (`Option Q` inside `P`, `Option P` inside `Q`);
* a member under **`List`** (`List Q` inside `P`), which becomes a recursive member of the
  family (`nil | cons Q (List Q)`);
* **several wrappers** and a nested occurrence of the member itself
  (`Option (Option Q)` and `Option P` inside `P`), each a member of its own;
* a **type parameter** (`P α`, `Q α`);
* a **user structure** and a **product** around members, in a **three-member** block
  mixing `Option` and `List`.

and several kinds of function on them: sums started at any member (including the
auxiliary type `Option (Option Q)`), non-recursive `match`es, a **map** that rebuilds the
value (its members answer `P2` and `Q2`, types with no `Inhabited` instance: the
translation builds the defaults it needs from their constructors,
`LeanScript.ToTerm.synthDefault?`), members answering different types, an accumulator, and
a recursion that reads two levels down.

Every translated function is run by the kernel (`kernel_rfl`) and compared with the Lean
function. -/

namespace TermTests.StructRec.MutualNestedMore

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## Both directions: `Option Q2` inside `P2`, `Option P2` inside `Q2` -/

mutual
/-- A leaf, or a node holding perhaps a `Q2`. -/
inductive P2 where
  | leaf (n : Nat)
  | node (q : Option Q2)
/-- Perhaps a `P2`, and a `P2`. -/
inductive Q2 where
  | mk (a : Option P2) (b : P2)
end
deriving instance LeanScriptTyWf for P2, Q2

-- members: `P2`, `Q2`, `Option Q2` (member 2), `Option P2` (member 3)
-- [SKIPPED BY PROFILE_LAKE] example : tyOf P2 = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 2] []))
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.familyMember 3, .familyMember 0, []⟩)
-- [SKIPPED BY PROFILE_LAKE]     [.ctors (.skip (.here ⟨.familyMember 1, []⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]      .ctors (.skip (.here ⟨.familyMember 0, []⟩ []))]) := rfl

mutual
/-- The sum of the leaves. -/
def P2.sum : P2 → Nat
  | .leaf n => n
  | .node none => 0
  | .node (some q) => q.sum
/-- The sum of the leaves. -/
def Q2.sum : Q2 → Nat
  | .mk none b => b.sum
  | .mk (some a) b => a.sum + b.sum
end

/-- A `P2` written out. -/
def p2 : P2 := .node (some (.mk (some (.leaf 3)) (.node (some (.mk none (.leaf 4))))))
/-- A `Q2` written out. -/
def q2 : Q2 :=
  .mk (some (.node (some (.mk (some (.leaf 3)) (.node (some (.mk none (.leaf 4))))))))
    (.leaf 5)

def p2_term : Term sigAdd [] (tyWfOf P2) := #leanscript_to_term p2
def q2_term : Term sigAdd [] (tyWfOf Q2) := #leanscript_to_term q2
def p2Sum_term : Term sigAdd [] (tyWfOf P2 ⇒ natT) := #leanscript_to_term P2.sum
def q2Sum_term : Term sigAdd [] (tyWfOf Q2 ⇒ natT) := #leanscript_to_term Q2.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2Sum_term (runAdd p2_term) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2Sum_term (runAdd p2_term) = p2.sum := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q2Sum_term (runAdd q2_term) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q2Sum_term (runAdd q2_term) = q2.sum := by kernel_rfl

/-- Is it a leaf?  (A `match`, no recursion.) -/
def P2.isLeaf : P2 → Bool
  | .leaf _ => true
  | .node _ => false

/-- The `Option Q2` a node holds.  (A `match` answering a member of the family.) -/
def P2.qOf : P2 → Option Q2
  | .leaf _ => none
  | .node q => q

def p2IsLeaf_term : Term sigAdd [] (tyWfOf P2 ⇒ .prim .bool) := #leanscript_to_term P2.isLeaf
def p2QOf_term : Term sigAdd [] (tyWfOf P2 ⇒ tyWfOf (Option Q2)) := #leanscript_to_term P2.qOf

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2IsLeaf_term (runAdd p2_term) = false := by kernel_rfl
/-- A leaf. -/
def leaf1 : P2 := .leaf 1
def leaf1_term : Term sigAdd [] (tyWfOf P2) := #leanscript_to_term leaf1
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2IsLeaf_term (runAdd leaf1_term) = true := by kernel_rfl

mutual
/-- Add one to every leaf: a map, whose members answer `P2` and `Q2`.  Neither type has an
    `Inhabited` instance; the defaults the fold's tuple needs are built from constructors. -/
def P2.inc : P2 → P2
  | .leaf n => .leaf (n + 1)
  | .node none => .node none
  | .node (some q) => .node (some q.inc)
/-- Add one to every leaf. -/
def Q2.inc : Q2 → Q2
  | .mk none b => .mk none b.inc
  | .mk (some a) b => .mk (some a.inc) b.inc
end

def p2Inc_term : Term sigAdd [] (tyWfOf P2 ⇒ tyWfOf P2) := #leanscript_to_term P2.inc
def q2Inc_term : Term sigAdd [] (tyWfOf Q2 ⇒ tyWfOf Q2) := #leanscript_to_term Q2.inc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2Sum_term (runAdd p2Inc_term (runAdd p2_term)) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2Sum_term (runAdd p2Inc_term (runAdd p2_term)) = p2.inc.sum := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q2Sum_term (runAdd q2Inc_term (runAdd q2_term)) = q2.inc.sum := by kernel_rfl

/-- `Bool.not`, inlinable. -/
@[inline] def boolNot (b : Bool) : Bool := match b with | true => false | false => true

mutual
/-- Has it a leaf?  (Answers `Bool`, while `Q2.count` answers `Nat`.) -/
def P2.hasLeaf : P2 → Bool
  | .leaf _ => true
  | .node none => false
  | .node (some q) => boolNot (q.count == 0)
/-- How many of its `P2`s have a leaf. -/
def Q2.count : Q2 → Nat
  | .mk none b => if b.hasLeaf then 1 else 0
  | .mk (some a) b => (if a.hasLeaf then 1 else 0) + (if b.hasLeaf then 1 else 0)
end

def p2HasLeaf_term : Term sigAdd [] (tyWfOf P2 ⇒ .prim .bool) := #leanscript_to_term P2.hasLeaf
def q2Count_term : Term sigAdd [] (tyWfOf Q2 ⇒ natT) := #leanscript_to_term Q2.count

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2HasLeaf_term (runAdd p2_term) = p2.hasLeaf := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q2Count_term (runAdd q2_term) = 2 := by kernel_rfl

mutual
/-- The sum of the leaves, with an accumulator. -/
def P2.sumAcc : P2 → Nat → Nat
  | .leaf n, acc => n + acc
  | .node none, acc => acc
  | .node (some q), acc => q.sumAcc acc
/-- The sum of the leaves, with an accumulator. -/
def Q2.sumAcc : Q2 → Nat → Nat
  | .mk none b, acc => b.sumAcc acc
  | .mk (some a) b, acc => b.sumAcc (a.sumAcc acc)
end

def p2SumAcc_term : Term sigAdd [] (tyWfOf P2 ⇒ natT ⇒ natT) := #leanscript_to_term P2.sumAcc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2SumAcc_term (runAdd p2_term) 100 = 107 := by kernel_rfl

mutual
/-- Reads two levels down: at a node whose `Q2` holds a `P2` node, the sum of *its* `Q2`
    as well. -/
def P2.deep : P2 → Nat
  | .leaf n => n
  | .node none => 0
  | .node (some (.mk none b)) => b.deep + 1
  | .node (some (.mk (some a) b)) =>
      a.deep + b.deep + (match b with | .node (some q) => q.deep | _ => 0)
/-- The `P2` on the right. -/
def Q2.deep : Q2 → Nat
  | .mk _ b => b.deep
end

def p2Deep_term : Term sigAdd [] (tyWfOf P2 ⇒ natT) := #leanscript_to_term P2.deep

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p2Deep_term (runAdd p2_term) = p2.deep := by kernel_rfl

/-! ## `List Q3` inside `P3` -/

mutual
/-- A leaf, or a node with a list of `Q3`s. -/
inductive P3 where
  | leaf (n : Nat)
  | node (qs : List Q3)
/-- Two `P3`s. -/
inductive Q3 where
  | mk (a : P3) (b : P3)
end
deriving instance LeanScriptTyWf for P3, Q3

-- member 2 is `List Q3`: `nil | cons (member 1) (member 2)`
-- [SKIPPED BY PROFILE_LAKE] example : tyOf P3 = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 2] []))
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.familyMember 0, .familyMember 0, []⟩)
-- [SKIPPED BY PROFILE_LAKE]     [.ctors (.skip (.here ⟨.familyMember 1, [.familyMember 2]⟩ []))]) := rfl

mutual
/-- The sum of the leaves. -/
def P3.sum : P3 → Nat
  | .leaf n => n
  | .node qs => P3.sumL qs
/-- The sum of the leaves of a list. -/
def P3.sumL : List Q3 → Nat
  | [] => 0
  | q :: qs => q.sum + P3.sumL qs
/-- The sum of the leaves. -/
def Q3.sum : Q3 → Nat
  | .mk a b => a.sum + b.sum
end

/-- A `P3` written out. -/
def p3 : P3 := .node [.mk (.leaf 3) (.leaf 4), .mk (.leaf 5) (.node [])]

def p3_term : Term sigAdd [] (tyWfOf P3) := #leanscript_to_term p3
def p3Sum_term : Term sigAdd [] (tyWfOf P3 ⇒ natT) := #leanscript_to_term P3.sum
def p3SumL_term : Term sigAdd [] (tyWfOf (List Q3) ⇒ natT) := #leanscript_to_term P3.sumL

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p3Sum_term (runAdd p3_term) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p3Sum_term (runAdd p3_term) = p3.sum := by kernel_rfl
/-- A `List Q3` written out. -/
def qs3 : List Q3 := [.mk (.leaf 1) (.leaf 2)]
def qs3_term : Term sigAdd [] (tyWfOf (List Q3)) := #leanscript_to_term qs3
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p3SumL_term (runAdd qs3_term) = 3 := by kernel_rfl

/-! ## `Option (Option Q4)` and `Option P4` inside `P4` -/

mutual
/-- A leaf, or a node with perhaps perhaps a `Q4`, and perhaps a `P4`. -/
inductive P4 where
  | leaf (n : Nat)
  | node (q : Option (Option Q4)) (p : Option P4)
/-- A `P4`. -/
inductive Q4 where
  | mk (a : P4)
end
deriving instance LeanScriptTyWf for P4, Q4

-- members: `P4`, `Q4`, `Option (Option Q4)`, `Option P4`, `Option Q4`
-- [SKIPPED BY PROFILE_LAKE] example : tyOf P4 = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 2, .familyMember 3] []))
-- [SKIPPED BY PROFILE_LAKE]     (.alias (.familyMember 0))
-- [SKIPPED BY PROFILE_LAKE]     [.ctors (.skip (.here ⟨.familyMember 4, []⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]      .ctors (.skip (.here ⟨.familyMember 0, []⟩ [])),
-- [SKIPPED BY PROFILE_LAKE]      .ctors (.skip (.here ⟨.familyMember 1, []⟩ []))]) := rfl

mutual
/-- The sum of the leaves, and `1` for each `some none`. -/
def P4.sum : P4 → Nat
  | .leaf n => n
  | .node q p => P4.sumOO q + P4.sumO p
/-- `P4.sum`, through two options. -/
def P4.sumOO : Option (Option Q4) → Nat
  | none => 0
  | some none => 1
  | some (some q) => q.sum
/-- `P4.sum`, through an option. -/
def P4.sumO : Option P4 → Nat
  | none => 0
  | some p => p.sum
/-- `P4.sum`. -/
def Q4.sum : Q4 → Nat
  | .mk a => a.sum
end

/-- A `P4` written out. -/
def p4 : P4 := .node (some (some (.mk (.leaf 5)))) (some (.node (some none) none))

def p4_term : Term sigAdd [] (tyWfOf P4) := #leanscript_to_term p4
def p4Sum_term : Term sigAdd [] (tyWfOf P4 ⇒ natT) := #leanscript_to_term P4.sum
def q4Sum_term : Term sigAdd [] (tyWfOf Q4 ⇒ natT) := #leanscript_to_term Q4.sum
-- started at the auxiliary type
def p4SumOO_term : Term sigAdd [] (tyWfOf (Option (Option Q4)) ⇒ natT) :=
  #leanscript_to_term P4.sumOO

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p4Sum_term (runAdd p4_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p4Sum_term (runAdd p4_term) = p4.sum := by kernel_rfl
/-- A `Q4` written out. -/
def q4 : Q4 := .mk (.node (some (some (.mk (.leaf 5)))) (some (.node (some none) none)))
/-- An `Option (Option Q4)` written out. -/
def oo4 : Option (Option Q4) := some (some (.mk (.leaf 6)))
def q4_term : Term sigAdd [] (tyWfOf Q4) := #leanscript_to_term q4
def oo4_term : Term sigAdd [] (tyWfOf (Option (Option Q4))) := #leanscript_to_term oo4
-- [SKIPPED BY PROFILE_LAKE] example : runAdd q4Sum_term (runAdd q4_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p4SumOO_term (runAdd oo4_term) = 6 := by kernel_rfl

/-! ## A type parameter -/

mutual
/-- A leaf holding an `α`, or a node holding perhaps a `Q5 α`. -/
inductive P5 (α : Type) where
  | leaf (a : α)
  | node (q : Option (Q5 α))
/-- Two `P5 α`s. -/
inductive Q5 (α : Type) where
  | mk (a : P5 α) (b : P5 α)
end
deriving instance LeanScriptTyWf for P5, Q5

mutual
/-- The sum of the leaves. -/
def P5.sum : P5 Nat → Nat
  | .leaf n => n
  | .node none => 0
  | .node (some q) => q.sum
/-- The sum of the leaves. -/
def Q5.sum : Q5 Nat → Nat
  | .mk a b => a.sum + b.sum
end

/-- A `P5 Nat` written out. -/
def p5 : P5 Nat := .node (some (.mk (.leaf 3) (.node (some (.mk (.leaf 4) (.node none))))))

def p5_term : Term sigAdd [] (tyWfOf (P5 Nat)) := #leanscript_to_term p5
def p5Sum_term : Term sigAdd [] (tyWfOf (P5 Nat) ⇒ natT) := #leanscript_to_term P5.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd p5Sum_term (runAdd p5_term) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd p5Sum_term (runAdd p5_term) = p5.sum := by kernel_rfl

/-! ## Three members: a product, a user structure and a list around members -/

/-- A number and perhaps an `α`. -/
structure Box (α : Type) where
  val : Nat
  item : Option α
  deriving LeanScriptTyWf

mutual
/-- A leaf, a `Y × X` pair, or a box of a `Z`. -/
inductive X where
  | leaf
  | pair (p : Y × X)
  | box (b : Box Z)
/-- Perhaps an `X`. -/
inductive Y where
  | mk (x : Option X)
/-- A list of `Y`s. -/
inductive Z where
  | mk (y : List Y)
end
deriving instance LeanScriptTyWf for X, Y, Z

mutual
/-- The leaves, plus the numbers in the boxes. -/
def X.size : X → Nat
  | .leaf => 1
  | .pair (y, x) => y.size + x.size
  | .box ⟨v, none⟩ => v
  | .box ⟨v, some z⟩ => v + z.size
/-- `X.size`, through an option. -/
def Y.size : Y → Nat
  | .mk none => 0
  | .mk (some x) => x.size
/-- `X.size`, through a list. -/
def Z.size : Z → Nat
  | .mk ys => Z.sizeL ys
/-- `X.size`, through a list. -/
def Z.sizeL : List Y → Nat
  | [] => 0
  | y :: ys => y.size + Z.sizeL ys
end

/-- An `X` written out. -/
def x1 : X :=
  .pair (.mk (some .leaf), .box ⟨10, some (.mk [.mk none, .mk (some (.box ⟨2, none⟩))])⟩)

def x1_term : Term sigAdd [] (tyWfOf X) := #leanscript_to_term x1
def xSize_term : Term sigAdd [] (tyWfOf X ⇒ natT) := #leanscript_to_term X.size

-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSize_term (runAdd x1_term) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd xSize_term (runAdd x1_term) = x1.size := by kernel_rfl

end TermTests.StructRec.MutualNestedMore

end
