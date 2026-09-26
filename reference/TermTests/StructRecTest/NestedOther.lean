module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Nested inductives through other type formers

`TermTests/StructRecTest/NestedArray.lean` folds a declaration of **one** constructor
whose occurrences sit directly in an `Array`.  This file covers the rest of what a nested
occurrence can sit in, apart from `List` (`TermTests/ShapesTest/Nested.lean`):

* **Several constructors** (`inductive UTree | leaf | node (v : Nat) (kids : Array UTree)`,
  a JSON-like type, and also `Option T` or a structure inside a constructor).  The fold of
  a recursive tagged union hands over an answer only at a field that *is* the union, so
  `deriving LeanScriptTyWf` gives such a declaration the tree of a **recursive newtype
  whose body is the union of its constructors**, `Ty.recAlias (Ty.taggedUnion …)`, whose
  fold hands over an answer wherever an occurrence sits.  A constructor is `recAlias_mk`
  around `taggedUnion_mk`, a `match` is `recAlias_casesOn` around `taggedUnion_casesOn`,
  and a structural recursion is `recAlias_rec k`.
* **An array of anything that holds the declaration**: `Array (Array T)`,
  `Array (Option T)`, `Array (String × T)`.  The window holds the array of the elements'
  windows, and each one is taken apart as its type says when the helper on
  `List (Array T)`, `List (Option T)`, … is folded over it (`array_rec`).
* **A function into the declaration** (`node (f : Nat → FnTree)`): the window is the
  function of the answers, so the answer at `f a` is the window applied to `a`.
* **A delay** (`Thunk T`): the window is the delayed answer.
  (Both are read by deeper folds too: `TermTests/StructRecTest/NestedFnDeep.lean`.)
* **A container of one's own** with a `LeanScriptTyWf` instance (`MyList T`), which,
  like `List`, becomes a member of a family.

An array inside a *family* — `List (Array T)`, `Array (List T)`, or an array of another
member of a `mutual` block — is folded too: the fold of a family hands over, beside a field
that holds members inside it, the answers at them in the field's shape.  One case is at the
end of this file; the others are in `TermTests/StructRecTest/NestedFamily.lean`. -/

namespace TermTests.StructRec.NestedOther

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## Several constructors, one of them with an array -/

/-- A tree whose inner nodes hold their children in an array. -/
inductive UTree where
  | leaf
  | node (v : Nat) (kids : Array UTree)
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf UTree =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.taggedUnion (.skip (.here ⟨.prim .nat, [.array .self]⟩ []))) := rfl

/-- A tree written out. -/
def ut1 : UTree := .node 1 #[.leaf, .node 2 #[.node 3 #[], .leaf], .node 4 #[]]

def ut1_term : Term sigAdd [] (tyWfOf UTree) := #leanscript_to_term ut1

mutual
def UTree.sum : UTree → Nat
  | .leaf => 0
  | .node v kids => v + UTree.sumA kids
def UTree.sumA : Array UTree → Nat
  | ⟨l⟩ => UTree.sumL l
def UTree.sumL : List UTree → Nat
  | [] => 0
  | t :: ts => t.sum + UTree.sumL ts
end

def utSum_term : Term sigAdd [] (tyWfOf UTree ⇒ natT) := #leanscript_to_term UTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd utSum_term (runAdd ut1_term) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd utSum_term (runAdd ut1_term) = ut1.sum := by kernel_rfl

mutual
/-- The number of leaves. -/
def UTree.leaves : UTree → Nat
  | .leaf => 1
  | .node _ kids => UTree.leavesL kids.toList
def UTree.leavesL : List UTree → Nat
  | [] => 0
  | t :: ts => t.leaves + UTree.leavesL ts
end

def utLeaves_term : Term sigAdd [] (tyWfOf UTree ⇒ natT) := #leanscript_to_term UTree.leaves

-- [SKIPPED BY PROFILE_LAKE] example : runAdd utLeaves_term (runAdd ut1_term) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd utLeaves_term (runAdd ut1_term) = ut1.leaves := by kernel_rfl

/-- A `match` that recurses on nothing: `recAlias_casesOn` around `taggedUnion_casesOn`. -/
def UTree.label : UTree → Nat
  | .leaf => 0
  | .node v _ => v

def utLabel_term : Term sigAdd [] (tyWfOf UTree ⇒ natT) := #leanscript_to_term UTree.label

-- [SKIPPED BY PROFILE_LAKE] example : runAdd utLabel_term (runAdd ut1_term) = 1 := by kernel_rfl

/-! ## A JSON-like type -/

/-- JSON values, with arrays and objects held in arrays. -/
inductive Json where
  | null
  | num (n : Nat)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving LeanScriptTyWf

def j1 : Json := .obj #[("ab", .num 3), ("c", .arr #[.num 4, .null, .str "xyz"])]

def j1_term : Term sigAdd [] (tyWfOf Json) := #leanscript_to_term j1

mutual
/-- The numbers, and the lengths of the strings and the keys, added up. -/
def Json.total : Json → Nat
  | .null => 0
  | .num n => n
  | .str s => s.length
  | .arr xs => Json.totalA xs
  | .obj kvs => Json.totalO kvs
def Json.totalA : Array Json → Nat
  | ⟨l⟩ => Json.totalL l
def Json.totalL : List Json → Nat
  | [] => 0
  | j :: js => j.total + Json.totalL js
def Json.totalO : Array (String × Json) → Nat
  | ⟨l⟩ => Json.totalOL l
def Json.totalOL : List (String × Json) → Nat
  | [] => 0
  | (k, j) :: kvs => k.length + j.total + Json.totalOL kvs
end

def total_term : Term sigAdd [] (tyWfOf Json ⇒ natT) := #leanscript_to_term Json.total

-- [SKIPPED BY PROFILE_LAKE] example : runAdd total_term (runAdd j1_term) = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd total_term (runAdd j1_term) = j1.total := by kernel_rfl

mutual
/-- How deeply arrays and objects are nested (a `match` with a wildcard). -/
def Json.depth : Json → Nat
  | .arr xs => Json.depthL xs.toList + 1
  | .obj kvs => Json.depthOL kvs.toList + 1
  | _ => 0
def Json.depthL : List Json → Nat
  | [] => 0
  | j :: js => max j.depth (Json.depthL js)
def Json.depthOL : List (String × Json) → Nat
  | [] => 0
  | (_, j) :: kvs => max j.depth (Json.depthOL kvs)
end

def depth_term : Term sigAdd [] (tyWfOf Json ⇒ natT) := #leanscript_to_term Json.depth

-- [SKIPPED BY PROFILE_LAKE] example : runAdd depth_term (runAdd j1_term) = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd depth_term (runAdd j1_term) = j1.depth := by kernel_rfl

/-! ## Several constructors, the occurrence inside a union or a structure -/

/-- A chain whose links may be missing. -/
inductive OTree where
  | leaf
  | node (v : Nat) (next : Option OTree)
  deriving LeanScriptTyWf

def OTree.sum : OTree → Nat
  | .leaf => 0
  | .node v none => v
  | .node v (some t) => v + t.sum

def ot1 : OTree := .node 1 (some (.node 2 none))
def ot1_term : Term sigAdd [] (tyWfOf OTree) := #leanscript_to_term ot1
def otSum_term : Term sigAdd [] (tyWfOf OTree ⇒ natT) := #leanscript_to_term OTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd otSum_term (runAdd ot1_term) = 3 := by kernel_rfl

/-- A chain whose links are pairs. -/
inductive PTree where
  | leaf
  | node (c : Nat × PTree)
  deriving LeanScriptTyWf

def PTree.sum : PTree → Nat
  | .leaf => 0
  | .node (v, t) => v + t.sum

def pt1 : PTree := .node (5, .node (6, .leaf))
def pt1_term : Term sigAdd [] (tyWfOf PTree) := #leanscript_to_term pt1
def ptSum_term : Term sigAdd [] (tyWfOf PTree ⇒ natT) := #leanscript_to_term PTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ptSum_term (runAdd pt1_term) = 11 := by kernel_rfl

/-! ## Arrays of values that hold the declaration -/

/-- A tree whose children come in groups. -/
inductive AATree where
  | node (v : Nat) (kids : Array (Array AATree))
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf AATree = .recObject ⟨.prim .nat, .array (.array .self), []⟩ := rfl

mutual
def AATree.sum : AATree → Nat
  | .node v kids => v + AATree.sumAA kids
def AATree.sumAA : Array (Array AATree) → Nat
  | ⟨l⟩ => AATree.sumLA l
def AATree.sumLA : List (Array AATree) → Nat
  | [] => 0
  | t :: ts => AATree.sumA t + AATree.sumLA ts
def AATree.sumA : Array AATree → Nat
  | ⟨l⟩ => AATree.sumL l
def AATree.sumL : List AATree → Nat
  | [] => 0
  | t :: ts => t.sum + AATree.sumL ts
end

def aa1 : AATree := .node 1 #[#[.node 2 #[]], #[], #[.node 3 #[#[.node 4 #[]]], .node 5 #[]]]
def aa1_term : Term sigAdd [] (tyWfOf AATree) := #leanscript_to_term aa1
def aaSum_term : Term sigAdd [] (tyWfOf AATree ⇒ natT) := #leanscript_to_term AATree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd aaSum_term (runAdd aa1_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aaSum_term (runAdd aa1_term) = aa1.sum := by kernel_rfl

/-- A tree some of whose child slots are empty. -/
inductive AOTree where
  | node (v : Nat) (kids : Array (Option AOTree))
  deriving LeanScriptTyWf

mutual
def AOTree.sum : AOTree → Nat
  | .node v kids => v + AOTree.sumA kids
def AOTree.sumA : Array (Option AOTree) → Nat
  | ⟨l⟩ => AOTree.sumL l
def AOTree.sumL : List (Option AOTree) → Nat
  | [] => 0
  | none :: ts => AOTree.sumL ts
  | some t :: ts => t.sum + AOTree.sumL ts
end

def ao1 : AOTree := .node 1 #[none, some (.node 2 #[some (.node 3 #[])]), none]
def ao1_term : Term sigAdd [] (tyWfOf AOTree) := #leanscript_to_term ao1
def aoSum_term : Term sigAdd [] (tyWfOf AOTree ⇒ natT) := #leanscript_to_term AOTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd aoSum_term (runAdd ao1_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aoSum_term (runAdd ao1_term) = ao1.sum := by kernel_rfl

/-! ## A function into the declaration -/

/-- An infinitely branching tree. -/
inductive FnTree where
  | leaf (n : Nat)
  | node (f : Nat → FnTree)
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf FnTree =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.taggedUnion (.payloadFirst ⟨.prim .nat, []⟩ [.fn (.prim .nat) .self] [])) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

/-- The leaves reached by the first two branches, all the way down. -/
def FnTree.firstTwo : FnTree → Nat
  | .leaf n => n
  | .node f => (f 0).firstTwo + (f 1).firstTwo

def ft1 : FnTree := .node fun n => .node fun m => .leaf (10 * n + m + 1)
def ft1_term : Term sigAdd [] (tyWfOf FnTree) := #leanscript_to_term ft1
def firstTwo_term : Term sigAdd [] (tyWfOf FnTree ⇒ natT) := #leanscript_to_term FnTree.firstTwo

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstTwo_term (runAdd ft1_term) = 26 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstTwo_term (runAdd ft1_term) = ft1.firstTwo := by kernel_rfl

/-! ## A delay -/

/-- A list whose tail is computed on demand. -/
inductive Stream' where
  | nil
  | cons (v : Nat) (rest : Thunk Stream')
  deriving LeanScriptTyWf

def Stream'.sum : Stream' → Nat
  | .nil => 0
  | .cons v ⟨f⟩ => v + (f ()).sum

def st1 : Stream' := .cons 1 (Thunk.mk fun _ => .cons 2 (Thunk.mk fun _ => .nil))
def st1_term : Term sigAdd [] (tyWfOf Stream') := #leanscript_to_term st1
def stSum_term : Term sigAdd [] (tyWfOf Stream' ⇒ natT) := #leanscript_to_term Stream'.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd stSum_term (runAdd st1_term) = 3 := by kernel_rfl

/-! ## A container of one's own -/

/-- A list type written by hand. -/
inductive MyList (α : Type) where
  | nil
  | cons (a : α) (t : MyList α)
  deriving LeanScriptTyWf

/-- A rose tree over it. -/
inductive MTree where
  | node (v : Nat) (kids : MyList MTree)
  deriving LeanScriptTyWf

mutual
def MTree.sum : MTree → Nat
  | .node v kids => v + MTree.sumL kids
def MTree.sumL : MyList MTree → Nat
  | .nil => 0
  | .cons t ts => t.sum + MTree.sumL ts
end

def mt1 : MTree := .node 1 (.cons (.node 2 .nil) (.cons (.node 3 (.cons (.node 4 .nil) .nil)) .nil))
def mt1_term : Term sigAdd [] (tyWfOf MTree) := #leanscript_to_term mt1
def mtSum_term : Term sigAdd [] (tyWfOf MTree ⇒ natT) := #leanscript_to_term MTree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd mtSum_term (runAdd mt1_term) = 10 := by kernel_rfl

/-! ## An array inside a family

`List (Array T)` makes `List (Array T)` a member of a family, and the array of `T` inside
it is not a member: the fold of the family binds, beside that field, the array of the
answers at its elements (`LeanScript.TyWf.famAnswerBinders`), which the helpers on
`Array LATree` and `List LATree` are folded over. -/

inductive LATree where
  | node (v : Nat) (kids : List (Array LATree))
  deriving LeanScriptTyWf

mutual
def LATree.sum : LATree → Nat
  | .node v kids => v + LATree.sumLA kids
def LATree.sumLA : List (Array LATree) → Nat
  | [] => 0
  | t :: ts => LATree.sumA t + LATree.sumLA ts
def LATree.sumA : Array LATree → Nat
  | ⟨l⟩ => LATree.sumL l
def LATree.sumL : List LATree → Nat
  | [] => 0
  | t :: ts => t.sum + LATree.sumL ts
end

def la1 : LATree := .node 1 [#[.node 2 [], .node 3 [#[.node 4 []]]], #[], #[.node 5 []]]
def la1_term : Term sigAdd [] (tyWfOf LATree) := #leanscript_to_term la1
def laSum_term : Term sigAdd [] (tyWfOf LATree ⇒ natT) := #leanscript_to_term LATree.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd laSum_term (runAdd la1_term) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd laSum_term (runAdd la1_term) = la1.sum := by kernel_rfl

end TermTests.StructRec.NestedOther

end
