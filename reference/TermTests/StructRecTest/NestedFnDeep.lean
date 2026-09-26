module

public import TermTests.NatRecDepthTest.Common
public import TermTests.StructRecTest.DeepFolds
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Function and delayed fields in a fold deeper than `0`

`TermTests/StructRecTest/NestedOther.lean` folds declarations with a field that is a
function into the declaration (`node (f : Nat → FT)`) or a delay of it (`Thunk TS`), but
only by the depth-`0` fold.  At depth `k` the window holds, at such a field, the function
of the **answer trees** (`Nat ⇒ ⟨answer, window⟩`) or the delayed answer tree, and the
translation binds beside it the function of the answers (`fun a => (window a).1`) or the
delayed answer (`Thunk.mk (window.get).1`), which the branch reads as it reads the
depth-`0` window.

So a recursion that reads further down elsewhere — through a direct field, an `Option`, …
— may now also read the answers at `f a` or at a delayed value, at any level it reaches:
the top level (where the window is `j = k` levels deep), inside a subvalue taken apart
(`j = k - 1`, …), or at the frontier (`j = 0`).

What stays out of reach is taking apart `f a` itself: Lean's structural recursion does
not accept `match f 0 with …` followed by a recursive call on what the match binds, so
no such program reaches the translation.

For each program the kernel checks (`kernel_rfl`) the depth of the fold, the value on a
sample input as a fixed number, and the value against the Lean definition.  The terms bound
beside the window are `Term.fnTreeAnswer` and `Term.thunkTreeAnswer`: that they give the
depth-`0` window, at every depth and in every environment, is proved in
`LeanScript/RecFnFieldFacts.lean`, and the checks below confirm that the translation
writes them. -/

namespace TermTests.StructRec.NestedFnDeep

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Deep

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## A function field, read at depth `1` and `2` -/

/-- An infinitely branching tree with unary nodes. -/
inductive FT where
  | leaf (n : Nat)
  | one (t : FT)
  | node (f : Nat → FT)
  deriving LeanScriptTyWf

/-- Depth `1`: it looks one level into a `one`, and reads the answers at `f a` both at the
    top level and one level down. -/
def FT.foo : FT → Nat
  | .leaf n => n
  | .one (.leaf n) => n + 1
  | .one (.one t) => t.foo * 2
  | .one (.node f) => (f 0).foo + (f 1).foo
  | .node f => (f 3).foo + 1

set_option leanscript.toTerm.normalize false in
/-- The translated term of `FT.foo` as the translation writes it, before normalization: at
    the function field of the top level (where the window is one level deep), it binds
    `Term.fnTreeAnswer`, whose value `LeanScript.eval_fnTreeAnswer_aliasAnswerTree`
    proves is the depth-`0` window. -/
def foo_term_raw : Term sigAdd [] (tyWfOf FT ⇒ natT) := #leanscript_to_term FT.foo

open Lean Elab Command in
run_cmd do
  let some ci := (← getEnv).find? ``foo_term_raw | throwError "no `foo_term_raw`"
  unless (ci.value!.find? (·.isConstOf ``Term.fnTreeAnswer)).isSome do
    throwError "the term of `FT.foo` does not bind `Term.fnTreeAnswer`"

def ft1 : FT := .one (.node fun n => .one (.one (.node fun m => .leaf (n + m))))
def ft1_term : Term sigAdd [] (tyWfOf FT) := #leanscript_to_term ft1
def foo_term : Term sigAdd [] (tyWfOf FT ⇒ natT) := #leanscript_to_term FT.foo

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? foo_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd foo_term (runAdd ft1_term) = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd foo_term (runAdd ft1_term) = ft1.foo := by kernel_rfl

/-- Depth `2`: the function field is read at every level `0 … 2` of the window. -/
def FT.bar : FT → Nat
  | .leaf n => n
  | .one (.one (.one t)) => t.bar + 3
  | .one (.one (.node f)) => (f 5).bar
  | .one (.one (.leaf n)) => n
  | .one (.node f) => (f 1).bar * 2
  | .one (.leaf n) => n + 1
  | .node f => (f 0).bar + (f 2).bar

def ft2 : FT :=
  .node fun n => .one (.node fun m => .one (.one (.one (.one (.one (.node fun p =>
    .leaf (n + m + p)))))))
def ft2_term : Term sigAdd [] (tyWfOf FT) := #leanscript_to_term ft2
def bar_term : Term sigAdd [] (tyWfOf FT ⇒ natT) := #leanscript_to_term FT.bar

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? bar_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bar_term (runAdd ft2_term) = 40 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd bar_term (runAdd ft2_term) = ft2.bar := by kernel_rfl

/-! ## A delayed field, read at depth `1` -/

/-- A stream whose tail is computed on demand, with a node that skips. -/
inductive TS where
  | nil
  | cons (v : Nat) (rest : Thunk TS)
  | two (t : TS)
  deriving LeanScriptTyWf

/-- Depth `1`: it looks one level into a `two`, and reads the delayed answer at the top
    level (where the window is one level deep). -/
def TS.f : TS → Nat
  | .nil => 0
  | .cons v ⟨g⟩ => v + (g ()).f
  | .two (.two t) => t.f + 10
  | .two t => t.f + 1

set_option leanscript.toTerm.normalize false in
/-- The translated term of `TS.f` before normalization binds `Term.thunkTreeAnswer` at the
    delayed field of the top level. -/
def tsF_term_raw : Term sigAdd [] (tyWfOf TS ⇒ natT) := #leanscript_to_term TS.f

open Lean Elab Command in
run_cmd do
  let some ci := (← getEnv).find? ``tsF_term_raw | throwError "no `tsF_term_raw`"
  unless (ci.value!.find? (·.isConstOf ``Term.thunkTreeAnswer)).isSome do
    throwError "the term of `TS.f` does not bind `Term.thunkTreeAnswer`"

def ts1 : TS :=
  .cons 1 (Thunk.mk fun _ => .two (.two (.cons 2 (Thunk.mk fun _ => .two .nil))))
def ts1_term : Term sigAdd [] (tyWfOf TS) := #leanscript_to_term ts1
def tsF_term : Term sigAdd [] (tyWfOf TS ⇒ natT) := #leanscript_to_term TS.f

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? tsF_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tsF_term (runAdd ts1_term) = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tsF_term (runAdd ts1_term) = ts1.f := by kernel_rfl

/-! ## A function inside an `Option`, in a record -/

/-- A record whose optional branching is a function. -/
inductive Cell where
  | mk (v : Nat) (next : Option Cell) (br : Option (Bool → Cell))
  deriving LeanScriptTyWf

/-- Depth `1`: it reads the label of the next cell, and the answers at the branches. -/
def Cell.s : Cell → Nat
  | .mk v none none => v
  | .mk v (some (.mk w _ _)) none => v + w
  | .mk v (some c) (some g) => v + c.s + (g true).s
  | .mk v none (some g) => v + (g false).s

def cell1 : Cell :=
  .mk 1 (some (.mk 2 none none)) (some fun b =>
    if b then .mk 3 (some (.mk 4 (some (.mk 5 none none)) none)) none
    else .mk 6 none none)
def cell1_term : Term sigAdd [] (tyWfOf Cell) := #leanscript_to_term cell1
def cellS_term : Term sigAdd [] (tyWfOf Cell ⇒ natT) := #leanscript_to_term Cell.s

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? cellS_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cellS_term (runAdd cell1_term) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd cellS_term (runAdd cell1_term) = cell1.s := by kernel_rfl

/-! ## A function and a delay side by side, read at depth `2` -/

/-- A node with both a delayed child and a function of children. -/
inductive T3 where
  | leaf (n : Nat)
  | one (t : T3)
  | node (t : Thunk T3) (f : Bool → T3)
  deriving LeanScriptTyWf

def T3.g : T3 → Nat
  | .leaf n => n
  | .one (.one (.node ⟨t⟩ f)) => (t ()).g + (f true).g
  | .one (.one t) => t.g + 1
  | .one (.leaf n) => n
  | .one (.node ⟨t⟩ f) => (t ()).g * (f false).g
  | .node ⟨t⟩ f => (t ()).g + (f true).g + (f false).g

def t31 : T3 :=
  .node ⟨fun _ => .one (.node ⟨fun _ => .leaf 3⟩ fun b => .leaf (if b then 4 else 5))⟩
    fun b => .one (.one (if b then .leaf 1 else
      .one (.one (.node ⟨fun _ => .leaf 7⟩ fun _ => .leaf 8))))
def t31_term : Term sigAdd [] (tyWfOf T3) := #leanscript_to_term t31
def t3g_term : Term sigAdd [] (tyWfOf T3 ⇒ natT) := #leanscript_to_term T3.g

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? t3g_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd t3g_term (runAdd t31_term) = 33 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd t3g_term (runAdd t31_term) = t31.g := by kernel_rfl

/-! ## Arrays of functions and of delays

The window of an array field holds the array of the elements' windows; an element that is
a function (or a delay) is read, when the helper on `List (Nat → AF)` is folded over it,
as a function (or delayed) field is. -/

/-- A node holding an array of functions of children. -/
inductive AF where
  | leaf (n : Nat)
  | one (t : AF)
  | node (fs : Array (Nat → AF))
  deriving LeanScriptTyWf

mutual
/-- Depth `2`. -/
def AF.s : AF → Nat
  | .leaf n => n
  | .one (.one (.one t)) => t.s + 3
  | .one t => t.s + 1
  | .node fs => AF.sA fs
def AF.sA : Array (Nat → AF) → Nat
  | ⟨l⟩ => AF.sL l
def AF.sL : List (Nat → AF) → Nat
  | [] => 0
  | f :: fs => (f 0).s + AF.sL fs
end

def af1 : AF :=
  .one (.node #[fun n => .one (.one (.one (.leaf (n + 1)))),
    fun _ => .node #[fun n => .one (.leaf (n + 5))]])
def af1_term : Term sigAdd [] (tyWfOf AF) := #leanscript_to_term af1
def afS_term : Term sigAdd [] (tyWfOf AF ⇒ natT) := #leanscript_to_term AF.s

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? afS_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd afS_term (runAdd af1_term) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd afS_term (runAdd af1_term) = af1.s := by kernel_rfl

/-- A node holding an array of delayed children. -/
inductive AT where
  | leaf (n : Nat)
  | one (t : AT)
  | node (ts : Array (Thunk AT))
  deriving LeanScriptTyWf

mutual
/-- Depth `2`. -/
def AT.s : AT → Nat
  | .leaf n => n
  | .one (.one (.one t)) => t.s + 3
  | .one t => t.s + 1
  | .node ts => AT.sA ts
def AT.sA : Array (Thunk AT) → Nat
  | ⟨l⟩ => AT.sL l
def AT.sL : List (Thunk AT) → Nat
  | [] => 0
  | ⟨f⟩ :: fs => (f ()).s + AT.sL fs
end

def at1 : AT :=
  .one (.node #[⟨fun _ => .one (.one (.one (.leaf 1)))⟩,
    ⟨fun _ => .node #[⟨fun _ => .one (.leaf 5)⟩]⟩])
def at1_term : Term sigAdd [] (tyWfOf AT) := #leanscript_to_term at1
def atS_term : Term sigAdd [] (tyWfOf AT ⇒ natT) := #leanscript_to_term AT.s

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? atS_term = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd atS_term (runAdd at1_term) = 11 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd atS_term (runAdd at1_term) = at1.s := by kernel_rfl

end TermTests.StructRec.NestedFnDeep
