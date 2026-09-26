module

public import TermTests.CtorFnTest.Module
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# `#leanscript_ctor`: constructor functions for every datatype

`#leanscript_ctor I c` is the constructor function of `I.c` and `#leanscript_layout I c` the
tree of what it builds (`LeanScript.CtorFn`).  This file checks them on datatypes of every
kind — the existentially typed `Process` has its own suite in
`TermTests.InductiveTypesTest.Existentials` — together with the cache and the refusals.
-/

open LeanScript

namespace CtorFnTest

abbrev natT : TyWf := .prim .nat
abbrev boolT : TyWf := .prim .bool
abbrev stringT : TyWf := .prim .string

/-- A signature with nothing in it. -/
abbrev sig : Sig := ⟨[], List.nodup_nil⟩

/-- Running a closed term of `sig`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig) PUnit.unit $t)

/-! ## The cache

`TermTests.CtorFnTest.Module` generated `Option.some` (and so `Option`'s layout); here it is
reused, not generated again: the constant is the one of that module. -/

def some4 : Term sig [] (#leanscript_layout `Option `some natT) :=
  #leanscript_ctor `Option `some natT (.nat_mk 4)

/--
info: @[expose] def CtorFnTest.some4 : Term sig [] (TermTests.CtorFnTest.Module.Option.leanScriptLayout natT) :=
TermTests.CtorFnTest.Module.Option.some.leanScriptCtor natT (Term.nat_mk 4)
-/
#guard_msgs in #print some4

-- [SKIPPED BY PROFILE_LAKE] /-- The layout of `Option` is the tree of `Option`'s own instance. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_layout `Option `some natT) = tyWfOf (Option Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run some4 = ⟨⟨1, by decide⟩, (4, ())⟩ := by kernel_rfl

/-! ## Library datatypes -/

def none' : Term sig [] (#leanscript_layout `Option `none natT) := #leanscript_ctor `Option `none natT
-- [SKIPPED BY PROFILE_LAKE] example : run none' = ⟨⟨0, by decide⟩, ()⟩ := by kernel_rfl

/-- A type with one constructor can be named alone. -/
def pair : Term sig [] (#leanscript_layout `Prod natT boolT) :=
  #leanscript_ctor `Prod natT boolT (.nat_mk 3) (.bool_mk true)
-- [SKIPPED BY PROFILE_LAKE] example : run pair = (3, true, ()) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_layout `Prod natT boolT) = tyWfOf (Nat × Bool) := by kernel_rfl

def inr : Term sig [] (#leanscript_layout `Sum `inr natT stringT) :=
  #leanscript_ctor `Sum `inr natT stringT (.string_mk "x")
-- [SKIPPED BY PROFILE_LAKE] example : run inr = ⟨⟨1, by decide⟩, ("x", ())⟩ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_layout `Sum `inr natT stringT) = tyWfOf (Nat ⊕ String) := by kernel_rfl

/-- `Bool` is the enum of its two constructors, which the language calls `bool`. -/
def tt : Term sig [] boolT := #leanscript_ctor `Bool `true
-- [SKIPPED BY PROFILE_LAKE] example : run tt = true := by kernel_rfl

/-- `Ordering`'s instance numbers its constructors from `-1`; the layout keeps that. -/
def gt : Term sig [] (tyWfOf Ordering) := #leanscript_ctor `Ordering `gt
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_layout `Ordering `gt) = tyWfOf Ordering := by kernel_rfl

/-- A recursive datatype is built one layer at a time: `List.cons` takes the tree of its
    tail, whatever it is. -/
def oneTwo : Term sig [] (#leanscript_layout `List `cons natT
    (#leanscript_layout `List `cons natT (#leanscript_layout `List `nil natT natT))) :=
  #leanscript_ctor `List `cons natT _ (.nat_mk 1)
    (#leanscript_ctor `List `cons natT _ (.nat_mk 2) (#leanscript_ctor `List `nil natT natT))
-- [SKIPPED BY PROFILE_LAKE] example : run oneTwo =
-- [SKIPPED BY PROFILE_LAKE]     ⟨⟨1, by decide⟩, (1, ⟨⟨1, by decide⟩, (2, ⟨⟨0, by decide⟩, ()⟩, ())⟩, ())⟩ := by kernel_rfl

/-! ## Datatypes of this file -/

/-- An enum. -/
inductive Shape3 | a | b | c
def shapeB : Term sig [] (#leanscript_layout `Shape3 `b) := #leanscript_ctor `Shape3 `b
-- [SKIPPED BY PROFILE_LAKE] example : run shapeB = ⟨1, by decide⟩ := by kernel_rfl

/-- A structure: erased fields are not arguments, and a structure with one field left is
    that field. -/
structure Wrap where
  val : Nat
  u : Unit
  p : val = val
def wrap : Term sig [] natT := #leanscript_ctor `Wrap (.nat_mk 5)
-- [SKIPPED BY PROFILE_LAKE] example : run wrap = 5 := by kernel_rfl

/-- Field types built from the type argument: `Option S` and `S × Nat` are rebuilt from their
    instances' trees, `List S` is `tyWfOf (List S.AsType)` (its tree is recursive), and a
    `Unit →` binder is dropped. -/
structure Fancy (S : Type) where
  o : Option S
  l : List S
  f : Unit → S → Array S
  n : Nat × S

/--
info: CtorFnTest.Fancy.mk.leanScriptCtor {Sg : Sig} {Γ : Ctx} (S : TyWf)
  (o : Term Sg Γ (TyWf.taggedUnion (LeanTaggedUnionSchema.skip (CtorsWithPayload.here { head := S, tail := [] } []))))
  (l : Term Sg Γ (tyWfOf (List S.AsType))) (f : Term Sg Γ (S ⇒ S.array))
  (n : Term Sg Γ (TyWf.record { fst := TyWf.prim LeanPrimTy.nat, snd := S, rest := [] })) :
  Term Sg Γ (Fancy.leanScriptLayout S)
-/
#guard_msgs in #leanscript_ctor `Fancy `mk

-- [SKIPPED BY PROFILE_LAKE] /-- `tyWfOf (List S.AsType)` is `List`'s own tree, at `S`. -/
-- [SKIPPED BY PROFILE_LAKE] example (S : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     tyWfOf (List S.AsType) = ⟨.recTaggedUnion (.skip (.here ⟨S.toTy, [.self]⟩ [])), by ty_wf⟩ := by kernel_rfl

/-- An indexed family: a value index (`n : Nat`) is an ordinary field, and the recursive
    occurrence is a type argument. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
/--
info: CtorFnTest.Vec.cons.leanScriptCtor {Sg : Sig} {Γ : Ctx} (α vTy : TyWf) (n : Term Sg Γ (TyWf.prim LeanPrimTy.nat))
  (a : Term Sg Γ α) (v : Term Sg Γ vTy) : Term Sg Γ (Vec.leanScriptLayout α vTy)
-/
#guard_msgs in #leanscript_ctor `Vec `cons

/-- A field whose type depends on a value gets its tree from an argument. -/
structure Dep where
  n : Nat
  f : Fin n
/--
info: CtorFnTest.Dep.mk.leanScriptCtor {Sg : Sig} {Γ : Ctx} (fTy : TyWf) (n : Term Sg Γ (TyWf.prim LeanPrimTy.nat))
  (f : Term Sg Γ fTy) : Term Sg Γ (Dep.leanScriptLayout fTy)
-/
#guard_msgs in #leanscript_ctor `Dep `mk

-- Two existentially typed members of a `mutual` block: each constructor has its own
-- layout, and the occurrence of the other member is a type argument.
mutual
  inductive Client (Req Resp : Type) : Type 1 where
    | stop (ServerState : Type) (get : ServerState → Nat) : Client Req Resp
    | mk (ClientState : Type) (seed : ClientState)
        (send : ClientState → Req × Server Req Resp) : Client Req Resp
  inductive Server (Req Resp : Type) : Type 1 where
    | stop (ClientState : Type) (get : ClientState → Nat) : Server Req Resp
    | mk (ServerState : Type) (seed : ServerState)
        (receive : ServerState → Req → Resp × Client Req Resp) : Server Req Resp
end
/--
info: CtorFnTest.Client.mk.leanScriptCtor {Sg : Sig} {Γ : Ctx} (Req Resp ClientState sendTy : TyWf)
  (seed : Term Sg Γ ClientState)
  (send : Term Sg Γ (ClientState ⇒ TyWf.record { fst := Req, snd := sendTy, rest := [] })) :
  Term Sg Γ (Client.mk.leanScriptLayout Req Resp ClientState sendTy)
-/
#guard_msgs in #leanscript_ctor `Client `mk

/-! ## Refusals -/

/-- error: `#leanscript_ctor`: the only constructor of `PUnit` carries no value — a unit-like type has no constructor function -/
#guard_msgs in #check #leanscript_ctor `Unit `unit

/-- error: `#leanscript_ctor`: `Nat` is modelled by a terminal type of the language, whose values are literals; it has no constructor function -/
#guard_msgs in #check #leanscript_ctor `Nat `succ

/-- error: `#leanscript_ctor`: `Array` is modelled by a built-in type former of the language, which has an introduction form of its own -/
#guard_msgs in #check #leanscript_ctor `Array `mk

/-- error: `#leanscript_ctor`: `True` is a proposition, which carries no value -/
#guard_msgs in #check #leanscript_ctor `True `intro

structure Keyed where
  State : Type
  Elem  : State → Type
  seed  : State
  get   : (s : State) → Elem s

/-- error: `#leanscript_ctor`: the type `CtorFnTest.Keyed` hides a family of types in the field `Elem` of `CtorFnTest.Keyed.mk`, which the language has no shape for -/
#guard_msgs in #check #leanscript_ctor `Keyed

/-- error: `#leanscript_ctor`: `Option` has no constructor `cons` -/
#guard_msgs in #check #leanscript_ctor `Option `cons

/-- error: `#leanscript_ctor`: `Option` has 2 constructors; name the one you mean -/
#guard_msgs in #check #leanscript_ctor `Option

-- The cache: what this file and `TermTests.CtorFnTest.Module` generated, which a module
-- importing this one reuses.
/--
info: layout of CtorFnModuleTest.Color: CtorFnModuleTest.Color.leanScriptLayout
fn of CtorFnModuleTest.Color.green: CtorFnModuleTest.Color.green.leanScriptCtor
layout of CtorFnModuleTest.Pt: CtorFnModuleTest.Pt.leanScriptLayout
fn of CtorFnModuleTest.Pt.mk: CtorFnModuleTest.Pt.mk.leanScriptCtor
layout of Option: TermTests.CtorFnTest.Module.Option.leanScriptLayout
fn of Option.some: TermTests.CtorFnTest.Module.Option.some.leanScriptCtor
fn of Option.none: TermTests.CtorFnTest.Option.none.leanScriptCtor
layout of Prod: TermTests.CtorFnTest.Prod.leanScriptLayout
fn of Prod.mk: TermTests.CtorFnTest.Prod.mk.leanScriptCtor
layout of Sum: TermTests.CtorFnTest.Sum.leanScriptLayout
fn of Sum.inr: TermTests.CtorFnTest.Sum.inr.leanScriptCtor
layout of Bool: TermTests.CtorFnTest.Bool.leanScriptLayout
fn of Bool.true: TermTests.CtorFnTest.Bool.true.leanScriptCtor
layout of Ordering: TermTests.CtorFnTest.Ordering.leanScriptLayout
fn of Ordering.gt: TermTests.CtorFnTest.Ordering.gt.leanScriptCtor
layout of List: TermTests.CtorFnTest.List.leanScriptLayout
fn of List.cons: TermTests.CtorFnTest.List.cons.leanScriptCtor
fn of List.nil: TermTests.CtorFnTest.List.nil.leanScriptCtor
layout of CtorFnTest.Shape3: CtorFnTest.Shape3.leanScriptLayout
fn of CtorFnTest.Shape3.b: CtorFnTest.Shape3.b.leanScriptCtor
layout of CtorFnTest.Wrap: CtorFnTest.Wrap.leanScriptLayout
fn of CtorFnTest.Wrap.mk: CtorFnTest.Wrap.mk.leanScriptCtor
layout of CtorFnTest.Fancy: CtorFnTest.Fancy.leanScriptLayout
fn of CtorFnTest.Fancy.mk: CtorFnTest.Fancy.mk.leanScriptCtor
layout of CtorFnTest.Vec: CtorFnTest.Vec.leanScriptLayout
fn of CtorFnTest.Vec.cons: CtorFnTest.Vec.cons.leanScriptCtor
layout of CtorFnTest.Dep: CtorFnTest.Dep.leanScriptLayout
fn of CtorFnTest.Dep.mk: CtorFnTest.Dep.mk.leanScriptCtor
layout of CtorFnTest.Client.mk: CtorFnTest.Client.mk.leanScriptLayout
fn of CtorFnTest.Client.mk: CtorFnTest.Client.mk.leanScriptCtor
-/
#guard_msgs in #leanscript_ctor_cache

end CtorFnTest
