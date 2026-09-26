module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public import LeanScript.CtorFn
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Datatypes with existentials that are **not structures**

```lean
inductive Src where
  | const (n : Nat)
  | gen (S : Type) (seed : S) (out : S → Nat)
  | pair (S T : Type) (a : S) (b : T) (f : S → T → Nat)
```

has several constructors, two of which hide types.  Like the structure `Unfold`
(`TermTests/StructRecTest/Existential.lean`) it has no tree of the language, and it is
translated anyway (`LeanScript.ToTerm.ExistentialArgs`):

* **a value** of it is built by the constructor function of its constructor, whose type is
  that constructor's layout at the types the value chose;
* **a call on a value written out** (`(Src.gen Nat 4 f).value`) is specialized to that value,
  and the `match` of the function on it reduces to the branch of its constructor;
* **a function of it** (`Src.value`) translates to a term **for every choice of the hidden
  types** of every constructor: a Lean function
  `fun (S S' T : TyWf) => (… : Term Sg Γ (TyWf.oneOf nat (gen layout S) [pair layout S' T] ⇒ …))`.
  Its argument is *one of* the layouts of the constructors, in the order of the
  constructors, and the function dispatches on which (`taggedUnion_casesOn`).  A constructor
  that carries no value (`Opt.empty`) is an alternative without a field.

The same holds for a datatype indexed by types whose constructors hide a type (a GADT,
`Tag : Type → Type` with `wrap {α} (x : α) (size : α → Nat) : Tag (List α)`): the function is
generic in the index, `{β} → Tag β → …`, and each branch is read at its constructor's index.

A *recursive* datatype with existentials (`Proc`, whose hidden types may differ from node to
node) still has values only.

A value is given to such a function by injecting it into the alternative of its constructor
(`inj` below).  Each case is checked by running the term, against fixed numbers and against the
Lean definition. -/

namespace TermTests.StructRec.ExistentialUnion

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-- A Boolean of the language. -/
abbrev boolT : TyWf := .prim .bool

/-- The value `v`, as the alternative `i` of `TyWf.oneOf a b cs`. -/
abbrev inj {Sg : Sig} {Γ : Ctx} {a b : TyWf} {cs : List TyWf} (i : Nat) {σ : TyWf}
    (v : Term Sg Γ σ)
    (h : i < (LeanTaggedUnionSchema.payloadFirst ⟨a, []⟩ [b] (cs.map fun c => [c])).length :=
      by decide)
    (hσ : (LeanTaggedUnionSchema.payloadFirst ⟨a, []⟩ [b] (cs.map fun c => [c])).get i h = [σ] :=
      by rfl) :
    Term Sg Γ (TyWf.oneOf a b cs) :=
  Term.taggedUnion_mk _ i h (hσ ▸ .cons v .nil)

noncomputable section

/-! ## `Src`: three constructors, two of them hiding types -/

/-- A source of a number: a constant, a generator with a hidden state, or a pair of hidden
    values and a function of both. -/
inductive Src where
  /-- A constant. -/
  | const (n : Nat)
  /-- A seed of a hidden type, and what it gives. -/
  | gen (S : Type) (seed : S) (out : S → Nat)
  /-- Two values of hidden types, and what they give. -/
  | pair (S T : Type) (a : S) (b : T) (f : S → T → Nat)

/--
error: the type `TermTests.StructRec.ExistentialUnion.Src` has no `Ty`: existential typing is not yet supported, `S` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Src

/-- The number a source gives. -/
def Src.value : Src → Nat
  | .const n => n
  | .gen _ s f => f s
  | .pair _ _ a b f => f a b

/-- `Src.value`, for every choice of the hidden types of `gen` and of `pair`. -/
def value_term := #leanscript_to_term (sig := sigAdd) Src.value

-- one hidden type for `gen`, two for `pair`
example (S S' T : TyWf) : Term sigAdd []
    (TyWf.oneOf natT (Src.gen.leanScriptLayout S) [Src.pair.leanScriptLayout S' T] ⇒ natT) :=
  value_term S S' T

/-! ### Values: the constructor function, at the types each value chose -/

/-- A generator whose state is a number. -/
def srcGen : Src := .gen Nat 4 (· * 3)
def srcGen_term := #leanscript_to_term (sig := sigAdd) srcGen

/-- A pair of a number and a Boolean. -/
def srcPair : Src := .pair Nat Bool 7 true (fun n b => if b then n + 1 else n)
def srcPair_term := #leanscript_to_term (sig := sigAdd) srcPair

/-- A constant, whose layout is its one field. -/
def srcConst : Src := .const 9
def srcConst_term : Term sigAdd [] natT := #leanscript_to_term srcConst

/-! ### Generic in the hidden types -/

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((value_term natT natT boolT).ap (inj 1 srcGen_term)) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((value_term natT natT boolT).ap (inj 1 srcGen_term)) = srcGen.value := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((value_term natT natT boolT).ap (inj 2 srcPair_term)) = 8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((value_term natT natT boolT).ap (inj 2 srcPair_term)) = srcPair.value := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((value_term natT natT boolT).ap (inj 0 srcConst_term)) = 9 := by kernel_rfl

/-- A source that is not the first argument, used under a recursion on a list. -/
def Src.valueTimes (k : Nat) (s : Src) : List Nat → Nat
  | [] => k * s.value
  | x :: xs => x + Src.valueTimes k s xs

def valueTimes_term := #leanscript_to_term (sig := sigAdd) Src.valueTimes

/-- `[7, 8]`. -/
@[inline] def l78L : List Nat := [7, 8]

/-- `[7, 8]`, as a value of the language. -/
def l78 : TyWf.Den (tyWfOf (List Nat)) :=
  runAdd (#leanscript_to_term l78L : Term sigAdd [] (tyWfOf (List Nat)))

-- `7 + 8 + 2 * 12`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((valueTimes_term natT natT boolT)) 2 (runAdd (inj 1 srcGen_term)) l78 = 39 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((valueTimes_term natT natT boolT)) 2 (runAdd (inj 1 srcGen_term)) l78 =
-- [SKIPPED BY PROFILE_LAKE]     Src.valueTimes 2 srcGen [7, 8] := by kernel_rfl

/-- Only one constructor is named: the others fall to the wildcard. -/
def Src.fromGen : Src → Nat
  | .gen _ s f => f s
  | _ => 0

def fromGen_term := #leanscript_to_term (sig := sigAdd) Src.fromGen

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((fromGen_term natT natT boolT).ap (inj 1 srcGen_term)) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((fromGen_term natT natT boolT).ap (inj 2 srcPair_term)) = 0 := by kernel_rfl

/-! ### Specialized to a value written out -/

/-- `Src.value` on a value built from the argument: the `match` of `Src.value` reduces to the
    branch of `gen`. -/
def valueOfPairSrc (n : Nat) : Nat :=
  (Src.gen (Nat × Nat) (n, n) (fun p => p.1 + p.2)).value

def valueOfPairSrc_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term valueOfPairSrc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd valueOfPairSrc_term 5 = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd valueOfPairSrc_term 6 = valueOfPairSrc 6 := by kernel_rfl

/-! ## `Opt`: a constructor that carries no value -/

/-- A generator, or nothing. -/
inductive Opt where
  /-- A seed of a hidden type, and what it gives. -/
  | gen (S : Type) (seed : S) (out : S → Nat)
  /-- Nothing. -/
  | empty

/-- The number, or `0`. -/
def Opt.value : Opt → Nat
  | .gen _ s f => f s
  | .empty => 0

/-- The argument is the tagged union of the layout of `gen` and of no field. -/
def optValue_term := #leanscript_to_term (sig := sigAdd) Opt.value

/-- `Opt.gen Nat 5 (· + 1)`. -/
def optGen : Opt := .gen Nat 5 (· + 1)
def optGen_term := #leanscript_to_term (sig := sigAdd) optGen

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((optValue_term natT).ap
-- [SKIPPED BY PROFILE_LAKE]     (Term.taggedUnion_mk _ 0 (by decide) (.cons optGen_term .nil))) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((optValue_term natT).ap (Term.taggedUnion_mk _ 1 (by decide) .nil)) = 0 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `Tag`: a GADT whose constructor hides the type its index is built from -/

/-- A number at index `Nat`, or a value of a hidden type at index `List α`. -/
inductive Tag : Type → Type 1 where
  /-- A number. -/
  | num (n : Nat) : Tag Nat
  /-- A value of the hidden type `α`, and its size. -/
  | wrap {α : Type} (x : α) (size : α → Nat) : Tag (List α)

/-- The size of the payload, plus one for a wrapped value. -/
def Tag.size : {β : Type} → Tag β → Nat
  | _, .num n => n
  | _, .wrap x f => f x + 1

/-- `Tag.size`, generic in the index and for every choice of `α`. -/
def tagSize_term := #leanscript_to_term (sig := sigAdd) @Tag.size

/-- A wrapped number. -/
def tagW : Tag (List Nat) := .wrap 5 (· + 10)
def tagW_term := #leanscript_to_term (sig := sigAdd) tagW

/-- A number. -/
def tagN : Tag Nat := .num 3
def tagN_term := #leanscript_to_term (sig := sigAdd) tagN

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((tagSize_term natT).ap (inj 1 tagW_term)) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((tagSize_term natT).ap (inj 1 tagW_term)) = tagW.size := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((tagSize_term natT).ap (inj 0 tagN_term)) = tagN.size := by kernel_rfl

/-- One constructor and an index: the argument is its layout itself. -/
inductive Box : Type → Type 1 where
  /-- A value of the hidden type `α`, and what it gives. -/
  | mk {α : Type} (x : α) (f : α → Nat) : Box (Option α)

/-- What the box gives. -/
def Box.get : {β : Type} → Box β → Nat
  | _, .mk x f => f x

def boxGet_term := #leanscript_to_term (sig := sigAdd) @Box.get

/-- A box holding a number. -/
def box1 : Box (Option Nat) := .mk 4 (· * 5)
def box1_term := #leanscript_to_term (sig := sigAdd) box1

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((boxGet_term natT).ap box1_term) = 20 := by kernel_rfl

/-! ## What stays refused: a recursive datatype with existentials -/

/-- A process: stop, or a step whose state has a hidden type, from which the rest follows. -/
inductive Proc where
  /-- Stop. -/
  | stop
  /-- A step. -/
  | step (S : Type) (s : S) (next : S → Proc)

/-- Does it stop at once? -/
def Proc.stops : Proc → Bool
  | .stop => true
  | .step _ _ _ => false

/--
error: `#leanscript_to_term`: the type Proc has no tree of the language: existential typing is not supported, `S` is an existential
-/
#guard_msgs in
def stops_term := #leanscript_to_term (sig := sigAdd) Proc.stops

end

end TermTests.StructRec.ExistentialUnion

end
