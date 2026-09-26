module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# `#leanscript_to_term`, run

Every example below translates a Lean definition into a `LeanScript.Term` and, where the
term is closed, checks by `kernel_rfl` — that is, by the kernel — that the evaluator gives it
the value the Lean definition has.  The examples continue in
`TermTests.ToTermTest.Data` and `TermTests.ToTermTest.Recursion`, and
`TermTests.ToTermTest.Refused` pins what the translation **refuses**.
-/

namespace TermTests.ToTerm

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`: `Term.run` evaluates every closed term, with no side
    condition.  It is a macro so that `run t x` applies the value of `t` to `x`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Functions, applications, `let` and literals -/

def idNat (n : Nat) : Nat := n

def idNat_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term idNat

-- [SKIPPED BY PROFILE_LAKE] example : run idNat_term 7 = 7 := by kernel_rfl

def constNat (a : Nat) (_b : Nat) : Nat := a

def constNat_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term constNat

-- [SKIPPED BY PROFILE_LAKE] example : run constNat_term 3 9 = 3 := by kernel_rfl

def letExample : Nat := let x := 4; x

def letExample_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term letExample

-- [SKIPPED BY PROFILE_LAKE] example : run letExample_term = 4 := by kernel_rfl

def applied : Nat := (fun (f : Nat → Nat) => f 5) (fun n => n)

def applied_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term applied

-- [SKIPPED BY PROFILE_LAKE] example : run applied_term = 5 := by kernel_rfl

def hello : String := "hello"

def hello_term : Term sig0 [] (TyWf.prim .string) := #leanscript_to_term hello

-- [SKIPPED BY PROFILE_LAKE] example : run hello_term = "hello" := by kernel_rfl

def yes : Bool := true

def yes_term : Term sig0 [] (TyWf.prim .bool) := #leanscript_to_term yes

-- [SKIPPED BY PROFILE_LAKE] example : run yes_term = true := by kernel_rfl

def negOne : Int := -1

def negOne_term : Term sig0 [] (TyWf.prim .int) := #leanscript_to_term negOne

-- [SKIPPED BY PROFILE_LAKE] example : run negOne_term = -1 := by kernel_rfl

/-! ## A test on a `Bool` -/

def pick (b : Bool) : Nat := if b then 1 else 0

def pick_term : Term sig0 [] (TyWf.prim .bool ⇒ TyWf.prim .nat) := #leanscript_to_term pick

-- [SKIPPED BY PROFILE_LAKE] example : run pick_term true = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pick_term false = 0 := by kernel_rfl

/-! ## Calling a declaration of the signature

A top-level function that is not inlinable is called through the signature, by the name
it is declared under: the declaration `"double"` below is what `double` translates to.
A name is matched in full (`TermTests.ToTerm.double`) or by its last component
(`double`). -/

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def sigDouble : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigDouble`. -/
def envDouble : GlobalEnv sigDouble.decls := (fun n => 2 * n, PUnit.unit)

def double (n : Nat) : Nat := 2 * n

def quadruple (n : Nat) : Nat := double (double n)

def quadruple_term : Term sigDouble [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term quadruple

-- [SKIPPED BY PROFILE_LAKE] example : (Term.run envDouble quadruple_term) 3 = 12 := by kernel_rfl

/-! ## Records -/

structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

def mkPoint (a : Nat) (b : Nat) : Point := ⟨a, b⟩

def mkPoint_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ tyWfOf Point) :=
  #leanscript_to_term mkPoint

def fstOf (p : Point) : Nat := p.x

def fstOf_term : Term sig0 [] (tyWfOf Point ⇒ TyWf.prim .nat) := #leanscript_to_term fstOf

-- [SKIPPED BY PROFILE_LAKE] example : run fstOf_term (run mkPoint_term 2 5) = 2 := by kernel_rfl

/-! ## Tagged unions -/

def orZero (o : Option Nat) : Nat :=
  match o with
  | none => 0
  | some n => n

def orZero_term : Term sig0 [] (tyWfOf (Option Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term orZero

def someThree : Option Nat := some 3

def someThree_term : Term sig0 [] (tyWfOf (Option Nat)) := #leanscript_to_term someThree

-- [SKIPPED BY PROFILE_LAKE] example : run orZero_term (run someThree_term) = 3 := by kernel_rfl

/-! ## Enums -/

inductive Colour where
  | red
  | green
  | blue
  deriving LeanScriptTyWf

def colourCode (c : Colour) : Nat :=
  match c with
  | .red => 0
  | .green => 1
  | .blue => 2

def colourCode_term : Term sig0 [] (tyWfOf Colour ⇒ TyWf.prim .nat) :=
  #leanscript_to_term colourCode

def blue : Colour := .blue

def blue_term : Term sig0 [] (tyWfOf Colour) := #leanscript_to_term blue

-- [SKIPPED BY PROFILE_LAKE] example : run colourCode_term (run blue_term) = 2 := by kernel_rfl

/-! ## Arrays

`Array α` is the grammar's `TyWf.array`, whose introduction form takes every element at
once, so an array literal translates and the term runs. -/

def digits : Array Nat := #[1, 2, 3]

def digits_term : Term sig0 [] (TyWf.array (TyWf.prim .nat)) := #leanscript_to_term digits

-- [SKIPPED BY PROFILE_LAKE] example : run digits_term = #[1, 2, 3] := by kernel_rfl

/-! ## Lists

`List α` is not `TyWf.array`: it is the recursive tagged union it is, `nil | cons α self`,
which is the tree of its `LeanScriptTyWf` instance.  So `[]` and `hd :: tl` translate to
`Term.recTaggedUnion_mk`, a `match` on a list to `Term.recTaggedUnion_casesOn` and
`List.rec` to `Term.recTaggedUnion_rec`.  Unlike an array literal, a list does not have
to be written out: `prepend` below builds one from a variable tail.

A value of a list is a W-tree of its constructors (`LeanScript.Ty.Den`), so these terms
run like any other; `Ty.DenRec.toList` reads a list back as a Lean list to compare it. -/

def digitList : List Nat := [1, 2, 3]

def digitList_term : Term sig0 [] (tyWfOf (List Nat)) := #leanscript_to_term digitList

def prepend (n : Nat) (l : List Nat) : List Nat := n :: l

def prepend_term :
    Term sig0 [] (TyWf.prim .nat ⇒ tyWfOf (List Nat) ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term prepend

def firstOrZero (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | hd :: _ => hd

def firstOrZero_term : Term sig0 [] (tyWfOf (List Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term firstOrZero

-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (run digitList_term) = [1, 2, 3] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (run prepend_term 7 (run digitList_term)) =
-- [SKIPPED BY PROFILE_LAKE]     [7, 1, 2, 3] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run firstOrZero_term (run digitList_term) = 1 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run firstOrZero_term (run prepend_term 7 (run digitList_term)) = 7 := by decide +kernel

/-- A `match` that does not recur is a case analysis: this is `nat_casesOn`. -/
def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k

def pred_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term pred

-- [SKIPPED BY PROFILE_LAKE] example : run pred_term 5 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pred_term 0 = 0 := by kernel_rfl

/-! ## The two folds

A recursion is written as `Nat.rec` or `List.rec` with a non-dependent motive: those are
the grammar's `nat_rec` and `recTaggedUnion_rec`.  Addition is not an operation of the
grammar, so `Nat.add` is called through the signature, under the name `"add"`. -/

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

noncomputable def sumUpTo (n : Nat) : Nat := Nat.rec 0 (fun k ih => k + ih) n

def sumUpTo_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumUpTo

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumUpTo_term 4 = 6 := by kernel_rfl

noncomputable def sumList (l : List Nat) : Nat :=
  List.rec 0 (fun hd _tl ih => hd + ih) l

/-- The fold over a list, which is `Term.recTaggedUnion_rec`: its `cons` branch binds the
    head, the tail and the value of the fold at the tail. -/
def sumList_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumList

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumList_term (run digitList_term) = 6 := by decide +kernel

end TermTests.ToTerm

end
