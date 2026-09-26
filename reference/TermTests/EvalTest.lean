module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# The evaluator, run

Every example below writes a closed term of `LeanScript.Term` and the value
`LeanScript.Term.eval` gives it, and checks the two agree by `kernel_rfl` — that is, by the
kernel.  The terms mirror those of `TermTests.TermTest`, which pins that the *grammar* is
usable; this file pins what each of them *computes*.

Nothing here supplies fuel or handles a failure: `Term.eval` is a total function, so a
term of type `τ` simply **has** a value of `LeanScript.Ty.Den τ`.
-/

namespace TermTests.Eval

open LeanScript

/-- The empty signature: a module that refers to no top-level declaration. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `doubleSig`: the one function `double`. -/
def doubleEnv : GlobalEnv doubleSig.decls := (fun n => 2 * n, PUnit.unit)

/-- Running a closed term of `emptySig`: `Term.run` evaluates every closed term, with no
    side condition.  It is a macro so that `run t x` applies the value of `t` to `x`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := emptySig) GlobalEnv.nil $t)

/-! ## Variables, functions, applications and `let` -/

/-- `fun x => x`, at `nat ⇒ nat`. -/
def idNat : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := .lam (.var (v♯0))

/-- `fun x => fun y => x`. -/
def constNat : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .bool ⇒ TyWf.prim .nat) :=
  .lam (.lam (.var (v♯1)))

/-- `let x = 3; x`. -/
def letThree : Term emptySig [] (TyWf.prim .nat) := .letE' (.nat_mk 3) (.var (v♯0))

/-- A call of the one declaration of `doubleSig`. -/
def callDouble : Term doubleSig [] (TyWf.prim .nat) := .ap (.global .here) (.nat_mk 21)

-- [SKIPPED BY PROFILE_LAKE] example : run idNat 7 = 7 := by kernel_rfl
-- `Term.run'` is the same thing for a module that declares nothing.
-- [SKIPPED BY PROFILE_LAKE] example : (Term.run' idNat) 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap idNat (.nat_mk 3)) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run constNat 7 true = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run letThree = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv callDouble = 42 := by kernel_rfl

/-! ## Literals -/

-- [SKIPPED BY PROFILE_LAKE] example : run (.bitvec_mk (v := 7#8)) = 7#8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.string_mk "hello") = "hello" := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.char_mk 'a') = 'a' := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.int_mk (-2)) = -2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.uint8_mk 255) = 255 := by kernel_rfl

/-! ## Eliminators of the terminal types -/

/-- `fun b => if b then 1 else 0`. -/
def boolToNat : Term emptySig [] (TyWf.prim .bool ⇒ TyWf.prim .nat) :=
  .lam (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))

/-- The predecessor, by case analysis on a natural number. -/
def pred : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_casesOn' (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- A fold over a natural number whose successor branch answers with the value of the
    fold at the predecessor — so it is `0` however big the number is. -/
def foldNatZero : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_rec' 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil) (.var (v♯1)))

/-- A fold over a natural number whose successor branch answers with the predecessor —
    so it is the predecessor. -/
def foldNatPred : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_rec' 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil) (.var (v♯0)))

/-- `fun i => match i with | .ofNat n => n | .negSucc n => n`. -/
def intMagnitude : Term emptySig [] (TyWf.prim .int ⇒ TyWf.prim .nat) :=
  .lam (.int_casesOn' (.var (v♯0)) (.var (v♯0)) (.var (v♯0)))

/-- The code point of a character. -/
def charCode : Term emptySig [] (TyWf.prim .char ⇒ TyWf.prim .uint32) :=
  .lam (.char_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- The byte index of an unchecked position. -/
def rawByteIdx : Term emptySig [] (TyWf.prim .stringPosRaw ⇒ TyWf.prim .nat) :=
  .lam (.stringPosRaw_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- The string an unchecked substring is into. -/
def substringStr : Term emptySig [] (TyWf.prim .substringRaw ⇒ TyWf.prim .string) :=
  .lam (.substringRaw_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- The bit vector inside an 8-bit unsigned value. -/
def uint8Bits : Term emptySig [] (TyWf.prim .uint8 ⇒ TyWf.prim (.bitvec 8)) :=
  .lam (.uint8_casesOn' (.var (v♯0)) (.var (v♯0)))

-- [SKIPPED BY PROFILE_LAKE] example : run boolToNat true = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run boolToNat false = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pred 0 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pred 5 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run foldNatZero 5 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run foldNatPred 5 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run intMagnitude 7 = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run intMagnitude (-8) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run charCode 'a' = 97 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run rawByteIdx ⟨12⟩ = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run substringStr ⟨"abc", ⟨0⟩, ⟨3⟩⟩ = "abc" := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run uint8Bits 5 = 5#8 := by kernel_rfl

/-! ## Delays, and arrays -/

-- [SKIPPED BY PROFILE_LAKE] example : run (.thunk_force (.thunk_mk (.nat_mk 3))) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.lazy_force (.lazy_mk (.nat_mk 3))) = 3 := by kernel_rfl

/-- The array `#[1, 2, 3]`. -/
def oneTwoThree : Term emptySig [] (TyWf.array (TyWf.prim .nat)) :=
  .array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil)))

/-- The first element of an array of naturals, or `0`. -/
def headOrZero : Term emptySig [] (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) :=
  .lam (.array_casesOn' (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- A fold over an array that answers with the value of the fold over the tail — so it
    is `0` however long the array is. -/
def foldArrayZero : Term emptySig [] (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) :=
  .lam (.array_rec' 0 (.var (v♯0)) (.nil (.nat_mk 0)) (.var (v♯2)))

/-- A fold over an array that answers with its **last** element, or `0`: the branch
    takes the head when the fold over the tail is the answer for the empty tail. -/
def lastOrZero : Term emptySig [] (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) :=
  .lam (.array_rec' 0 (.var (v♯0)) (.nil (.nat_mk 0))
    (.array_casesOn' (.var (v♯1)) (.var (v♯0)) (.var (v♯4))))

-- [SKIPPED BY PROFILE_LAKE] example : run oneTwoThree = #[1, 2, 3] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run headOrZero #[1, 2, 3] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run headOrZero #[] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run foldArrayZero #[1, 2, 3] = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run lastOrZero #[1, 2, 3] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run lastOrZero #[] = 0 := by kernel_rfl

/-! ## Enums -/

/-- An enum of exactly three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- An enum of five constructors. -/
def five : LeanEnumSchema := ⟨2, 0⟩

/-- The middle constructor of `three`. -/
def middle : Term emptySig [] (TyWf.enum three) := .enum_mk three ⟨1, by decide⟩

/-- A dispatch on `three`: one branch per constructor, and no default. -/
def enumToNat : Term emptySig [] (TyWf.enum three ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOn' (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2)))

/-- A dispatch on `five`. -/
def fiveToNat : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOn' (.var (v♯0))
    (.cons (.nat_mk 0) (.cons (.nat_mk 1)
      (.three (.nat_mk 2) (.nat_mk 3) (.nat_mk 4)))))

/-- A dispatch on `three` that names only its last constructor. -/
def enumLastOrZero : Term emptySig [] (TyWf.enum three ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0)) (.last ⟨2, by decide⟩ (.nat_mk 2))
    (.nat_mk 0))

/-- Two of the five constructors, named smallest first. -/
def fiveTwoOrZero : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0))
    (.cons 1 (.nat_mk 1) (.last 3 (.nat_mk 3))) (.nat_mk 0))

-- [SKIPPED BY PROFILE_LAKE] example : run middle = ⟨1, by decide⟩ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run enumToNat ⟨0, by decide⟩ = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run enumToNat ⟨1, by decide⟩ = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run enumToNat ⟨2, by decide⟩ = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveToNat ⟨0, by decide⟩ = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveToNat ⟨3, by decide⟩ = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveToNat ⟨4, by decide⟩ = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run enumLastOrZero ⟨2, by decide⟩ = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run enumLastOrZero ⟨0, by decide⟩ = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveTwoOrZero ⟨1, by decide⟩ = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveTwoOrZero ⟨3, by decide⟩ = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run fiveTwoOrZero ⟨4, by decide⟩ = 0 := by kernel_rfl

/-! ## Records -/

/-- A record of a `nat` and a `bool`. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .bool, []⟩

/-- The record `(3, true)`. -/
def pair : Term emptySig [] (TyWf.record pairSchema) :=
  .record_mk pairSchema (.cons (.nat_mk 3) (.cons (.bool_mk true) .nil))

/-- Its first field. -/
def pairFst : Term emptySig [] (TyWf.prim .nat) := .record_casesOn' pair (.var (v♯0))

/-- Its second field. -/
def pairSnd : Term emptySig [] (TyWf.prim .bool) := .record_casesOn' pair (.var (v♯1))

-- [SKIPPED BY PROFILE_LAKE] example : run pair = (3, true, PUnit.unit) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pairFst = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run pairSnd = true := by kernel_rfl

/-! ## Tagged unions

A value of a union is its constructor's number together with exactly that constructor's
fields. -/

/-- A union of a constructor with one `nat` field and a field-less one. -/
def optNat : LeanTaggedUnionSchema TyWf := .payloadFirst ⟨TyWf.prim .nat, []⟩ [] []

/-- Its first constructor, applied to `3`. -/
def someThree : Term emptySig [] (TyWf.taggedUnion optNat) :=
  .taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil)

/-- Its second, field-less constructor. -/
def noneNat : Term emptySig [] (TyWf.taggedUnion optNat) :=
  .taggedUnion_mk optNat 1 (fields := .nil)

/-- A dispatch on it, with one branch per constructor. -/
def optNatOrZero : Term emptySig [] (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOn' (.var (v♯0)) (.payloadFirst (.var (v♯0)) (.nat_mk 0) .nil))

/-- A dispatch on only its first constructor, with a default. -/
def optNatOrZeroWithDefault : Term emptySig [] (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.last 0 (branch := .var (v♯0))) (.nat_mk 0))

-- [SKIPPED BY PROFILE_LAKE] example : (run someThree).1 = ⟨0, by decide⟩ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run someThree).2 = (3, PUnit.unit) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : (run noneNat).1 = ⟨1, by decide⟩ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap optNatOrZero someThree) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap optNatOrZero noneNat) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap optNatOrZeroWithDefault someThree) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap optNatOrZeroWithDefault noneNat) = 0 := by kernel_rfl

/-- A union whose first constructor carries no fields. -/
def natOrNothing : LeanTaggedUnionSchema TyWf := .skip (.here ⟨TyWf.prim .nat, []⟩ [])

/-- Its dispatch. -/
def natOrNothingToNat : Term emptySig [] (TyWf.taggedUnion natOrNothing ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOn' (.var (v♯0)) (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- Its field-less constructor. -/
def nothing' : Term emptySig [] (TyWf.taggedUnion natOrNothing) :=
  .taggedUnion_mk natOrNothing 0 (fields := .nil)

/-- Its constructor that carries a `nat`, applied to `5`. -/
def justFive : Term emptySig [] (TyWf.taggedUnion natOrNothing) :=
  .taggedUnion_mk natOrNothing 1 (fields := .cons (.nat_mk 5) .nil)

-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natOrNothingToNat nothing') = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natOrNothingToNat justFive) = 5 := by kernel_rfl

/-- A union with three constructors: `nat`, `bool`, `nat`. -/
def natBoolNat : LeanTaggedUnionSchema TyWf :=
  .payloadFirst ⟨TyWf.prim .nat, []⟩ [TyWf.prim .bool] [[TyWf.prim .nat]]

/-- Two of its three constructors, each binding its field; the third takes the
    default. -/
def natBoolNatTwoOrZero :
    Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 2 (branch := .var (v♯0))))
    (.nat_mk 0))

/-- One branch per constructor, with no default: the middle constructor's branch binds
    its `bool`. -/
def natBoolNatAll : Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOn' (.var (v♯0))
    (.payloadFirst (.var (v♯0)) (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))
      (.cons (.var (v♯0)) .nil)))

/-- Constructor `0` of `natBoolNat`, carrying a `nat`. -/
def nbnZero : Term emptySig [] (TyWf.taggedUnion natBoolNat) :=
  .taggedUnion_mk natBoolNat 0 (fields := .cons (.nat_mk 7) .nil)

/-- Constructor `1`, carrying a `bool`. -/
def nbnOne : Term emptySig [] (TyWf.taggedUnion natBoolNat) :=
  .taggedUnion_mk natBoolNat 1 (fields := .cons (.bool_mk true) .nil)

/-- Constructor `2`, carrying a `nat`. -/
def nbnTwo : Term emptySig [] (TyWf.taggedUnion natBoolNat) :=
  .taggedUnion_mk natBoolNat 2 (fields := .cons (.nat_mk 9) .nil)

-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatTwoOrZero nbnZero) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatTwoOrZero nbnOne) = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatTwoOrZero nbnTwo) = 9 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatAll nbnZero) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatAll nbnOne) = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run (.ap natBoolNatAll nbnTwo) = 9 := by kernel_rfl

end TermTests.Eval

end
