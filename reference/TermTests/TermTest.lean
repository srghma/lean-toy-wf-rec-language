module

public import LeanScript.Expr.Build

/-!
# The grammar is usable: a few terms, written out

Each example below builds a `LeanScript.Term` of a stated type, so the file fails to
build if a constructor of the grammar cannot be applied as its documentation says.
-/

namespace TermTests

open LeanScript

/-- The empty signature: a module that refers to no top-level declaration. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-! ## Variables, functions and applications -/

/-- `fun x => x`, at `nat ⇒ nat`. -/
def idNat : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := .lam (.var (v♯0))

/-- `(fun x => x) 3`. -/
def idNatAt3 : Term emptySig [] (TyWf.prim .nat) := .ap idNat (.nat_mk 3)

/-- `fun x => fun y => x`: a curried constant function. -/
def constNat : Term emptySig []
    (TyWf.prim .nat ⇒ TyWf.prim .bool ⇒ TyWf.prim .nat) :=
  .lam (.lam (.var (v♯1)))

/-- `let x = 3; x`. -/
def letThree : Term emptySig [] (TyWf.prim .nat) := .letE' (.nat_mk 3) (.var (v♯0))

/-- A call of the one declaration of `doubleSig`. -/
def callDouble : Term doubleSig [] (TyWf.prim .nat) :=
  .ap (.global .here) (.nat_mk 21)

/-! ## Literals -/

/-- A bit-vector literal: the positivity of the width is written by `by decide`. -/
def bv : Term emptySig [] (TyWf.prim (.bitvec 8)) := .bitvec_mk (v := 7#8)

/-- A string literal. -/
def hello : Term emptySig [] (TyWf.prim .string) := .string_mk "hello"

/-- A character literal. -/
def theLetterA : Term emptySig [] (TyWf.prim .char) := .char_mk 'a'

/-- A 64-bit float literal. -/
def half : Term emptySig [] (TyWf.prim .float) := .float_mk 0.5

/-! ## Eliminators of the terminal types -/

/-- `if b then 1 else 0`, as a function of `b`. -/
def boolToNat : Term emptySig [] (TyWf.prim .bool ⇒ TyWf.prim .nat) :=
  .lam (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))

/-- `fun n => match n with | 0 => 0 | k + 1 => k`: the predecessor, by case analysis. -/
def pred : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_casesOn' (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- `fun n => Nat.rec 0 (fun k ih => ih) n`: a fold over a natural number.  The
    successor branch binds the predecessor at index `0` and the value of the fold at
    index `1`, and this one answers with the latter. -/
def foldNat : Term emptySig [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_rec' 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil) (.var (v♯1)))

/-- The code point of a character, as a `uint32`. -/
def charCode : Term emptySig [] (TyWf.prim .char ⇒ TyWf.prim .uint32) :=
  .lam (.char_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- The byte index of an unchecked position. -/
def rawByteIdx : Term emptySig [] (TyWf.prim .stringPosRaw ⇒ TyWf.prim .nat) :=
  .lam (.stringPosRaw_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- The string an unchecked substring is into: its branch binds the three fields, and
    the string is the first of them. -/
def substringStr : Term emptySig [] (TyWf.prim .substringRaw ⇒ TyWf.prim .string) :=
  .lam (.substringRaw_casesOn' (.var (v♯0)) (.var (v♯0)))

/-! ## Delays, and arrays -/

/-- A memoised delay of `3`, forced again. -/
def thunkedThree : Term emptySig [] (TyWf.prim .nat) :=
  .thunk_force (.thunk_mk (.nat_mk 3))

/-- An unmemoised delay of `3`, forced again. -/
def lazyThree : Term emptySig [] (TyWf.prim .nat) :=
  .lazy_force (.lazy_mk (.nat_mk 3))

/-- The array `#[1, 2, 3]`. -/
def oneTwoThree : Term emptySig [] (TyWf.array (TyWf.prim .nat)) :=
  .array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil)))

/-- The first element of an array of naturals, or `0`: the non-empty branch binds the
    head and the tail, in that order. -/
def headOrZero : Term emptySig [] (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) :=
  .lam (.array_casesOn' (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- The fold of an array: the non-empty branch binds the head at index `0`, the tail at
    index `1` and the value of the fold over the tail at index `2`. -/
def foldArray : Term emptySig [] (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) :=
  .lam (.array_rec' 0 (.var (v♯0)) (.nil (.nat_mk 0)) (.var (v♯2)))

/-! ## The user-defined shapes -/

/-- An enum of exactly three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- The middle constructor of `three`. -/
def middle : Term emptySig [] (TyWf.enum three) := .enum_mk three ⟨1, by decide⟩

/-- A dispatch on `three`: one branch per constructor, and no default.  The branches
    follow the shape of the schema, which has exactly the three constructors an enum has
    at minimum. -/
def enumToNat : Term emptySig [] (TyWf.enum three ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOn' (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2)))

/-- An enum of five constructors: two beyond the minimum. -/
def five : LeanEnumSchema := ⟨2, 0⟩

/-- Its dispatch: a branch for each of the two extra constructors, and then the three an
    enum always has. -/
def fiveToNat : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOn' (.var (v♯0))
    (.cons (.nat_mk 0) (.cons (.nat_mk 1)
      (.three (.nat_mk 2) (.nat_mk 3) (.nat_mk 4)))))

/-- A record of a `nat` and a `bool`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .bool, []⟩

/-- The record `(3, true)`. -/
def pair : Term emptySig [] (TyWf.record pairSchema) :=
  .record_mk pairSchema (.cons (.nat_mk 3) (.cons (.bool_mk true) .nil))

/-- Its first field: the eliminator binds both fields, and the first is index `0`. -/
def pairFst : Term emptySig [] (TyWf.prim .nat) :=
  .record_casesOn' pair (.var (v♯0))

/-- Its second field, at index `1`. -/
def pairSnd : Term emptySig [] (TyWf.prim .bool) :=
  .record_casesOn' pair (.var (v♯1))

/-- A union of a constructor with one `nat` field and a field-less one. -/
def optNat : LeanTaggedUnionSchema TyWf := .payloadFirst ⟨TyWf.prim .nat, []⟩ [] []

/-- Its first constructor, applied to `3`: the bound on the tag is written by the
    default tactic, so nothing stands between the tag and the fields. -/
def someThree : Term emptySig [] (TyWf.taggedUnion optNat) :=
  .taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil)

/-- Its second, field-less constructor: the tag is `1`, which is in range because the
    union has two constructors. -/
def noneNat : Term emptySig [] (TyWf.taggedUnion optNat) :=
  .taggedUnion_mk optNat 1 (fields := .nil)

/-- A bound that is given by hand still works. -/
def someThree' : Term emptySig [] (TyWf.taggedUnion optNat) :=
  .taggedUnion_mk optNat 0 (by decide) (.cons (.nat_mk 3) .nil)

/-- A dispatch on it: the branches follow the shape of the schema — the first
    constructor carries a field, so its branch binds it; the second binds nothing; and
    there is no constructor after them. -/
def optNatOrZero : Term emptySig [] (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOn' (.var (v♯0)) (.payloadFirst (.var (v♯0)) (.nat_mk 0) .nil))

/-- A dispatch on *some* of its constructors, with a default: only constructor `0` gets
    a branch — and that branch binds its field — while constructor `1` falls to the
    default.  A one-branch list is `last`; the bound on the tag is written by `ctor_tag`
    and the bound that keeps the numbers in order by `ctor_ge`. -/
def optNatOrZeroWithDefault : Term emptySig [] (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.last 0 (branch := .var (v♯0))) (.nat_mk 0))

/-- A union whose first constructor carries no fields: the branches then go through
    `CtorsWithPayloadCases`. -/
def natOrNothing : LeanTaggedUnionSchema TyWf := .skip (.here ⟨TyWf.prim .nat, []⟩ [])

/-- Its dispatch: a branch for the field-less constructor, then the branch of the
    constructor that carries the `nat`, which binds it. -/
def natOrNothingToNat : Term emptySig [] (TyWf.taggedUnion natOrNothing ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOn' (.var (v♯0)) (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- A dispatch on the enum `three` that names only its last constructor and sends the
    other two to the default.  A one-branch list is `last`, and the bound that keeps the
    numbers in order is written by `ctor_ge`. -/
def enumLastOrZero : Term emptySig [] (TyWf.enum three ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0)) (.last ⟨2, by decide⟩ (.nat_mk 2))
    (.nat_mk 0))

/-- Two of the five constructors, named smallest first; the other three take the
    default. -/
def fiveTwoOrZero : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0))
    (.cons 1 (.nat_mk 1) (.last 3 (.nat_mk 3))) (.nat_mk 0))

-- The order is not a convention but a typing rule: a list whose numbers go down does
-- not elaborate.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  ↑3 + 1 ≤ ↑1
is false
-/
#guard_msgs (error) in
def fiveOutOfOrder : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0))
    (.cons 3 (.nat_mk 3) (.last 1 (.nat_mk 1))) (.nat_mk 0))

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  ↑1 + 1 ≤ ↑1
is false
-/
#guard_msgs (error) in
def fiveRepeated : Term emptySig [] (TyWf.enum five ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0))
    (.cons 1 (.nat_mk 1) (.last 1 (.nat_mk 2))) (.nat_mk 0))

/-! ## A partial dispatch on a union is validated the same way -/

/-- A union with three constructors: `nat`, `bool`, `nat`. -/
def natBoolNat : LeanTaggedUnionSchema TyWf :=
  .payloadFirst ⟨TyWf.prim .nat, []⟩ [TyWf.prim .bool] [[TyWf.prim .nat]]

/-- Two of its three constructors, named smallest first, each binding its field; the
    third takes the default.  Both bounds — the tag's and the order's — are written by
    the default tactics. -/
def natBoolNatTwoOrZero :
    Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 2 (branch := .var (v♯0))))
    (.nat_mk 0))

-- As for an enum, the order is a typing rule: a list whose numbers go down does not
-- elaborate.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  2 + 1 ≤ 0
is false
-/
#guard_msgs (error) in
def natBoolNatOutOfOrder :
    Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 2 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
    (.nat_mk 0))

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  0 + 1 ≤ 0
is false
-/
#guard_msgs (error) in
def natBoolNatRepeated :
    Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
    (.nat_mk 0))

/-! ## A partial dispatch may not name **every** constructor

The default of a `xxx_casesOnWithDefault` has to be reachable.  A list of branches that
names every constructor of the type leaves the default unreachable — it is an exhaustive
dispatch written the long way round, and `Term.enum_casesOn'` /
`Term.taggedUnion_casesOn'` is how it has to be written.  The branch list **counts its
branches**, and the count is bounded by the number of constructors, so the long way
round does not elaborate. -/

-- All three constructors of `three` named, with a default that can never be taken.
/--
error: could not synthesize default value for parameter 'hk' using tactics
---
error: Tactic `decide` proved that the proposition
  1 + 1 + 1 < three.nOfConstructors
is false
-/
#guard_msgs (error) in
def threeAllNamed : Term emptySig [] (TyWf.enum three ⇒ TyWf.prim .nat) :=
  .lam (.enum_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (.nat_mk 0) (.cons 1 (.nat_mk 1) (.last 2 (.nat_mk 2))))
    (.nat_mk 9))

-- Both constructors of `optNat` named, likewise.
/--
error: could not synthesize default value for parameter 'hk' using tactics
---
error: Tactic `decide` proved that the proposition
  1 + 1 < optNat.length
is false
-/
#guard_msgs (error) in
def optNatAllNamed : Term emptySig [] (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 1 (branch := .nat_mk 1)))
    (.nat_mk 0))

/-- Naming all but one constructor is still fine: the two smallest constructors of
    `natBoolNat`, with the third taking the default — one fewer branch than the union has
    constructors, which is what `ctor_lt` checks. -/
def natBoolNatAllButOne :
    Term emptySig [] (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault' (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 1 (branch := .nat_mk 1)))
    (.nat_mk 0))

/-! ## A term is indexed by a **type**, not by a tree

`Term` and `Ctx` are indexed by `LeanScript.TyWf` — a tree together with the proof that it
is a type of the language — so the type of a term, and every type in its context, is a
type by construction.  Nothing has to be written by hand for it: `TyWf.prim`, `⇒`,
`TyWf.array`, `TyWf.record`, `TyWf.taggedUnion`, … compose the proof out of their
arguments'. -/

/-- The type of a term is always a type of the language: its proof is part of the index.
    (This is why no introduction form of a non-recursive shape has to ask for one.) -/
theorem type_of_term_is_wf {Sg : Sig} {Γ : Ctx} {τ : TyWf} (_t : Term Sg Γ τ) :
    Ty.Wf τ.toTy := τ.isWf

/-- Every type in the context of a term is a type of the language, for the same reason. -/
theorem ctx_of_term_is_wf {Sg : Sig} {Γ : Ctx} {τ : TyWf} (_t : Term Sg Γ τ) :
    Ty.WfAllIn 0 (Γ.map TyWf.toTy) := Ty.wfAllIn_map_toTy Γ

-- A tree becomes an index by `Ty.toTyWf`, whose proof is written by `ty_wf` — and a tree
-- that is not a type is refused there, so it indexes no term at all.  A free occurrence
-- leaf is one such tree.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ty_wf: `Ty.self` is not a type in a scope of 0 members
-/
#guard_msgs (error) in
def atOccurrenceLeaf : Term emptySig [] (Ty.self.toTyWf) := .nat_mk 0

-- So is a binder that mentions itself to the left of an arrow.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs (error) in
def atNonPositiveBinder : Term emptySig []
    ((Ty.recTaggedUnion (.payloadFirst ⟨.fn .self (.prim .nat), []⟩ [] [])).toTyWf) :=
  .nat_mk 0

end TermTests
