module

public import LeanScript.Expr.Build
public import LeanScript.Eval
public meta import LeanScript.KernelRfl

/-!
# The recursive shapes of the grammar, written out

`Ty` has four recursive binders, and `LeanScript.Term` has an introduction form, a case
analysis and a fold for each of them, plus a partial case analysis with a default where
the shape has constructors to leave out.  Each example below builds a term of a stated
type, so the file fails to build if one of those constructors cannot be applied as its
documentation says.

The examples also pin the two things that make the recursive forms usable without writing
anything by hand: the **unfolding** of a payload reduces (`Ty.recTaggedUnionUnfold` of a
concrete schema is a concrete schema, so a field written `Ty.self` really does take a
value of the recursive type), and the tag's bound is written by `ctor_tag`.
-/

namespace TermTests

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- The empty signature, as in `TermTests.TermTest`. -/
def recEmptySig : Sig := ⟨[], by decide⟩

/-! ## A recursive tagged union: a list of naturals

`nil` carries nothing and `cons` carries a natural and a list, which is `Ty.self`. -/

/-- The schema of `List Nat` as the language sees it: constructor `0` is `nil`, which has
    no fields; constructor `1` is `cons`, whose fields are a natural and the list
    itself. -/
def natListSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.prim .nat).toTyWfIn, [Ty.self.toTyWfIn]⟩ [])

/-- The type of a list of naturals. -/
def natListTy : TyWf := .recTaggedUnion natListSchema

-- The unfolding really is the schema with `Ty.self` replaced by the list type, so the
-- second field of `cons` takes a list.
-- [SKIPPED BY PROFILE_LAKE] example : (TyWf.recTaggedUnionUnfold natListSchema).get 1 (by decide) =
-- [SKIPPED BY PROFILE_LAKE]     [TyWf.prim .nat, natListTy] := by kernel_rfl

/-- The empty list.  The tag's bound is written by `ctor_tag`. -/
def natNil : Term recEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 0) (fields := .nil)

/-- `[3]`: `cons` of `3` and the empty list. -/
def natOne : Term recEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 1)
    (fields := .cons (.nat_mk 3) (.cons natNil .nil))

/-- The head of a list, or `0` — a dispatch on **every** constructor, whose `cons` branch
    binds the head at index `0` and the tail at index `1`. -/
def natHead : Term recEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_casesOn' (.var (v♯0))
    (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- The tail of a list, or the empty list — a dispatch on the one constructor that has
    one, with a default for the other. -/
def natTail : Term recEmptySig [] (natListTy ⇒ natListTy) :=
  .lam (.recTaggedUnion_casesOnWithDefault' (.var (v♯0))
    (.last 1 (branch := .var (v♯1)))
    (.recTaggedUnion_mk natListSchema (t := 0) (fields := .nil)))

/-- **A fold over a list**: the `nil` branch answers `0`, and the `cons` branch binds the
    head at index `0`, the tail at index `1` and the value of the fold at the tail at
    index `2`, and answers with that value — so the whole fold answers `0`.  The
    recursive value is *given* to the branch, so the term is terminating by
    construction.  (The grammar has no arithmetic, so the branch cannot add the head to
    it; an operation on naturals is a declaration of the signature.) -/
def natFoldZero : Term recEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_rec' 0 (.var (v♯0))
    (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯2))) .nil)))

/-! ## A recursive record -/

/-- A rose tree: a label and an array of subtrees. -/
def roseSchema : LeanRecordSchema (TyWfIn 1) :=
  ⟨(Ty.prim .nat).toTyWfIn, (Ty.array Ty.self).toTyWfIn, []⟩

/-- The type of a rose tree. -/
def roseTy : TyWf := .recObject roseSchema

/-- A leaf: the label `1` and no children. -/
def roseLeaf : Term recEmptySig [] roseTy :=
  .recObject_mk roseSchema (fields := .cons (.nat_mk 1) (.cons (.array_mk .nil) .nil))

/-- A tree with one child. -/
def roseOne : Term recEmptySig [] roseTy :=
  .recObject_mk roseSchema
    (fields := .cons (.nat_mk 2) (.cons (.array_mk (.cons roseLeaf .nil)) .nil))

/-- The label of a tree: the eliminator binds every field, so the label is index `0`. -/
def roseLabel : Term recEmptySig [] (roseTy ⇒ TyWf.prim .nat) :=
  .lam (.recObject_casesOn' (.var (v♯0)) (.var (v♯0)))

/-- A record whose **second field is the record itself**: the payload of a binder is
    written in the scope the binder opens, so `Ty.self` is a field of it. -/
def cellSchema : LeanRecordSchema (TyWfIn 1) :=
  ⟨(Ty.prim .nat).toTyWfIn, Ty.self.toTyWfIn, []⟩

-- The record it describes states the equation `T = Nat × T`, which no value satisfies,
-- so it is **not a type of the language** and `TyWf.recObject` has no proof to be given.
-- A `Term` is indexed by a type, so there is now no term of it at all — not even a fold
-- over it, which the `Ty`-indexed grammar still admitted because it carried the proof at
-- the introduction forms only.
/--
error: could not synthesize default value for parameter 'hwf' using tactics
---
error: ty_wf: the declaration being defined is assumed to have a value by its own definition, so the definition describes no value
-/
#guard_msgs (error) in
def cellTy : TyWf := .recObject cellSchema

/-! ## A recursive newtype -/

/-- A newtype whose body is an array of itself: a tree with no labels. -/
def forestTy : TyWf := .recAlias (Ty.array Ty.self).toTyWfIn

-- Its body unfolds to an array of the newtype.
-- [SKIPPED BY PROFILE_LAKE] example : TyWf.recAliasUnfold (Ty.array Ty.self).toTyWfIn = TyWf.array forestTy := by kernel_rfl

/-- The empty forest.  The wrapper is erased, so this is the empty array. -/
def emptyForest : Term recEmptySig [] forestTy :=
  .recAlias_mk (Ty.array Ty.self).toTyWfIn (value := .array_mk .nil)

/-- A forest of one empty forest. -/
def oneForest : Term recEmptySig [] forestTy :=
  .recAlias_mk (Ty.array Ty.self).toTyWfIn (value := .array_mk (.cons emptyForest .nil))

/-- Is a forest empty?  The eliminator binds the body, which is an array. -/
def forestIsEmpty : Term recEmptySig [] (forestTy ⇒ TyWf.prim .bool) :=
  .lam (.recAlias_casesOn' (.var (v♯0))
    (.array_casesOn' (.var (v♯0)) (.bool_mk true) (.bool_mk false)))

/-! ## A mutual recursive family

Two members: `A` has two constructors, the second of which holds a `B`; `B` is a record
holding a natural and an `A`. -/

/-- Member `A`: constructor `0` has no fields, constructor `1` holds a `B`. -/
def memberA : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 1).toTyWfIn, []⟩ []))

/-- Member `B`: a record of a natural and an `A`. -/
def memberB : LeanFamMemberSchema (TyWfIn 2) :=
  .record ⟨(Ty.prim .nat).toTyWfIn, (Ty.familyMember 0).toTyWfIn, []⟩

/-- The family, selecting member `A`. -/
def famA : LeanMutualRecFamily (TyWfIn 2) := .selectedThenMore [] memberA memberB []

/-- The family, selecting member `B`. -/
def famB : LeanMutualRecFamily (TyWfIn 2) := .selectedLast memberA [] memberB

/-- The type of member `A`. -/
def tyA : TyWf := .mutualRecursiveFamily famA

/-- The type of member `B`. -/
def tyB : TyWf := .mutualRecursiveFamily famB

-- Selecting a member of either family gives the type of that member, so an occurrence
-- of `Ty.familyMember i` inside the family unfolds to the type of member `i`.
-- [SKIPPED BY PROFILE_LAKE] example : Ty.unfoldFamily (famB.map TyWfIn.toTy) (Ty.familyMember 0) = tyA.toTy := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Ty.unfoldFamily (famA.map TyWfIn.toTy) (Ty.familyMember 1) = tyB.toTy := by kernel_rfl

/-- The field-less constructor of `A`. -/
def aNil : Term recEmptySig [] tyA :=
  .mutualRecursiveFamily_mk famA (value := .ctors _ 0 (fields := .nil))

/-- A `B`: the natural `7` and the `A` above. -/
def bOne : Term recEmptySig [] tyB :=
  .mutualRecursiveFamily_mk famB
    (value := .record _ (.cons (.nat_mk 7) (.cons aNil .nil)))

/-- An `A` built from that `B`. -/
def aOne : Term recEmptySig [] tyA :=
  .mutualRecursiveFamily_mk famA (value := .ctors _ 1 (fields := .cons bOne .nil))

/-- The natural a `B` holds: a record member has one branch, which binds its fields. -/
def bLabel : Term recEmptySig [] (tyB ⇒ TyWf.prim .nat) :=
  .lam (.mutualRecursiveFamily_casesOn' (.var (v♯0)) (.record (.var (v♯0))))

/-- Is an `A` the field-less constructor?  A dispatch on every constructor of the member
    `A` is. -/
def aIsNil : Term recEmptySig [] (tyA ⇒ TyWf.prim .bool) :=
  .lam (.mutualRecursiveFamily_casesOn' (.var (v♯0))
    (.ctors (.skip (.bool_mk true) (.here (.bool_mk false) .nil))))

/-- The same, written as a dispatch on the one constructor that has a field, with a
    default for the other. -/
def aIsNil' : Term recEmptySig [] (tyA ⇒ TyWf.prim .bool) :=
  .lam (.mutualRecursiveFamily_casesOnWithDefault' (.var (v♯0))
    (.ctors (.last 1 (branch := .bool_mk false))) (.bool_mk true))

/-- **A fold over the whole family**: branches for *both* members, in declaration order.
    The `A` branch that holds a `B` binds it at index `0` and the value of the fold at it
    at index `1`; the `B` branch binds its natural at index `0`, its `A` at index `1` and
    the value of the fold at that `A` at index `2`. -/
def famFold : Term recEmptySig [] (tyA ⇒ TyWf.prim .nat) :=
  .lam (.mutualRecursiveFamily_rec' 0 (.var (v♯0))
    (.cons (.ctors (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯1))) .nil)))
      (.cons (.record (.here (.var (v♯2)))) .nil)))

/-- A fold over the whole family that reads a label: an `A` that holds a `B` answers the
    value of the fold at that `B`, and a `B` answers its natural. -/
def famLabel : Term recEmptySig [] (tyA ⇒ TyWf.prim .nat) :=
  .lam (.mutualRecursiveFamily_rec' 0 (.var (v♯0))
    (.cons (.ctors (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯1))) .nil)))
      (.cons (.record (.here (.var (v♯0)))) .nil)))

/-! ## The branch families match the constructors of the type

The branches of a dispatch on a recursive shape are indexed by the shape's own schema, so
a list that branches on constructors the type does not have, or that stops before the
constructors run out, does not elaborate. -/

-- The list type's second constructor carries fields, so its branch is `here` and not
-- another `skip`.
/--
error: Unknown constant `LeanScript.CtorsWithPayloadFoldCases.nil`

Note: Inferred this name from the expected resulting type of `.nil`:
  CtorsWithPayloadFoldCases ?m.35 ?m.29 ?m.30 ?m.31 ?m.34 (TyWf.prim LeanPrimTy.nat)
-/
#guard_msgs (error) in
def natHeadNotExhaustive : Term recEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_casesOn' (.var (v♯0))
    (.skip (.nat_mk 0) (.skip (.nat_mk 0) .nil)))

-- A fold over the family needs the branches of **every** member: a list that stops after
-- the first does not elaborate.
/--
error: Application type mismatch: The argument
  FamilyFoldKCases.nil
has type
  FamilyFoldKCases ?m.97 ?m.98 ?m.99 ?m.100 ?m.101 ?m.102 [] ?m.103
but is expected to have type
  FamilyFoldKCases recEmptySig 0 famA.members (TyWf.famRecBinders famA tyA._proof_1 (TyWf.prim LeanPrimTy.nat)) [tyA]
    (TyWf.prim LeanPrimTy.nat) [memberB] 0
in the application
  FamilyFoldKCases.cons
    (FamilyMemberFoldKCases.ctors
      (FamilyTaggedUnionFoldKCases.skip (FamilyFoldKBranch.here (Term.nat_mk 0))
        (FamilyCtorsWithPayloadFoldKCases.here (FamilyFoldKBranch.here (Term.var DeBruijn.head.tail))
          FamilyTaggedUnionFoldKCasesRest.nil)))
    FamilyFoldKCases.nil
-/
#guard_msgs (error) in
def famFoldPartial : Term recEmptySig [] (tyA ⇒ TyWf.prim .nat) :=
  .lam (.mutualRecursiveFamily_rec' 0 (.var (v♯0))
    (.cons (.ctors (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯1))) .nil))) .nil))

/-! ## An introduction form builds a value of a **type**

`Ty` is a tree, and not every tree is a type: a binder may fail to mention itself, may
mention itself in the domain of a function — `μX. X ⇒ Nat`, at which a term language
diverges — or may describe an equation no value satisfies, like `μX. Nat × X`.  The four
recursive introduction forms therefore carry `LeanScript.Ty.Wf` of the tree they build a
value of, written by `ty_wf`, so none of those trees has a value in the grammar.  The
eliminators do not carry it, and they do not have to: a `Term` is indexed by a **type**,
so a tree that is not one has no term of it to take apart in the first place.  The two
examples below are the two ways a binder fails to be a type, and each of them is now
refused where the type is written rather than where a value of it is. -/

-- `cellTy`, above, is the equation `T = Nat × T`: refused at the type.

-- A union that mentions itself in the **domain** of a function would be `μX. (X ⇒ Nat)`.
-- It is inhabited — its first constructor has no fields — but it is not positive, and
-- here it is refused one step earlier still: `Ty.self ⇒ Ty.prim .nat` is not even a
-- well-formed *payload*, since the domain of a function is checked in the closed scope,
-- so the schema of such a union cannot be written.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs (error) in
def negativeSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.fn Ty.self (Ty.prim .nat)).toTyWfIn, []⟩ [])

/-! ## What the evaluator says about them

Every recursive shape has values — `LeanScript.Ty.Den` gives a recursive **tagged union**
the W-tree of its constructors, a recursive **record** and a recursive **newtype** the
W-tree of their fields and of their body, and a **mutual family** the indexed W-tree of
its members — so `LeanScript.Term.eval` interprets all of their forms, the introduction
forms included. -/

-- [SKIPPED BY PROFILE_LAKE] /-- The empty list is constructor `0`. -/
-- [SKIPPED BY PROFILE_LAKE] example : (TyWf.DenRec.unfold natListSchema _ (Term.run GlobalEnv.nil natNil)).1.val = 0 :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The one-element list `[3]` is constructor `1`. -/
-- [SKIPPED BY PROFILE_LAKE] example : (TyWf.DenRec.unfold natListSchema _ (Term.run GlobalEnv.nil natOne)).1.val = 1 :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The head of `[3]` is `3`, and the head of the empty list is the default `0`. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap natHead natOne) = 3 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap natHead natNil) = 0 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- The tail of `[3]` is empty, so its head is the default. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap natHead (.ap natTail natOne)) = 0 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- The fold that answers `0` answers `0`. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap natFoldZero natOne) = 0 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- Building a recursive **record** is inside the model: its label reads back. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap roseLabel roseLeaf) = 1 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap roseLabel roseOne) = 2 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- Building a recursive **newtype** is inside the model too: the empty forest is empty,
-- [SKIPPED BY PROFILE_LAKE]     and a forest of one forest is not. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap forestIsEmpty emptyForest) = true := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap forestIsEmpty oneForest) = false := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- Building a member of a **mutual family** is inside the model as well: a `B` reads back
-- [SKIPPED BY PROFILE_LAKE]     its natural, an `A` reads back its constructor — by a full dispatch and by a partial
-- [SKIPPED BY PROFILE_LAKE]     one with a default — and the folds over the whole family run, passing from a member
-- [SKIPPED BY PROFILE_LAKE]     to the other and back. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap bLabel bOne) = 7 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap aIsNil aNil) = true := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap aIsNil aOne) = false := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap aIsNil' aNil) = true := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap aIsNil' aOne) = false := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap famFold aOne) = 0 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap famLabel aNil) = 0 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : Term.run GlobalEnv.nil (.ap famLabel aOne) = 7 := by decide +kernel

end TermTests
