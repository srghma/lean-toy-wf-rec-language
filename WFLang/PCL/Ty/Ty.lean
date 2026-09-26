module

public import LeanScript.Ty.Shape

@[expose] public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# `Ty`: one tree for every type of the language

`Ty` is a **tree of types**.  There are no names, no side tables and no proofs inside it:
a type is built out of its own parts, and two types are equal when their trees are equal.

## One tree, not two

There used to be two languages — `Ty` for a *closed* type and `RTy Occ` for a type written
*inside* a recursive declaration — with the six non-recursive shapes, the equality
development and the traversals written once for each, and four sealed structures carrying
a proof of well-formedness between them.  They are now the same type.  A `Ty` may be an
occurrence of the declaration it sits in:

* `Ty.self` — the declaration that recurses **on its own**; it carries no number, because
  there is exactly one declaration in scope to point at;
* `Ty.familyMember i` — member `i` of the **mutual family** in scope.

Whether a tree uses those leaves in a scope that has them is no longer a property of the
type but a proposition about the tree, `LeanScript.Ty.Wf` (`LeanScript.Ty.Wf`), which is
what a `LeanScript.LeanScriptTyWf` instance carries beside its tree.

## The shapes

| shape                      | payload                     | what cannot be written                                    |
| :------------------------- | :-------------------------- | :--------------------------------------------------------- |
| `Ty.enum`                  | `LeanEnumSchema`            | fewer than three constructors                               |
| `Ty.record`                | `LeanRecordSchema Ty`       | fewer than two fields                                       |
| `Ty.taggedUnion`           | `LeanTaggedUnionSchema Ty`  | fewer than two constructors, or none with a field           |
| `Ty.recObject`             | `LeanRecordSchema Ty`       | fewer than two fields                                       |
| `Ty.recTaggedUnion`        | `LeanTaggedUnionSchema Ty`  | fewer than two constructors, or none with a field           |
| `Ty.mutualRecursiveFamily` | `LeanMutualRecFamily Ty`    | fewer than two members, or a member number out of range     |

A constructor is a *position* in the list of constructors and a field is a *position* in
the list of fields, so a value of a user-defined type is `{ tag: 0, _1: …, _2: … }` — a
number and positional fields, never a string.
-/

/-- A type of the language: a shape whose children are types, an occurrence of the
    declaration the type sits inside, or one of the four recursive binders, each of which
    opens a scope of its own.

    A tree is *closed* when it holds no occurrence outside a binder; that, and the other
    conditions of `LeanScript.Ty.Wf`, are stated about a tree rather than carried by it. -/
inductive Ty where
  /-- An occurrence of the declaration being defined, when that declaration recurses on
      its own.  It carries no number: there is one declaration in scope to point at. -/
  | self : Ty
  /-- An occurrence of member `i` of the mutual family being defined. -/
  | familyMember : Nat → Ty
  /-- A shape: a terminal type, a function, an array, an enum, a record or a tagged
      union.  See `LeanScript.TyShape`. -/
  | shape : TyShape Ty → Ty
  /-- A recursive sum type; `Ty.self` inside it is an occurrence of *it*. -/
  | recTaggedUnion : LeanTaggedUnionSchema Ty → Ty
  /-- A recursive single-constructor type with at least two fields. -/
  | recObject : LeanRecordSchema Ty → Ty
  /-- A recursive newtype, whose wrapper is erased into its single field. -/
  | recAlias : Ty → Ty
  /-- A mutual recursive family, together with which member of it this type is;
      `Ty.familyMember i` inside it is an occurrence of member `i` of *this* family. -/
  | mutualRecursiveFamily : LeanMutualRecFamily Ty → Ty
  deriving Repr

namespace Ty

/-! ## The shapes, as patterns

Every shape is `Ty.shape (…)`; the abbreviations below name them directly.  They are
`@[match_pattern]`, so each works in a pattern as well as in a term. -/

/-- A terminal type. -/
@[match_pattern] abbrev prim (p : LeanPrimTy) : Ty := .shape (.prim p)
/-- A curried function type, `σ ⇒ τ`. -/
@[match_pattern] abbrev fn (a b : Ty) : Ty := .shape (.fn a b)
/-- An array, thunk or lazy value. -/
@[match_pattern] abbrev primCovariant (s : LeanPrimTyCovariant Ty) : Ty :=
  .shape (.primCovariant s)
/-- A non-recursive enum. -/
@[match_pattern] abbrev enum (e : LeanEnumSchema) : Ty := .shape (.enum e)
/-- A single-constructor record. -/
@[match_pattern] abbrev record (fs : LeanRecordSchema Ty) : Ty := .shape (.record fs)
/-- A non-recursive sum type with fields. -/
@[match_pattern] abbrev taggedUnion (l : LeanTaggedUnionSchema Ty) : Ty :=
  .shape (.taggedUnion l)

/-- In JS: an array. -/
@[match_pattern] abbrev array (α : Ty) : Ty := .primCovariant (.array α)
/-- A memoised delay. -/
@[match_pattern] abbrev thunk (α : Ty) : Ty := .primCovariant (.thunk α)
/-- An unmemoised delay. -/
@[match_pattern] abbrev lazy (α : Ty) : Ty := .primCovariant (.lazy α)

/-! ## Small constructors -/

/-- The enum with `n` constructors numbered from `shift`; `none` unless `n` is a number of
    constructors an enum can have. -/
def enumOfCount? (n : Nat) (shift : Int := 0) : Option Ty :=
  (LeanEnumSchema.ofCount? n shift).map Ty.enum

/-- The type of a field-less sum with `n` constructors: `Ty.prim .bool` for two of them
    and an enum for three or more, and `none` for the degenerate cases. -/
def enumOrBool? (n : Nat) (shift : Int := 0) : Option Ty :=
  if n == 2 && shift == 0 then some (.prim .bool) else enumOfCount? n shift

/-- The schema of a list of `a`, the payload of the recursive tagged union that models
    `List`: constructor `0` (`nil`) has no field, constructor `1` (`cons`) has an element
    and the list itself (`Ty.self`).  `LeanScript.TyWf.list` is the type built from it. -/
abbrev listSchema (a : Ty) : LeanTaggedUnionSchema Ty := .skip (.here ⟨a, [.self]⟩ [])

/-! ## The children of a node

Every traversal of a tree — well-formedness, rendering, a backend — needs the types one
node holds, so they are given once, here, per node.  A recursive binder's children are
the types of *its* payload, written in *its* scope. -/

/-- The types one member of a mutual family holds. -/
def memberTys : LeanFamMemberSchema Ty → List Ty
  | .ctors l => l.toList.flatten
  | .record fs => fs.toList
  | .alias b => [b]

/-- The types a mutual family holds, member by member, in declaration order. -/
def familyTys (f : LeanMutualRecFamily Ty) : List Ty := f.members.flatMap memberTys

/-- The types a node holds directly.  For a binder these are the types of its payload,
    which are written in the scope the binder opens and not in the scope the binder sits
    in. -/
def children : Ty → List Ty
  | .self | .familyMember _ => []
  | .shape s => s.children
  | .recTaggedUnion l => l.toList.flatten
  | .recObject fs => fs.toList
  | .recAlias b => [b]
  | .mutualRecursiveFamily f => familyTys f

/-! ## Equality

Two types are equal when their trees are equal, and this is that test.  It is a plain
Boolean function with no lemmas about it: the tree carries no proofs, and nothing in the
language needs equality of types to be reflected into a proposition. -/

mutual

/-- Are these two types the same tree? -/
def beq : Ty → Ty → Bool
  | .self, .self => true
  | .familyMember i, .familyMember j => i == j
  | .shape s, .shape t => Ty.beqShape s t
  | .recTaggedUnion a, .recTaggedUnion b => Ty.beqTU a b
  | .recObject a, .recObject b => Ty.beqA2 a b
  | .recAlias a, .recAlias b => Ty.beq a b
  | .mutualRecursiveFamily a, .mutualRecursiveFamily b => Ty.beqFamily a b
  | _, _ => false

/-- `Ty.beq`, on a shape. -/
def beqShape : TyShape Ty → TyShape Ty → Bool
  | .prim p, .prim q => p == q
  | .fn a b, .fn c d => Ty.beq a c && Ty.beq b d
  | .primCovariant s, .primCovariant t => Ty.beqCov s t
  | .enum a, .enum b => a == b
  | .record a, .record b => Ty.beqA2 a b
  | .taggedUnion a, .taggedUnion b => Ty.beqTU a b
  | _, _ => false

/-- `Ty.beq`, on an array, a thunk or a lazy value. -/
def beqCov : LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty → Bool
  | .array a, .array b => Ty.beq a b
  | .thunk a, .thunk b => Ty.beq a b
  | .lazy a, .lazy b => Ty.beq a b
  | _, _ => false

/-- `Ty.beq`, on a list of types. -/
def beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

/-- `Ty.beq`, on the fields of each constructor. -/
def beqCtors : List (List Ty) → List (List Ty) → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beqList a b && Ty.beqCtors as bs
  | _, _ => false

/-- `Ty.beq`, on the fields of a record. -/
def beqA2 : LeanRecordSchema Ty → LeanRecordSchema Ty → Bool
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => Ty.beq a1 b1 && Ty.beq a2 b2 && Ty.beqList as bs

/-- `Ty.beq`, on the fields of a constructor that has at least one. -/
def beqNE : NonEmptyList Ty → NonEmptyList Ty → Bool
  | ⟨a, as⟩, ⟨b, bs⟩ => Ty.beq a b && Ty.beqList as bs

/-- `Ty.beq`, on the constructors of a tagged union. -/
def beqTU : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst f n r, .payloadFirst g m s =>
      Ty.beqNE f g && Ty.beqList n m && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

/-- `Ty.beq`, on the constructors that follow a field-less one. -/
def beqCP : CtorsWithPayload Ty → CtorsWithPayload Ty → Bool
  | .here f r, .here g s => Ty.beqNE f g && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

/-- `Ty.beq`, on one member of a mutual family. -/
def beqFam : LeanFamMemberSchema Ty → LeanFamMemberSchema Ty → Bool
  | .ctors a, .ctors b => Ty.beqTU a b
  | .record a, .record b => Ty.beqA2 a b
  | .alias a, .alias b => Ty.beq a b
  | _, _ => false

/-- `Ty.beq`, on a list of members. -/
def beqFamList : List (LeanFamMemberSchema Ty) → List (LeanFamMemberSchema Ty) → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beqFam a b && Ty.beqFamList as bs
  | _, _ => false

/-- `Ty.beq`, on a mutual family together with the member that is selected. -/
def beqFamily : LeanMutualRecFamily Ty → LeanMutualRecFamily Ty → Bool
  | .selectedThenMore b1 c1 n1 a1, .selectedThenMore b2 c2 n2 a2 =>
      Ty.beqFamList b1 b2 && Ty.beqFam c1 c2 && Ty.beqFam n1 n2 && Ty.beqFamList a1 a2
  | .selectedLast f1 b1 c1, .selectedLast f2 b2 c2 =>
      Ty.beqFam f1 f2 && Ty.beqFamList b1 b2 && Ty.beqFam c1 c2
  | _, _ => false

end

end Ty

/-- Notation for a curried function type: `σ ⇒ τ` is `Ty.fn σ τ`.  It is scoped to
    `LeanScript`, so it is in force inside the namespace and for whoever opens it. -/
scoped infixr:25 " ⇒ " => Ty.fn

instance : BEq Ty := ⟨Ty.beq⟩
instance : Inhabited Ty := ⟨.prim .bool⟩

/-! ## Coercions

A node, or a leaf, *is* a type wherever a type is wanted.  That `Ty.beq` is the equality
of trees — and the `LawfulBEq` and `DecidableEq` instances that follow from it — is
`LeanScript.Ty.TyBEq`, which is a module of its own because it is a proof rather than a
definition. -/

/-- A terminal type is a type. -/
instance : CoeOut LeanPrimTy Ty := ⟨.prim⟩
/-- An array, a thunk or a lazy value is a type. -/
instance : CoeOut (LeanPrimTyCovariant Ty) Ty := ⟨.primCovariant⟩
/-- A node whose children are types is a type. -/
instance : CoeOut (TyShape Ty) Ty := ⟨.shape⟩
/-- An enum schema is a type. -/
instance : CoeOut LeanEnumSchema Ty := ⟨Ty.enum⟩

end LeanScript

end
