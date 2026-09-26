module

public import LeanScript.Ty.Ty

@[expose] public section

namespace LeanScript

/-!
# `Ty.Wf`: the proposition that a tree is a type

A `LeanScript.Ty` is a plain tree: nothing stops a tree from using `Ty.self` where no
declaration is being defined, or from naming member `7` of a family of two, or from
calling itself recursive while mentioning itself nowhere.  Those conditions are stated
here, as **inductive propositions** about a tree, and a `LeanScript.LeanScriptTyWf` instance
carries a proof of them beside its tree.

They are propositions rather than a Boolean check (`wf t = true`) for one reason: a proof
is *composed*.  `LeanScriptTyWf (Option α)` builds its tree out of the tree of `α` and its
proof out of the proof of `α`, without ever looking inside either — so a type that has
been checked is not checked again at any of its use sites, in this module or in a later
one.  See `LeanScript.Ty.WfTactic` for the tactic that composes them.

## The scope index

`Ty.WfIn n t` reads: `t` is well formed **in a scope of `n` members**.

| `n` | where | which occurrences are legal |
| :-- | :-- | :-- |
| `0` | a closed type | none |
| `1` | inside a binder that recurses on its own | `Ty.self` |
| `n ≥ 2` | inside a family of `n` members | `Ty.familyMember i` for `i < n` |

`Ty.Wf t` is `Ty.WfIn 0 t`: the tree of a real, closed type.  A closed tree is well formed
in every scope (`Ty.WfIn.closed`), which is what lets a checked type be dropped into the
payload of a new declaration for nothing.

## What is checked

* **Scope.** Every occurrence names a member the scope has.
* **Recursion.** Every recursive binder is really recursive — its payload mentions it —
  and every member of a family is mentioned by the family.
* **Positivity.** An occurrence never stands in the *domain* of a function type: the
  domain of `Ty.fn` is checked in the closed scope (`Ty.WfShapeIn.fn`), so `μX. X → Nat`,
  at which a term language diverges, is not a type.
* **Inhabitation.** Every binder describes a type that has *values*: its payload is
  inhabited without assuming that the declaration being defined is (`Ty.HabIn`), and in a
  family every member becomes inhabited in some order (`Ty.FamHab`).  So `μX. X` — the
  equation `T = T`, which no value satisfies — is not a type, while `μX. Array X` is (the
  empty array), and neither is `inductive Bad | mk : Bad → Bad`, which Lean does accept
  and which therefore has to be refused here rather than at the front end.

Inhabitation is a *least fixpoint*: `μX. F X` has a value exactly when `F ∅` does, because
`F` is monotone — which is why the payload of a binder is checked with nothing assumed
(`Ty.HabIn … []`), and why positivity has to be checked for the monotonicity to hold.  A
family needs the iteration, and `Ty.FamKnown` performs it: it grows the set of members
already known to have values, one member at a time.
-/

namespace Ty

/-! ## Where a declaration is mentioned -/

mutual

/-- `Ty.OccursIn i t`: the tree `t` contains an occurrence of member `i` of the scope it
    is written in.  A nested binder is *not* looked into: the occurrences inside it belong
    to its own scope. -/
inductive OccursIn : Nat → Ty → Prop where
  /-- `Ty.self` is an occurrence of member `0` — the only member a lone binder has. -/
  | self : OccursIn 0 .self
  /-- `Ty.familyMember i` is an occurrence of member `i`. -/
  | familyMember {i : Nat} : OccursIn i (.familyMember i)
  /-- A shape mentions a member when one of its children does. -/
  | shape {i : Nat} {s : TyShape Ty} : OccursSomeIn i s.children → OccursIn i (.shape s)

/-- `Ty.OccursSomeIn i ts`: one of the trees `ts` mentions member `i`. -/
inductive OccursSomeIn : Nat → List Ty → Prop where
  /-- The first of them does. -/
  | head {i : Nat} {t : Ty} {ts : List Ty} : OccursIn i t → OccursSomeIn i (t :: ts)
  /-- A later one does. -/
  | tail {i : Nat} {t : Ty} {ts : List Ty} : OccursSomeIn i ts → OccursSomeIn i (t :: ts)

end

/-- `Ty.MembersOccur k ts`: each of the members `0, …, k-1` is mentioned somewhere in the
    trees `ts`.  This is what makes a family a family rather than a `mutual` block of
    declarations that happen to be written together. -/
inductive MembersOccur : Nat → List Ty → Prop where
  /-- No member has to be mentioned. -/
  | zero {ts : List Ty} : MembersOccur 0 ts
  /-- Members below `k` are mentioned, and so is member `k`. -/
  | succ {k : Nat} {ts : List Ty} :
      MembersOccur k ts → OccursSomeIn k ts → MembersOccur (k + 1) ts

/-! ## Inhabitation: a type that has values

`Ty.HabIn S t` reads: the tree `t` describes a type that **has a value**, given that
member `i` of the scope `t` is written in has one for each `i ∈ S`.

The list `S` is what makes this a least fixpoint rather than a circular argument.  A
binder is checked with `S = []` — nothing about the declaration being defined is assumed,
which is exactly "`F ∅` has a value" — and a family grows `S` one member at a time
(`Ty.FamKnown`), so `A = B`, `B = Nat` is accepted in two rounds and `A = B`, `B = A` is
not accepted at all.

What has a value at each shape: a terminal type and an enum always; an array always, since
the empty array is one; a thunk or a lazy value when what it delays has one; a function
when its *result* has one (the constant function), whatever its domain; a record when all
of its fields have one; a sum when *some* constructor's fields all have one. -/

mutual

/-- `Ty.HabIn S t`: `t` has a value, given that every member listed in `S` has one.  See
    this section's header. -/
inductive HabIn : List Nat → Ty → Prop where
  /-- The declaration being defined has a value only where that is assumed. -/
  | self {S : List Nat} : 0 ∈ S → HabIn S .self
  /-- A member of the family has a value only where that is assumed. -/
  | familyMember {S : List Nat} {i : Nat} : i ∈ S → HabIn S (.familyMember i)
  /-- A shape has a value when its shape does. -/
  | shape {S : List Nat} {s : TyShape Ty} : HabShapeIn S s → HabIn S (.shape s)
  /-- A recursive sum has a value when one of its constructors can be built without
      assuming that the sum itself has one. -/
  | recTaggedUnion {S : List Nat} {l : LeanTaggedUnionSchema Ty} :
      HabSomeIn [] l.toList → HabIn S (.recTaggedUnion l)
  /-- A recursive record has a value when all of its fields do, without assuming that the
      record itself has one. -/
  | recObject {S : List Nat} {fs : LeanRecordSchema Ty} :
      HabAllIn [] fs.toList → HabIn S (.recObject fs)
  /-- A recursive newtype has a value when its body does, without assuming that the
      newtype itself has one. -/
  | recAlias {S : List Nat} {b : Ty} : HabIn [] b → HabIn S (.recAlias b)
  /-- A family has values when every one of its members does. -/
  | mutualRecursiveFamily {S : List Nat} {f : LeanMutualRecFamily Ty} :
      FamHab f.members → HabIn S (.mutualRecursiveFamily f)

/-- `Ty.HabIn`, on one shape. -/
inductive HabShapeIn : List Nat → TyShape Ty → Prop where
  /-- Every terminal type has values — a type with one value is erased before it becomes
      one, and a type with none is not one. -/
  | prim {S : List Nat} {p : LeanPrimTy} : HabShapeIn S (.prim p)
  /-- An enum has at least three constructors. -/
  | enum {S : List Nat} {e : LeanEnumSchema} : HabShapeIn S (.enum e)
  /-- The constant function: only the result has to have a value. -/
  | fn {S : List Nat} {a b : Ty} : HabIn S b → HabShapeIn S (.fn a b)
  /-- The empty array is a value of every array type. -/
  | array {S : List Nat} {t : Ty} : HabShapeIn S (.primCovariant (.array t))
  /-- A delayed value has to be a value. -/
  | thunk {S : List Nat} {t : Ty} : HabIn S t → HabShapeIn S (.primCovariant (.thunk t))
  /-- A delayed value has to be a value. -/
  | lazy {S : List Nat} {t : Ty} : HabIn S t → HabShapeIn S (.primCovariant (.lazy t))
  /-- Every field of a record. -/
  | record {S : List Nat} {fs : LeanRecordSchema Ty} :
      HabAllIn S fs.toList → HabShapeIn S (.record fs)
  /-- Some constructor of a sum. -/
  | taggedUnion {S : List Nat} {l : LeanTaggedUnionSchema Ty} :
      HabSomeIn S l.toList → HabShapeIn S (.taggedUnion l)

/-- `Ty.HabIn`, on every type of a list: the fields of one constructor. -/
inductive HabAllIn : List Nat → List Ty → Prop where
  /-- A constructor with no fields is a value on its own. -/
  | nil {S : List Nat} : HabAllIn S []
  /-- The first one and the rest. -/
  | cons {S : List Nat} {t : Ty} {ts : List Ty} :
      HabIn S t → HabAllIn S ts → HabAllIn S (t :: ts)

/-- `Ty.HabSomeIn S cs`: some constructor of `cs` — a list of the field types of each
    constructor — can be built. -/
inductive HabSomeIn : List Nat → List (List Ty) → Prop where
  /-- This one can. -/
  | head {S : List Nat} {c : List Ty} {cs : List (List Ty)} :
      HabAllIn S c → HabSomeIn S (c :: cs)
  /-- A later one can. -/
  | tail {S : List Nat} {c : List Ty} {cs : List (List Ty)} :
      HabSomeIn S cs → HabSomeIn S (c :: cs)

/-- `Ty.MemberHab S m`: this member of a family has a value, given `S`. -/
inductive MemberHab : List Nat → LeanFamMemberSchema Ty → Prop where
  /-- Some constructor of the member. -/
  | ctors {S : List Nat} {l : LeanTaggedUnionSchema Ty} :
      HabSomeIn S l.toList → MemberHab S (.ctors l)
  /-- Every field of the member. -/
  | record {S : List Nat} {fs : LeanRecordSchema Ty} :
      HabAllIn S fs.toList → MemberHab S (.record fs)
  /-- The body of the member. -/
  | alias {S : List Nat} {b : Ty} : HabIn S b → MemberHab S (.alias b)

/-- `Ty.FamKnown ms S`: every member listed in `S` has been shown to have a value, one
    member at a time and each on the strength of the ones before it.  This is the
    iteration of the least fixpoint. -/
inductive FamKnown : List (LeanFamMemberSchema Ty) → List Nat → Prop where
  /-- Nothing is known yet. -/
  | nil {ms : List (LeanFamMemberSchema Ty)} : FamKnown ms []
  /-- Member `i` has a value on the strength of what is known already. -/
  | cons {ms : List (LeanFamMemberSchema Ty)} {S : List Nat} {i : Nat}
      {m : LeanFamMemberSchema Ty} :
      FamKnown ms S → ms[i]? = some m → MemberHab S m → FamKnown ms (i :: S)

/-- `Ty.FamHab ms`: every member of the family has values, in some order of discovery. -/
inductive FamHab : List (LeanFamMemberSchema Ty) → Prop where
  /-- The iteration reached every member. -/
  | mk {ms : List (LeanFamMemberSchema Ty)} {S : List Nat} :
      FamKnown ms S → (∀ i, i < ms.length → i ∈ S) → FamHab ms

end

/-! ## Well-formedness -/

mutual

/-- `Ty.WfIn n t`: `t` is a type of the language, written in a scope of `n` members.  See
    this module's header for what `n` means and for what is and is not checked. -/
inductive WfIn : Nat → Ty → Prop where
  /-- A closed type is a type in every scope: this is the rule that lets a checked type
      be used inside a new declaration without being checked again. -/
  | closed {n : Nat} {t : Ty} : WfIn 0 t → WfIn n t
  /-- `Ty.self` is legal exactly in the scope of a binder that recurses on its own. -/
  | self : WfIn 1 .self
  /-- A member occurrence is legal in a family that has that member. -/
  | familyMember {n i : Nat} : 2 ≤ n → i < n → WfIn n (.familyMember i)
  /-- A shape is well formed when its children are. -/
  | shape {n : Nat} {s : TyShape Ty} : WfShapeIn n s → WfIn n (.shape s)
  /-- A recursive sum: its payload is written in the scope it opens, mentions it, and has
      a constructor that does not. -/
  | recTaggedUnion {n : Nat} {l : LeanTaggedUnionSchema Ty} :
      WfAllIn 1 l.toList.flatten → OccursSomeIn 0 l.toList.flatten →
      HabSomeIn [] l.toList → WfIn n (.recTaggedUnion l)
  /-- A recursive record. -/
  | recObject {n : Nat} {fs : LeanRecordSchema Ty} :
      WfAllIn 1 fs.toList → OccursSomeIn 0 fs.toList → HabAllIn [] fs.toList →
      WfIn n (.recObject fs)
  /-- A recursive newtype. -/
  | recAlias {n : Nat} {b : Ty} :
      WfIn 1 b → OccursIn 0 b → HabIn [] b → WfIn n (.recAlias b)
  /-- A mutual family: every member is written in the scope of the whole family, every
      member of the family is mentioned by it, and every member has values. -/
  | mutualRecursiveFamily {n : Nat} {f : LeanMutualRecFamily Ty} :
      WfAllIn f.members.length (familyTys f) →
      MembersOccur f.members.length (familyTys f) →
      FamHab f.members →
      WfIn n (.mutualRecursiveFamily f)

/-- `Ty.WfIn`, on one shape. -/
inductive WfShapeIn : Nat → TyShape Ty → Prop where
  /-- A terminal type. -/
  | prim {n : Nat} {p : LeanPrimTy} : WfShapeIn n (.prim p)
  /-- An enum. -/
  | enum {n : Nat} {e : LeanEnumSchema} : WfShapeIn n (.enum e)
  /-- A function type.  The **domain** is checked in the closed scope: an occurrence of
      the declaration being defined may not stand to the left of an arrow, which is what
      makes every binder of the language a least fixpoint of a monotone operator. -/
  | fn {n : Nat} {a b : Ty} : WfIn 0 a → WfIn n b → WfShapeIn n (.fn a b)
  /-- An array, a thunk or a lazy value. -/
  | primCovariant {n : Nat} {s : LeanPrimTyCovariant Ty} :
      WfIn n s.val → WfShapeIn n (.primCovariant s)
  /-- A record. -/
  | record {n : Nat} {fs : LeanRecordSchema Ty} :
      WfAllIn n fs.toList → WfShapeIn n (.record fs)
  /-- A tagged union. -/
  | taggedUnion {n : Nat} {l : LeanTaggedUnionSchema Ty} :
      WfAllIn n l.toList.flatten → WfShapeIn n (.taggedUnion l)

/-- `Ty.WfIn`, on a list of types. -/
inductive WfAllIn : Nat → List Ty → Prop where
  /-- No types to check. -/
  | nil {n : Nat} : WfAllIn n []
  /-- The first one and the rest. -/
  | cons {n : Nat} {t : Ty} {ts : List Ty} : WfIn n t → WfAllIn n ts → WfAllIn n (t :: ts)

end

/-- `Ty.Wf t`: `t` is the tree of a **closed** type — one that mentions no declaration
    outside itself.  This is what a `LeanScript.LeanScriptTyWf` instance carries. -/
abbrev Wf (t : Ty) : Prop := WfIn 0 t

/-! ## A checked type has values

A type that has been checked can be dropped into the payload of a new declaration, and the
new declaration's inhabitation condition has to be discharged for it.  `Ty.HabIn.of_wf`
is what discharges it: a closed type has values, so nothing about it is looked at a second
time.  This is the inhabitation counterpart of `Ty.WfIn.closed`, and it is a theorem
rather than a rule so that `Ty.HabIn` is a definition in its own right. -/

/-- A list is all types exactly when each of its elements is one, so facts about sublists,
    concatenations and flattenings follow from the `List` membership lemmas. -/
theorem WfAllIn.iff_forall {n : Nat} {ts : List Ty} : WfAllIn n ts ↔ ∀ t ∈ ts, WfIn n t := by
  induction ts with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => .nil⟩
  | cons t ts ih =>
      constructor
      · intro h; cases h with
        | cons ht hs => exact List.forall_mem_cons.2 ⟨ht, ih.1 hs⟩
      · intro h
        have h' := List.forall_mem_cons.1 h
        exact .cons h'.1 (ih.2 h'.2)

/-- A list of fields all has values exactly when each of its elements has. -/
theorem HabAllIn.iff_forall {S : List Nat} {ts : List Ty} :
    HabAllIn S ts ↔ ∀ t ∈ ts, HabIn S t := by
  induction ts with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => .nil⟩
  | cons t ts ih =>
      constructor
      · intro h; cases h with
        | cons ht hs => exact List.forall_mem_cons.2 ⟨ht, ih.1 hs⟩
      · intro h
        have h' := List.forall_mem_cons.1 h
        exact .cons h'.1 (ih.2 h'.2)

/-- **A closed type has values.**  Every rule of `Ty.WfIn` that builds a binder carries
    the binder's own inhabitation condition, and every other rule preserves inhabitation,
    so a tree that is a closed type has a value in every scope. -/
theorem HabIn.of_wf {S : List Nat} {t : Ty} (h : Wf t) : HabIn S t := by
  have key : ∀ {n : Nat} {u : Ty}, WfIn n u → n = 0 → HabIn S u := by
    intro n u hu
    induction hu using Ty.WfIn.rec
      (motive_2 := fun n s _ => n = 0 → HabShapeIn S s)
      (motive_3 := fun n ts _ => n = 0 → HabAllIn S ts) with
    | closed _ ih => intro _; exact ih rfl
    | self => intro hn; omega
    | familyMember h2 _ => intro hn; omega
    | shape _ ih => intro hn; exact .shape (ih hn)
    | recTaggedUnion _ _ hh _ => intro _; exact .recTaggedUnion hh
    | recObject _ _ hh _ => intro _; exact .recObject hh
    | recAlias _ _ hh _ => intro _; exact .recAlias hh
    | mutualRecursiveFamily _ _ hh _ => intro _; exact .mutualRecursiveFamily hh
    | prim _ => exact .prim
    | enum _ => exact .enum
    | fn _ _ _ ihb hn => exact .fn (ihb hn)
    | @primCovariant _ s _ ih hn =>
        cases s with
        | array _ => exact .array
        | thunk _ => exact .thunk (ih hn)
        | lazy _ => exact .lazy (ih hn)
    | record _ ih hn => exact .record (ih hn)
    | @taggedUnion _ l _ ih hn =>
        have hall := ih hn
        cases l with
        | payloadFirst _ _ _ =>
            exact .taggedUnion (.head (HabAllIn.iff_forall.2 fun _ ht =>
              HabAllIn.iff_forall.1 hall _ (List.mem_append_left _ ht)))
        | skip _ => exact .taggedUnion (.head .nil)
    | nil _ => exact .nil
    | cons _ _ ih1 ih2 hn => exact .cons (ih1 hn) (ih2 hn)
  exact key h rfl

end Ty

end LeanScript

end
