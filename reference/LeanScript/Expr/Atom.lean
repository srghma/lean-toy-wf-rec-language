module
public import LeanScript.Expr.NatRecCtx
public import LeanScript.Expr.Extern
public import LeanScript.Ty.Unfold
public import LeanScript.Ty.TyWfIn
public import LeanScript.Ty.Wf
public meta import LeanScript.CtorTag

@[expose] public section

set_option autoImplicit false

/-!
# Atoms: the operands of an A-normal term

`LeanScript.Term` is in **A-normal form by construction**: every operand of a
computation — the function and the argument of an application, the value a `casesOn` or a
fold takes apart, the arguments of an extern, the fields of a constructor, the elements of
an array — is an **atom**, never a computation.  An intermediate value is always *named*
by a `let` (`LeanScript.Term.letE`) before it is used.

An atom is a **variable**, and nothing else: evaluating it does no work, so it may be
duplicated or moved freely.  A reference to a top-level declaration, and a literal, are
computation steps (`LeanScript.Comp`), bound by a `let` like any other.  This file
holds atoms and the lists of them the grammar uses; it has no term in it, so it sits
before the `mutual` block of `LeanScript.Expr.Term`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- **An atom**: an operand that needs no computation, which in this language is exactly a
    **variable** of `Γ`.  A reference to a top-level declaration and a literal are *not*
    atoms: each is a computation step of its own (`LeanScript.Comp.global`,
    `LeanScript.Comp.nat_mk`, …) and is named by a `let` before it is used, so an operand
    is always something already in the environment. -/
inductive Atom : Ctx → TyWf → Type
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → Atom Γ τ

/-- A list of atoms, typed by the list of their types: the arguments of an extern, the
    fields of a constructor, the base values of a fold. -/
inductive Args (Sg : Sig) : Ctx → List TyWf → Type
  /-- No more arguments. -/
  | nil : ∀ {Γ}, Args Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Atom Γ σ → Args Sg Γ σs → Args Sg Γ (σ :: σs)

/-- The operands of a value of one member of a mutual recursive family: the family has the
    same three cases as `LeanScript.LeanFamMemberSchema`, and the type says which of them
    a member is.  The member it is indexed by is the **unfolded** one, so a field written
    `Ty.familyMember i` is a value of member `i`. -/
inductive FamilyMemberArgs (Sg : Sig) : Ctx → LeanFamMemberSchema TyWf → Type
  /-- A member with constructors: constructor `t` of it, and that constructor's
      fields. -/
  | ctors {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Args Sg Γ (l.get t ht)) :
      FamilyMemberArgs Sg Γ (.ctors l)
  /-- A record member: its fields, in declaration order. -/
  | record {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Args Sg Γ fs.toList) :
      FamilyMemberArgs Sg Γ (.record fs)
  /-- A newtype member: a value of its body, whose wrapper is erased. -/
  | alias {Γ : Ctx} (b : TyWf) (value : Atom Γ b) : FamilyMemberArgs Sg Γ (.alias b)

/-! ## Join points -/

/-- The join points in scope, by the type of their one parameter.  A join point is a
    continuation *inside* a function body — what follows a dispatch or a fold whose value
    is used — so it answers with the type of that body, and it lives in this context of its
    own, apart from the variables (`Ctx`): it is not a value, and it can only be jumped
    to, from tail position. -/
abbrev JCtx := List TyWf

/-- **Where the answer of a fold goes.**  A fold is a tail: it is the last thing its block
    does, so its answer is either the value of the whole term (`ret`, when the fold answers
    with the term's own type), or the argument of a jump to a join point (`jump`). -/
inductive Dest : JCtx → TyWf → TyWf → Type
  /-- The answer is the value of the term. -/
  | ret : ∀ {J : JCtx} {τ : TyWf}, Dest J τ τ
  /-- The answer is passed to the join point `j`. -/
  | jump : ∀ {J : JCtx} {ρ τ : TyWf}, J ∋ ρ → Dest J ρ τ

end LeanScript

end
