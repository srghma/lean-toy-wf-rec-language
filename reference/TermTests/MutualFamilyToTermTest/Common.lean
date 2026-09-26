module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `mutualRecursiveFamily_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci`, `pentanacci`, … ; the other `…ToTermTest/` directories do the
same for the other folds.  These files do it for
`LeanScript.Term.mutualRecursiveFamily_rec k`, the fold of a **mutual recursive family**,
whose branches may look `k` constructors further down into any member of the family —
into one subvalue after another along a path, or, after one of them, into a sibling
(`TermTests/MutualFamilyToTermTest/BothSubtrees/`).

**Which Lean program is a `mutualRecursiveFamily_rec k`.**  A structural recursion on a
member of a `mutual … end` block of inductive types.  Each member's tree is
`Ty.mutualRecursiveFamily`, selecting that member.  Lean compiles the recursion into
`A.brecOn` (or `B.brecOn`), which takes a branch per member, and the translation
(`LeanScript.ToTerm.TransRecFamily`) reads it as `mutualRecursiveFamily_rec k`.  The
programs are written as ordinary Lean — `mutual … end` blocks of functions, or a single
function that goes *through* the other member — with no annotation and nothing added for
the translation.

The main family is two chains of labelled links that alternate:

```lean
mutual
  inductive A where
    | stop
    | next (label : Nat) (b : B)
  inductive B where
    | stop
    | next (label : Nat) (a : A)
end
```

and the depth-`k` programs are the Fibonacci-like recursions of
`TermTests/NatRecDepthTest/` on the number of links, written as a pair of mutual
functions.  `K0.lean` also folds two families whose members have other shapes: `Ev`/`Od`
(`Od` has one constructor of one field, so it is a *newtype* member) and `Tm`/`Pr` (`Pr`
has one constructor of two fields, so it is a *record* member).

One file per depth, `K0.lean` … `K4.lean`.  Each program is checked three ways:

* the translated term **is** a `mutualRecursiveFamily_rec` of the expected depth
  (`familyRecDepth?`);
* the term computes the expected numbers;
* the term computes what the Lean definition computes.

The inputs are built by translated Lean programs too: `A.ofNat n` and `B.ofNat n` (a
`nat_rec` whose branch builds links with `mutualRecursiveFamily_mk`) and literal values.

The equations are checked by `kernel_rfl` rather than `rfl`: the elaborator's own check of
such an equation runs out of heartbeats, while the kernel checks it quickly (see
`LeanScript/KernelRfl.lean`).  `kernel_rfl` is still a proof by `Eq.refl`, checked by the
kernel.
-/

namespace TermTests.MutualFamilyToTerm

open LeanScript TermTests.NatRecDepth

mutual
  /-- A chain that starts with an `A` link: the end, or a label and a chain that starts
      with a `B` link. -/
  inductive A where
    /-- The end of the chain. -/
    | stop
    /-- A label, and the rest of the chain. -/
    | next (label : Nat) (b : B)
  /-- A chain that starts with a `B` link. -/
  inductive B where
    /-- The end of the chain. -/
    | stop
    /-- A label, and the rest of the chain. -/
    | next (label : Nat) (a : A)
end

deriving instance LeanScriptTyWf for A
deriving instance LeanScriptTyWf for B

mutual
  /-- Even numbers: zero, or the successor of an odd number. -/
  inductive Ev where
    /-- Zero. -/
    | zero
    /-- The successor of an odd number. -/
    | succ (o : Od)
  /-- Odd numbers: the successor of an even number.  One constructor of one field, so
      this member is a newtype. -/
  inductive Od where
    /-- The successor of an even number. -/
    | succ (e : Ev)
end

deriving instance LeanScriptTyWf for Ev
deriving instance LeanScriptTyWf for Od

mutual
  /-- A term: a number, or a pair of terms. -/
  inductive Tm where
    /-- A number. -/
    | lit (n : Nat)
    /-- A pair of terms. -/
    | pair (p : Pr)
  /-- A pair of terms.  One constructor of two fields, so this member is a record. -/
  inductive Pr where
    /-- The two terms. -/
    | mk (l r : Tm)
end

deriving instance LeanScriptTyWf for Tm
deriving instance LeanScriptTyWf for Pr

/-- The type of an `A` chain, in the language. -/
abbrev aT : TyWf := tyWfOf A

/-- The type of a `B` chain, in the language. -/
abbrev bT : TyWf := tyWfOf B

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

-- The derived trees: one family, each member selecting itself.
-- [SKIPPED BY PROFILE_LAKE] example : tyOf A = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 0]⟩ []))) []) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf B = .mutualRecursiveFamily (.selectedLast
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     [] (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 0]⟩ [])))) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Od = .mutualRecursiveFamily (.selectedLast
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 1, []⟩ []))) [] (.alias (.familyMember 0))) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Pr = .mutualRecursiveFamily (.selectedLast
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 1] []))
-- [SKIPPED BY PROFILE_LAKE]     [] (.record ⟨.familyMember 0, .familyMember 0, []⟩)) := rfl

mutual
/-- The depth of the `mutualRecursiveFamily_rec` a translated function is: the fold under
    the `fun`s of its arguments, applied to the arguments that Lean put in the motive.
    `none` if the translation is not of that shape. -/
def familyRecDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .mutualRecursiveFamily_rec k _ _ _ => some k
  | .letE c body => (familyRecDepth?.comp c).orElse fun _ => familyRecDepth? body
  | .letJ jp body => (familyRecDepth? body).orElse fun _ => familyRecDepth? jp
  | _ => none

/-- `familyRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def familyRecDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => familyRecDepth? b
  | _ => none
end

/-- An `A` chain of `n` links, labelled `n - 1, …, 1, 0` from the top. -/
def A.ofNat : Nat → A
  | 0 => .stop
  | 1 => .next 0 .stop
  | n + 2 => .next (n + 1) (.next n (A.ofNat n))

/-- A `B` chain of `n` links, labelled `n - 1, …, 1, 0` from the top. -/
def B.ofNat : Nat → B
  | 0 => .stop
  | 1 => .next 0 .stop
  | n + 2 => .next (n + 1) (.next n (B.ofNat n))

/-- `A.ofNat`, as a term: a `nat_rec` whose branch builds links with
    `mutualRecursiveFamily_mk`. -/
def aOfNat_term : Term sigAdd [] (natT ⇒ aT) := #leanscript_to_term A.ofNat

/-- `B.ofNat`, as a term. -/
def bOfNat_term : Term sigAdd [] (natT ⇒ bT) := #leanscript_to_term B.ofNat

/-- The `A` chain of `n` links, as a value of the language. -/
def aOfNat (n : Nat) : TyWf.Den aT := runAdd aOfNat_term n

/-- The `B` chain of `n` links, as a value of the language. -/
def bOfNat (n : Nat) : TyWf.Den bT := runAdd bOfNat_term n

/-- An `A` chain written out, as a closed Lean value. -/
def a4 : A := .next 3 (.next 1 (.next 4 (.next 1 .stop)))

/-- `a4`, as a term: nested `mutualRecursiveFamily_mk`s. -/
def a4_term : Term sigAdd [] aT := #leanscript_to_term a4

/-- A `B` chain written out, as a closed Lean value. -/
def b5 : B := .next 2 (.next 7 (.next 1 (.next 8 (.next 2 .stop))))

/-- `b5`, as a term. -/
def b5_term : Term sigAdd [] bT := #leanscript_to_term b5

end TermTests.MutualFamilyToTerm

end
