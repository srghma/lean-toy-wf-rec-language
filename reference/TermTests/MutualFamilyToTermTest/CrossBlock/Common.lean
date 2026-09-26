module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `mutualRecursiveFamily_rec k` on a family whose members hold **another family**

The members of this `mutual` block hold values of `A` and `B`, the members of the other
`mutual` block of `TermTests/MutualFamilyToTermTest/Common.lean`:

```lean
mutual
  inductive C where
    | leaf (a : A)
    | node (d : D)
  inductive D where
    | mk (c : C) (b : B)
end
```

For the fold of `C`/`D`, a field of type `A` or `B` does not mention the family: it is a
plain field, whose tree is the *whole* other family (`Ty.mutualRecursiveFamily`, closed),
nested inside this family's tree.  A branch may do anything with such a field that a
term may do with a value of `A` or `B`:

* fold it — a call of a function on `A`, which is then a `mutualRecursiveFamily_rec` of
  `A`/`B` inside the branch of the `mutualRecursiveFamily_rec` of `C`/`D`.  The function
  is written `@[inline]`, as any function a term calls without declaring it in the
  signature (`LeanScript/ToTerm/Overview.lean`);
* take it apart — a call of a function that matches on it (`aHead`, `bHead`), which is
  a `mutualRecursiveFamily_casesOn` of `A` inside the branch.  (A `match` on the field
  written directly in the branch of a recursive function is not translated: Lean's
  compilation passes the recursion's history through that `match`.)

One file per depth, `K0.lean` … `K4.lean`, checked as in
`TermTests/MutualFamilyToTermTest/Common.lean`.
-/

namespace TermTests.MutualFamilyToTerm.CrossBlock

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

mutual
  /-- A `C`: a chain of `A` links, or a `D`. -/
  inductive C where
    /-- A value of the other family. -/
    | leaf (a : A)
    /-- A `D`. -/
    | node (d : D)
  /-- A `D`: a `C` and a chain of `B` links.  One constructor of two fields, so a record
      member. -/
  inductive D where
    /-- The `C` and the `B` chain. -/
    | mk (c : C) (b : B)
end

deriving instance LeanScriptTyWf for C
deriving instance LeanScriptTyWf for D

/-- The type of a `C`, in the language. -/
abbrev cT : TyWf := tyWfOf C
/-- The type of a `D`, in the language. -/
abbrev dT : TyWf := tyWfOf D

-- the derived tree of `C`: its `leaf` holds the closed tree of `A`, the whole other
-- family, selecting `A`
-- [SKIPPED BY PROFILE_LAKE] example : tyOf C = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨tyOf A, []⟩ [.familyMember 1] []))
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.familyMember 0, tyOf B, []⟩) []) := rfl

mutual
/-- The sum of the labels of an `A` chain, callable from a term (it is `@[inline]`). -/
@[inline] def aSum : A → Nat
  | .stop => 0
  | .next l b => l + bSum b
/-- The sum of the labels of a `B` chain. -/
@[inline] def bSum : B → Nat
  | .stop => 0
  | .next l a => l + aSum a
end

mutual
/-- The number of links of an `A` chain, callable from a term. -/
@[inline] def aLen : A → Nat
  | .stop => 0
  | .next _ b => bLen b + 1
/-- The number of links of a `B` chain. -/
@[inline] def bLen : B → Nat
  | .stop => 0
  | .next _ a => aLen a + 1
end

/-- The label of the first link of an `A` chain (`0` for `stop`), callable from a term: a
    `match`, so a `mutualRecursiveFamily_casesOn` of `A`. -/
@[inline] def aHead : A → Nat
  | .stop => 0
  | .next l _ => l

/-- The label of the first link of a `B` chain (`0` for `stop`). -/
@[inline] def bHead : B → Nat
  | .stop => 0
  | .next l _ => l

/-- A `C` of `n` nodes: `node (mk (node (mk … (leaf stop) …) b₁) b₀)`, where the `B`
    chain of the node at height `i + 1` is the single link labelled `i`. -/
def C.chain : Nat → C
  | 0 => .leaf .stop
  | n + 1 => .node (.mk (C.chain n) (.next n .stop))

/-- `C.chain`, as a term: a `nat_rec` building values of both families. -/
def chain_term : Term sigAdd [] (natT ⇒ cT) := #leanscript_to_term C.chain

/-- `C.chain n`, as a value of the language. -/
def chainOf (n : Nat) : TyWf.Den cT := runAdd chain_term n

/-- A `C` written out. -/
def c1 : C :=
  .node (.mk (.node (.mk (.leaf (.next 1 (.next 2 .stop))) (.next 5 (.next 6 .stop))))
    (.next 7 .stop))

/-- `c1`, as a term: `mutualRecursiveFamily_mk`s of both families, one inside the other. -/
def c1_term : Term sigAdd [] cT := #leanscript_to_term c1

/-- A `D` written out. -/
def d1 : D := .mk (.leaf (.next 3 (.next 4 (.next 5 .stop)))) (.next 1 .stop)

/-- `d1`, as a term. -/
def d1_term : Term sigAdd [] dT := #leanscript_to_term d1

end TermTests.MutualFamilyToTerm.CrossBlock

end
