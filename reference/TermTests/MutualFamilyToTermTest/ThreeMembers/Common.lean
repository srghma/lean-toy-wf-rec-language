module

public import TermTests.MutualFamilyToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `mutualRecursiveFamily_rec k` on a family of **three** members

`TermTests/MutualFamilyToTermTest/K0.lean` … `K4.lean` fold families of two members.
These files fold a family of three, whose occurrences go round in a cycle:

```lean
mutual
  inductive X where | stop | next (label : Nat) (y : Y)
  inductive Y where | stop | next (label : Nat) (z : Z)
  inductive Z where | stop | next (label : Nat) (x : X)
end
```

so a program that reads `k + 1` links down passes through all three members, in turn,
and its branch for an `X` link looks into a `Y` link, then a `Z` link, then an `X` link
again.  `K0.lean` also folds `M1`/`M2`/`M3` below, a family of three members of the
three different shapes a member can have (constructors, a record, a newtype).

One file per depth, `K0.lean` … `K3.lean`.  Each program is checked three ways, as in
`TermTests/MutualFamilyToTermTest/Common.lean`: the translated term is a
`mutualRecursiveFamily_rec` of the expected depth, it computes the expected numbers, and
it computes what the Lean definition computes (on chains built by translated programs,
and on written-out chains).  Every depth also has programs of two and three arguments,
before and after the chain.
-/

namespace TermTests.MutualFamilyToTerm.ThreeMembers

open LeanScript TermTests.NatRecDepth TermTests.MutualFamilyToTerm

mutual
  /-- A chain that starts with an `X` link. -/
  inductive X where
    /-- The end of the chain. -/
    | stop
    /-- A label, and the rest of the chain, which starts with a `Y` link. -/
    | next (label : Nat) (y : Y)
  /-- A chain that starts with a `Y` link. -/
  inductive Y where
    /-- The end of the chain. -/
    | stop
    /-- A label, and the rest of the chain, which starts with a `Z` link. -/
    | next (label : Nat) (z : Z)
  /-- A chain that starts with a `Z` link. -/
  inductive Z where
    /-- The end of the chain. -/
    | stop
    /-- A label, and the rest of the chain, which starts with an `X` link. -/
    | next (label : Nat) (x : X)
end

deriving instance LeanScriptTyWf for X
deriving instance LeanScriptTyWf for Y
deriving instance LeanScriptTyWf for Z

mutual
  /-- The first member of a family of three shapes: it has constructors. -/
  inductive M1 where
    /-- The end. -/
    | done
    /-- One more step, an `M2`. -/
    | step (r : M2)
  /-- The second member: one constructor of two fields, so a record. -/
  inductive M2 where
    /-- A label and an `M3`. -/
    | mk (label : Nat) (n : M3)
  /-- The third member: one constructor of one field, so a newtype. -/
  inductive M3 where
    /-- An `M1`, wrapped. -/
    | wrap (m : M1)
end

deriving instance LeanScriptTyWf for M1
deriving instance LeanScriptTyWf for M2
deriving instance LeanScriptTyWf for M3

/-- The type of an `X` chain, in the language. -/
abbrev xT : TyWf := tyWfOf X
/-- The type of a `Y` chain, in the language. -/
abbrev yT : TyWf := tyWfOf Y
/-- The type of a `Z` chain, in the language. -/
abbrev zT : TyWf := tyWfOf Z
/-- The type of an `M1`, in the language. -/
abbrev m1T : TyWf := tyWfOf M1

-- the derived trees: one family of three members, each selecting itself
-- [SKIPPED BY PROFILE_LAKE] example : tyOf X = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 1]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.prim .nat, [.familyMember 2]⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     [.ctors (.skip (.here ⟨.prim .nat, [.familyMember 0]⟩ []))]) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf M1 = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 1, []⟩ [])))
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.prim .nat, .familyMember 2, []⟩)
-- [SKIPPED BY PROFILE_LAKE]     [.alias (.familyMember 0)]) := rfl

/-- An `X` chain of `n` links, labelled `n - 1, …, 1, 0` from the top. -/
def X.ofNat : Nat → X
  | 0 => .stop
  | 1 => .next 0 .stop
  | 2 => .next 1 (.next 0 .stop)
  | n + 3 => .next (n + 2) (.next (n + 1) (.next n (X.ofNat n)))

/-- A `Y` chain of `n` links, labelled `n - 1, …, 1, 0` from the top. -/
def Y.ofNat : Nat → Y
  | 0 => .stop
  | 1 => .next 0 .stop
  | 2 => .next 1 (.next 0 .stop)
  | n + 3 => .next (n + 2) (.next (n + 1) (.next n (Y.ofNat n)))

/-- `X.ofNat`, as a term: a `nat_rec` whose branch builds three links with
    `mutualRecursiveFamily_mk`. -/
def xOfNat_term : Term sigAdd [] (natT ⇒ xT) := #leanscript_to_term X.ofNat

/-- `Y.ofNat`, as a term. -/
def yOfNat_term : Term sigAdd [] (natT ⇒ yT) := #leanscript_to_term Y.ofNat

/-- The `X` chain of `n` links, as a value of the language. -/
def xOfNat (n : Nat) : TyWf.Den xT := runAdd xOfNat_term n

/-- The `Y` chain of `n` links, as a value of the language. -/
def yOfNat (n : Nat) : TyWf.Den yT := runAdd yOfNat_term n

/-- An `X` chain written out. -/
def x7 : X := .next 3 (.next 1 (.next 4 (.next 1 (.next 5 (.next 9 (.next 2 .stop))))))

/-- `x7`, as a term: nested `mutualRecursiveFamily_mk`s of all three members. -/
def x7_term : Term sigAdd [] xT := #leanscript_to_term x7

/-- A `Y` chain written out. -/
def y5 : Y := .next 2 (.next 7 (.next 1 (.next 8 (.next 2 .stop))))

/-- `y5`, as a term. -/
def y5_term : Term sigAdd [] yT := #leanscript_to_term y5

/-- An `M1` written out: three steps, labelled `4`, `5`, `6`. -/
def m1Three : M1 := .step (.mk 4 (.wrap (.step (.mk 5 (.wrap (.step (.mk 6 (.wrap .done))))))))

/-- `m1Three`, as a term. -/
def m1Three_term : Term sigAdd [] m1T := #leanscript_to_term m1Three

end TermTests.MutualFamilyToTerm.ThreeMembers

end
