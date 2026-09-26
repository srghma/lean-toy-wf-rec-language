module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recAlias_rec k` on a recursive newtype whose body is a **structure**

```lean
inductive Pair2 where
  | mk (p : Nat × Option Pair2)
```

is a recursive newtype (one constructor, one field) whose body is the structure
`Nat × Option Pair2` rather than a union.  Its tree is
`Ty.recAlias (record ⟨nat, none | some self⟩)` (checked below), and a structural recursion on
it is `recAlias_rec k`: the branch takes the body's record apart, then dispatches on the
`Option` inside it (`LeanScript.ToTerm.TransRecObject`).

The same holds for a body that nests unions and structures more deeply
(`Tri | mk (Option (Nat × Option Tri × Bool))`) and for a recursive record one of whose
fields is such a structure (`PCell | mk (tag : Nat) (rest : Nat × Option PCell)`).

A body that is a structure declared by the user (`Pair3 | mk (Cell Pair3)`) is in
`TermTests.StructRec.NewtypeUserStruct`.

Each program is checked three ways: the translation is a `recAlias_rec` (or
`recObject_rec`) of the expected depth, the term computes the expected numbers, and the term
computes what the Lean definition computes (`kernel_rfl`). -/

namespace TermTests.StructRec.NewtypeStruct

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- The depth of the `recAlias_rec` or `recObject_rec` a translated function is, under
    the `fun`s of its arguments. -/
def foldDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .recAlias_rec k _ _ _ => some k
  | .recObject_rec k _ _ _ => some k
  | .letE c body => (foldDepth?.comp c).orElse fun _ => foldDepth? body
  | .letJ jp body => (foldDepth? body).orElse fun _ => foldDepth? jp
  | _ => none

/-- `foldDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def foldDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => foldDepth? b
  | _ => none
end

/-! ## `Pair2`: a chain of labels, the body a pair -/

/-- A recursive newtype whose body is a structure. -/
inductive Pair2 where
  /-- The one constructor, of one field. -/
  | mk (p : Nat × Option Pair2)
  deriving LeanScriptTyWf

/-- The type of `Pair2`, in the language. -/
abbrev pair2T : TyWf := tyWfOf Pair2

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Pair2 =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.record ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩) := rfl

/-- The chain of `n + 1` labels `n, n - 1, …, 0`. -/
def Pair2.ofNat : Nat → Pair2
  | 0 => .mk (0, none)
  | n + 1 => .mk (n + 1, some (Pair2.ofNat n))

/-- `Pair2.ofNat`, as a term: a `nat_rec` that builds with `recAlias_mk`. -/
def ofNat_term : Term sigAdd [] (natT ⇒ pair2T) := #leanscript_to_term Pair2.ofNat

/-- The chain `Pair2.ofNat n`, as a value of the language. -/
def pair2Of (n : Nat) : TyWf.Den pair2T := runAdd ofNat_term n

/-- The sum of the labels. -/
def Pair2.sum : Pair2 → Nat
  | .mk (n, none) => n
  | .mk (n, some p) => n + p.sum

def sum_term : Term sigAdd [] (pair2T ⇒ natT) := #leanscript_to_term Pair2.sum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? sum_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (pair2Of 4) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (pair2Of 7) = (Pair2.ofNat 7).sum := by kernel_rfl

/-- The number of labels. -/
def Pair2.len : Pair2 → Nat
  | .mk (_, none) => 1
  | .mk (_, some p) => p.len + 1

def len_term : Term sigAdd [] (pair2T ⇒ natT) := #leanscript_to_term Pair2.len

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? len_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd len_term (pair2Of 5) = 6 := by kernel_rfl

/-- Reads the label one link down, beside the answer there. -/
def Pair2.adjProd : Pair2 → Nat
  | .mk (_, none) => 0
  | .mk (a, some (.mk (b, none))) => a * b
  | .mk (a, some (.mk (b, some p))) => a * b + (Pair2.mk (b, some p)).adjProd

def adjProd_term : Term sigAdd [] (pair2T ⇒ natT) := #leanscript_to_term Pair2.adjProd

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? adjProd_term = some 1 := by kernel_rfl
-- `4*3 + 3*2 + 2*1 + 1*0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd adjProd_term (pair2Of 4) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd adjProd_term (pair2Of 6) = (Pair2.ofNat 6).adjProd := by kernel_rfl

/-- The labels two links down, beside the answer there: depth `1`. -/
def Pair2.skipSum : Pair2 → Nat
  | .mk (a, some (.mk (_, some p))) => a + p.skipSum
  | .mk (a, _) => a

def skipSum_term : Term sigAdd [] (pair2T ⇒ natT) := #leanscript_to_term Pair2.skipSum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? skipSum_term = some 1 := by kernel_rfl
-- `6 + 4 + 2 + 0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd skipSum_term (pair2Of 6) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd skipSum_term (pair2Of 9) = (Pair2.ofNat 9).skipSum := by kernel_rfl

/-! ## `Tri`: unions and structures nested three deep -/

/-- A newtype whose body is a union of a structure that holds a union. -/
inductive Tri where
  /-- The one constructor. -/
  | mk (b : Option (Nat × Option Tri × Bool))
  deriving LeanScriptTyWf

/-- The type of `Tri`, in the language. -/
abbrev triT : TyWf := tyWfOf Tri

/-- `n + 1` nodes, the flag alternating from `b` at the top. -/
def Tri.ofNat : Nat → Bool → Tri
  | 0, _ => .mk none
  | n + 1, b => .mk (some (n, some (Tri.ofNat n (if b then false else true)), b))

def triOfNat_term : Term sigAdd [] (natT ⇒ .prim .bool ⇒ triT) :=
  #leanscript_to_term Tri.ofNat

/-- The sum of the flagged labels. -/
def Tri.flagged : Tri → Nat
  | .mk none => 0
  | .mk (some (n, none, b)) => if b then n else 0
  | .mk (some (n, some t, b)) => (if b then n else 0) + t.flagged

def flagged_term : Term sigAdd [] (triT ⇒ natT) := #leanscript_to_term Tri.flagged

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? flagged_term = some 0 := by kernel_rfl
-- labels `4, 3, 2, 1, 0`, flagged `true, false, true, false, true`: `4 + 2 + 0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd flagged_term (runAdd triOfNat_term 5 true) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd flagged_term (runAdd triOfNat_term 8 false) =
-- [SKIPPED BY PROFILE_LAKE]     (Tri.ofNat 8 false).flagged := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## A recursive record one of whose fields is a structure around it -/

/-- A recursive record whose second field is `Nat × Option PCell`. -/
inductive PCell where
  /-- The one constructor. -/
  | mk (tag : Nat) (rest : Nat × Option PCell)
  deriving LeanScriptTyWf

/-- The type of `PCell`, in the language. -/
abbrev pcellT : TyWf := tyWfOf PCell

-- [SKIPPED BY PROFILE_LAKE] example : tyOf PCell = .recObject ⟨.prim .nat,
-- [SKIPPED BY PROFILE_LAKE]     .record ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩, []⟩ := rfl

def PCell.ofNat : Nat → PCell
  | 0 => .mk 0 (1, none)
  | n + 1 => .mk (n + 1) (2, some (PCell.ofNat n))

def pcellOfNat_term : Term sigAdd [] (natT ⇒ pcellT) := #leanscript_to_term PCell.ofNat

/-- `tag * weight`, summed. -/
def PCell.weighted : PCell → Nat
  | .mk t (w, none) => t * w
  | .mk t (w, some c) => t * w + c.weighted

def weighted_term : Term sigAdd [] (pcellT ⇒ natT) := #leanscript_to_term PCell.weighted

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? weighted_term = some 0 := by kernel_rfl
-- `2 * (3 + 2 + 1) + 0 * 1`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd weighted_term (runAdd pcellOfNat_term 3) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd weighted_term (runAdd pcellOfNat_term 6) = (PCell.ofNat 6).weighted := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.StructRec.NewtypeStruct

end
