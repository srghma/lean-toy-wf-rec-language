module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # A `mutual` block whose members also occur nested

```lean
mutual
  inductive P where
    | leaf (n : Nat)
    | node (q : Option Q)
  inductive Q where
    | mk (a : P) (b : P)
end
```

`Q` occurs in `P` *inside* `Option`.  Lean folds this block with **three** motives — `P`,
`Q` and the auxiliary type `Option Q` — so `deriving LeanScriptTyWf` now hoists `Option Q`
into a third member of the family (`LeanScript.Deriving.hoistAux`), in the order of the
recursor's motives, and gives `Option Q` an instance selecting that member.  The family is
then the one the recursor folds, and a structural recursion on it is
`mutualRecursiveFamily_rec k` (`LeanScript.ToTerm.TransRecFamily`).

The same happens for a structure around a member (`Nat × B`), and for a single declaration
that is a family because it recurses through `List` and that also holds an `Option` of
itself.  A lone declaration with only non-recursive wrappers around itself (`Cell | mk Nat
(Option Cell)`) keeps its old tree, a recursive record. -/

namespace TermTests.StructRec.MutualNested

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- The depth of the outermost fold of a translated function. -/
def foldDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .mutualRecursiveFamily_rec k _ _ _ => some k
  | .letE c body => (foldDepth?.comp c).orElse fun _ => foldDepth? body
  | .letJ jp body => (foldDepth? body).orElse fun _ => foldDepth? jp
  | _ => none

/-- `foldDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def foldDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => foldDepth? b
  | _ => none
end

/-! ## `Option Q` inside `P` -/

mutual
/-- A leaf, or a node holding perhaps a `Q`. -/
inductive P where
  | leaf (n : Nat)
  | node (q : Option Q)
/-- Two `P`s. -/
inductive Q where
  | mk (a : P) (b : P)
end
deriving instance LeanScriptTyWf for P, Q

/-- The type of a `P`, in the language. -/
abbrev pT : TyWf := tyWfOf P

-- member `2` is `Option Q`: `none | some (member 1)`, and `P.node` holds it
-- [SKIPPED BY PROFILE_LAKE] example : tyOf P = .mutualRecursiveFamily (.selectedThenMore []
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 2] []))
-- [SKIPPED BY PROFILE_LAKE]     (.record ⟨.familyMember 0, .familyMember 0, []⟩)
-- [SKIPPED BY PROFILE_LAKE]     [.ctors (.skip (.here ⟨.familyMember 1, []⟩ []))]) := rfl

-- `Option Q` is that member too
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Option Q) = .mutualRecursiveFamily (.selectedLast
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 2] []))
-- [SKIPPED BY PROFILE_LAKE]     [.record ⟨.familyMember 0, .familyMember 0, []⟩]
-- [SKIPPED BY PROFILE_LAKE]     (.ctors (.skip (.here ⟨.familyMember 1, []⟩ [])))) := rfl

/-- A balanced `P` of depth `n`, leaves labelled `1`. -/
def P.full : Nat → P
  | 0 => .leaf 1
  | n + 1 => .node (some (.mk (P.full n) (P.full n)))

def pFull_term : Term sigAdd [] (natT ⇒ pT) := #leanscript_to_term P.full

/-- A `P` written out. -/
def p1 : P := .node (some (.mk (.leaf 3) (.node (some (.mk (.leaf 4) (.node none))))))

def p1_term : Term sigAdd [] pT := #leanscript_to_term p1

mutual
/-- The sum of the leaves. -/
def P.sum : P → Nat
  | .leaf n => n
  | .node none => 0
  | .node (some q) => q.sum
/-- The sum of the leaves. -/
def Q.sum : Q → Nat
  | .mk a b => a.sum + b.sum
end

def pSum_term : Term sigAdd [] (pT ⇒ natT) := #leanscript_to_term P.sum

-- `P.sum` does not recurse on `Option Q` itself (its motive there is `PUnit`), so the
-- branch at `P.node` looks through that member into the `Q` below: depth `1`
-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? pSum_term = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd p1_term) = 7 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd p1_term) = p1.sum := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd pFull_term 4) = 16 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pSum_term (runAdd pFull_term 5) = (P.full 5).sum := by kernel_rfl

mutual
/-- The number of `node none`s. -/
def P.empties : P → Nat
  | .leaf _ => 0
  | .node none => 1
  | .node (some q) => q.empties
/-- The number of `node none`s. -/
def Q.empties : Q → Nat
  | .mk a b => a.empties + b.empties
end

def pEmpties_term : Term sigAdd [] (pT ⇒ natT) := #leanscript_to_term P.empties

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pEmpties_term (runAdd p1_term) = 1 := by kernel_rfl

/-- One function reading through `Q` into the `P`s below: the left leaf of a node's pair,
    two members down. -/
def P.leftLeaves : P → Nat
  | .leaf n => n
  | .node none => 0
  | .node (some (.mk a b)) => a.leftLeaves + b.leftLeaves

def pLeftLeaves_term : Term sigAdd [] (pT ⇒ natT) := #leanscript_to_term P.leftLeaves

-- [SKIPPED BY PROFILE_LAKE] example : runAdd pLeftLeaves_term (runAdd p1_term) = P.leftLeaves p1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd pLeftLeaves_term (runAdd pFull_term 3) = 8 := by kernel_rfl

/-! ## A structure around a member: `Nat × B` inside `A` -/

mutual
/-- The end, or a weight and a `B`. -/
inductive A where
  | stop
  | step (p : Nat × B)
/-- A label and an `A`. -/
inductive B where
  | mk (label : Nat) (a : A)
end
deriving instance LeanScriptTyWf for A, B

/-- The type of an `A`, in the language. -/
abbrev aT : TyWf := tyWfOf A

/-- `n` steps, weights `n, …, 1`, labels `2 n, …, 2`. -/
def A.ofNat : Nat → A
  | 0 => .stop
  | n + 1 => .step (n + 1, .mk (n + n + 2) (A.ofNat n))

def aOfNat_term : Term sigAdd [] (natT ⇒ aT) := #leanscript_to_term A.ofNat

mutual
/-- The sum of the weights and the labels. -/
def A.total : A → Nat
  | .stop => 0
  | .step (w, b) => w + b.total
/-- The sum of the weights and the labels. -/
def B.total : B → Nat
  | .mk l a => l + a.total
end

def aTotal_term : Term sigAdd [] (aT ⇒ natT) := #leanscript_to_term A.total

-- through the member `Nat × B`: depth `1`
-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? aTotal_term = some 1 := by kernel_rfl
-- weights `3 + 2 + 1`, labels `6 + 4 + 2`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTotal_term (runAdd aOfNat_term 3) = 18 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd aTotal_term (runAdd aOfNat_term 6) = (A.ofNat 6).total := by kernel_rfl

/-! ## A lone declaration nested through `List` and `Option` -/

/-- A rose tree whose nodes may also name a favourite child. -/
inductive Fav where
  | node (v : Nat) (kids : List Fav) (fav : Option Fav)
  deriving LeanScriptTyWf

/-- The type of a `Fav`, in the language. -/
abbrev favT : TyWf := tyWfOf Fav

def fav1 : Fav :=
  .node 1 [.node 2 [] none, .node 3 [.node 4 [] none] (some (.node 5 [] none))]
    (some (.node 6 [] none))

def fav1_term : Term sigAdd [] favT := #leanscript_to_term fav1

mutual
/-- The sum of every label, in the children and in the favourites. -/
def Fav.sum : Fav → Nat
  | .node v kids fav => v + Fav.sumList kids + Fav.sumOpt fav
/-- `Fav.sum` of a list. -/
def Fav.sumList : List Fav → Nat
  | [] => 0
  | t :: ts => t.sum + Fav.sumList ts
/-- `Fav.sum` of an option. -/
def Fav.sumOpt : Option Fav → Nat
  | none => 0
  | some t => t.sum
end

def favSum_term : Term sigAdd [] (favT ⇒ natT) := #leanscript_to_term Fav.sum

-- [SKIPPED BY PROFILE_LAKE] example : runAdd favSum_term (runAdd fav1_term) = 21 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd favSum_term (runAdd fav1_term) = fav1.sum := by kernel_rfl

/-! ## A lone declaration with only a non-recursive wrapper keeps its tree -/

/-- A chain of cells. -/
inductive Cell where
  | mk (label : Nat) (next : Option Cell)
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf Cell = .recObject ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩ :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

end TermTests.StructRec.MutualNested

end
