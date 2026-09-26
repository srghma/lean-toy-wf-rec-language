module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Folds deeper than the old search limits

The translation reads the depth `k` of a fold off the compiled recursion by trying
`k = 0, 1, 2, …`.  The search used to stop at `16` for `nat_rec`, `8` for
`recObject_rec`/`recAlias_rec` and `6` for `recTaggedUnion_rec`/`mutualRecursiveFamily_rec`.
The bounds are now options (`LeanScript/ToTerm/Options.lean`), with larger defaults —
`64`, `24`, `16` and `16` — and any of them can be raised further with `set_option`:

* `leanscript.toTerm.maxNatRecDepth` (`nat_rec k`, `array_rec k`),
* `leanscript.toTerm.maxRecObjectRecDepth` (`recObject_rec k`, `recAlias_rec k`),
* `leanscript.toTerm.maxRecUnionRecDepth` (`recTaggedUnion_rec k`),
* `leanscript.toTerm.maxRecFamilyRecDepth` (`mutualRecursiveFamily_rec k`).

Each program below is deeper than the old limit of its fold.  It is checked to be a fold of
the expected depth and to compute what the Lean definition computes, and, with the option
lowered back to the old limit (before the program is translated, so that nothing comes
from the translation cache), to be refused. -/

namespace TermTests.StructRec.Deep

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- The depth of the outermost fold of a translated function, under the `fun`s of its
    arguments. -/
def foldDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .nat_rec k _ _ _ _ => some k
  | .array_rec k _ _ _ _ => some k
  | .recTaggedUnion_rec k _ _ _ => some k
  | .recObject_rec k _ _ _ => some k
  | .recAlias_rec k _ _ _ => some k
  | .mutualRecursiveFamily_rec k _ _ _ => some k
  | .letE c body => (foldDepth?.comp c).orElse fun _ => foldDepth? body
  | .letJ jp body => (foldDepth? body).orElse fun _ => foldDepth? jp
  | _ => none

/-- `foldDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def foldDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => foldDepth? b
  | _ => none
end

/-! ## `nat_rec 17` and `nat_rec 24` (old limit `16`) -/

/-- Reads its value `18` steps back and `1` step back. -/
def lag18 : Nat → Nat
  | n + 18 => lag18 n + lag18 (n + 17)
  | _ => 1

-- with the old bound, the same program is refused
set_option leanscript.toTerm.maxNatRecDepth 16 in
example : Term sigAdd [] (natT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term lag18
  exact .lam (.nat_mk 0)

def lag18_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term lag18

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? lag18_term = some 17 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lag18_term 20 = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lag18_term 40 = lag18 40 := by kernel_rfl

/-- Reads its value `25` steps back. -/
def lag25 : Nat → Nat
  | n + 25 => lag25 n + 1
  | _ => 0

def lag25_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term lag25

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? lag25_term = some 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lag25_term 60 = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lag25_term 77 = lag25 77 := by kernel_rfl

/-! ## `recObject_rec 9` (old limit `8`) -/

/-- A chain of labelled cells, a recursive record. -/
inductive Cell where
  | mk (label : Nat) (next : Option Cell)
  deriving LeanScriptTyWf

/-- The type of a chain of cells, in the language. -/
abbrev cellT : TyWf := tyWfOf Cell

/-- `n + 1` cells labelled `n, …, 0`. -/
def Cell.ofNat : Nat → Cell
  | 0 => .mk 0 none
  | n + 1 => .mk (n + 1) (some (Cell.ofNat n))

def cellOfNat_term : Term sigAdd [] (natT ⇒ cellT) := #leanscript_to_term Cell.ofNat

/-- The label and the answer ten cells down. -/
def Cell.tenth : Cell → Nat
  | .mk a (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (c)))))))))))))))))))) =>
      a + c.tenth
  | .mk a _ => a

-- with the old bound, the same program is refused
set_option leanscript.toTerm.maxRecObjectRecDepth 8 in
example : Term sigAdd [] (cellT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term Cell.tenth
  exact .lam (.nat_mk 0)

def tenth_term : Term sigAdd [] (cellT ⇒ natT) := #leanscript_to_term Cell.tenth

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? tenth_term = some 9 := by kernel_rfl
-- `25 + 15 + 5`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tenth_term (runAdd cellOfNat_term 25) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd tenth_term (runAdd cellOfNat_term 31) = (Cell.ofNat 31).tenth := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `recAlias_rec 9` (old limit `8`) -/

/-- One link: the end, or a label and the rest. -/
inductive Link (α : Type) where
  | stop
  | step (label : Nat) (rest : α)
  deriving LeanScriptTyWf

/-- A chain of links, a recursive newtype. -/
inductive Chain where
  | mk (link : Link Chain)
  deriving LeanScriptTyWf

/-- The type of a chain, in the language. -/
abbrev chainT : TyWf := tyWfOf Chain

/-- `n` links labelled `n, …, 1`. -/
def Chain.ofNat : Nat → Chain
  | 0 => .mk .stop
  | n + 1 => .mk (.step (n + 1) (Chain.ofNat n))

def chainOfNat_term : Term sigAdd [] (natT ⇒ chainT) := #leanscript_to_term Chain.ofNat

/-- The label and the answer ten links down. -/
def Chain.tenth : Chain → Nat
  | .mk (.step a (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (.mk (.step _ (c)))))))))))))))))))) =>
      a + c.tenth
  | .mk (.step a _) => a
  | .mk .stop => 0

def chainTenth_term : Term sigAdd [] (chainT ⇒ natT) := #leanscript_to_term Chain.tenth

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? chainTenth_term = some 9 := by kernel_rfl
-- `25 + 15 + 5`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTenth_term (runAdd chainOfNat_term 25) = 45 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd chainTenth_term (runAdd chainOfNat_term 33) = (Chain.ofNat 33).tenth := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `recTaggedUnion_rec 7` (old limit `6`) -/

/-- A binary tree, a recursive tagged union. -/
inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)
  deriving LeanScriptTyWf

/-- The type of a tree, in the language. -/
abbrev treeT : TyWf := tyWfOf Tree

/-- The left spine of `n` nodes, labelled `n, …, 1` from the top. -/
def Tree.leftSpine : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (Tree.leftSpine n) (n + 1) .leaf

def leftSpine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.leftSpine

/-- The label and the answer eight levels down the left spine: seven looks. -/
def leftEighth : Tree → Nat
  | .node (.node (.node (.node (.node (.node (.node (.node a _ _) _ _) _ _) _ _) _ _) _ _)
      _ _) v _ => v + leftEighth a
  | _ => 0

-- with the old bound, the same program is refused
set_option leanscript.toTerm.maxRecUnionRecDepth 6 in
example : Term sigAdd [] (treeT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term leftEighth
  exact .lam (.nat_mk 0)

-- the depth search up to `7` needs more than the default heartbeats
set_option maxHeartbeats 800000 in
def leftEighth_term : Term sigAdd [] (treeT ⇒ natT) := #leanscript_to_term leftEighth

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? leftEighth_term = some 7 := by kernel_rfl
-- `20 + 12`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftEighth_term (runAdd leftSpine_term 20) = 32 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd leftEighth_term (runAdd leftSpine_term 27) =
-- [SKIPPED BY PROFILE_LAKE]     leftEighth (Tree.leftSpine 27) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `mutualRecursiveFamily_rec 7` (old limit `6`) -/

mutual
/-- Even levels of an alternating spine. -/
inductive ESpine where
  | stop
  | step (v : Nat) (next : OSpine)
/-- Odd levels of an alternating spine. -/
inductive OSpine where
  | stop
  | step (v : Nat) (next : ESpine)
end
deriving instance LeanScriptTyWf for ESpine, OSpine

/-- The type of an even spine, in the language. -/
abbrev espineT : TyWf := tyWfOf ESpine

mutual
/-- `n` levels, labelled `n, …, 1`, starting on an even one. -/
def ESpine.ofNat : Nat → ESpine
  | 0 => .stop
  | n + 1 => .step (n + 1) (OSpine.ofNat n)
/-- `n` levels, labelled `n, …, 1`, starting on an odd one. -/
def OSpine.ofNat : Nat → OSpine
  | 0 => .stop
  | n + 1 => .step (n + 1) (ESpine.ofNat n)
end

def espineOfNat_term : Term sigAdd [] (natT ⇒ espineT) := #leanscript_to_term ESpine.ofNat

/-- The label and the answer eight levels down: seven looks. -/
def ESpine.eighth : ESpine → Nat
  | .step v (.step _ (.step _ (.step _ (.step _ (.step _ (.step _ (.step _ (e)))))))) =>
      v + e.eighth
  | .step v _ => v
  | .stop => 0

-- with the old bound, the same program is refused
set_option leanscript.toTerm.maxRecFamilyRecDepth 6 in
example : Term sigAdd [] (espineT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term ESpine.eighth
  exact .lam (.nat_mk 0)

def eighth_term : Term sigAdd [] (espineT ⇒ natT) := #leanscript_to_term ESpine.eighth

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? eighth_term = some 7 := by kernel_rfl
-- `20 + 12 + 4`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eighth_term (runAdd espineOfNat_term 20) = 36 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd eighth_term (runAdd espineOfNat_term 26) = (ESpine.ofNat 26).eighth := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end TermTests.StructRec.Deep

end
