module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Recursive newtypes whose body is a **user-defined** structure

`TermTests.StructRec.NewtypeStruct` covers a body built from `×` and `Option`
(`Pair2 | mk (Nat × Option Pair2)`).  Here the body is a structure declared by the user,
with the recursive occurrence under one of its fields:

```lean
structure Cell (α : Type) where
  val  : Nat
  next : Option α

inductive Pair3 where
  | mk (c : Cell Pair3)
```

`deriving LeanScriptTyWf` reads `Cell Pair3` from `Cell`'s own model, asked for at a
stand-in parameter.  The fields of that model are the models of other types built from the
parameter (`tyOf (Option α)`), so each of them is translated at the real argument
(`LeanScript.Deriving.expandHoleLeaves`).  `Pair3` gets the same tree as the `×`
version, `Ty.recAlias (record ⟨nat, none | some self⟩)`, and its structural recursions are
`recAlias_rec k`.

Also covered: a structure with two occurrences (`Fork`), a structure nested in a
structure (`Outer`), a newtype with a type parameter (`PL α`), a recursive record and a
union holding such a structure (`RC`, `UC`), and a structure with a `List α` field
(`LCell`), whose `List` becomes one more member of a family.

Each program is checked by running the term in the kernel against fixed numbers and
against the Lean definition (`kernel_rfl`). -/

namespace TermTests.StructRec.NewtypeUserStruct

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

/-! ## `Pair3`: the body is the structure `Cell Pair3` -/

/-- A label and an optional link. -/
structure Cell (α : Type) where
  /-- The label. -/
  val : Nat
  /-- The rest, if any. -/
  next : Option α
  deriving LeanScriptTyWf

/-- A recursive newtype whose body is a user-defined structure. -/
inductive Pair3 where
  /-- The one constructor, of one field. -/
  | mk (c : Cell Pair3)
  deriving LeanScriptTyWf

/-- The type of `Pair3`, in the language. -/
abbrev pair3T : TyWf := tyWfOf Pair3

-- [SKIPPED BY PROFILE_LAKE] /-- The same tree as `Pair2 | mk (Nat × Option Pair2)`. -/
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Pair3 =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.record ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩) := rfl

/-- The chain of `n + 1` labels `n, n - 1, …, 0`. -/
def Pair3.ofNat : Nat → Pair3
  | 0 => .mk ⟨0, none⟩
  | n + 1 => .mk ⟨n + 1, some (Pair3.ofNat n)⟩

def ofNat_term : Term sigAdd [] (natT ⇒ pair3T) := #leanscript_to_term Pair3.ofNat

/-- The chain `Pair3.ofNat n`, as a value of the language. -/
def pair3Of (n : Nat) : TyWf.Den pair3T := runAdd ofNat_term n

/-- The sum of the labels. -/
def Pair3.sum : Pair3 → Nat
  | .mk ⟨v, none⟩ => v
  | .mk ⟨v, some p⟩ => v + p.sum

def sum_term : Term sigAdd [] (pair3T ⇒ natT) := #leanscript_to_term Pair3.sum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? sum_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (pair3Of 4) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (pair3Of 7) = (Pair3.ofNat 7).sum := by kernel_rfl

/-- The first label, read with a projection of the structure. -/
def Pair3.head : Pair3 → Nat
  | .mk c => c.val

def head_term : Term sigAdd [] (pair3T ⇒ natT) := #leanscript_to_term Pair3.head

-- [SKIPPED BY PROFILE_LAKE] example : runAdd head_term (pair3Of 6) = 6 := by kernel_rfl

/-- The labels two links down, beside the answer there: depth `1`. -/
def Pair3.skipSum : Pair3 → Nat
  | .mk ⟨a, some (.mk ⟨_, some p⟩)⟩ => a + p.skipSum
  | .mk ⟨a, _⟩ => a

def skipSum_term : Term sigAdd [] (pair3T ⇒ natT) := #leanscript_to_term Pair3.skipSum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? skipSum_term = some 1 := by kernel_rfl
-- `6 + 4 + 2 + 0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd skipSum_term (pair3Of 6) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd skipSum_term (pair3Of 9) = (Pair3.ofNat 9).skipSum := by kernel_rfl

/-- Adds one to every label: a fold that builds a new chain. -/
def Pair3.inc : Pair3 → Pair3
  | .mk ⟨n, none⟩ => .mk ⟨n + 1, none⟩
  | .mk ⟨n, some p⟩ => .mk ⟨n + 1, some p.inc⟩

def inc_term : Term sigAdd [] (pair3T ⇒ pair3T) := #leanscript_to_term Pair3.inc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd inc_term (pair3Of 4)) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term (runAdd inc_term (pair3Of 5)) = (Pair3.ofNat 5).inc.sum := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- An accumulator: the fold answers with a function. -/
def Pair3.sumAcc : Pair3 → Nat → Nat
  | .mk ⟨n, none⟩, acc => acc + n
  | .mk ⟨n, some p⟩, acc => p.sumAcc (acc + n)

def sumAcc_term : Term sigAdd [] (pair3T ⇒ natT ⇒ natT) := #leanscript_to_term Pair3.sumAcc

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sumAcc_term (pair3Of 5) 100 = 115 := by kernel_rfl

/-! ## `BT`: a structure with two occurrences -/

/-- A label and two optional children. -/
structure Fork (α : Type) where
  /-- The label. -/
  tag : Nat
  /-- The left child, if any. -/
  l : Option α
  /-- The right child, if any. -/
  r : Option α
  deriving LeanScriptTyWf

/-- A binary tree, as a newtype around `Fork`. -/
inductive BT where
  /-- The one constructor. -/
  | mk (f : Fork BT)
  deriving LeanScriptTyWf

/-- The type of `BT`, in the language. -/
abbrev btT : TyWf := tyWfOf BT

/-- The full tree of depth `n`, every label `1`. -/
def BT.full : Nat → BT
  | 0 => .mk ⟨1, none, none⟩
  | n + 1 => .mk ⟨1, some (BT.full n), some (BT.full n)⟩

def full_term : Term sigAdd [] (natT ⇒ btT) := #leanscript_to_term BT.full

/-- The sum of the labels. -/
def BT.size : BT → Nat
  | .mk ⟨t, none, none⟩ => t
  | .mk ⟨t, some l, none⟩ => t + l.size
  | .mk ⟨t, none, some r⟩ => t + r.size
  | .mk ⟨t, some l, some r⟩ => t + l.size + r.size

def size_term : Term sigAdd [] (btT ⇒ natT) := #leanscript_to_term BT.size

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? size_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd full_term 3) = 15 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd full_term 4) = (BT.full 4).size := by kernel_rfl

/-! ## `PO`: a structure nested in a structure -/

/-- A `Cell` beside a flag. -/
structure Outer (α : Type) where
  /-- The cell, which holds the occurrence. -/
  c : Cell α
  /-- The flag. -/
  flag : Bool
  deriving LeanScriptTyWf

/-- A newtype whose body is a structure one of whose fields is a structure. -/
inductive PO where
  /-- The one constructor. -/
  | mk (o : Outer PO)
  deriving LeanScriptTyWf

/-- The type of `PO`, in the language. -/
abbrev poT : TyWf := tyWfOf PO

-- [SKIPPED BY PROFILE_LAKE] example : tyOf PO = .recAlias (.record ⟨
-- [SKIPPED BY PROFILE_LAKE]     .record ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩,
-- [SKIPPED BY PROFILE_LAKE]     .prim .bool, []⟩) := rfl

/-- `n + 1` cells, the flag alternating from `b` at the top. -/
def PO.ofNat : Nat → Bool → PO
  | 0, b => .mk ⟨⟨0, none⟩, b⟩
  | n + 1, b => .mk ⟨⟨n + 1, some (PO.ofNat n (if b then false else true))⟩, b⟩

def poOfNat_term : Term sigAdd [] (natT ⇒ .prim .bool ⇒ poT) := #leanscript_to_term PO.ofNat

/-- The number of flagged cells. -/
def PO.count : PO → Nat
  | .mk ⟨⟨_, none⟩, b⟩ => if b then 1 else 0
  | .mk ⟨⟨_, some p⟩, b⟩ => (if b then 1 else 0) + p.count

def count_term : Term sigAdd [] (poT ⇒ natT) := #leanscript_to_term PO.count

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? count_term = some 0 := by kernel_rfl
-- six cells, flagged `true, false, true, false, true, false`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd count_term (runAdd poOfNat_term 5 true) = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd count_term (runAdd poOfNat_term 8 false) = (PO.ofNat 8 false).count := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-! ## `PL α`: a newtype with a type parameter -/

/-- A chain of cells, over a type parameter it does not use in its body. -/
inductive PL (α : Type) where
  /-- The one constructor. -/
  | mk (c : Cell (PL α))
  deriving LeanScriptTyWf

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (PL Bool) =
-- [SKIPPED BY PROFILE_LAKE]     .recAlias (.record ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩) := rfl

/-- The chain of `n + 1` cells. -/
def PL.ofNat {α : Type} : Nat → PL α
  | 0 => .mk ⟨0, none⟩
  | n + 1 => .mk ⟨n + 1, some (PL.ofNat n)⟩

/-- The number of cells. -/
def PL.len {α : Type} : PL α → Nat
  | .mk ⟨_, none⟩ => 1
  | .mk ⟨_, some p⟩ => p.len + 1

def plOfNat_term := #leanscript_to_term (sig := sigAdd) (PL.ofNat (α := Bool))
def plLen_term := #leanscript_to_term (sig := sigAdd) (PL.len (α := Bool))

-- [SKIPPED BY PROFILE_LAKE] example : runAdd plLen_term (runAdd plOfNat_term 6) = 7 := by kernel_rfl

/-! ## A recursive record and a union holding such a structure -/

/-- A recursive record whose second field is `Cell RC`. -/
inductive RC where
  /-- The one constructor. -/
  | mk (tag : Nat) (rest : Cell RC)
  deriving LeanScriptTyWf

/-- The type of `RC`, in the language. -/
abbrev rcT : TyWf := tyWfOf RC

def RC.ofNat : Nat → RC
  | 0 => .mk 0 ⟨1, none⟩
  | n + 1 => .mk (n + 1) ⟨2, some (RC.ofNat n)⟩

def rcOfNat_term : Term sigAdd [] (natT ⇒ rcT) := #leanscript_to_term RC.ofNat

/-- `tag * weight`, summed. -/
def RC.weighted : RC → Nat
  | .mk t ⟨w, none⟩ => t * w
  | .mk t ⟨w, some c⟩ => t * w + c.weighted

def weighted_term : Term sigAdd [] (rcT ⇒ natT) := #leanscript_to_term RC.weighted

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? weighted_term = some 0 := by kernel_rfl
-- `2 * (3 + 2 + 1) + 0 * 1`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd weighted_term (runAdd rcOfNat_term 3) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd weighted_term (runAdd rcOfNat_term 6) = (RC.ofNat 6).weighted := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- A union one of whose constructors holds `Cell UC`. -/
inductive UC where
  /-- No cell. -/
  | leaf
  /-- A cell. -/
  | node (c : Cell UC)
  deriving LeanScriptTyWf

/-- The type of `UC`, in the language. -/
abbrev ucT : TyWf := tyWfOf UC

def UC.ofNat : Nat → UC
  | 0 => .leaf
  | n + 1 => .node ⟨n, some (UC.ofNat n)⟩

def ucOfNat_term : Term sigAdd [] (natT ⇒ ucT) := #leanscript_to_term UC.ofNat

/-- The number of cells along the chain. -/
def UC.depth : UC → Nat
  | .leaf => 0
  | .node ⟨_, none⟩ => 1
  | .node ⟨_, some u⟩ => u.depth + 1

def depth_term : Term sigAdd [] (ucT ⇒ natT) := #leanscript_to_term UC.depth

-- [SKIPPED BY PROFILE_LAKE] example : runAdd depth_term (runAdd ucOfNat_term 5) = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd depth_term (runAdd ucOfNat_term 7) = (UC.ofNat 7).depth := by kernel_rfl

/-! ## `Rose2`: a structure with a `List α` field

`LCell Rose2` holds `List Rose2`, so the block is nested and `List Rose2` becomes a member
of the family `Rose2`, `LCell Rose2`, `List Rose2`. -/

/-- A label and a list of children. -/
structure LCell (α : Type) where
  /-- The label. -/
  v : Nat
  /-- The children. -/
  kids : List α
  deriving LeanScriptTyWf

/-- A rose tree, as a newtype around `LCell`. -/
inductive Rose2 where
  /-- The one constructor. -/
  | mk (c : LCell Rose2)
  deriving LeanScriptTyWf

/-- The type of `Rose2`, in the language. -/
abbrev rose2T : TyWf := tyWfOf Rose2

/-- A node labelled `n + 1` with the tree for `n` and a leaf `7` below it. -/
def Rose2.build : Nat → Rose2
  | 0 => .mk ⟨0, []⟩
  | n + 1 => .mk ⟨n + 1, [Rose2.build n, .mk ⟨7, []⟩]⟩

def build_term : Term sigAdd [] (natT ⇒ rose2T) := #leanscript_to_term Rose2.build

/-- The sum of the labels. -/
def Rose2.sum : Rose2 → Nat
  | .mk ⟨v, kids⟩ => v + sumL kids
where
  /-- The sum over a list of trees. -/
  sumL : List Rose2 → Nat
  | [] => 0
  | r :: rs => r.sum + sumL rs

def rose2Sum_term : Term sigAdd [] (rose2T ⇒ natT) := #leanscript_to_term Rose2.sum

-- `3 + 2 + 1 + 0` and three leaves `7`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rose2Sum_term (runAdd build_term 3) = 27 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd rose2Sum_term (runAdd build_term 5) = (Rose2.build 5).sum := by kernel_rfl

end TermTests.StructRec.NewtypeUserStruct

end
