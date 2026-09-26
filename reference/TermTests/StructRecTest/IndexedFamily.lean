module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Structural recursion on **indexed families**

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

is an inductive family with an index.  `deriving LeanScriptTyWf` gives it one tree for every
index — the index is erased from the type, and a constructor's value index (`{n : Nat}` of
`cons`) is an ordinary field — so `Vec α n` is the recursive tagged union
`nil | cons (n : Nat) (a : α) (v : self)` whatever `n` is (checked below).

A function on it takes the index as an ordinary argument (`{n : Nat} → Vec Nat n → …` is a
term of `nat ⇒ vec ⇒ …`), and:

* a structural recursion on the vector (`Vec.brecOn`) is `recTaggedUnion_rec k`: the
  branch is read at each constructor with the indices that constructor has, and a look
  into the tail `v : Vec α n` sets the field `n` to the index of the constructor found
  there (`Vec.adj` below, depth `1`);
* a motive that mentions the index (`Vec Nat n` for `Vec.map`, `(m : Nat) → Vec Nat m → …`
  for `Vec.append`) is accepted when the type of the language it denotes does not depend
  on the index — it is the same tree at every index;
* a structural recursion on the index that builds a vector (`Vec.ofNat : (n : Nat) → Vec
  Nat n`) is a `nat_rec` whose motive mentions the index, the same way;
* a plain `match` (`Vec.casesOn`, with the equations between the indices a `match` carries)
  is `recTaggedUnion_casesOn`; a constructor the index rules out (`nil` for a value of
  `Vec Nat (n + 1)`, in `Vec.head`) is a branch of the language that a value of the Lean
  type never takes, and holds the `default` of the answer's type;
* a second vector of the same length, taken apart beside the one recursed on
  (`Vec.zipSum`), is dispatched on in the branch of the fold.

The same holds for other indices: `Fin'` (indexed by `Nat`, no value field) and a typed
expression language `Ex : Code → Type` indexed by a user-defined enumeration.

Each program is checked two ways: the term computes the expected numbers, and it computes
what the Lean definition computes (`kernel_rfl`). -/

namespace TermTests.StructRec.IndexedFamily

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

mutual
/-- The depth of the `recTaggedUnion_rec` a translated function is, under the `fun`s of its
    arguments. -/
def foldDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .recTaggedUnion_rec k _ _ _ => some k
  | .letE c body => (foldDepth?.comp c).orElse fun _ => foldDepth? body
  | .letJ jp body => (foldDepth? body).orElse fun _ => foldDepth? jp
  | _ => none

/-- `foldDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def foldDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => foldDepth? b
  | _ => none
end

/-! ## `Vec`: vectors indexed by their length -/

/-- Vectors of a known length. -/
inductive Vec (α : Type) : Nat → Type where
  /-- The empty vector. -/
  | nil : Vec α 0
  /-- One more element. -/
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
  deriving LeanScriptTyWf

/-- The type of `Vec Nat n`, in the language: the same at every length. -/
abbrev vecT : TyWf := tyWfOf (Vec Nat 0)

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Vec Nat 3) = tyOf (Vec Nat 0) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (Vec Nat 3) =
-- [SKIPPED BY PROFILE_LAKE]     .recTaggedUnion (.skip (.here ⟨.prim .nat, [.prim .nat, .self]⟩ [])) := rfl

/-- `n - 1, …, 1, 0`: a recursion on the index that builds a vector of that length. -/
def Vec.ofNat : (n : Nat) → Vec Nat n
  | 0 => .nil
  | n + 1 => .cons n (Vec.ofNat n)

def ofNat_term : Term sigAdd [] (natT ⇒ vecT) := #leanscript_to_term Vec.ofNat

/-- The vector `Vec.ofNat n`, as a value of the language. -/
def vecOf (n : Nat) : TyWf.Den vecT := runAdd ofNat_term n

/-- The sum of the elements. -/
def Vec.sum : {n : Nat} → Vec Nat n → Nat
  | _, .nil => 0
  | _, .cons a v => a + v.sum

def sum_term : Term sigAdd [] (natT ⇒ vecT ⇒ natT) := #leanscript_to_term @Vec.sum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? sum_term = some 0 := by kernel_rfl
-- `4 + 3 + 2 + 1 + 0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term 5 (vecOf 5) = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term 7 (vecOf 7) = (Vec.ofNat 7).sum := by kernel_rfl

/-- Each element weighted by its position from the end: the index at each node is the
    field `n` of its constructor. -/
def Vec.idxSum : {n : Nat} → Vec Nat n → Nat
  | _, .nil => 0
  | n + 1, .cons a v => n * a + v.idxSum

def idxSum_term : Term sigAdd [] (natT ⇒ vecT ⇒ natT) := #leanscript_to_term @Vec.idxSum

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? idxSum_term = some 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd idxSum_term 5 (vecOf 5) = (Vec.ofNat 5).idxSum := by kernel_rfl

/-- The length, which is the index. -/
def Vec.len : {n : Nat} → Vec Nat n → Nat
  | n, _ => n

def len_term : Term sigAdd [] (natT ⇒ vecT ⇒ natT) := #leanscript_to_term @Vec.len

-- [SKIPPED BY PROFILE_LAKE] example : runAdd len_term 4 (vecOf 4) = 4 := by kernel_rfl

/-- Reads the element one link down, beside the answer there: depth `1`, and the look into
    the tail sets its length. -/
def Vec.adj : {n : Nat} → Vec Nat n → Nat
  | _, .nil => 0
  | _, .cons _ .nil => 0
  | _, .cons a (.cons b v) => a * b + (Vec.cons b v).adj

def adj_term : Term sigAdd [] (natT ⇒ vecT ⇒ natT) := #leanscript_to_term @Vec.adj

-- [SKIPPED BY PROFILE_LAKE] example : foldDepth? adj_term = some 1 := by kernel_rfl
-- `4*3 + 3*2 + 2*1 + 1*0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd adj_term 5 (vecOf 5) = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd adj_term 6 (vecOf 6) = (Vec.ofNat 6).adj := by kernel_rfl

/-- A map: the motive `Vec Nat n` mentions the index. -/
def Vec.map : {n : Nat} → (Nat → Nat) → Vec Nat n → Vec Nat n
  | _, _, .nil => .nil
  | _, f, .cons a v => .cons (f a) (v.map f)

def map_term : Term sigAdd [] (natT ⇒ (natT ⇒ natT) ⇒ vecT ⇒ vecT) :=
  #leanscript_to_term @Vec.map

-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term 5 (runAdd map_term 5 (fun x => x + 1) (vecOf 5)) = 15 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The elements, as a list. -/
def Vec.toList : {n : Nat} → Vec Nat n → List Nat
  | _, .nil => []
  | _, .cons a v => a :: v.toList

def toList_term : Term sigAdd [] (natT ⇒ vecT ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term @Vec.toList

/-- Appending: the motive is the dependent function type `(m : Nat) → Vec Nat m →
    Vec Nat (m + n)`, which is `nat ⇒ vec ⇒ vec` at every index. -/
def Vec.append : {n m : Nat} → Vec Nat n → Vec Nat m → Vec Nat (m + n)
  | _, _, .nil, w => w
  | _, _, .cons a v, w => .cons a (Vec.append v w)

def append_term : Term sigAdd [] (natT ⇒ natT ⇒ vecT ⇒ vecT ⇒ vecT) :=
  #leanscript_to_term @Vec.append

-- `(2 + 1 + 0) + (3 + 2 + 1 + 0)`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd sum_term 7 (runAdd append_term 3 4 (vecOf 3) (vecOf 4)) = 9 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The inner product of two vectors of the same length: the second is taken apart in the
    branch of the fold on the first. -/
def Vec.zipSum : {n : Nat} → Vec Nat n → Vec Nat n → Nat
  | _, .nil, .nil => 0
  | _, .cons a v, .cons b w => a * b + Vec.zipSum v w

def zipSum_term : Term sigAdd [] (natT ⇒ vecT ⇒ vecT ⇒ natT) :=
  #leanscript_to_term @Vec.zipSum

-- `3*3 + 2*2 + 1*1 + 0*0`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd zipSum_term 4 (vecOf 4) (vecOf 4) = 14 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd zipSum_term 5 (vecOf 5) (runAdd map_term 5 (· * 2) (vecOf 5)) =
-- [SKIPPED BY PROFILE_LAKE]     Vec.zipSum (Vec.ofNat 5) ((Vec.ofNat 5).map (· * 2)) := by kernel_rfl

/-! ### Plain `match`es -/

/-- Is the vector empty? -/
def Vec.isEmpty : {n : Nat} → Vec Nat n → Bool
  | _, .nil => true
  | _, .cons _ _ => false

def isEmpty_term : Term sigAdd [] (natT ⇒ vecT ⇒ .prim .bool) :=
  #leanscript_to_term @Vec.isEmpty

-- [SKIPPED BY PROFILE_LAKE] example : runAdd isEmpty_term 0 (vecOf 0) = true := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd isEmpty_term 3 (vecOf 3) = false := by kernel_rfl

/-- The first element of a vector that has one: `nil` is ruled out by the index, and its
    branch of the language, never taken, holds `default`. -/
def Vec.head : {n : Nat} → Vec Nat (n + 1) → Nat
  | _, .cons a _ => a

def head_term : Term sigAdd [] (natT ⇒ vecT ⇒ natT) := #leanscript_to_term @Vec.head

-- [SKIPPED BY PROFILE_LAKE] example : runAdd head_term 4 (vecOf 5) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd head_term 6 (vecOf 7) = (Vec.ofNat 7).head := by kernel_rfl

/-- The first elements of two vectors of the same length, multiplied. -/
def Vec.firstProd : {n : Nat} → Vec Nat n → Vec Nat n → Nat
  | _, .nil, .nil => 0
  | _, .cons a _, .cons b _ => a * b

def firstProd_term : Term sigAdd [] (natT ⇒ vecT ⇒ vecT ⇒ natT) :=
  #leanscript_to_term @Vec.firstProd

-- [SKIPPED BY PROFILE_LAKE] example : runAdd firstProd_term 4 (vecOf 4) (vecOf 4) = 9 := by kernel_rfl

/-! ## `Fin'`: an index and no value field -/

/-- The numbers below an index. -/
inductive Fin' : Nat → Type where
  /-- Zero, below any successor. -/
  | zero {n : Nat} : Fin' (n + 1)
  /-- One more. -/
  | succ {n : Nat} (i : Fin' n) : Fin' (n + 1)
  deriving LeanScriptTyWf

/-- The number. -/
def Fin'.val : {n : Nat} → Fin' n → Nat
  | _, .zero => 0
  | _, .succ i => i.val + 1

def val_term : Term sigAdd [] (natT ⇒ tyWfOf (Fin' 0) ⇒ natT) := #leanscript_to_term @Fin'.val

/-- `k` below `k + 1`. -/
def Fin'.ofNat : (k : Nat) → Fin' (k + 1)
  | 0 => .zero
  | k + 1 => .succ (Fin'.ofNat k)

def finOfNat_term : Term sigAdd [] (natT ⇒ tyWfOf (Fin' 0)) := #leanscript_to_term Fin'.ofNat

-- [SKIPPED BY PROFILE_LAKE] example : runAdd val_term 7 (runAdd finOfNat_term 6) = 6 := by kernel_rfl

/-! ## `Ex`: a typed expression language, indexed by a user-defined enumeration -/

/-- The types of the expression language. -/
inductive Code where
  | num
  | bool
  deriving LeanScriptTyWf

/-- Expressions, indexed by their type. -/
inductive Ex : Code → Type where
  | lit (k : Nat) : Ex .num
  | tt : Ex .bool
  | ff : Ex .bool
  | add (a b : Ex .num) : Ex .num
  | ite (c : Ex .bool) (t e : Ex .num) : Ex .num
  deriving LeanScriptTyWf

/-- The number of nodes. -/
def Ex.size : {c : Code} → Ex c → Nat
  | _, .lit _ => 1
  | _, .tt => 1
  | _, .ff => 1
  | _, .add a b => a.size + b.size + 1
  | _, .ite c t e => c.size + t.size + e.size + 1

def size_term : Term sigAdd [] (tyWfOf Code ⇒ tyWfOf (Ex .num) ⇒ natT) :=
  #leanscript_to_term @Ex.size

/-- A sample expression. -/
def sample : Ex .num := .ite .tt (.add (.lit 1) (.lit 2)) (.lit 5)

def sample_term : Term sigAdd [] (tyWfOf (Ex .num)) := #leanscript_to_term sample

/-- The index `Code.num`. -/
def numCode : Code := .num

/-- The index `Code.num`, as a term (the index is an ordinary argument). -/
def num_term : Term sigAdd [] (tyWfOf Code) := #leanscript_to_term numCode

-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd num_term) (runAdd sample_term) = 6 := by kernel_rfl

/-- The sum of the literals. -/
def Ex.lits : {c : Code} → Ex c → Nat
  | _, .lit k => k
  | _, .tt => 0
  | _, .ff => 0
  | _, .add a b => a.lits + b.lits
  | _, .ite c t e => c.lits + t.lits + e.lits

def lits_term : Term sigAdd [] (tyWfOf Code ⇒ tyWfOf (Ex .num) ⇒ natT) :=
  #leanscript_to_term @Ex.lits

-- [SKIPPED BY PROFILE_LAKE] example : runAdd lits_term (runAdd num_term) (runAdd sample_term) = sample.lits := by kernel_rfl

end TermTests.StructRec.IndexedFamily

end
