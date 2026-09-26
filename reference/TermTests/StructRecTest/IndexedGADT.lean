module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Inductive families indexed by **types**, and indices a look rules out

```lean
inductive TExpr : Type → Type 1 where
  | nat (n : Nat) : TExpr Nat
  | add (a b : TExpr Nat) : TExpr Nat
  | pair {α β : Type} (a : TExpr α) (b : TExpr β) : TExpr (α × β)
  | fst {α β : Type} (p : TExpr (α × β)) : TExpr α
```

is a typed expression language (a GADT).  Its constructors `pair` and `fst` have type fields
`α` and `β`, but no value of the constructor depends on them: they appear only in the
indices of the occurrences of `TExpr` (`TExpr α`, `TExpr (α × β)`), which the language
erases, and in the constructor's own index.  So they hide nothing, and `deriving
LeanScriptTyWf` erases them like any other type: `TExpr α` is the recursive tagged union
`nat (n : Nat) | add self self | pair self self | fst self` at every `α` (checked below).

A structural recursion on it (`TExpr.brecOn`, whose motive mentions the index) is
`recTaggedUnion_rec k`: the type fields are Lean variables of each branch and not
variables of the language, and a look into a subvalue (`add (nat m) b`) does not choose a
branch of the language by a type index.

A type field that a value *does* depend on (`lit {α} (x : α) : TExpr α`) is still an
existential, and refused as a tree (`TermTests/StructRecTest/ExistentialUnion.lean` translates
functions of such a datatype when it is not recursive).  A function whose *answer's* type is
the index (`eval : TExpr α → α`) has no term: the language's type of its answers would change
with the index.

The last section is about a family indexed by a value, `V : Nat → Type`, whose recursion
looks into a field of type `V 0`: the constructor `neg : V 1` cannot be there, and its branch
of the language — never taken on a value of the Lean type — holds a default of the answer's
type.

Each program is checked by running the term, against fixed numbers and against the Lean
definition (`kernel_rfl`). -/

namespace TermTests.StructRec.IndexedGADT

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-! ## `TExpr`: an expression language indexed by the Lean type of its values -/

/-- Typed expressions: numbers, sums, pairs and first projections. -/
inductive TExpr : Type → Type 1 where
  /-- A number. -/
  | nat (n : Nat) : TExpr Nat
  /-- A sum of two numbers. -/
  | add (a b : TExpr Nat) : TExpr Nat
  /-- A pair. -/
  | pair {α β : Type} (a : TExpr α) (b : TExpr β) : TExpr (α × β)
  /-- The first component of a pair. -/
  | fst {α β : Type} (p : TExpr (α × β)) : TExpr α
  deriving LeanScriptTyWf

/-- The type of `TExpr α`, in the language: the same at every `α`. -/
abbrev exT : TyWf := tyWfOf (TExpr Nat)

-- [SKIPPED BY PROFILE_LAKE] example : tyOf (TExpr (Nat × Bool)) = tyOf (TExpr Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf (TExpr Nat) =
-- [SKIPPED BY PROFILE_LAKE]     .recTaggedUnion (.payloadFirst ⟨.prim .nat, []⟩ [.self, .self] [[.self, .self], [.self]]) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

/-- `fst (pair (3 + 4) 5)`. -/
def ex1 : TExpr Nat := .fst (.pair (.add (.nat 3) (.nat 4)) (.nat 5))

def ex1_term : Term sigAdd [] exT := #leanscript_to_term ex1

/-- The number of nodes. -/
def TExpr.size : {α : Type} → TExpr α → Nat
  | _, .nat _ => 1
  | _, .add a b => a.size + b.size + 1
  | _, .pair a b => a.size + b.size + 1
  | _, .fst p => p.size + 1

def size_term : Term sigAdd [] (exT ⇒ natT) := #leanscript_to_term @TExpr.size

-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd ex1_term) = 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd size_term (runAdd ex1_term) = ex1.size := by kernel_rfl

/-- The sum of the literals. -/
def TExpr.lits : {α : Type} → TExpr α → Nat
  | _, .nat n => n
  | _, .add a b => a.lits + b.lits
  | _, .pair a b => a.lits + b.lits
  | _, .fst p => p.lits

def lits_term : Term sigAdd [] (exT ⇒ natT) := #leanscript_to_term @TExpr.lits

-- [SKIPPED BY PROFILE_LAKE] example : runAdd lits_term (runAdd ex1_term) = 12 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lits_term (runAdd ex1_term) = ex1.lits := by kernel_rfl

/-- Every literal doubled: the motive `TExpr α` mentions the index, and is the same type of
    the language at every index. -/
def TExpr.double : {α : Type} → TExpr α → TExpr α
  | _, .nat n => .nat (2 * n)
  | _, .add a b => .add a.double b.double
  | _, .pair a b => .pair a.double b.double
  | _, .fst p => .fst p.double

def double_term : Term sigAdd [] (exT ⇒ exT) := #leanscript_to_term @TExpr.double

-- [SKIPPED BY PROFILE_LAKE] example : runAdd lits_term (runAdd double_term (runAdd ex1_term)) = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd lits_term (runAdd double_term (runAdd ex1_term)) = ex1.double.lits := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- The literals that are the left operand of a sum: a look into the subvalue `a`, whose
    index `Nat` does not choose a branch of the language (depth `1`). -/
def TExpr.addLits : {α : Type} → TExpr α → Nat
  | _, .add (.nat m) b => m + b.addLits
  | _, .add a b => a.addLits + b.addLits
  | _, .nat _ => 0
  | _, .pair a b => a.addLits + b.addLits
  | _, .fst p => p.addLits

def addLits_term : Term sigAdd [] (exT ⇒ natT) := #leanscript_to_term @TExpr.addLits

/-- `(1 + 2) + (3 + 4)`, in a pair. -/
def ex2 : TExpr (Nat × Nat) :=
  .pair (.add (.add (.nat 1) (.nat 2)) (.add (.nat 3) (.nat 4))) (.nat 9)

def ex2_term : Term sigAdd [] exT := #leanscript_to_term ex2

-- [SKIPPED BY PROFILE_LAKE] example : runAdd addLits_term (runAdd ex2_term) = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd addLits_term (runAdd ex2_term) = ex2.addLits := by kernel_rfl

/-- Is it a literal: a plain `match` with a wildcard. -/
def TExpr.isLit : {α : Type} → TExpr α → Bool
  | _, .nat _ => true
  | _, _ => false

def isLit_term : Term sigAdd [] (exT ⇒ .prim .bool) := #leanscript_to_term @TExpr.isLit

-- [SKIPPED BY PROFILE_LAKE] example : runAdd isLit_term (runAdd ex1_term) = false := by kernel_rfl

/-! ### What stays refused -/

/-- A literal of any modelled type: `x : α` depends on the type field. -/
inductive LitExpr : Type → Type 1 where
  /-- A literal. -/
  | lit {α : Type} (x : α) : LitExpr α
  /-- A pair. -/
  | pair {α β : Type} (a : LitExpr α) (b : LitExpr β) : LitExpr (α × β)

/--
error: the type `TermTests.StructRec.IndexedGADT.LitExpr` has no `Ty`: existential typing is not yet supported, `α` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for LitExpr

/-- The value of an expression, whose type is the index. -/
def TExpr.eval : {α : Type} → TExpr α → α
  | _, .nat n => n
  | _, .add a b => a.eval + b.eval
  | _, .pair a b => (a.eval, b.eval)
  | _, .fst p => p.eval.1

/--
error: `#leanscript_to_term`: TermTests.StructRec.IndexedGADT.TExpr.brecOn is used with a dependent motive, which the language has no eliminator for
-/
#guard_msgs in
def eval_term := #leanscript_to_term (sig := sigAdd) (@TExpr.eval Nat)

/-! ## `V`: a look at an index that rules a constructor out -/

/-- Sums of numbers at index `0`, and a negation at index `1`. -/
inductive V : Nat → Type where
  /-- A number. -/
  | nat (n : Nat) : V 0
  /-- A sum. -/
  | add (a b : V 0) : V 0
  /-- A negation, of another index. -/
  | neg (a : V 0) : V 1
  deriving LeanScriptTyWf

/-- The literals that are the left operand of a sum.  The look into `a : V 0` finds `nat`,
    `add` or — in the language, never on a Lean value — `neg`, whose branch holds `0`. -/
def V.addLits : {n : Nat} → V n → Nat
  | _, .add (.nat m) b => m + b.addLits
  | _, .add a b => a.addLits + b.addLits
  | _, .nat _ => 0
  | _, .neg a => a.addLits

def vAddLits_term : Term sigAdd [] (natT ⇒ tyWfOf (V 0) ⇒ natT) := #leanscript_to_term @V.addLits

/-- `3 + (4 + ((1 + 2) + 5))`. -/
def v1 : V 0 := .add (.nat 3) (.add (.nat 4) (.add (.add (.nat 1) (.nat 2)) (.nat 5)))

def v1_term : Term sigAdd [] (tyWfOf (V 0)) := #leanscript_to_term v1

-- `3 + 4 + 1`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd vAddLits_term 0 (runAdd v1_term) = 8 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd vAddLits_term 0 (runAdd v1_term) = v1.addLits := by kernel_rfl

end TermTests.StructRec.IndexedGADT

end
