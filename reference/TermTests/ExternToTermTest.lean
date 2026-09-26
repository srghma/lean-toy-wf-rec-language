module

public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude
public import LeanScript.Ty.Instances
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# Externs in functions translated by `#leanscript_to_term`

A call of a Lean function implemented by a pure extern of `Init` is translated to the
entry of the catalogue `LeanScript.LeanInitPureExtern` that models it:

* with arguments known only when the term runs, to `Term.externCall` — the terms of the
  arguments, and the function that builds the entry from their values;
* for an entry that takes a proof, to `Term.externCallChecked`: the proposition is decided
  on the values when the term runs and the proof handed to the entry, with a fallback for
  values that do not satisfy it (which a Lean program cannot give);
* with arguments that are all closed Lean values, for an entry that takes a proof, to
  `Term.extern` of the entry with the program's own proof.

Each value is checked by `kernel_rfl` (see `LeanScript/KernelRfl.lean`).
-/

namespace TermTests.ExternToTerm

open LeanScript

def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

mutual
/-- The first of `Term.extern`, `Term.externCall` and `Term.externCallChecked` in the term,
    looking under binders, applications and `let`s.  (The translation of `a + b` goes
    through the instances `HAdd Nat` and `Add Nat`, each a function applied to its
    arguments, before it reaches `Nat.add`.) -/
def externForm? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sig0 Γ τ J → Option String
  | .externCallChecked _ _ _ _ => some "externCallChecked"
  | .letE c body => (externForm?.comp c).orElse fun _ => externForm? body
  | .letJ jp body => (externForm? body).orElse fun _ => externForm? jp
  | _ => none

/-- `externForm?`, in the computation a `let` binds: the body of a `fun`. -/
def externForm?.comp {Γ : Ctx} {τ : TyWf} : Comp sig0 Γ τ → Option String
  | .extern _ => some "extern"
  | .externCall _ _ => some "externCall"
  | .lam b => externForm? b
  | _ => none
end

/-! ## An extern without a proof: `Term.externCall` -/

def addN (a b : Nat) : Nat := a + b

def addN_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term addN

-- [SKIPPED BY PROFILE_LAKE] example : externForm? addN_term = some "externCall" := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run addN_term 2 3 = 5 := by kernel_rfl

/-- `Array.toList` is the extern `lean_array_to_list`, whose value is a list of the
    language. -/
def asList (a : Array Nat) : List Nat := a.toList

def asList_term : Term sig0 [] (TyWf.array (TyWf.prim .nat) ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term asList

-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (run asList_term #[4, 5, 6]) = [4, 5, 6] := by decide +kernel

/-! ## An extern that takes a proof: `Term.externCallChecked`

`xs[i]` in the branch of `if h : i < xs.size` is `Array.getInternal xs i h`.  The proof is
erased, so the term decides `i < xs.size` again when it runs and hands the proof it gets
to `Array.getInternal`. -/

def getOr (a : Array Nat) (i : Nat) : Nat := if h : i < a.size then a[i] else 0

def getOr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term getOr

-- [SKIPPED BY PROFILE_LAKE] example : run getOr_term #[10, 20, 30] 0 = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run getOr_term #[10, 20, 30] 2 = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run getOr_term #[10, 20, 30] 5 = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run getOr_term #[10, 20, 30] 1 = getOr #[10, 20, 30] 1 := by kernel_rfl

/-- `Array.set` with its proof. -/
def setOr (a : Array Nat) (i v : Nat) : Array Nat := if h : i < a.size then a.set i v h else a

def setOr_term :
    Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.array (.prim .nat)) :=
  #leanscript_to_term setOr

-- [SKIPPED BY PROFILE_LAKE] example : run setOr_term #[1, 2, 3] 1 7 = #[1, 7, 3] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run setOr_term #[1, 2, 3] 3 7 = #[1, 2, 3] := by kernel_rfl

/-! ## Closed arguments: `Term.extern`, with the program's own proof -/

def second : Nat := #[1, 2, 3][1]

def second_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term second

-- [SKIPPED BY PROFILE_LAKE] example : externForm? second_term = some "extern" := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : run second_term = 2 := by kernel_rfl

/-! ## `Lean.Name` is an ordinary inductive of the language -/

def sameName (a b : Lean.Name) : Bool := a == b

def sameName_term : Term sig0 [] (TyWf.leanName ⇒ TyWf.leanName ⇒ TyWf.prim .bool) :=
  #leanscript_to_term sameName

-- [SKIPPED BY PROFILE_LAKE] example : run sameName_term (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.b) = true := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : run sameName_term (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.c) = false := by decide +kernel

/-! ## `Nat.gcd` is an ordinary function

It is translated as if it had no `@[extern]`: a call of it is a call of the declaration
`gcd` of the signature. -/

def sigGcd : Sig :=
  ⟨[⟨"gcd", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

def gcdTwice (a : Nat) : Nat := Nat.gcd a (2 * a)

def gcdTwice_term : Term sigGcd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term gcdTwice

-- [SKIPPED BY PROFILE_LAKE] example : (Term.run (Sg := sigGcd) (Nat.gcd, PUnit.unit) gcdTwice_term) 6 = 6 := by decide +kernel

end TermTests.ExternToTerm
