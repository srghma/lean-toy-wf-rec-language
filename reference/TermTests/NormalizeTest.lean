module

public import TermTests.StructRecTest.Existential
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Normalizing a translated term changes nothing but its form

`#leanscript_to_term` reduces its result once to constructors of the grammar
(`LeanScript.ToTerm.Normalize`, option `leanscript.toTerm.normalize`).  The theorems below
state, for the terms of `TermTests/StructRecTest/Existential.lean`, that the normalized
term **is equal** to the direct-style term the translation gives with the option off —
closed terms and the terms generic in the hidden type alike — so every fact about one is a
fact about the other.  The checks at the end confirm that normalization did change the form:
the normalized terms mention no builder of `LeanScript.Expr.Build`, the direct-style ones
do. -/

namespace TermTests.Normalize

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Existential

noncomputable section

set_option leanscript.toTerm.normalize false in
/-- `takeCountdown`, left in direct style. -/
def takeCountdown_direct : Term sigAdd [] (natT ⇒ listT) := #leanscript_to_term takeCountdown

set_option leanscript.toTerm.normalize false in
/-- `takeFibs`, left in direct style. -/
def takeFibs_direct : Term sigAdd [] (natT ⇒ listT) := #leanscript_to_term takeFibs

set_option leanscript.toTerm.normalize false in
/-- `mixed`, left in direct style. -/
def mixed_direct : Term sigAdd [] (natT ⇒ natT ⇒ listT ⇒ listT) := #leanscript_to_term mixed

set_option leanscript.toTerm.normalize false in
/-- `Unfold.take`, for every choice of `State`, left in direct style. -/
def take_direct := #leanscript_to_term (sig := sigAdd) (Unfold.take (α := Nat))

set_option leanscript.toTerm.normalize false in
/-- `Boxed.iter`, for every choice of `T`, left in direct style. -/
def iter_direct := #leanscript_to_term (sig := sigAdd) Boxed.iter

set_option leanscript.toTerm.normalize false in
/-- `Pipe.run`, for every choice of `In` and `Out`, left in direct style. -/
def pipeRun_direct := #leanscript_to_term (sig := sigAdd) Pipe.run

/-- The normalized `takeCountdown_term` is the direct-style term. -/
theorem takeCountdown_normalize_eq : takeCountdown_term = takeCountdown_direct := by kernel_rfl

/-- The normalized `takeFibs_term` is the direct-style term. -/
theorem takeFibs_normalize_eq : takeFibs_term = takeFibs_direct := by kernel_rfl

/-- The normalized `mixed_term` is the direct-style term. -/
theorem mixed_normalize_eq : mixed_term = mixed_direct := by kernel_rfl

/-- The normalized `take_term` is the direct-style term, at every hidden type. -/
theorem take_normalize_eq (S : TyWf) : take_term S = take_direct S := by kernel_rfl

/-- The normalized `iter_term` is the direct-style term, at every hidden type. -/
theorem iter_normalize_eq (T : TyWf) : iter_term T = iter_direct T := by kernel_rfl

/-- The normalized `pipeRun_term` is the direct-style term, at every pair of hidden types. -/
theorem pipeRun_normalize_eq (I O : TyWf) : pipeRun_term I O = pipeRun_direct I O := by
  kernel_rfl

/-- Hence the two forms run to the same value, at every input. -/
theorem mixed_normalize_eval (k n : Nat) (xs : TyWf.Den listT) :
    runAdd mixed_term k n xs = runAdd mixed_direct k n xs := by
  rw [mixed_normalize_eq]

end

open Lean Meta in
/-- Whether the body of the definition `d` mentions a builder of `LeanScript.Expr.Build`. -/
meta def mentionsBuilder (d : Name) : MetaM Bool := do
  let some v := (← getEnv).find? d |>.bind (·.value?) | throwError "no body: {d}"
  let env ← getEnv
  let some mod := env.getModuleIdx? `LeanScript.Expr.Build | throwError "no builder module"
  return v.getUsedConstants.any fun n => env.getModuleIdxFor? n == some mod

-- the normalized terms mention no builder; the direct-style ones do
run_meta do
  for d in [``takeCountdown_term, ``takeFibs_term, ``mixed_term, ``take_term, ``iter_term,
      ``pipeRun_term] do
    if ← mentionsBuilder d then throwError "{d} is not normalized"
  for d in [``TermTests.Normalize.takeCountdown_direct, ``TermTests.Normalize.mixed_direct,
      ``TermTests.Normalize.take_direct] do
    unless ← mentionsBuilder d do throwError "{d} mentions no builder"

end TermTests.Normalize
