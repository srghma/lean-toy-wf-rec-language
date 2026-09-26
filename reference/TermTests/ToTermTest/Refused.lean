module

public import TermTests.ToTermTest.Recursion
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `#leanscript_to_term`, run: what the translation refuses
-/

namespace TermTests.ToTerm

open LeanScript

/-! ## What is refused -/

/-- A definition that is neither declared in the signature nor inlinable cannot be
    called. -/
def notDeclared (n : Nat) : Nat := n

def callsNotDeclared (n : Nat) : Nat := notDeclared n

/-- error: `#leanscript_to_term`: `TermTests.ToTerm.notDeclared` is not declared in the signature and is not inlinable, so a term cannot call it.  Either add a `GlobalDecl` named "notDeclared" (or "TermTests.ToTerm.notDeclared") to the signature, or mark `TermTests.ToTerm.notDeclared` `@[inline]`.  (A structural recursion is inlined without either.) -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term callsNotDeclared

/-- A `partial` definition has no value to translate. -/
partial def loop (n : Nat) : Nat := loop n

/-- error: `#leanscript_to_term`: `TermTests.ToTerm.loop` is `partial`, and a `partial` definition has no value the grammar can express -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term loop

/-- An `unsafe` definition is refused as well. -/
unsafe def unsafeId (n : Nat) : Nat := n

/-- error: `#leanscript_to_term`: `TermTests.ToTerm.unsafeId` is `unsafe` -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term unsafeId

-- `Array.toList` used to be refused here; it is the extern `lean_array_to_list`, and is now
-- translated (`TermTests/ExternToTermTest.lean`).

/-- A well-founded recursion is refused. -/
def halve (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + halve (n - 2)
decreasing_by omega

/-- error: `#leanscript_to_term`: well-founded recursion (WellFounded.Nat.fix) is not supported — the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term halve

/-- A `partial_fixpoint` is refused: the grammar has no fixpoint that does not
    descend. -/
def spin (n : Nat) : Option Nat := spin n
partial_fixpoint

/-- error: `#leanscript_to_term`: a partial fixpoint (Lean.Order.fix) is not supported: the grammar has no fixpoint that does not descend -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ tyWfOf (Option Nat)) := #leanscript_to_term spin

/-! ## An existentially typed structure

The type a `Process` carries is hidden in the value, which the language has no shape
for, so `Process` has no tree — `deriving LeanScriptTyWf` refuses it — and a definition
of that type has no translation either. -/

structure Process (Out : Type) where
  State : Type
  seed : State
  step : State → Option (State × Out)

def stuck : Process Nat := ⟨Nat, 0, fun _ => none⟩

#guard_msgs (drop error) in
example : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term stuck


end TermTests.ToTerm

end
