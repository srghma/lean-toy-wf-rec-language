module

public import Lean.Meta

@[expose] public section

meta section

/-!
# A default value of a type, with or without `Inhabited`

A recursion on a `mutual` block whose members answer different types is translated as a
fold answering the tuple of all the answers, each member filling in its own component and
a default in the others (`LeanScript.ToTerm.TransRecFamily`).  Such a default used to be
taken from an `Inhabited` instance only, so a map over a `mutual` block (answers `P` and
`Q`) needed `instance : Inhabited P` and `instance : Inhabited Q` written by hand, which
Lean does not provide for a `mutual` or nested block.

`synthDefault?` takes the instance when there is one, and otherwise **builds** a closed
value: the first constructor of the (inductive) type all of whose fields have a default,
found the same way, a bounded number of constructors deep.  A function type gets the
constant function of a default of its codomain.  A proof field, an indexed family or a
type that is not an inductive type (or a function into one) has none.

The value is only ever *used* in a component of the tuple that the fold never reads back,
so which value it is does not matter; only that it is a closed value the language can
write.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- A closed value of type `t`: `default` of an `Inhabited` instance, or, failing that, a
    constructor of `t` applied to defaults of its fields, at most `fuel` constructors deep.
    `none` when there is none of either kind. -/
partial def synthDefault? (t : Expr) (fuel : Nat := 6) : MetaM (Option Expr) := do
  let lvl ← try getLevel t catch _ => return none
  if let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Inhabited [lvl]) t)
      catch _ => pure none) then
    return some (mkApp2 (mkConst ``Inhabited.default [lvl]) t inst)
  if fuel == 0 then return none
  let t ← whnf t
  if t.isForall then
    -- a function: the constant function of a default of its (non-dependent) codomain
    if t.bindingBody!.hasLooseBVars then return none
    let some b ← synthDefault? t.bindingBody! fuel | return none
    return some (.lam t.bindingName! t.bindingDomain! b .default)
  let .const n lvls := t.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? n | return none
  if ii.numIndices != 0 then return none
  let params := t.getAppArgs.extract 0 ii.numParams
  if params.size != ii.numParams then return none
  for c in ii.ctors do
    let mut v := mkAppN (mkConst c lvls) params
    let mut ty ← whnf (← inferType v)
    let mut ok := true
    while ok && ty.isForall do
      let d := ty.bindingDomain!
      if ← isProp d then ok := false
      else
        match ← synthDefault? d (fuel - 1) with
        | some a =>
            v := mkApp v a
            ty ← whnf (ty.bindingBody!.instantiate1 a)
        | none => ok := false
    if ok then return some v
  return none

end LeanScript.ToTerm
