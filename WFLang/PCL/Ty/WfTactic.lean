module

public meta import LeanScript.Ty.WfTactic.WfIn

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace LeanScript.Ty

/-!
# `ty_wf`: the proof that a tree is a type, composed rather than computed

`ty_wf` closes a goal of the form `Ty.Wf t`, `Ty.WfIn n t`, or any of the auxiliary
propositions of `LeanScript.Ty.Wf`, by **writing the derivation directly**: it walks the
tree one node at a time and applies the rule of that node.

The point of the tactic — and the reason `Ty.Wf` is an inductive proposition rather than
a Boolean check — is what it does at a leaf it does *not* walk into:

* a subtree that is the tree of a bundled `LeanScript.TyWf` — `(tyWfOf α).toTy` for some
  instance, say — is closed by that bundle's own `isWf`.  The tree of `α` is never looked
  at, in this module or in any later one: the proof is reused, not recomputed;
* a subtree that is a local variable — the parameter of a generated
  `…leanScriptTyOf (a : Ty)` — is closed by a hypothesis `Ty.Wf a` from the context.

So checking a type costs the size of *its own* layer, not the size of its transitive
content, and importing a module that already checked a type costs nothing at all.
-/


/-- A proof of whichever proposition of `LeanScript.Ty.Wf` the goal is. -/
def mkWfProof (goal : Expr) : MetaM Expr := do
  let goal ← whnfR goal
  match goal.getAppFnArgs with
  | (``LeanScript.Ty.WfIn, #[n, t]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfIn n t
  | (``LeanScript.Ty.WfShapeIn, #[n, s]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfShapeIn n s
  | (``LeanScript.Ty.WfAllIn, #[n, ts]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfAllIn n ts
  | (``LeanScript.Ty.OccursIn, #[i, t]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member {i} is unknown"
      mkOccursIn i t
  | (``LeanScript.Ty.OccursSomeIn, #[i, ts]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member {i} is unknown"
      mkOccursSomeIn i ts
  | (``LeanScript.Ty.MembersOccur, #[k, ts]) =>
      let some k := (← natOf? k) | throwError "ty_wf: the number of members {k} is unknown"
      mkMembersOccur k ts
  | (``LeanScript.Ty.HabIn, #[s, t]) => mkHabIn (← natListOf s) t
  | (``LeanScript.Ty.HabShapeIn, #[s, x]) => mkHabShapeIn (← natListOf s) x
  | (``LeanScript.Ty.HabAllIn, #[s, ts]) => mkHabAllIn (← natListOf s) ts
  | (``LeanScript.Ty.HabSomeIn, #[s, cs]) => mkHabSomeIn (← natListOf s) cs
  | (``LeanScript.Ty.MemberHab, #[s, m]) => mkMemberHab (← natListOf s) m
  | (``LeanScript.Ty.FamHab, #[ms]) => mkFamHab ms
  | _ => throwError "ty_wf: the goal is not a well-formedness of a type: {goal}"

/-- `ty_wf` proves that a tree is a type of the language, reusing the proof of every
    subtree that already has one instead of checking it again. -/
syntax (name := tyWfTactic) "ty_wf" : tactic

@[tactic tyWfTactic]
def elabTyWf : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let proof ← mkWfProof target
    unless ← isDefEq (← inferType proof) target do
      throwError "ty_wf: built a proof of {← inferType proof}, not of {target}"
    g.assign proof
  replaceMainGoal []


end LeanScript.Ty

end

end
