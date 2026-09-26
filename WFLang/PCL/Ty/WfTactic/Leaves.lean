module

public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Elab.Tactic.Basic
public meta import LeanScript.Ty.Wf

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace LeanScript.Ty

/-!
# `ty_wf`: reading the goal, and the leaves it does not walk into

Small readers of lists and numerals, and the recognition of a subtree that is already
answered for: the tree of a bundled `LeanScript.TyWf`, or a local variable with a
hypothesis.
-/

/-- The occurrences a node holds, as a list of terms: `whnf` the spine of a `List Ty`. -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) => return h :: (← listElems t)
  | _ => throwError "ty_wf: not a list of types: {e}"

/-- A natural number argument of a goal, when it reduces to a literal: core's
    `Lean.Meta.getNatValue?` after `whnf`. -/
def natOf? (e : Expr) : MetaM (Option Nat) := do
  getNatValue? (← whnf e)

/-- A natural number as an expression. -/
def natE (n : Nat) : Expr := mkNatLit n

/-- A list of natural numbers — the members already known to have values — as an
    expression. -/
def natListE (S : List Nat) : MetaM Expr := mkListLit (mkConst ``Nat) (S.map natE)

/-- The members a goal assumes to have values, when they are literals. -/
partial def natListOf (e : Expr) : MetaM (List Nat) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
      let some i ← natOf? h | throwError "ty_wf: the member number {h} is unknown"
      return i :: (← natListOf t)
  | _ => throwError "ty_wf: not a list of member numbers: {e}"

/-- A proof of `i ∈ S`, for a list of literals. -/
def memProof (i : Nat) (S : List Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``Membership.mem #[← natListE S, natE i])

/-- A proof of `a ≤ b`. -/
def leProof (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LE.le #[natE a, natE b])

/-- A proof of `a < b`. -/
def ltProof (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LT.lt #[natE a, natE b])

/-! ### The bundled tree, named rather than imported

`LeanScript.TyWf` — a tree together with the proof that it is one — is declared *after*
this module, because the proof it carries is written `by ty_wf`.  So the two projections
it is recognised by are named here as plain `Name`s rather than resolved at compile time;
they are in the environment by the time the tactic runs, which is every module from
`LeanScript.Ty.TyWf` on. -/

/-- The structure of a tree together with its proof, `LeanScript.TyWf`. -/
def tyWfStruct : Name := `LeanScript.TyWf
/-- Its tree, `LeanScript.TyWf.toTy`. -/
def tyWfToTy : Name := `LeanScript.TyWf.toTy
/-- Its proof, `LeanScript.TyWf.isWf`. -/
def tyWfIsWf : Name := `LeanScript.TyWf.isWf

/-- Is `t` the tree of a bundled `LeanScript.TyWf` — the tree of an instance, say?  If so,
    the proof that it is a type, which is that bundle's own field — no tree is
    traversed. -/
def instanceWf? (t : Expr) : MetaM (Option Expr) := do
  let bundle? : Option Expr :=
    match t with
    | .proj s 0 b => if s == tyWfStruct then some b else none
    | _ =>
      match t.getAppFn, t.getAppArgs with
      | .const c _, #[b] => if c == tyWfToTy then some b else none
      | _, _ => none
  let some bundle := bundle? | return none
  return some (mkApp (mkConst tyWfIsWf) bundle)

/-- Is there a hypothesis saying that `t` is a type?  This is what closes the parameters
    of a generated tree, which stand for the trees of the type's own parameters. -/
def hypWf? (t : Expr) : MetaM (Option Expr) := do
  unless t.isFVar do return none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match (← whnfR d.type).getAppFnArgs with
    | (``LeanScript.Ty.WfIn, #[n, x]) =>
        if x == t && (← natOf? n) == some 0 then return some d.toExpr
    | _ => pure ()
  return none

/-- Is the head of `t` a constructor of `LeanScript.Ty`? -/
def isTyCtor (t : Expr) : Bool :=
  match t.getAppFn with
  | .const n _ =>
      n == ``LeanScript.Ty.self || n == ``LeanScript.Ty.familyMember ||
        n == ``LeanScript.Ty.shape || n == ``LeanScript.Ty.recTaggedUnion ||
        n == ``LeanScript.Ty.recObject || n == ``LeanScript.Ty.recAlias ||
        n == ``LeanScript.Ty.mutualRecursiveFamily
  | _ => false

/-- Expose what a tree is at its root, **without** unfolding past a leaf that some
    instance or some hypothesis already answers for.  Ordinary `whnf` would unfold such a
    leaf into the tree behind it, which is exactly the copying this class exists to
    avoid, so the definition at the head is unfolded one step at a time and the leaf is
    looked for before each step. -/
partial def tyHeadNorm (t : Expr) : MetaM Expr := do
  let t ← whnfCore t
  if isTyCtor t then return t
  if (← instanceWf? t).isSome then return t
  if (← hypWf? t).isSome then return t
  match ← unfoldDefinition? t with
  | some t' => tyHeadNorm t'
  | none => return t

end LeanScript.Ty

end

end
