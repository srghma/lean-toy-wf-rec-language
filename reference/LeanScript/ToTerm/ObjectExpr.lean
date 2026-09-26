module

public meta import Lean.Elab.Command
public meta import LeanScript.Expr.NatRecCtx
public meta import LeanScript.Expr.Extern
public meta import LeanScript.Expr.SelfField
public meta import LeanScript.Ty.Unfold
public meta import LeanScript.Ty.TyWfIn
public meta import LeanScript.Ty.Wf
public meta import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving

@[expose] public section

meta section

/-!
# The expressions of the object language

The pieces of `LeanScript.TyWf`, `LeanScript.Ctx` and the schemas, as `Lean.Expr`s: what
the translation builds its output out of, and how a payload of trees is bundled with its
well-formedness proof.  Overview: `LeanScript.ToTerm.Overview`.

**Names of `LeanScript.Term`.**  The translator does not import `LeanScript.Expr.Term`, so
that it builds in parallel with that (slow) module.  The types of `Expr/Term.lean`
(`LeanScript.Term`, `LeanScript.Spine`, `LeanScript.TaggedUnionCases`, …) and their
constructors are therefore written with a single backquote, `` `LeanScript.Term.lam ``,
which Lean does not check; `TermTests/ToTermTest/TermNames.lean` checks that every such
name exists.  Every other name keeps the checked double backquote.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## Expressions of the object language -/

/-- The type `LeanScript.TyWf` — a type of the language — as an expression.  This is the
    currency of the translation: `LeanScript.Term` is indexed by it. -/
def tyE : Expr := mkConst ``LeanScript.TyWf

/-- `LeanScript.TyWfIn n`, the trees written in a scope of `n` members, as an
    expression. -/
def tyWfInE (n : Nat) : Expr := mkApp (mkConst ``LeanScript.TyWfIn) (mkNatLit n)

/-- `id : List TyWf → List TyWf`, as an expression: what a branch of a **plain** dispatch
    binds (`LeanScript.TaggedUnionCases` is the fold-case family at `ι := TyWf` and this
    `bind`). -/
def idBindE : Expr :=
  mkApp (mkConst ``id [Level.one]) (mkApp (mkConst ``List [Level.zero]) tyE)

/-- The bundles of a scope: `TyWf` closed, `TyWfIn n` inside a binder. -/
def scopeTyE (n : Nat) : Expr := if n == 0 then tyE else tyWfInE n

/-- The type `LeanScript.Ctx = List TyWf`, as an expression. -/
def ctxE : Expr := mkApp (mkConst ``List [Level.zero]) tyE

/-- The empty context, as an expression. -/
def nilCtxE : Expr := mkApp (mkConst ``List.nil [Level.zero]) tyE

/-- `τ :: Γ`, as an expression. -/
def consCtxE (t rest : Expr) : Expr :=
  mkApp3 (mkConst ``List.cons [Level.zero]) tyE t rest

/-- The context `ts ++ base`, with `ts` innermost first. -/
def mkCtxE (ts : List Expr) (base : Expr) : Expr := ts.foldr consCtxE base

/-- The schema of `List α` as the language sees it, as a schema of **trees**:
    `LeanScript.Ty.listSchema σ`, the schema the `LeanScriptTyWf (List α)` instance
    (`LeanScript.TyWf.list`) is built from — constructor `0` is `nil`, which has no fields,
    and constructor `1` is `cons`, whose fields are an element and the list itself
    (`Ty.self`).  Every use goes through `reduceTy`, which unfolds it. -/
def listSchemaE (σ : Expr) : Expr := mkApp (mkConst ``LeanScript.Ty.listSchema) σ

/-- The tree of `List α`: the recursive tagged union `nil | cons α self`. -/
def listTyE (σ : Expr) : Expr :=
  mkApp (mkConst ``LeanScript.Ty.recTaggedUnion) (listSchemaE σ)

/-- `@id TyWf`, the projection the variable scopes use. -/
def idTyE : Expr := mkApp (mkConst ``id [Level.one]) tyE

/-- The empty context of join points, `([] : List TyWf)`: the translation writes every
    dispatch in direct style, with no join point in scope, and the builders of
    `LeanScript.Expr.Build` introduce the join points. -/
def jnilE : Expr := mkApp (mkConst ``List.nil [Level.zero]) tyE

/-! ## From a tree to a type of the language

A tree becomes a **type** by being bundled with the proof that it is one, which
`LeanScript.Ty.mkWfIn` — what `ty_wf` runs — writes.  The bundle keeps the tree it was
given as its `toTy`, so a bundle built here is definitionally the one the grammar's own
constructors build out of the bundled payload, and the proofs never have to agree.
-/

/-- The tree `t`, bundled at scope `n`: `LeanScript.TyWf` closed, `LeanScript.TyWfIn n`
    inside a binder. -/
def bundleTyE (n : Nat) (t : Expr) : MetaM Expr := do
  -- the tree of a bundle, bundled again, is that bundle
  if n == 0 then
    if let (``LeanScript.TyWf.toTy, #[b]) := t.getAppFnArgs then return b
    if let .proj ``LeanScript.TyWf 0 b := t then return b
  let prf ← LeanScript.Ty.mkWfIn n t
  if n == 0 then
    return mkApp2 (mkConst ``LeanScript.TyWf.mk) t prf
  else
    return mkApp3 (mkConst ``LeanScript.TyWfIn.mk) (mkNatLit n) t prf

/-- The tree of a bundle: the `toTy` it was built from, or the projection of it. -/
def treeOfTyE (τ : Expr) : MetaM Expr := do
  match τ.getAppFnArgs with
  | (``LeanScript.TyWf.mk, #[t, _]) => return t
  | (``LeanScript.TyWfIn.mk, #[_, t, _]) => return t
  | _ => whnf (mkApp (mkConst ``LeanScript.TyWf.toTy) τ)

/-- Reduce an expression to the constructor tree it denotes.  Trees of the language are
    data, so this is the form every match below is written against. -/
def reduceTy (e : Expr) : MetaM Expr :=
  withTransparency .default <|
    reduce e (explicitOnly := false) (skipTypes := false) (skipProofs := true)

/-- The elements of a fully reduced `List α` expression. -/
partial def listOfExpr (e : Expr) : MetaM (List Expr) := do
  match (← whnf e).getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, a, as]) => return a :: (← listOfExpr as)
  | _ => throwError "`#leanscript_to_term`: not a list of types: {e}"

/-- The value of a fully reduced `Nat` expression. -/
def natOfExpr (e : Expr) : MetaM Nat := do
  let some n ← evalNat (← whnf e) | throwError "`#leanscript_to_term`: not a number: {e}"
  return n

/-! ## Bundling a payload

A schema of the grammar is a schema **of bundles**: the fields of a record are
`LeanRecordSchema TyWf`, the payload of a recursive union is
`LeanTaggedUnionSchema (TyWfIn 1)`.  The functions below rebuild a schema of trees as the
schema of bundles it stands for, one field at a time, so that mapping the result back to
trees gives the schema they were given. -/

/-- A list of bundles, from a list of trees. -/
def bundleListE (n : Nat) (ts : Expr) : MetaM Expr := do
  let xs ← (← listOfExpr ts).mapM (bundleTyE n)
  let elem := scopeTyE n
  return xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) elem)

/-- A non-empty list of bundles, from one of trees. -/
def bundleNEE (n : Nat) (ne : Expr) : MetaM Expr := do
  match (← whnf ne).getAppFnArgs with
  | (``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk, #[_, hd, tl]) =>
      return mkApp3 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
        [Level.zero]) (scopeTyE n) (← bundleTyE n hd) (← bundleListE n tl)
  | _ => throwError "`#leanscript_to_term`: not a non-empty list of types: {ne}"

/-- The constructors a schema leaves unconstrained, bundled. -/
def bundleCtorsE (n : Nat) (cs : Expr) : MetaM Expr := do
  let xs ← (← listOfExpr cs).mapM (bundleListE n)
  let elem := mkApp (mkConst ``List [Level.zero]) (scopeTyE n)
  return xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) elem)

/-- The fields of a record, bundled. -/
def bundleRecordE (n : Nat) (fs : Expr) : MetaM Expr := do
  match (← whnf fs).getAppFnArgs with
  | (``LeanScript.LeanRecordSchema.mk, #[_, a, b, rest]) =>
      return mkAppN (mkConst ``LeanScript.LeanRecordSchema.mk)
        #[scopeTyE n, ← bundleTyE n a, ← bundleTyE n b, ← bundleListE n rest]
  | _ => throwError "`#leanscript_to_term`: not a record schema: {fs}"

mutual

/-- The constructors of a tagged union, bundled. -/
partial def bundleTUE (n : Nat) (l : Expr) : MetaM Expr := do
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      return mkAppN (mkConst ``LeanScript.LeanTaggedUnionSchema.payloadFirst)
        #[scopeTyE n, ← bundleNEE n fields, ← bundleListE n next, ← bundleCtorsE n rest]
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.skip) (scopeTyE n)
        (← bundleCPE n rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- The constructors that follow a field-less one, bundled. -/
partial def bundleCPE (n : Nat) (cp : Expr) : MetaM Expr := do
  match (← whnf cp).getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
      return mkApp3 (mkConst ``LeanScript.CtorsWithPayload.here) (scopeTyE n)
        (← bundleNEE n fields) (← bundleCtorsE n rest)
  | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
      return mkApp2 (mkConst ``LeanScript.CtorsWithPayload.skip) (scopeTyE n)
        (← bundleCPE n rest)
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"

end

end LeanScript.ToTerm

end

end
