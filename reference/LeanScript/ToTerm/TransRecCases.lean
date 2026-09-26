module

public meta import LeanScript.ToTerm.TransRec

@[expose] public section

meta section

/-!
# The translation: a plain `match` on a value of a recursive type

`transRecKindCasesOn?`, the clause of the translation for `X.casesOn` — the one-level case
analysis a `match` compiles to — when the tree of `X` is one of the four recursive
binders with a user-defined inductive behind it:

| the tree of `X` | the dispatch |
|---|---|
| `Ty.recTaggedUnion` (`Tree`, `Nat`-like unions) | `recTaggedUnion_casesOn` |
| `Ty.recObject` (`Cell := mk (label : Nat) (next : Option Cell)`) | `recObject_casesOn` |
| `Ty.recAlias` (`Chain := mk (Link Chain)`) | `recAlias_casesOn` |
| `Ty.mutualRecursiveFamily` (a member of a `mutual` block) | `mutualRecursiveFamily_casesOn` |

Without this clause `X.casesOn` is unfolded to `X.rec`, which for a recursive type is
either not an eliminator of the language (a nested or mutual type has several motives) or
refused as a recursion — although the `match` recurses on nothing.  The branches bind the
constructor's fields **unfolded**, exactly as the `…_mk` of the same type builds them, so a
field that holds the type again is bound as a value of the type, which a further `match`
may take apart in turn (a match several levels deep is a nest of these dispatches).

A structural *recursion* is not a `casesOn`: Lean compiles it into `X.brecOn`, which is
the fold (`LeanScript.ToTerm.TransRecUnion`, `TransRecObject`, `TransRecFamily`).
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The dispatch on a value of a declaration of **several constructors** whose tree is a
    recursive newtype (it holds itself inside another type, `Array T`, and its body is the
    union of its constructors): `recAlias_casesOn` binds the body, unfolded, and a
    `taggedUnion_casesOn` on it dispatches on the constructors. -/
def transUnionAliasCases (trans : TransFn) (c : TCtx) (τ b hwf scrut : Expr)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recAliasUnfold) b hwf)
  let .taggedUnion l ← tyView unfE
    | throwError "`#leanscript_to_term`: internal: the body of a recursive newtype of \
        several constructors is not a tagged union"
  let fid ← mkFreshFVarId
  let c1 := c.push fid unfE
  let cases ← mkTaggedUnionCases (transBranch trans c1) c1 τ l 0 minors ctors
  let body := mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn')
    #[c1.sg, c1.gamma, τ, l, ← c1.var fid, cases]
  return mkAppN (mkConst `LeanScript.Term.recAlias_casesOn')
    #[c.sg, c.gamma, τ, b, hwf, scrut, body]

/-- The dispatch of the language on `scrut`, a value of the recursive tagged union, record
    or newtype `view`, answering with `τ`: one branch per constructor of the Lean type
    (`ctors`), read off the Lean branches `minors`.  `none` for any other tree. -/
def transRecShapeCases (trans : TransFn) (c : TCtx) (τ scrut : Expr) (view : TyView)
    (minors : Array Expr) (ctors : Array Name) : MetaM (Option Expr) := do
  let core ← match view with
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionCases (transBranch trans c) c τ unfE 0 minors ctors
        pure <| mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOn')
          #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
    | .recObject fs hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recObjectUnfold) fs hwf)
        let body ← transBranch trans c minors[0]! ctors[0]! (← recordFieldTys unfE)
        pure <| mkAppN (mkConst `LeanScript.Term.recObject_casesOn')
          #[c.sg, c.gamma, τ, fs, hwf, scrut, body]
    | .recAlias b hwf =>
        if ctors.size > 1 then
          transUnionAliasCases trans c τ b hwf scrut minors ctors
        else
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recAliasUnfold) b hwf)
        let body ← transBranch trans c minors[0]! ctors[0]! [unfE]
        pure <| mkAppN (mkConst `LeanScript.Term.recAlias_casesOn')
          #[c.sg, c.gamma, τ, b, hwf, scrut, body]
    | _ => return none
  return some core

/-- `X.casesOn` on a value of an **indexed family** (`Vec α n`), whose tree is a recursive
    tagged union, record or newtype: the dispatch of the same tree, whose branches are
    read off the whole application — the `match` Lean compiled carries equations between
    the indices in its motive, `n = m + 1 → x ≍ cons a v → …`, which hold at the
    constructor.  So at each constructor the application is instantiated at the value
    `C fields` and at the indices it has (a variable of the context that is an index is
    unified with the constructor's: `n + 1 = m + 1` sets `n := m`), and reduced.

    A constructor the index rules out (`nil` for a value of `Vec α (n + 1)`) has no Lean
    branch; the dispatch of the language still has one, never taken on a value of the
    Lean type, and it is the `default` of the answer's type.  `none` when the value is not
    a variable (the translation then refuses the recursor). -/
def transIndexedCasesOn? (trans : TransFn) (c : TCtx) (e : Expr)
    (ii : InductiveVal) (args : Array Expr) : MetaM (Option Expr) := do
  let nP := ii.numParams
  let nI := ii.numIndices
  let nC := ii.ctors.length
  let arity := nP + 2 + nI + nC
  if args.size < nP + 2 + nI then return none
  let major := args[nP + 1 + nI]!
  let sty ← tyOfTerm major
  let view ← tyView sty
  match view with
  | .recTaggedUnion .. | .recObject .. | .recAlias .. => pure ()
  | _ => return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  unless major.isFVar do return none
  let some (_, minors) ← indexedCasesMinors? e | return none
  let τ ← tyOfType (← instantiateMVars (← inferType e))
  let ctors := ii.ctors.toArray
  let scrut ← trans c major
  transRecShapeCases trans c τ scrut view minors ctors

/-- `X.casesOn` on a value whose tree is a recursive tagged union, a recursive record, a
    recursive newtype or a member of a mutual family: the matching `…_casesOn` of the
    grammar (see the module documentation).  `none` for any other type, which the other
    clauses of the translation serve. -/
def transRecKindCasesOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "casesOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  if ii.numIndices != 0 then
    return ← transIndexedCasesOn? trans c e ii args
  -- `List` and `Nat` keep their own translation — but a list of the declarations of a
  -- nested inductive (`List Rose`) is a member of their family
  if ind == ``Nat then return none
  -- inside the branches of a fold of this very type, taking a value apart is the fold's
  -- look further down (see `TCtx.foldInds`)
  if c.foldInds.contains ind then return none
  let nP := ii.numParams
  let nC := ii.ctors.length
  let arity := nP + 2 + nC
  if args.size < nP + 2 then return none
  let major := args[nP + 1]!
  let sty ← tyOfTerm major
  let view ← tyView sty
  match view with
  | .mutualRecursiveFamily .. => pure ()
  | .recTaggedUnion .. | .recObject .. | .recAlias .. => if ind == ``List then return none
  | _ => return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[nP]!
  unless motive.isLambda do return none
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    tyOfType body
  let minors := args.extract (nP + 2) arity
  let ctors := ii.ctors.toArray
  let scrut ← trans c major
  let core ← match view with
    | .mutualRecursiveFamily nE f hwf =>
        let unfE ← famCurrentUnfolded nE f hwf
        let cases ← match unfE.getAppFnArgs with
          | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
              let cs ← mkTaggedUnionCases (transBranch trans c) c τ l 0 minors ctors
              pure <| mkAppN (mkConst `LeanScript.FamilyMemberCases.ctors)
                #[c.sg, c.gamma, τ, jnilE, l, cs]
          | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
              let body ← transBranch trans c minors[0]! ctors[0]! (← recordFieldTys fs)
              pure <| mkAppN (mkConst `LeanScript.FamilyMemberCases.record)
                #[c.sg, c.gamma, τ, jnilE, fs, body]
          | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
              let body ← transBranch trans c minors[0]! ctors[0]! [b]
              pure <| mkAppN (mkConst `LeanScript.FamilyMemberCases.alias)
                #[c.sg, c.gamma, τ, jnilE, b, body]
          | _ => throwError "`#leanscript_to_term`: internal: the member of the family \
              {ind} has no shape: {unfE}"
        pure <| mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_casesOn')
          #[c.sg, c.gamma, τ, nE, f, hwf, scrut, cases]
    | _ =>
        let some core ← transRecShapeCases trans c τ scrut view minors ctors | return none
        pure core
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
