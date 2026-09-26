module

public meta import LeanScript.ToTerm.Pieces

@[expose] public section

meta section

/-!
# The branches of a dispatch

The builders of the branch families of a dispatch (`TaggedUnionCases`, `EnumCases`, their
partial forms, …).  They are given the translation of a single branch as an argument, so
they stand apart from the `mutual` block of the translation (`LeanScript.ToTerm.Trans`),
which passes them `transBranch`.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The translation of one branch: a minor premise, the constructor it is the branch of,
    and the trees of that constructor's fields. -/
abbrev BranchFn := Expr → Name → List Expr → MetaM Expr

mutual

/-- The branches of a **partial** dispatch on a tagged union: the constructors `named`,
    in increasing order, each binding its fields.  `lo` is the smallest constructor a
    branch may still name, which is what keeps the list in order. -/
partial def mkTaggedUnionSomeCases (mkBranch : BranchFn) (c : TCtx) (τ l : Expr) (named : List Nat) (lo : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  let ctys ← taggedUnionCtorTys l
  let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
  let branchOf (t : Nat) : MetaM (Expr × Expr) := do
    let some fieldTys := ctys[t]?
      | throwError "`#leanscript_to_term`: the tree of the dispatched type has no \
          constructor {t}"
    let ht ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit t, lenE])
    return (ht, ← mkBranch minors[t]! ctors[t]! fieldTys)
  match named with
  | [] =>
      throwError "`#leanscript_to_term`: internal: a partial dispatch names no \
        constructor"
  | [t] =>
      let (ht, branch) ← branchOf t
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit t])
      return mkAppN (mkConst `LeanScript.TaggedUnionSomeCases.last)
        #[c.sg, c.gamma, l, τ, jnilE, mkNatLit lo, mkNatLit t, ht, branch, hi]
  | t :: rest =>
      let (ht, branch) ← branchOf t
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit t])
      let restCases ← mkTaggedUnionSomeCases mkBranch c τ l rest (t + 1) minors ctors
      return mkAppN (mkConst `LeanScript.TaggedUnionSomeCases.cons)
        #[c.sg, c.gamma, l, τ, jnilE, mkNatLit rest.length, mkNatLit lo, mkNatLit t, ht, branch,
          restCases, hi]

/-- The branches of a **partial** dispatch on an enum: the constructors `named`, in
    increasing order. -/
partial def mkEnumSomeCases (mkBranch : BranchFn) (c : TCtx) (τ s : Expr) (named : List Nat) (lo : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
  match named with
  | [] =>
      throwError "`#leanscript_to_term`: internal: a partial dispatch names no \
        constructor"
  | [i] =>
      let iE ← mkFinLit nE i
      let branch ← mkBranch minors[i]! ctors[i]! []
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit i])
      return mkAppN (mkConst `LeanScript.EnumSomeCases.last)
        #[c.sg, c.gamma, τ, jnilE, s, mkNatLit lo, iE, branch, hi]
  | i :: rest =>
      let iE ← mkFinLit nE i
      let branch ← mkBranch minors[i]! ctors[i]! []
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit i])
      let restCases ← mkEnumSomeCases mkBranch c τ s rest (i + 1) minors ctors
      return mkAppN (mkConst `LeanScript.EnumSomeCases.cons)
        #[c.sg, c.gamma, τ, jnilE, s, mkNatLit rest.length, mkNatLit lo, iE, branch, restCases,
          hi]

/-- The branches of a dispatch on a tagged union, in the shape of its schema. -/
partial def mkTaggedUnionCases (mkBranch : BranchFn) (c : TCtx) (τ l : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      let f0 ← nonEmptyTys fields
      let f1 ← listOfExpr next
      let b0 ← mkBranch minors[start]! ctors[start]! f0
      let b1 ← mkBranch minors[start + 1]! ctors[start + 1]! f1
      let restCases ← mkTaggedUnionRest mkBranch c τ rest (start + 2) minors ctors
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldCases.payloadFirst)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, fields, next, rest, b0, b1, restCases]
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      let b0 ← mkBranch minors[start]! ctors[start]! []
      let restCases ← mkCtorsWithPayloadCases mkBranch c τ rest (start + 1) minors ctors
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldCases.skip)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, rest, b0, restCases]
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- The branches of the constructors a `CtorsWithPayload` holds. -/
partial def mkCtorsWithPayloadCases (mkBranch : BranchFn) (c : TCtx) (τ cp : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf cp).getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
      let b ← mkBranch minors[start]! ctors[start]! (← nonEmptyTys fields)
      let restCases ← mkTaggedUnionRest mkBranch c τ rest (start + 1) minors ctors
      return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldCases.here)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, fields, rest, b, restCases]
  | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
      let b ← mkBranch minors[start]! ctors[start]! []
      let restCases ← mkCtorsWithPayloadCases mkBranch c τ rest (start + 1) minors ctors
      return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldCases.skip)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, rest, b, restCases]
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"

/-- The branches of the constructors a schema leaves as a plain list. -/
partial def mkTaggedUnionRest (mkBranch : BranchFn) (c : TCtx) (τ rest : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf rest).getAppFnArgs with
  | (``List.nil, _) =>
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldCasesRest.nil)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE]
  | (``List.cons, #[_, fs, more]) =>
      let b ← mkBranch minors[start]! ctors[start]! (← listOfExpr fs)
      let restCases ← mkTaggedUnionRest mkBranch c τ more (start + 1) minors ctors
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldCasesRest.cons)
        #[c.sg, tyE, idBindE, c.gamma, τ, jnilE, fs, more, b, restCases]
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {rest}"

/-- The branches of a dispatch on an enum, in the shape of its schema. -/
partial def mkEnumCases (mkBranch : BranchFn) (c : TCtx) (τ s : Expr) (minors : Array Expr)
    (ctors : Array Name) : MetaM Expr := do
  let (extra, shift) ← match (← whnf s).getAppFnArgs with
    | (``LeanScript.LeanEnumSchema.mk, #[e, sh]) => pure (← natOfExpr e, sh)
    | _ => throwError "`#leanscript_to_term`: not an enum schema: {s}"
  let rec go (i : Nat) (k : Nat) : MetaM Expr := do
    if k == 0 then
      let b0 ← mkBranch minors[i]! ctors[i]! []
      let b1 ← mkBranch minors[i + 1]! ctors[i + 1]! []
      let b2 ← mkBranch minors[i + 2]! ctors[i + 2]! []
      return mkAppN (mkConst `LeanScript.EnumCases.three)
        #[c.sg, c.gamma, τ, jnilE, shift, b0, b1, b2]
    else
      let b ← mkBranch minors[i]! ctors[i]! []
      let rest ← go (i + 1) (k - 1)
      return mkAppN (mkConst `LeanScript.EnumCases.cons)
        #[c.sg, c.gamma, τ, jnilE, mkNatLit (k - 1), shift, b, rest]
  go 0 extra

end

end LeanScript.ToTerm

end

end
