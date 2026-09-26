module
public import Lean.ToExpr
public import NonEmpty.String.Basic
public import NonEmpty.Utils.Decidable

open Lean Meta Elab

@[expose] public section

@[default_instance]
instance instToExprNonEmptyString : ToExpr NonEmpty.String.NonEmptyString where
  toTypeExpr := mkConst ``NonEmpty.String.NonEmptyString
  toExpr
    | ⟨s, _⟩ =>
      let sExpr := toExpr s
      let emptyStrExpr := toExpr ""

      let propIsEqEmpty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) sExpr emptyStrExpr
      let instDecEqEmptyExpr := mkApp2 (mkConst ``instDecidableEqString) sExpr emptyStrExpr
      let propIsNonEmpty := mkApp (mkConst ``Not) propIsEqEmpty
      let instDecNeEmptyExpr := mkApp2 (mkConst ``instDecidableNot) propIsEqEmpty instDecEqEmptyExpr

      let finalProofExpr := mkDecidableProof propIsNonEmpty instDecNeEmptyExpr

      mkApp2 (mkConst ``NonEmpty.String.NonEmptyString.mk) sExpr finalProofExpr
