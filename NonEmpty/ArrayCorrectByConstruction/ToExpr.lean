module
public import Lean.ToExpr
public import NonEmpty.ArrayCorrectByConstruction.Basic
public import NonEmpty.ArrayCorrectByConstruction.Ops
public import NonEmpty.ArrayCorrectByConstruction.Instances
public import NonEmpty.ArrayCorrectByConstruction.Notation

open Lean

@[expose] public section

/-! `ToExpr` for `NonEmptyArray`, derived: it quotes a value as `NonEmptyArray.mk head tail`. -/
deriving instance ToExpr for NonEmpty.ArrayCorrectByConstruction.NonEmptyArray
