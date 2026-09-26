module
public import Lean.ToExpr
public import NonEmpty.ListCorrectByConstruction.Basic
public import NonEmpty.ListCorrectByConstruction.Ops
public import NonEmpty.ListCorrectByConstruction.Instances
public import NonEmpty.ListCorrectByConstruction.Notation

open Lean

@[expose] public section

/-! `ToExpr` for `NonEmptyList`, derived: it quotes a value as `NonEmptyList.mk head tail`. -/
deriving instance ToExpr for NonEmpty.ListCorrectByConstruction.NonEmptyList
