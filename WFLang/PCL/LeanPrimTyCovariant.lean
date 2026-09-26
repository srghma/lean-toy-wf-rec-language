module

prelude
public import Init.Prelude
public import Init.Data.Format.Basic
public import Init.Data.Format.Instances
public import Init.Data.ToString.Basic
public import Init.LawfulBEqTactics
public import Init.Core
public import Init.Data.Bool

@[expose] public section

namespace LeanScript

open Std (Format ToFormat)

/-!
# `LeanPrimTyCovariant`: the leaf type formers

The type formers of the language that take one type and are covariant in it — arrays,
thunks and lazy values — with the child abstracted, so the same former serves `Ty` and the
backends.
-/

/-- A leaf type former with one covariant argument of type `α`. -/
inductive LeanPrimTyCovariant (α : Type) where
  /-- Always a JS array. -/
  | array : α → LeanPrimTyCovariant α
  -- -- /-- In JS: `Promise<α>` (async task / worker). -/
  -- | task : α → LeanPrimTyCovariant α
  -- -- /-- In JS: `Promise<α>`. -/
  -- | promise : α → LeanPrimTyCovariant α
  /-- In JS: `(fn) => { let r; return () => (r === undefined ? (r = fn()) : r); }`. -/
  | thunk : α → LeanPrimTyCovariant α
  /-- In JS: `() => { return ... }`. -/
  | lazy : α → LeanPrimTyCovariant α
  -- | shareCommonState : α → LeanPrimTyCovariant α
  deriving Repr, DecidableEq, Inhabited, BEq, ReflBEq, LawfulBEq

namespace LeanPrimTyCovariant

/-- Extracts the inner wrapped value. -/
def val : LeanPrimTyCovariant α → α
  | .array a   => a
  -- | .task a    => a
  -- | .promise a => a
  | .thunk a   => a
  | .lazy a    => a
  -- | .shareCommonState a    => a

/-- Maps a function over the covariant wrapper. -/
def map (f : α → β) : LeanPrimTyCovariant α → LeanPrimTyCovariant β
  | .array a   => .array (f a)
  -- | .task a    => .task (f a)
  -- | .promise a => .promise (f a)
  | .thunk a   => .thunk (f a)
  | .lazy a    => .lazy (f a)
  -- | .shareCommonState a    => .shareCommonState (f a)

instance : Functor LeanPrimTyCovariant where
  map := map

/-- Formats the covariant type into a `Format` document. -/
def format [ToFormat α] : LeanPrimTyCovariant α → Format
  | .array a   => "(array " ++ Std.format a ++ ")"
  -- | .task a    => "(task " ++ Std.format a ++ ")"
  -- | .promise a => "(promise " ++ Std.format a ++ ")"
  | .thunk a   => "(thunk " ++ Std.format a ++ ")"
  | .lazy a    => "(lazy " ++ Std.format a ++ ")"
  -- | .shareCommonState a    => "(shareCommonState " ++ Std.format a ++ ")"

instance [ToFormat α] : ToFormat (LeanPrimTyCovariant α) where
  format := format

instance [ToFormat α] : ToString (LeanPrimTyCovariant α) where
  toString x := toString (format x)

end LeanPrimTyCovariant

end LeanScript

end
