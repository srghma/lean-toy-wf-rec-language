module

public import LeanScript.Expr.Build
public import LeanScript.Den
public import Mathlib.Data.Prod.TProd

@[expose] public section

set_option autoImplicit false

/-!
# Environments and folds for the evaluator

The environments `Term.eval` reads its variables and globals from, and the folds (with
their lookback windows) it interprets the eliminators of `Nat` and arrays by.  The
evaluator itself is `LeanScript.Eval`.
-/

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-! ## Environments -/

/-- An environment: a value for every type of the context, innermost first. -/
abbrev Env (Γ : Ctx) : Type := TyWf.DenList Γ

/-- The empty environment, of the empty context. -/
abbrev Env.nil : Env [] := PUnit.unit

/-- One more value, in front. -/
abbrev Env.cons {Γ : Ctx} {τ : TyWf} (v : TyWf.Den τ) (env : Env Γ) : Env (τ :: Γ) :=
  (v, env)

/-- The value a variable stands for. -/
def Env.get : {Γ : Ctx} → {τ : TyWf} → (Γ ∋ τ) → Env Γ → TyWf.Den τ
  | _ :: _, _, .head, env => env.1
  | _ :: _, _, .tail v, env => Env.get v env.2

/-- Bind a whole block of values at once — the fields an eliminator's branch binds are
    in front of the context that branch is written in. -/
def Env.append : {as : List TyWf} → {Γ : Ctx} → TyWf.DenList as → Env Γ → Env (as ++ Γ)
  | [], _, _, env => env
  | _ :: _, _, vs, env => (vs.1, Env.append vs.2 env)

/-- An environment for the module's signature: a value for every top-level declaration,
    at the type the signature gives it.  This is Mathlib's `List.TProd` — the right-nested
    product `TyWf.Den d₁.ty × (TyWf.Den d₂.ty × (… × PUnit))` over the declarations. -/
abbrev GlobalEnv (ds : List GlobalDecl) : Type :=
  List.TProd (fun d : GlobalDecl => TyWf.Den d.ty) ds

/-- No declarations, nothing to supply. -/
abbrev GlobalEnv.nil : GlobalEnv [] := PUnit.unit

/-- The value a reference to a top-level declaration stands for. -/
def GlobalEnv.get : {ds : List GlobalDecl} → {τ : TyWf} → GlobalRef ds τ → GlobalEnv ds →
    TyWf.Den τ
  | _ :: _, _, .head, g => g.1
  | _ :: _, _, .tail r, g => GlobalEnv.get r g.2

/-- The values of a list of types are Mathlib's `List.TProd` of their values, so the
    `List.TProd` lemmas apply to them.  `Ty.DenList` itself stays a shape of the `mutual`
    translation to polynomial functors, where `List.TProd` (a `List.foldr`) would not be
    structural. -/
theorem Ty.denList_eq_tprod : ∀ ts : List Ty, Ty.DenList ts = List.TProd Ty.Den ts
  | [] => rfl
  | t :: ts => by
      show (Ty.Den t × Ty.DenList ts) = (Ty.Den t × List.TProd Ty.Den ts)
      rw [Ty.denList_eq_tprod ts]

/-- The values of a list of bundled types are Mathlib's `List.TProd` of their values. -/
theorem TyWf.denList_eq_tprod (ts : List TyWf) :
    TyWf.DenList ts = List.TProd TyWf.Den ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      show (TyWf.Den t × TyWf.DenList ts) = (TyWf.Den t × List.TProd TyWf.Den ts)
      rw [ih]

/-! ## Two folds

`Term.nat_rec` and `Term.array_rec` are `Nat.rec` and `List.rec` with a non-dependent
motive, each with a **depth**: at depth `k` the branch is given the answers at the `k + 1`
previous arguments — the `k + 1` predecessors of a natural number, the `k + 1` next
suffixes of a list — instead of at the immediate one alone.  They are named here so that
the evaluator's clause for each is one line, and so that it is visible that the recursion
is over the *value*, which is already in hand, and not over the term. -/

/-- `Nat.rec` with a non-dependent motive: the fold of a natural number.  It is literally
    the library's `Nat.rec`, which the compiler supports; `List.rec` is not supported by
    the compiler, which is why `listFold` below is written out. -/
abbrev natFold {α : Type} (z : α) (s : Nat → α → α) (n : Nat) : α :=
  Nat.rec (motive := fun _ => α) z s n

/-! ### The window of a fold that descends more than one step

`Term.nat_rec k` descends `k + 1` steps, so its branch is given the answers at the
`k + 1` previous arguments.  The evaluator carries them as a **window** — `k + 1` values
of `τ`, nearest first — and shifts a new answer in at each step, so the fold is linear
and no answer is ever recomputed.  The window is literally an environment of the block
`natRecCtx τ (k + 1) []` of the branch's context, which is why the base values (an
ordinary `Spine`) and the branch's environment need no conversion and no cast. -/

/-- The window a depth-`k` fold carries: `k` values of `τ`, nearest first. -/
abbrev NatWin (τ : TyWf) (k : Nat) : Type := TyWf.DenList (natRecCtx τ k [])

/-- Shift a new answer in at the front, dropping the oldest: the one step of the fold. -/
def NatWin.push {τ : TyWf} : {k : Nat} → TyWf.Den τ → NatWin τ (k + 1) → NatWin τ (k + 1)
  | 0, a, _ => (a, PUnit.unit)
  | _ + 1, a, w => (a, NatWin.push w.1 w.2)

/-- The oldest answer the window holds: the value of the fold at the argument the window
    was built for. -/
def NatWin.last {τ : TyWf} : {k : Nat} → NatWin τ (k + 1) → TyWf.Den τ
  | 0, w => w.1
  | _ + 1, w => NatWin.last w.2

/-- The environment the branch of a depth-`k` fold runs in: the window in front of the
    environment of the ambient context. -/
def Env.ofWin {τ : TyWf} {Γ : Ctx} :
    {k : Nat} → NatWin τ k → Env Γ → Env (natRecCtx τ k Γ)
  | 0, _, env => env
  | _ + 1, w, env => (w.1, Env.ofWin w.2 env)

/-- The window of the depth-`k + 1` fold at `n`: it holds the answers at
    `n + k, …, n + 1, n`. -/
def natFoldKAux {τ : TyWf} {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) : Nat → NatWin τ (k + 1)
  | 0 => z
  | n + 1 => let w := natFoldKAux z s n; NatWin.push (s n w) w

/-- The depth-`k + 1` fold of a natural number: the meaning of `Term.nat_rec k`.  `z`
    holds the answers at `k, …, 0`, nearest first, and `s n w` is the branch at
    `n + k + 1`, given `n` and the window of the previous `k + 1` answers. -/
def natFoldK {τ : TyWf} {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) (n : Nat) : TyWf.Den τ :=
  NatWin.last (natFoldKAux z s n)

/-- `List.rec` with a non-dependent motive: the fold of an array.  The step is given the
    head, the tail, and the value of the fold over the tail — the three things
    `Term.array_rec`'s branch binds. -/
def listFold {α β : Type} (z : β) (s : α → List α → β → β) : List α → β
  | [] => z
  | a :: as => s a as (listFold z s as)

/-! ### The window of a fold of an array that descends more than one element

`Term.array_rec k` descends `k + 1` elements, so its branch, at `a :: as`, is given the
answers at the `k + 1` suffixes `as`, `as.drop 1`, …, `as.drop k`.  The evaluator carries
them in the very same window as the fold of a natural number does — `k + 1` values of
`τ`, nearest first — and shifts a new answer in at each element, so this fold is linear
too.  The lists that are **shorter** than the window are answered by a separate function
of the list, which in the evaluator is `LeanScript.ArrayRecBases.eval`. -/

/-- A window every entry of which is the same answer: the window of the empty list, whose
    every suffix is the empty list again. -/
def NatWin.const {τ : TyWf} (a : TyWf.Den τ) : (k : Nat) → NatWin τ k
  | 0 => PUnit.unit
  | k + 1 => (a, NatWin.const a k)

/-- The window of the depth-`k + 1` fold of an array at `l`: it holds the answers at `l`,
    `l.drop 1`, …, `l.drop k`, nearest first. -/
def listFoldKAux {α : Type} {τ : TyWf} {k : Nat} (z : List α → TyWf.Den τ)
    (s : α → List α → NatWin τ (k + 1) → TyWf.Den τ) : List α → NatWin τ (k + 1)
  | [] => NatWin.const (z []) (k + 1)
  | a :: as =>
      let w := listFoldKAux z s as
      NatWin.push (if as.length < k then z (a :: as) else s a as w) w

/-- The depth-`k + 1` fold of an array: the meaning of `Term.array_rec k`.  `z` answers
    for the lists of at most `k` elements, and `s a as w` is the branch at `a :: as` when
    `as` has at least `k` elements, given the head, the tail and the window of the
    answers at `as`, `as.drop 1`, …, `as.drop k`. -/
def listFoldK {α : Type} {τ : TyWf} {k : Nat} (z : List α → TyWf.Den τ)
    (s : α → List α → NatWin τ (k + 1) → TyWf.Den τ) (l : List α) : TyWf.Den τ :=
  (listFoldKAux z s l).1

end LeanScript

end
