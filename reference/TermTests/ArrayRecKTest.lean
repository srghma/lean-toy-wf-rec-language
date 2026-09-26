module

public import LeanScript.ArrayRecFacts
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# One fold of an array for every lookback depth

`TermTests/NatRecKTest.lean` checks that **one** constructor serves `nat_rec`, `nat_rec2`,
`nat_rec3`, … at once.  This file is the same check for the fold of an *array*, which now
carries the same depth:

```lean
| array_rec : ∀ {Γ σ τ} (k : Nat := 0), Term Sg Γ (.array σ) →
    ArrayRecBases Sg Γ σ τ k →
    Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ → Term Sg Γ τ
```

A recursion over a list that reads the answer at more than the immediate tail — the
analogue of `fib`'s `n + 2` pattern — is exactly what a depth needs to be added for:

```lean
def cont : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * cont (b :: as) + cont as
```

That is the **continuant**: the numerator of the continued fraction
`a₀ + 1/(a₁ + 1/(a₂ + …))`, and the array-valued `fib` — on a list of `n` ones it is
`fib (n + 1)`, which `TermTests/ArrayRecDepthTest.lean` proves.  It reads the answer at
`as`, which is the tail of the tail, so no one-element fold writes it.

What is checked here, at the level of the meaning (`LeanScript.listFoldK`):

1. **Every depth is the one fold.**  Depth zero **is** the old one-element fold
   `LeanScript.listFold` (`LeanScript.listFoldK_eq_listFold`), depth one computes the
   continuant, and a genuine depth-two recursion — the continuant that looks back three
   suffixes — runs on it.

2. **The types reduce to what one would have written by hand.**  The branch's context at
   a literal depth is the readable `σ :: array σ :: τ :: τ :: Γ`, depth zero is the old
   `array_rec`'s own type definitionally, and the window the evaluator carries **is** the
   environment of that block of the context.
-/

namespace TermTests.ArrayRecK

open LeanScript

/-- The type the folds below run at: its values are Lean's `Nat`. -/
abbrev natT : TyWf := TyWf.prim .nat

-- [SKIPPED BY PROFILE_LAKE] example : TyWf.Den natT = Nat := by kernel_rfl

/-! ## Depth zero is the fold that was there before -/

/-- The sum of a list, as the depth-zero fold: the short lists are the empty one alone,
    and the window holds the single answer at the tail. -/
def sumFold : List Nat → Nat :=
  listFoldK (τ := natT) (k := 0) (fun _ => 0) (fun a _ w => a + w.1)

/-- It **is** `listFold`, which is what the node meant before it had a depth. -/
theorem sumFold_eq_listFold (l : List Nat) :
    sumFold l = listFold 0 (fun a _ ih => a + ih) l :=
  listFoldK_eq_listFold (τ := natT) 0 (fun a _ ih => a + ih) l

-- [SKIPPED BY PROFILE_LAKE] example : sumFold [1, 2, 3, 4] = 10 := by kernel_rfl

/-! ## Depth one: a recursion that reads the tail of the tail -/

/-- The continuant, the array-valued `fib`: `K [] = 1`, `K [a] = a` and
    `K (a :: b :: as) = a * K (b :: as) + K as`. -/
def cont : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * cont (b :: as) + cont as

/-- The continuant as the depth-**one** fold: the lists of at most one element are
    answered directly, and the branch at `a :: as` reads the answers at `as` (`w.1`) and
    at `as.drop 1` (`w.2.1`). -/
def contFold : List Nat → Nat :=
  listFoldK (τ := natT) (k := 1)
    (fun l => match l with | [] => 1 | a :: _ => a)
    (fun a _ w => a * w.1 + w.2.1)

-- [SKIPPED BY PROFILE_LAKE] example : contFold [] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contFold [3] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contFold [3, 4] = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contFold [1, 1, 1, 1, 1, 1] = 13 := by kernel_rfl

/-- **Any** depth-one fold with these three equations computes the continuant: the empty
    list answers `1`, a one-element list answers its element, and the branch multiplies
    the head into the answer at the tail and adds the answer at the tail of the tail.

    It is stated of an arbitrary `z` and `s` so that it serves both the fold written here
    and the one `Term.eval` runs for the term of `TermTests/ArrayRecDepthTest.lean`, whose
    branches are closures over an environment. -/
theorem listFoldK_eq_cont (z : List Nat → Nat) (s : Nat → List Nat → NatWin natT 2 → Nat)
    (hz0 : z [] = 1) (hz1 : ∀ a, z [a] = a)
    (hs : ∀ a as w, s a as w = a * w.1 + w.2.1) :
    (l : List Nat) → listFoldK (τ := natT) (k := 1) z s l = cont l
  | [] => by rw [listFoldK_base (τ := natT) (k := 1) _ _ [] (by simp), hz0]; rfl
  | [a] => by rw [listFoldK_base (τ := natT) (k := 1) _ _ [a] (by simp), hz1]; rfl
  | a :: b :: as => by
      rw [listFoldK_step (τ := natT) (k := 1) _ _ a (b :: as) (by simp), hs]
      show a * listFoldK (τ := natT) (k := 1) z s (b :: as) +
        listFoldK (τ := natT) (k := 1) z s as = cont (a :: b :: as)
      rw [listFoldK_eq_cont z s hz0 hz1 hs (b :: as), listFoldK_eq_cont z s hz0 hz1 hs as]
      rfl

/-- The base equation, read off `listFoldK_base`. -/
theorem contFold_nil : contFold [] = 1 :=
  listFoldK_base (τ := natT) (k := 1) _ _ [] (by simp)

theorem contFold_single (a : Nat) : contFold [a] = a :=
  listFoldK_base (τ := natT) (k := 1) _ _ [a] (by simp)

/-- The step equation, read off `listFoldK_step`: at a list with at least two elements
    the branch is given the answers at the two next suffixes. -/
theorem contFold_step (a b : Nat) (as : List Nat) :
    contFold (a :: b :: as) = a * contFold (b :: as) + contFold as :=
  listFoldK_step (τ := natT) (k := 1) _ _ a (b :: as) (by simp)

/-- And the fold **is** the continuant, at every list. -/
theorem contFold_eq (l : List Nat) : contFold l = cont l :=
  listFoldK_eq_cont _ _ rfl (fun _ => rfl) (fun _ _ _ => rfl) l

/-! ## Depth two: a recursion that reads three suffixes -/

/-- A continuant that looks back three suffixes — the array-valued tribonacci
    numbers. -/
def cont3 : List Nat → Nat
  | [] => 1
  | [a] => a
  | [a, b] => a * b
  | a :: b :: c :: as => a * cont3 (b :: c :: as) + cont3 (c :: as) + cont3 as

/-- Its depth-**two** fold: three short lists to answer, and a window of three. -/
def cont3Fold : List Nat → Nat :=
  listFoldK (τ := natT) (k := 2)
    (fun l => match l with | [] => 1 | [a] => a | a :: b :: _ => a * b)
    (fun a _ w => a * w.1 + w.2.1 + w.2.2.1)

-- [SKIPPED BY PROFILE_LAKE] example : cont3Fold [] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont3Fold [5] = 5 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont3Fold [5, 6] = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont3Fold [1, 1, 1, 1, 1, 1] = 17 := by kernel_rfl

theorem cont3Fold_nil : cont3Fold [] = 1 :=
  listFoldK_base (τ := natT) (k := 2) _ _ [] (by simp)

theorem cont3Fold_single (a : Nat) : cont3Fold [a] = a :=
  listFoldK_base (τ := natT) (k := 2) _ _ [a] (by simp)

theorem cont3Fold_two (a b : Nat) : cont3Fold [a, b] = a * b :=
  listFoldK_base (τ := natT) (k := 2) _ _ [a, b] (by simp)

theorem cont3Fold_step (a b c : Nat) (as : List Nat) :
    cont3Fold (a :: b :: c :: as) =
      a * cont3Fold (b :: c :: as) + cont3Fold (c :: as) + cont3Fold as :=
  listFoldK_step (τ := natT) (k := 2) _ _ a (b :: c :: as) (by simp)

/-- **Any** depth-two fold with these four equations computes `cont3`. -/
theorem listFoldK_eq_cont3 (z : List Nat → Nat) (s : Nat → List Nat → NatWin natT 3 → Nat)
    (hz0 : z [] = 1) (hz1 : ∀ a, z [a] = a) (hz2 : ∀ a b, z [a, b] = a * b)
    (hs : ∀ a as w, s a as w = a * w.1 + w.2.1 + w.2.2.1) :
    (l : List Nat) → listFoldK (τ := natT) (k := 2) z s l = cont3 l
  | [] => by rw [listFoldK_base (τ := natT) (k := 2) _ _ [] (by simp), hz0]; rfl
  | [a] => by rw [listFoldK_base (τ := natT) (k := 2) _ _ [a] (by simp), hz1]; rfl
  | [a, b] => by rw [listFoldK_base (τ := natT) (k := 2) _ _ [a, b] (by simp), hz2]; rfl
  | a :: b :: c :: as => by
      rw [listFoldK_step (τ := natT) (k := 2) _ _ a (b :: c :: as) (by simp), hs]
      show a * listFoldK (τ := natT) (k := 2) z s (b :: c :: as) +
          listFoldK (τ := natT) (k := 2) z s (c :: as) +
          listFoldK (τ := natT) (k := 2) z s as = cont3 (a :: b :: c :: as)
      rw [listFoldK_eq_cont3 z s hz0 hz1 hz2 hs (b :: c :: as),
        listFoldK_eq_cont3 z s hz0 hz1 hz2 hs (c :: as),
        listFoldK_eq_cont3 z s hz0 hz1 hz2 hs as]
      rfl

/-- The depth-two fold **is** that recursion, at every list. -/
theorem cont3Fold_eq (l : List Nat) : cont3Fold l = cont3 l :=
  listFoldK_eq_cont3 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) l

/-! ## Depth three, and the pattern that continues

Nothing about the node stops at two: a recursion that reads four suffixes is the same
constructor at `k = 3`.  Its window is four wide, and it has four short lists to
answer. -/

/-- A continuant that looks back four suffixes — the array-valued tetranacci numbers. -/
def cont4 : List Nat → Nat
  | [] => 1
  | [a] => a
  | [a, b] => a * b
  | [a, b, c] => a * b * c
  | a :: b :: c :: d :: as =>
      a * cont4 (b :: c :: d :: as) + cont4 (c :: d :: as) + cont4 (d :: as) + cont4 as

/-- Its depth-**three** fold. -/
def cont4Fold : List Nat → Nat :=
  listFoldK (τ := natT) (k := 3)
    (fun l => match l with
      | [] => 1
      | [a] => a
      | [a, b] => a * b
      | a :: b :: c :: _ => a * b * c)
    (fun a _ w => a * w.1 + w.2.1 + w.2.2.1 + w.2.2.2.1)

-- [SKIPPED BY PROFILE_LAKE] example : cont4Fold [] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont4Fold [2, 3, 4] = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont4Fold [1, 1, 1, 1, 1, 1] = 13 := by kernel_rfl

/-- **Any** depth-three fold with these five equations computes `cont4`. -/
theorem listFoldK_eq_cont4 (z : List Nat → Nat) (s : Nat → List Nat → NatWin natT 4 → Nat)
    (hz0 : z [] = 1) (hz1 : ∀ a, z [a] = a) (hz2 : ∀ a b, z [a, b] = a * b)
    (hz3 : ∀ a b c, z [a, b, c] = a * b * c)
    (hs : ∀ a as w, s a as w = a * w.1 + w.2.1 + w.2.2.1 + w.2.2.2.1) :
    (l : List Nat) → listFoldK (τ := natT) (k := 3) z s l = cont4 l
  | [] => by rw [listFoldK_base (τ := natT) (k := 3) _ _ [] (by simp), hz0]; rfl
  | [a] => by rw [listFoldK_base (τ := natT) (k := 3) _ _ [a] (by simp), hz1]; rfl
  | [a, b] => by rw [listFoldK_base (τ := natT) (k := 3) _ _ [a, b] (by simp), hz2]; rfl
  | [a, b, c] => by
      rw [listFoldK_base (τ := natT) (k := 3) _ _ [a, b, c] (by simp), hz3]; rfl
  | a :: b :: c :: d :: as => by
      rw [listFoldK_step (τ := natT) (k := 3) _ _ a (b :: c :: d :: as) (by simp), hs]
      show a * listFoldK (τ := natT) (k := 3) z s (b :: c :: d :: as) +
          listFoldK (τ := natT) (k := 3) z s (c :: d :: as) +
          listFoldK (τ := natT) (k := 3) z s (d :: as) +
          listFoldK (τ := natT) (k := 3) z s as = cont4 (a :: b :: c :: d :: as)
      rw [listFoldK_eq_cont4 z s hz0 hz1 hz2 hz3 hs (b :: c :: d :: as),
        listFoldK_eq_cont4 z s hz0 hz1 hz2 hz3 hs (c :: d :: as),
        listFoldK_eq_cont4 z s hz0 hz1 hz2 hz3 hs (d :: as),
        listFoldK_eq_cont4 z s hz0 hz1 hz2 hz3 hs as]
      rfl

/-- The depth-three fold **is** that recursion, at every list. -/
theorem cont4Fold_eq (l : List Nat) : cont4Fold l = cont4 l :=
  listFoldK_eq_cont4 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) l

/-! ## The window really is the history

The reason the fold is linear and not exponential: the `k + 1` answers the branch is
given are carried, not recomputed. -/

example (l : List Nat) :
    listFoldKAux (τ := natT) (k := 1)
        (fun l => match l with | [] => 1 | a :: _ => a) (fun a _ w => a * w.1 + w.2.1) l =
      (contFold l, contFold (l.drop 1), PUnit.unit) :=
  listFoldKAux_eq_ofFunList (τ := natT) (k := 1) _ _ l

/-! ## The types the node asks for -/

section Types

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf}

-- [SKIPPED BY PROFILE_LAKE] /-- Depth zero: the branch's context is exactly the one-element fold's, so the node
-- [SKIPPED BY PROFILE_LAKE]     subsumes it **definitionally** — no term had to be rewritten for the depth. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term Sg (σ :: TyWf.array σ :: natRecCtx τ 1 Γ) τ =
-- [SKIPPED BY PROFILE_LAKE]     Term Sg (σ :: TyWf.array σ :: τ :: Γ) τ := by kernel_rfl

/-- Depth one: the context a hand-written two-suffix fold would be written in. -/
theorem arrayBranchCtx_two : σ :: TyWf.array σ :: natRecCtx τ 2 Γ =
    σ :: TyWf.array σ :: τ :: τ :: Γ := rfl

/-- Depth two, and so on: the de Bruijn indices of the branch stay readable. -/
theorem arrayBranchCtx_three : σ :: TyWf.array σ :: natRecCtx τ 3 Γ =
    σ :: TyWf.array σ :: τ :: τ :: τ :: Γ := rfl

/-- The short lists are answered by a block written out as usual: the answer for the
    empty list, then — with the first element bound — the answer for what is left. -/
def basesOne (empty : Term Sg Γ τ) (single : Term Sg (σ :: Γ) τ) :
    ArrayRecBases Sg Γ σ τ 1 :=
  .cons empty (.nil single)

/-- At depth zero there is one short list, the empty one, and its answer binds
    nothing. -/
def basesZero (empty : Term Sg Γ τ) : ArrayRecBases Sg Γ σ τ 0 := .nil empty

/-- The window the evaluator carries is the same one the fold of a natural number
    carries: the environment of that block of the context. -/
theorem win_eq_denList : NatWin τ 3 = TyWf.DenList (natRecCtx τ 3 []) := rfl

/-- And the environment of the branch is the head, the tail, and the window in front of
    the environment of the ambient context — no cast and no length proof. -/
example (hd : TyWf.Den σ) (tl : Array (TyWf.Den σ)) (w : NatWin τ 2) (env : Env Γ) :
    Env (σ :: TyWf.array σ :: natRecCtx τ 2 Γ) := (hd, tl, Env.ofWin w env)

end Types

end TermTests.ArrayRecK

end
