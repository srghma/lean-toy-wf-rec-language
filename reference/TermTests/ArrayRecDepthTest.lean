module

public import TermTests.ArrayRecDepthTest.Cont
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over arrays: `array_rec` written out at every depth

`TermTests/NatRecDepthTest/` takes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, the `for` loop, and the
tribonacci … hexanacci numbers — and writes each of them as a term of the grammar.  This
file is the same exercise for a recursion over an **array**, which is what
`LeanScript.Term.array_rec' k` is for.

The array-valued `fib` is the **continuant**:

```lean
def cont : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * cont (b :: as) + cont as
```

It is `fib` with a coefficient at each step — on a list of `n` ones it **is** `fib (n + 1)`
(`cont_replicate_one`) — and, exactly like `fib`'s `n + 2` pattern, it reads the answer at
a suffix that is not the immediate tail.  That is the recursion the depth is for: at
`k = 1` the branch of `array_rec` is given the answers at `as` and at `as.drop 1`.

What is written out here, in the grammar and with the value of every term proved at
**every** list rather than at a few:

| the program | the node it is | here |
| :-- | :-- | :-- |
| `cont` (reads the tail of the tail) | `array_rec 1` | `contTerm_eval` |
| `cont3`, `cont4` (three and four suffixes) | `array_rec 2`, `array_rec 3` | `cont3Term_eval`, `cont4Term_eval` |
| `contTR` (tail-recursive, two accumulators) | `array_rec 0` **at a function type** | `contTRTerm_eval` |
| `contPair` (pair recursion) | `array_rec 0` at a record type | `contPairTerm_eval` |
| `contLoop` (`for x in l do …`) | the same fold, written as a loop | `contLoop_eq` |
| a recursion that **halves** the list | no depth reaches it | prose at the end |

Every program runs in one signature, `sigArith`, whose two declarations are `add` and
`mul`: arithmetic is external to the language.

Every term here is the Lean program **translated** by `#leanscript_to_term`, which reads
a structurally recursive function on `List Nat` applied to `a.toList` as `array_rec k` on
`a` (`TermTests/ArrayRecToTermTest/Common.lean`).  The bases and the branch the proofs
name are read back out of the translated term with `#leanscript_fold_bases` and
`#leanscript_fold_branch`, and an `example` beside each pins the term it is.  What is
checked on top is the value of each term, at **every** argument.
-/

namespace TermTests.ArrayRecDepth

open LeanScript
open TermTests.ArrayRecK (natT cont cont3 cont4 listFoldK_eq_cont listFoldK_eq_cont3
  listFoldK_eq_cont4)
open TermTests.FibWindow (fib)

/-- Running a closed term of `sigArith`. -/
local macro:max "runArith" t:term:max : term => `(Term.run (Sg := sigArith) envArith $t)

/-! Sections 1 and 2 — `cont` at depth one, and `cont3`, `cont4` at depths two and three —
are in `TermTests/ArrayRecDepthTest/Cont.lean`. -/

/-! ## 3. The tail-recursive loop: a fold of an array whose value is a function

```lean
def contTR : List Nat → Nat → Nat → Nat
  | [], a, _ => a
  | x :: xs, a, b => contTR xs (x * a + b) a
```

This is the array-valued `fibLoopTR`: it walks the list from the **front**, carrying the
two continuants of the prefix read so far.  It descends one element at a time, so it is
the fold at the **default** depth — but its value is not a number, it is the function of
the two accumulators.  `array_rec` folds at any type, function types included. -/

/-- The tail-recursive form. -/
def contTR : List Nat → Nat → Nat → Nat
  | [], a, _ => a
  | x :: xs, a, b => contTR xs (x * a + b) a

/-- The continuant of the tail of a list, and `0` for the empty list: the second thing
    the accumulators carry. -/
def contTail : List Nat → Nat
  | [] => 0
  | _ :: xs => cont xs

/-- One element of the continuant, in the form the accumulators use. -/
theorem cont_cons : (x : Nat) → (xs : List Nat) → cont (x :: xs) = x * cont xs + contTail xs
  | x, [] => by show x = x * 1 + 0; omega
  | _, _ :: _ => rfl

/-- The invariant of the loop: it is linear in the two accumulators, with the continuant
    of the list and the continuant of its tail as the coefficients. -/
theorem contTR_eq : (l : List Nat) → (a b : Nat) → contTR l a b = a * cont l + b * contTail l
  | [], a, b => by show a = a * 1 + b * 0; omega
  | x :: xs, a, b => by
      show contTR xs (x * a + b) a = a * cont (x :: xs) + b * contTail (x :: xs)
      rw [contTR_eq xs (x * a + b) a, cont_cons x xs,
        show contTail (x :: xs) = cont xs from rfl]
      grind

/-- Started at `(1, 0)`, the loop is the continuant. -/
theorem contTR_start (l : List Nat) : contTR l 1 0 = cont l := by
  rw [contTR_eq]
  omega

/-- The type the fold runs at: the two accumulators. -/
abbrev Acc2 : TyWf := natT ⇒ natT ⇒ natT

/-- The loop started at `(1, 0)`, on the elements of an array. -/
def contTRArr (a : Array Nat) : Nat := contTR a.toList 1 0

/-- `contTR`, as a term: the fold of an array at a function type. -/
def contTRTerm : Term sigArith [] (TyWf.array natT ⇒ natT) := #leanscript_to_term contTRArr

/-- The short-list answer of the loop: `.nil loopZero`. -/
def loopBases : ArrayRecBases sigArith ArrCtx natT Acc2 0 := #leanscript_fold_bases contTRTerm

/-- The value for the empty list: `fun a _ => a`. -/
def loopZero : Term sigArith ArrCtx Acc2 := match loopBases with | .nil z => z

/-- The step: it binds the head `x` (index `0`), the tail (index `1`) and the loop over
    the tail (index `2`), and answers `fun a b => loop (x * a + b) a`. -/
def loopStep : Term sigArith (natT :: TyWf.array natT :: natRecCtx Acc2 1 ArrCtx) Acc2 :=
  #leanscript_fold_branch contTRTerm

-- [SKIPPED BY PROFILE_LAKE] example : contTRTerm =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.ap (.ap (.array_rec' 0 (.var (v♯0)) (.nil loopZero) loopStep) (.nat_mk 1))
-- [SKIPPED BY PROFILE_LAKE]       (.nat_mk 0)) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : loopZero = .lam (.lam (.var (v♯1))) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : loopStep =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.lam
-- [SKIPPED BY PROFILE_LAKE]       (.ap (.ap (.var (v♯4)) (addT (mulT (.var (v♯2)) (.var (v♯1))) (.var (v♯0))))
-- [SKIPPED BY PROFILE_LAKE]         (.var (v♯1)))) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runArith contTRTerm #[] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTRTerm #[3, 4] = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTRTerm #[1, 2, 3] = 10 := by kernel_rfl

/-- **Any** depth-zero fold at the accumulator type with these two equations is the
    tail-recursive loop. -/
theorem listFoldK_eq_contTR (z : List Nat → TyWf.Den Acc2)
    (s : Nat → List Nat → NatWin Acc2 1 → TyWf.Den Acc2)
    (hz : z [] = fun a _ => a)
    (hs : ∀ x xs w, s x xs w = fun a b => w.1 (x * a + b) a) :
    (l : List Nat) → (a b : Nat) →
      listFoldK (τ := Acc2) (k := 0) z s l a b = contTR l a b
  | [], a, b => by
      rw [listFoldK_base (τ := Acc2) (k := 0) _ _ [] (by simp), hz]
      rfl
  | x :: xs, a, b => by
      rw [listFoldK_step (τ := Acc2) (k := 0) _ _ x xs (by simp), hs]
      show listFoldK (τ := Acc2) (k := 0) z s xs (x * a + b) a = contTR (x :: xs) a b
      rw [listFoldK_eq_contTR z s hz hs xs (x * a + b) a]
      rfl

/-- The short-list answers `Term.eval` uses for the loop. -/
def loopEvalZ (env : Env ArrCtx) : List Nat → TyWf.Den Acc2 :=
  fun m => ArrayRecBases.eval envArith loopBases env m

/-- The branch `Term.eval` uses for the loop. -/
def loopEvalS (env : Env ArrCtx) :
    Nat → List Nat → NatWin Acc2 1 → TyWf.Den Acc2 :=
  fun hd tl w =>
    Term.eval envArith loopStep (hd, tl.toArray, Env.ofWin w env)

theorem loopEvalFold_eq (env : Env ArrCtx) (l : List Nat) (a b : Nat) :
    listFoldK (τ := Acc2) (k := 0) (loopEvalZ env) (loopEvalS env) l a b = contTR l a b :=
  listFoldK_eq_contTR _ _ rfl (fun _ _ _ => rfl) l a b

/-- The tail-recursive term computes the continuant, at every list. -/
theorem contTRTerm_eval (l : List Nat) : runArith contTRTerm l.toArray = cont l := by
  show listFoldK (τ := Acc2) (k := 0) (loopEvalZ (l.toArray, Env.nil)) (loopEvalS (l.toArray, Env.nil))
    l 1 0 = cont l
  rw [loopEvalFold_eq]
  exact contTR_start l

/-! ## 4. The pair recursion: a fold of an array whose value is a record

```lean
def contPair : List Nat → Nat × Nat
  | [] => (1, 0)
  | x :: xs => let (a, b) := contPair xs; (x * a + b, a)
```

The array-valued `fibPair`: the one-element fold at a two-field record, whose fields are
the continuant of the list and the continuant of its tail. -/

/-- The pair recursion (`@[inline]`, so that `contFromPair` below translates to the
    fold itself). -/
@[inline] def contPair : List Nat → Nat × Nat
  | [] => (1, 0)
  | x :: xs =>
    let (a, b) := contPair xs
    (x * a + b, a)

/-- The user's own invariant: the pair at `l` is `(K l, K (tail l))`. -/
theorem contPair_eq : (l : List Nat) → contPair l = (cont l, contTail l)
  | [] => rfl
  | x :: xs => by
      show (match contPair xs with | (a, b) => ((x * a + b, a) : Nat × Nat)) =
        (cont (x :: xs), contTail (x :: xs))
      rw [contPair_eq xs, cont_cons x xs, show contTail (x :: xs) = cont xs from rfl]

/-- The record the fold runs at: the two continuants. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- Its type. -/
abbrev Pair : TyWf := TyWf.record pairSchema

/-- The pair recursion on the elements of an array. -/
def contPairArr (a : Array Nat) : Nat × Nat := contPair a.toList

/-- The continuant read off the pair. -/
def contFromPair (a : Array Nat) : Nat := (contPair a.toList).1

/-- `contPair`, as a term: the fold of an array at a record type. -/
def contPairTerm : Term sigArith [] (TyWf.array natT ⇒ Pair) :=
  #leanscript_to_term contPairArr

/-- The short-list answer of the pair recursion: `.nil pairZero`. -/
def pairBases : ArrayRecBases sigArith ArrCtx natT Pair 0 := #leanscript_fold_bases contPairTerm

/-- The pair of the empty list: `(1, 0)`. -/
def pairZero : Term sigArith ArrCtx Pair := match pairBases with | .nil z => z

/-- The step: it binds the head (index `0`), the tail (index `1`) and the pair at the
    tail (index `2`), takes that pair apart — so inside, index `0` is `K xs` and index
    `1` is `K (tail xs)`, and the head has moved to index `2` — and answers with the pair
    at `x :: xs`. -/
def pairStep : Term sigArith (natT :: TyWf.array natT :: natRecCtx Pair 1 ArrCtx) Pair :=
  #leanscript_fold_branch contPairTerm

-- [SKIPPED BY PROFILE_LAKE] example : contPairTerm = .lam (.array_rec' 0 (.var (v♯0)) (.nil pairZero) pairStep) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : pairZero = .record_mk pairSchema (.cons (.nat_mk 1) (.cons (.nat_mk 0) .nil)) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : pairStep =
-- [SKIPPED BY PROFILE_LAKE]     .record_casesOn' (.var (v♯2))
-- [SKIPPED BY PROFILE_LAKE]       (.record_mk pairSchema
-- [SKIPPED BY PROFILE_LAKE]         (.cons (addT (mulT (.var (v♯2)) (.var (v♯0))) (.var (v♯1)))
-- [SKIPPED BY PROFILE_LAKE]           (.cons (.var (v♯0)) .nil))) := by kernel_rfl

/-- The continuant read off the pair: its first field.  The translation inlines the
    fold, so the term takes apart the fold itself rather than applying `contPairTerm`:
    `.lam (.record_casesOn' (.array_rec' 0 (.var (v♯0)) pairBases pairStep) (.var (v♯0)))`. -/
def contFromPairTerm : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  #leanscript_to_term contFromPair

-- [SKIPPED BY PROFILE_LAKE] example : contFromPairTerm =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.record_casesOn' (fs := pairSchema) (.array_rec' 0 (.var (v♯0)) pairBases pairStep)
-- [SKIPPED BY PROFILE_LAKE]       (.var (v♯0))) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runArith contFromPairTerm #[] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contFromPairTerm #[3, 4] = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contFromPairTerm #[1, 2, 3] = 10 := by kernel_rfl

/-- **Any** depth-zero fold at the record type with these two equations is the pair
    recursion. -/
theorem listFoldK_eq_contPair (z : List Nat → TyWf.Den Pair)
    (s : Nat → List Nat → NatWin Pair 1 → TyWf.Den Pair)
    (hz : z [] = (1, 0, PUnit.unit))
    (hs : ∀ x xs w, s x xs w = (x * w.1.1 + w.1.2.1, w.1.1, PUnit.unit)) :
    (l : List Nat) →
      listFoldK (τ := Pair) (k := 0) z s l = (cont l, contTail l, PUnit.unit)
  | [] => by
      rw [listFoldK_base (τ := Pair) (k := 0) _ _ [] (by simp), hz]
      rfl
  | x :: xs => by
      rw [listFoldK_step (τ := Pair) (k := 0) _ _ x xs (by simp), hs]
      show ((x * (listFoldK (τ := Pair) (k := 0) z s xs).1 +
            (listFoldK (τ := Pair) (k := 0) z s xs).2.1,
          (listFoldK (τ := Pair) (k := 0) z s xs).1, PUnit.unit) : Nat × Nat × PUnit) = _
      rw [listFoldK_eq_contPair z s hz hs xs, cont_cons x xs,
        show contTail (x :: xs) = cont xs from rfl]

/-- The short-list answers and the branch `Term.eval` uses for the pair recursion. -/
def pairEvalZ (env : Env ArrCtx) : List Nat → TyWf.Den Pair :=
  fun m => ArrayRecBases.eval envArith pairBases env m

def pairEvalS (env : Env ArrCtx) : Nat → List Nat → NatWin Pair 1 → TyWf.Den Pair :=
  fun hd tl w =>
    Term.eval envArith pairStep (hd, tl.toArray, Env.ofWin w env)

theorem pairEvalFold_eq (env : Env ArrCtx) (l : List Nat) :
    listFoldK (τ := Pair) (k := 0) (pairEvalZ env) (pairEvalS env) l =
      (cont l, contTail l, PUnit.unit) :=
  listFoldK_eq_contPair _ _ rfl (fun _ _ _ => rfl) l

/-- The record-valued term **is** `contPair`, field by field. -/
theorem contPairTerm_eval (l : List Nat) :
    runArith contPairTerm l.toArray = ((contPair l).1, (contPair l).2, PUnit.unit) := by
  show listFoldK (τ := Pair) (k := 0) (pairEvalZ (l.toArray, Env.nil)) (pairEvalS (l.toArray, Env.nil)) l = _
  rw [pairEvalFold_eq, contPair_eq l]

/-- And its first field is the continuant, at every list. -/
theorem contFromPairTerm_eval (l : List Nat) : runArith contFromPairTerm l.toArray = cont l := by
  show (listFoldK (τ := Pair) (k := 0) (pairEvalZ (l.toArray, Env.nil)) (pairEvalS (l.toArray, Env.nil))
    l).1 = cont l
  rw [pairEvalFold_eq]

/-! ## 5. The `for` loop

```lean
def contLoop (l : List Nat) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a
```

Desugared, this is `ForIn.forIn l (1, 0) …` in the identity monad: a fold over the list
whose state is the pair of mutable variables — that is, §3 and §4 written with different
syntax, and so the same term of the grammar. -/

/-- The loop, as one would write it. -/
def contLoop (l : List Nat) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a

-- [SKIPPED BY PROFILE_LAKE] example : contLoop [] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contLoop [3, 4] = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contLoop [1, 2, 3] = 10 := by kernel_rfl

/-- The same loop, started anywhere: what the induction needs. -/
def contLoopFrom (l : List Nat) (a0 b0 : Nat) : Nat := Id.run do
  let mut a := a0
  let mut b := b0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a

/-- One turn of the loop. -/
theorem contLoopFrom_cons (x : Nat) (xs : List Nat) (a b : Nat) :
    contLoopFrom (x :: xs) a b = contLoopFrom xs (x * a + b) a := by
  simp [contLoopFrom, Id.run]

/-- The loop **is** the tail-recursive form, from any state. -/
theorem contLoopFrom_eq : (l : List Nat) → (a b : Nat) → contLoopFrom l a b = contTR l a b
  | [], _, _ => rfl
  | x :: xs, a, b => by
      rw [contLoopFrom_cons, contLoopFrom_eq xs (x * a + b) a]
      rfl

/-- So the loop is the continuant, at every list. -/
theorem contLoop_eq (l : List Nat) : contLoop l = cont l := by
  show contLoopFrom l 1 0 = cont l
  rw [contLoopFrom_eq]
  exact contTR_start l

/-! ## 6. What no depth reaches

The one program of the `fib` family that is refused is `fibFast`, whose recursive call is
at `n / 2`.  Its array analogue is a recursion that **halves the list**:

```lean
def contFast : List Nat → Nat
  | [] => 1
  | l => … contFast (l.take (l.length / 2)) … contFast (l.drop (l.length / 2)) …
```

A depth is a fixed number of *elements* to descend by, and the window the evaluator
carries holds the answers at the `k + 1` immediate suffixes.  A call at a list that is
half as long is not a call at a suffix at all, so no `k` reaches it, exactly as no depth
of `nat_rec` reaches `n / 2`.  That is a limit of the folds, not of the depth: it needs a
recursion justified by a measure, which this grammar deliberately does not have.
-/

end TermTests.ArrayRecDepth

end