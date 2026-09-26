module

public import TermTests.NatRecKTest
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# The five `fib`s, and which of them the grammar already writes

`proposals/FibProposals.md` is written around five Lean definitions of the same function — the
two-step recursion, the tail-recursive loop, the `for` loop with two mutable variables,
the pair recursion, and fast doubling.  The point of supporting them *as they are* is
that the code the backend prints should look like the code that was written, so the
question "which of these is a term of the grammar today?" has to be answered one
definition at a time rather than for `fib` in general.

This file answers it by translating the definitions with `#leanscript_to_term` (the terms
are written out beside them in `example`s) and proving what they compute.  It is the
evidence behind the table in §2 of `proposals/FibProposals.md`:

| definition | what it needs | here |
| :-- | :-- | :-- |
| `fibLoopTR` / `fibTR` | `nat_rec` **at a function type** — already there | `fibTR_term_eval` |
| `fibPair` / `fib2` | `nat_rec` at a record type — already there | `fibPair_term_eval` |
| `fibLoop` (`for` loop) | the same fold, and a case for `for` in the translation | prose below; translated in `TermTests/NatRecDepthTest/` |
| `fib` (`n + 2` pattern) | a depth-two fold: a window, or the depth-indexed node | `TermTests/FibWindowTest.lean`, `TermTests/NatRecKTest.lean`, `TermTests/NatRecDepthTest/` |
| `fibFast` (`n / 2`) | a descent that is not by a fixed number of steps | prose below |

Since this file was written, the node and the two translation cases it names as missing
have been implemented: `LeanScript.Term.nat_rec' k` descends `k + 1` steps, and
`#leanscript_to_term` translates both the `n + 2` pattern and a `for` loop over a range.
`TermTests/NatRecDepthTest/` hands each of the five definitions to the translation as
it is written.  What is below is the evidence that the first two need nothing beyond a
fold at a function type and at a record type.

Everything below runs in the signature of `TermTests/FibWindowTest.lean`: one declaration,
`add`.
-/

namespace TermTests.FibAlgorithms

open LeanScript
open TermTests.FibWindow (fib sigAdd envAdd addT)

local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-! ## 1. The tail-recursive loop: a fold whose value is a function

```lean
def fibLoopTR : Nat → Nat → Nat → Nat
  | 0     => fun a _ => a
  | n + 1 => fun a b => fibLoopTR n b (a + b)

def fibTR (n : Nat) : Nat := fibLoopTR n 0 1
```

The recursion descends one step, but its accumulators change on the way down, so the
value of the fold is not a number: it is the **function** `Nat → Nat → Nat` that takes
the two accumulators.  `Term.nat_rec` folds at any type `τ`, function types included, so
this needs nothing new — which is worth saying, because a first reading of "the branch is
given the value at the predecessor" suggests that an accumulator-passing loop is out of
reach.
-/

/-- The Lean definition to be expressed.  It matches on the counter only and answers
    with the function of the two accumulators, so that its translation is the fold
    itself, `.lam (.nat_rec' …)`; matching on all three arguments would translate to the
    same fold under three `lam`s, applied to the accumulators (`@[inline]`, so that
    `fibTR` below translates to the fold applied to `0` and `1`). -/
@[inline] def fibLoopTR : Nat → Nat → Nat → Nat
  | 0 => fun a _ => a
  | n + 1 => fun a b => fibLoopTR n b (a + b)

/-- `fibTR`, the wrapper. -/
def fibTR (n : Nat) : Nat := fibLoopTR n 0 1

/-- The type the fold runs at: the two accumulators. -/
abbrev Acc2 : TyWf := TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat

-- kept in direct style (not normalized, `LeanScript.ToTerm.Normalize`), so that
-- `#leanscript_fold_bases` reads its base value as a term (a `Spine`)
set_option leanscript.toTerm.normalize false in
/-- `fibLoopTR`, as a term: a fold at a function type. -/
def loop_term : Term sigAdd [] (TyWf.prim .nat ⇒ Acc2) := #leanscript_to_term fibLoopTR

/-- The base value: `fun a _ => a`. -/
def loopZero : Term sigAdd [TyWf.prim .nat] Acc2 :=
  match (#leanscript_fold_bases loop_term :
      Spine sigAdd [TyWf.prim .nat] (natRecCtx Acc2 1 [])) with
  | .cons z .nil => z

/-- The step: it binds the predecessor (index `0`) and the loop at the predecessor
    (index `1`), and answers `fun a b => loop b (a + b)`. -/
def loopStep : Term sigAdd (TyWf.prim .nat :: Acc2 :: [TyWf.prim .nat]) Acc2 :=
  #leanscript_fold_branch loop_term

-- [SKIPPED BY PROFILE_LAKE] example : loopZero = .lam (.lam (.var (v♯1))) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : loopStep =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.lam
-- [SKIPPED BY PROFILE_LAKE]       (.ap (.ap (.var (v♯3)) (.var (v♯0))) (addT (.var (v♯1)) (.var (v♯0))))) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : loop_term = .lam (.nat_rec' 0 (.var (v♯0)) (.cons loopZero .nil) loopStep) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

/-- `fibTR`, as a term: the loop started at `(0, 1)`.  The translation inlines the loop,
    so the term applies the fold itself rather than `loop_term`. -/
def fibTR_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term fibTR

-- [SKIPPED BY PROFILE_LAKE] example : fibTR_term =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.ap (.ap (.nat_rec' 0 (.var (v♯0)) (.cons loopZero .nil) loopStep) (.nat_mk 0))
-- [SKIPPED BY PROFILE_LAKE]       (.nat_mk 1)) := by kernel_rfl

/-- The term **is** `fibLoopTR`, at every argument and at both accumulators. -/
theorem loop_term_eval (n a b : Nat) : runAdd loop_term n a b = fibLoopTR n a b := by
  induction n generalizing a b with
  | zero => kernel_rfl
  | succ n ih =>
      have h : runAdd loop_term (n + 1) a b = runAdd loop_term n b (a + b) := by kernel_rfl
      rw [h]
      exact ih b (a + b)

/-- `fibLoopTR` started at `(fib k, fib (k + 1))` answers `fib (n + k)` — the user's own
    invariant, which is what makes the tail-recursive loop correct. -/
theorem fibLoopTR_eq (n k : Nat) : fibLoopTR n (fib k) (fib (k + 1)) = fib (n + k) := by
  induction n generalizing k with
  | zero =>
      show fib k = fib (0 + k)
      rw [Nat.zero_add]
  | succ n ih =>
      have h : fib k + fib (k + 1) = fib (k + 2) := rfl
      show fibLoopTR n (fib (k + 1)) (fib k + fib (k + 1)) = fib (n + 1 + k)
      rw [h, ih (k + 1)]
      congr 1
      omega

/-- The tail-recursive term computes `fib`, at every argument. -/
theorem fibTR_term_eval (n : Nat) : runAdd fibTR_term n = fib n := by
  have h : runAdd fibTR_term n = runAdd loop_term n 0 1 := rfl
  rw [h, loop_term_eval]
  exact (fibLoopTR_eq n 0).trans (by rw [Nat.add_zero])

-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTR_term 0 = 0 := by rw [fibTR_term_eval]; rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTR_term 10 = 55 := by rw [fibTR_term_eval]; rfl
-- [SKIPPED BY PROFILE_LAKE] example : runAdd fibTR_term 20 = 6765 := by rw [fibTR_term_eval]; rfl

/-! ## 2. The pair recursion: a fold whose value is a record

```lean
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

def fib2 (n : Nat) : Nat := (fibPair n).1
```

This is the one-step fold at a record type, and it is **exactly** the term
`TermTests/FibWindowTest.lean` already builds: `window` is `fibPair` and `fib_term` is
`fib2`.  Nothing new is needed, and the theorem below says so in the user's own terms.
-/

/-- The Lean definition to be expressed. -/
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibPair n
    (b, a + b)

/-- `fib2`, the wrapper. -/
def fib2 (n : Nat) : Nat := (fibPair n).1

/-- The user's own invariant: the pair at `n` is `(fib n, fib (n + 1))`. -/
theorem fibPair_eq : (n : Nat) → fibPair n = (fib n, fib (n + 1))
  | 0 => rfl
  | n + 1 => by
      rw [show fibPair (n + 1) = ((fibPair n).2, (fibPair n).1 + (fibPair n).2) from rfl,
        fibPair_eq n]
      rfl

/-- The pair recursion is the fold at a two-field record: the term of
    `TermTests/FibWindowTest.lean` computes `fibPair`, field by field. -/
theorem fibPair_term_eval (n : Nat) :
    runAdd TermTests.FibWindow.window n = ((fibPair n).1, (fibPair n).2, PUnit.unit) := by
  rw [TermTests.FibWindow.window_eval, fibPair_eq n]

/-- And its projection is `fib_term`, so `fib2` is written today. -/
theorem fib2_term_eval (n : Nat) : runAdd TermTests.FibWindow.fib_term n = fib2 n := by
  rw [TermTests.FibWindow.fib_term_eval]
  show fib n = (fibPair n).1
  rw [fibPair_eq n]

/-! ## 3. The `for` loop

```lean
def fibLoop (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let next := a + b
    a := b
    b := next
  return a
```

Desugared, this is `ForIn.forIn [:n] (a, b) …` in the identity monad: a fold over
`[:n]` whose state is the pair of mutable variables — that is, `fibPair` written with
different syntax, and so the *same* term as §2, at the same record type.

What is missing is therefore nothing in `Term` and nothing in `Term.eval`: it is a case
in `#leanscript_to_term` for `ForIn.forIn` on a range with a literal-free bound, turning
the loop body into the step of a `nat_rec` whose type is the record of the mutable
variables.  That case now exists — `LeanScript.ToTerm.transForInRange?` — and
`TermTests/NatRecDepthTest/` translates `fibLoop` as it is written.

## 4. `fib` itself

The `n + 2` pattern was the one definition of the five that the grammar could not write
directly, and it is the subject of `proposals/FibProposals.md`.  It is now the depth-two instance
of `Term.nat_rec`, written out and translated in `TermTests/NatRecDepthTest/`.  Two
further things are proved elsewhere in the test suite:

* `TermTests.FibWindow.fib_term_eval` — it is writable **today** as a one-step fold whose
  value is the window of the last two answers;
* `TermTests.NatRecK.natFoldK_fib` — and the depth-indexed fold the node evaluates to
  computes it directly, at `k = 1`.

## 5. `fibFast`

```lean
def fibFastAux (n : Nat) : Nat × Nat :=
  if h : n = 0 then (0, 1) else
    let (a, b) := fibFastAux (n / 2)
    …
termination_by n
```

This one is **out of reach of every proposal in the note**, and it is worth being precise
about why: the recursive call is at `n / 2`, so the argument does not descend by a fixed
number of steps, and no depth-`k` fold — window, a two-step node, or the general
`nat_rec k` — reaches it.  It is genuinely a well-founded recursion, and Lean's own elaboration says so
(`termination_by`).

There is one way to write it without well-foundedness, and it is worth recording: fast
doubling is a **fold over the binary digits of `n`, most significant first**, which is a
`recTaggedUnion_rec` over a list.  The catch is that producing those digits is itself a
recursion at `n / 2`, so the digits would have to come from a declaration in the
signature (an external `Nat.toBits`) rather than from a term.  Until the language has
well-founded recursion, that is the honest shape of the answer: the *algorithm* is a
fold, the *bit decomposition* is not.
-/

end TermTests.FibAlgorithms
