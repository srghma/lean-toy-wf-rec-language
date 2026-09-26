module

public import TermTests.RecObjectRecDepthTest.Programs
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive record: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TermTests.RecObjectRecDepthTest.Programs`; this file translates the programs to terms
of the language with `#leanscript_to_term` and checks the terms against the references.
-/

namespace TermTests.RecObjectRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`: the depth-one fold

`Cell.fib` reads the answer two cells down, so it translates to `recObject_rec 1`.  Its
branch binds the label (index `0`), the `Option` of cells below (index `1`) and the
window (index `2`).  Taking the window apart is the descent: its second field is an
`Option` of the answer tree at the cell below, and

* `none` — no cell below — answers `0`;
* `some d` binds that tree, whose first field is the answer at the cell below and whose
  second field is *its* fields' shape: a label and an `Option` of the answer at the cell
  below **that**.  `none` there answers `1`, and `some y` answers
  `fib (cell below) + fib (cell below that)`, which is the `fib n + fib (n + 1)` of the
  program. -/

/-- **`fib` over a recursive record**: `Cell.fib`, translated to the depth-one fold. -/
def fibTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.fib

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

Each further level is the same three steps — take the answer tree apart (the answer at
that cell, and its fields' shape), take that shape apart (the label, and the `Option`
below it), and dispatch — so a level pushes five binders in front of the context and the
answers read so far sit at the indices `3, 8, 13, …`, nearest first. -/

/-- `trib`, as a term: a depth-two fold. -/
def tribTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.trib

/-- `tetra`, as a term: a depth-three fold. -/
def tetraTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.tetra

/-- `penta`, as a term: a depth-four fold. -/
def pentaTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.penta

/-- `hexa`, as a term: a depth-five fold. -/
def hexaTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.hexa

mutual
/-- The depth of the `recObject_rec` a translated function is: the fold under the `fun`s
    of its arguments, and under the applications and the case analysis around it.  `none`
    if the translation is not of that shape. -/
def recObjectRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sigAdd Γ τ J → Option Nat
  | .recObject_rec k _ _ _ => some k
  | .letE c body => (recObjectRecDepth?.comp c).orElse fun _ => recObjectRecDepth? body
  | .letJ jp body => (recObjectRecDepth? body).orElse fun _ => recObjectRecDepth? jp
  | _ => none

/-- `recObjectRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recObjectRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sigAdd Γ τ → Option Nat
  | .lam b => recObjectRecDepth? b
  | _ => none
end

-- Each program is the fold at the depth it reads.
-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? fibTerm = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? tribTerm = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? tetraTerm = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? pentaTerm = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? hexaTerm = some 5 := by kernel_rfl

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the cell immediately below, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added.  `fibTR` is that loop
applied to `0` and `1`. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.fibTR

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? fibTRTerm = some 0 := by kernel_rfl

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at one cell more alongside
the answer at this one.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib t, fib (cell above t))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.fibPairFst

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? fibPairTerm = some 0 := by kernel_rfl

/-! ## 6. The continuant: a fold that reads the record's **own field** as well

Every branch above ignores the label the record carries.  The continuant `Cell.cont` does
not: it is the `fib`-shaped recursion

```lean
def cont : Cell → Nat
  | .mk a none => a
  | .mk a (some (.mk b none)) => a * cont (.mk b none) + 1
  | .mk a (some (.mk b (some g))) => a * cont (.mk b (some g)) + cont g
```

so its branch multiplies the label — index `0` of the branch, pushed further out by each
descent — by the answer one cell down and adds the answer two cells down. -/

/-- The continuant, as a term: the depth-one fold that also reads the label. -/
def contTerm : Term sigAdd [] (cellTy ⇒ natT) := #leanscript_to_term Cell.cont

-- [SKIPPED BY PROFILE_LAKE] example : recObjectRecDepth? contTerm = some 1 := by kernel_rfl

/-! ## 7. Running the terms

A recursive record has values in the model (`LeanScript.Ty.Den` gives it the W-tree of
its fields), so these terms run, and the kernel checks them against their Lean
references.  The depth-`k` folds are evaluated with every answer remembered
(`LeanScript.WType.memo`), and the window a branch takes apart is read off those
memos (`LeanScript.objRecEnv`). -/


/-- The values of `add` and `mul`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
scoped macro:max "runP" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- A cell with no cell below it, labelled by the argument: `Cell.last`, translated. -/
def lastCellTerm : Term sigAdd [] (natT ⇒ cellTy) := #leanscript_to_term Cell.last

/-- A cell labelled by the first argument, on top of the second: `Cell.push`, translated. -/
def consCellTerm : Term sigAdd [] (natT ⇒ cellTy ⇒ cellTy) := #leanscript_to_term Cell.push

/-- The chain `c`, built by the introduction form. -/
def cellVal : Cell → TyWf.Den cellTy
  | .mk l none => runP lastCellTerm l
  | .mk l (some c) => runP consCellTerm l (cellVal c)

-- Each run is checked by the kernel against the value its Lean reference has at the
-- same chain, which §0 of `TermTests.RecObjectRecDepthTest.Programs` checks by `#guard`
-- (the two are compared through that number; `Correct.lean` proves them equal on every
-- chain).
-- [SKIPPED BY PROFILE_LAKE] example : runP fibTerm (cellVal (Cell.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP fibTRTerm (cellVal (Cell.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP fibPairTerm (cellVal (Cell.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP tribTerm (cellVal (Cell.ofNat 10)) = 81 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP tetraTerm (cellVal (Cell.ofNat 10)) = 56 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP pentaTerm (cellVal (Cell.ofNat 10)) = 31 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP hexaTerm (cellVal (Cell.ofNat 10)) = 16 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP contTerm (cellVal (.mk 3 (some (.mk 2 (some (.mk 1 none)))))) = 10 := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- `fib` of the chain of `n + 1` cells is the ordinary `fib n` (`Cell.fib_ofNat`), and the
-- term agrees with it along the first few chains.
-- [SKIPPED BY PROFILE_LAKE] example : ∀ n < 8, runP fibTerm (cellVal (Cell.ofNat n)) = TermTests.FibWindow.fib n := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-! ## 8. The depth-zero fold, and what no depth reaches

At depth `0` the window holds the answer at the cell below and nothing more, so there is
nothing to take apart there and the `fib` branch of §2 cannot be written: the answers two
cells down are not in scope at all.  `LeanScript.TyWf.recObjectRecBinders_zero` is the
statement that the default depth is the old branch context — the record's fields — with
exactly that one answer appended. -/

example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 0 =
      TyWf.recBinders cellTy τ cellSchema.toList ++ [TyWf.recObjectMap cellSchema τ] :=
  TyWf.recObjectRecBinders_zero cellSchema (by ty_wf) τ

example (τ : TyWf) :
    (TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 5).length = cellSchema.length + 1 :=
  TyWf.length_recObjectRecBinders cellSchema (by ty_wf) τ 5

-- And at depth `0` there is nothing below the answer to take apart: the `some` of the
-- window binds the answer at the cell below, a `nat`, so the second descent of §2 —
-- which is what `fib` needs — cannot be written.
/--
error: Application type mismatch: The argument
  DeBruijn.head
has type
  DeBruijn (?m.62 :: ?m.63) ?m.62
but is expected to have type
  id { head := treeTy natT 0, tail := [] }.toList ++
      ({ fst := natT, snd := optTy (treeTy natT 0), rest := [] }.toList ++ branchCtx natT 0) ∋
    TyWf.record ?m.57
in the application
  Term.var DeBruijn.head
-/
#guard_msgs (error) in
def fibBranchTooShallow : Term sigAdd (branchCtx natT 0) natT :=
  .record_casesOn' (.var (v♯2))
    (.taggedUnion_casesOn' (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here (.record_casesOn' (.var (v♯0)) (.nat_mk 1)) .nil)))

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: the cell half way down a chain is not the cell a fixed number
of links below it, so there is no depth at which the branch is *given* the answer at it.
A fold is given the answers on the path it descended, and a recursion that jumps needs a
measure and a proof, which a `Term` does not carry.  This is the same boundary
`TermTests/NatRecDepthTest/` records for `Nat`.
-/

end TermTests.RecObjectRecDepth

end
