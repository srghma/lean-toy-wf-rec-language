module

public import TermTests.RecAliasRecDepthTest.Programs
public meta import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive newtype: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TermTests.RecAliasRecDepthTest.Programs`; this file translates the programs to terms
of the language with `#leanscript_to_term` and checks the terms against the references.
-/

namespace TermTests.RecAliasRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`: the depth-one fold

`Chain.fib` reads the answer two links down, so it translates to `recAlias_rec 1`.  Its
branch binds the body (index `0`) and the window (index `1`).  Taking the window apart is
the descent: it is an `Option` of a label and the answer tree at the chain below, and

* `none` — the chain ends here — answers `0`;
* `some` binds that link, whose second field is the answer tree at the chain below, and
  whose tree in turn holds the answer at that chain and *its* window: a label and an
  `Option` of the answer at the chain below **that**.  `none` there answers `1`, and
  `some` answers `fib (chain below) + fib (chain below that)`, which is the
  `fib n + fib (n + 1)` of the program. -/

/-- **`fib` over a recursive newtype**: `Chain.fib`, translated to the depth-one fold. -/
def fibTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.fib

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

Each further level is the same three steps — take the link apart (a label, and the answer
tree at the chain below), take that tree apart (the answer there, and its own window), and
dispatch — so a level pushes five binders in front of the context and the answers read so
far sit at the indices `1, 3, 8, 13, …`, nearest first. -/

/-- `trib`, as a term: a depth-two fold. -/
def tribTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.trib

/-- `tetra`, as a term: a depth-three fold. -/
def tetraTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.tetra

/-- `penta`, as a term: a depth-four fold. -/
def pentaTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.penta

/-- `hexa`, as a term: a depth-five fold. -/
def hexaTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.hexa

mutual
/-- The depth of the `recAlias_rec` a translated function is: the fold under the `fun`s
    of its arguments, and under the applications and the case analysis around it.  `none`
    if the translation is not of that shape. -/
def recAliasRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sigAdd Γ τ J → Option Nat
  | .recAlias_rec k _ _ _ => some k
  | .letE c body => (recAliasRecDepth?.comp c).orElse fun _ => recAliasRecDepth? body
  | .letJ jp body => (recAliasRecDepth? body).orElse fun _ => recAliasRecDepth? jp
  | _ => none

/-- `recAliasRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recAliasRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sigAdd Γ τ → Option Nat
  | .lam b => recAliasRecDepth? b
  | _ => none
end

-- Each program is the fold at the depth it reads.
-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? fibTerm = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? tribTerm = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? tetraTerm = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? pentaTerm = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? hexaTerm = some 5 := by kernel_rfl

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the chain immediately below, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added.  `fibTR` is that
loop applied to `0` and `1`. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.fibTR

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? fibTRTerm = some 0 := by kernel_rfl

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at one link more alongside
the answer at this one.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib t, fib (link above t))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.fibPairFst

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? fibPairTerm = some 0 := by kernel_rfl

/-! ## 6. The continuant: a fold that reads the newtype's **own label** as well

Every branch above ignores the labels the chain carries.  The continuant `Chain.cont` does
not: it is the `fib`-shaped recursion

```lean
def cont : Chain → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a (.cons l r) => a * cont (.cons l r) + cont r
```

so its branch multiplies the label — which the window carries beside the answer, and which
each descent pushes further out — by the answer one link down and adds the answer two
links down. -/

/-- The continuant, as a term: the depth-one fold that also reads the label. -/
def contTerm : Term sigAdd [] (chainTy ⇒ natT) := #leanscript_to_term Chain.cont

-- [SKIPPED BY PROFILE_LAKE] example : recAliasRecDepth? contTerm = some 1 := by kernel_rfl

/-! ## 7. Running the terms

A recursive newtype has values in the model (`LeanScript.Ty.Den` gives it the W-tree of
its body), so these terms run, and the kernel checks them against their Lean
references.  The depth-`k` folds are evaluated with every answer remembered
(`LeanScript.WType.memo`), and the window a branch takes apart is read off those
memos (`LeanScript.aliasRecEnv`). -/


/-- The values of `add` and `mul`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
scoped macro:max "runP" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- The chain `c`, built by the introduction form (`nilTerm` and `consTerm`). -/
def chainVal : Chain → TyWf.Den chainTy
  | .nil => runP nilTerm
  | .cons l r => runP consTerm l (chainVal r)

-- Each run is checked by the kernel against the value its Lean reference has at the
-- same chain, which §0 of `TermTests.RecAliasRecDepthTest.Programs` checks by `#guard`
-- (the two are compared through that number; `Correct.lean` proves them equal on every
-- chain).
-- [SKIPPED BY PROFILE_LAKE] example : runP fibTerm (chainVal (Chain.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP fibTRTerm (chainVal (Chain.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP fibPairTerm (chainVal (Chain.ofNat 10)) = 55 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP tribTerm (chainVal (Chain.ofNat 10)) = 81 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP tetraTerm (chainVal (Chain.ofNat 10)) = 56 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP pentaTerm (chainVal (Chain.ofNat 10)) = 31 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP hexaTerm (chainVal (Chain.ofNat 10)) = 16 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP contTerm (chainVal (.cons 3 (.cons 2 (.cons 1 .nil)))) = 10 := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- `fib` of the chain of `n` links is the ordinary `fib n`, and the term agrees with it
-- along the first few chains.
-- [SKIPPED BY PROFILE_LAKE] example : ∀ n < 8, runP fibTerm (chainVal (Chain.ofNat n)) = TermTests.FibWindow.fib n := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-! ## 8. The depth-zero fold, and what no depth reaches

At depth `0` the window holds the answer at the chain below and nothing more, so there is
nothing to take apart there and the `fib` branch of §2 cannot be written: the answers two
links down are not in scope at all.  `LeanScript.TyWf.recAliasRecBinders_zero` is the
statement that the default depth is the old branch context — the newtype's body — with
exactly that one answer appended. -/

example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 =
      TyWf.recBinders chainTy τ [chainBodyW] ++ [TyWf.recAliasMap chainBodyW τ] :=
  TyWf.recAliasRecBinders_zero chainBodyW (by ty_wf) τ

example (τ : TyWf) :
    (TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 5).length = 2 :=
  TyWf.length_recAliasRecBinders chainBodyW (by ty_wf) τ 5

-- And at depth `0` there is nothing below the answer to take apart: the `some` of the
-- window binds a label and the answer at the chain below, a `nat`, so the second descent
-- of §2 — which is what `fib` needs — cannot be written.
/--
error: Application type mismatch: The argument
  DeBruijn.head
has type
  DeBruijn (?m.58 :: ?m.59) ?m.58
but is expected to have type
  DeBruijn
    (((linkSchema (treeTy natT 0)).snd :: (linkSchema (treeTy natT 0)).rest).append
      (id { head := linkTy (treeTy natT 0), tail := [] }.toList ++ branchCtx natT 0))
    (TyWf.record ?m.49)
in the application
  DeBruijn.head.tail
-/
#guard_msgs (error) in
def fibBranchTooShallow : Term sigAdd (branchCtx natT 0) natT :=
  .taggedUnion_casesOn' (.var (v♯1))
    (.skip (.nat_mk 0)
      (.here
        (.record_casesOn' (.var (v♯0))
          (.record_casesOn' (.var (v♯1)) (.nat_mk 1)))
        .nil))

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: the link half way down a chain is not the link a fixed number
of steps below it, so there is no depth at which the branch is *given* the answer at it.
A fold is given the answers on the path it descended, and a recursion that jumps needs a
measure and a proof, which a `Term` does not carry.  This is the same boundary
`TermTests/NatRecDepthTest/` records for `Nat`.
-/

end TermTests.RecAliasRecDepth

end
