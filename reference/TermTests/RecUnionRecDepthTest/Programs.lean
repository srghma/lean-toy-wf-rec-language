module

public import LeanScript.Expr.Build
public import LeanScript.Eval
public import LeanScript.RecUnionRecFacts
public import TermTests.FibWindowTest
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a recursive tagged union: `recTaggedUnion_rec` at every depth

`TermTests/NatRecDepthTest/` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`, and `TermTests/ArrayRecDepthTest.lean` does the
same for a fold over an array.  This file is that exercise for a fold over a **recursive
tagged union**, which is `LeanScript.Term.recTaggedUnion_rec`.

The union is the Peano naturals, written as a union of the language:

```lean
inductive Peano where
  | zero
  | succ (n : Peano)
```

so `fib` is the program the depth is for:

```lean
def Peano.fib : Peano → Nat
  | .zero            => 0
  | .succ .zero      => 1
  | .succ (.succ n)  => fib n + fib (.succ n)
```

Its `succ` branch does not answer: it **looks one constructor further down**, and only
then answers, using the value of the recursion at the value it descended past *and* at
the one it arrived at.  That is exactly the shape of a depth-one branch of the fold —
`LeanScript.FoldKBranch.deep`, which names the field descended into and dispatches on the
union again — and the nesting of the Lean `match` above is the nesting of the case tree
below, one for one.

| the program | the node it is | here |
| :-- | :-- | :-- |
| `Peano.fib` (reads two constructors down) | `recTaggedUnion_rec 1` | `fibTerm` |
| `Peano.trib`, `Peano.tetra`, `Peano.penta`, `Peano.hexa` | `recTaggedUnion_rec 2 … 5` | `tribTerm`, `tetraTerm`, `pentaTerm`, `hexaTerm` |
| `Peano.fibLoopTR` (tail-recursive, two accumulators) | `recTaggedUnion_rec 0` **at a function type** | `fibTRTerm` |
| `Peano.fibPair` (pair recursion) | `recTaggedUnion_rec 0` at a record type | `fibPairTerm` |
| `cont` (the continuant, over a **list** union) | `recTaggedUnion_rec 1`, descending into the *second* field | `contTerm` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

**What is checked.**  Each definition states the type of the term it builds, so the file
fails to build if the branch a program needs cannot be written at that depth, or is
written in a context other than the documented one.  A recursive tagged union also has
values in the model (`LeanScript.Ty.Den` gives it the W-tree of its constructors), so §7
of `TermTests.RecUnionRecDepthTest` **runs** every term and checks it, by the kernel,
against its Lean program.  What the contexts are is pinned separately, by the `rfl`
examples of §1, and the Lean programs at the top of each section say what each term
means.

Those Lean programs are themselves checked, in §0: their values at `10` by `#guard`, that
`Peano.fib` is the ordinary `fib` at *every* argument (`Peano.fib_ofNat`), and the three
theorems of the request — `Peano.fibPair_eq`, `Peano.fibPair_fst_eq_fib` and
`Peano.fibTR_eq_fib`, that the pair recursion and the tail-recursive loop both compute
`fib`.

The depth-zero fold is the fold that was there before the depth was added: §8 checks
that, at `k = 0`, no branch can look down at all, and `LeanScript.RecUnionRecFacts` proves
that the branches of a depth-zero fold are exactly the branches of the plain fold.

The terms are **written out**, as the first half of `TermTests/NatRecDepthTest/` and all
of `TermTests/ArrayRecDepthTest.lean` are: `#leanscript_to_term` compiles a recursion on a
`Nat` at any depth, and a recursion on a list one constructor at a time, so a depth-`k`
recursion on a union is not something it reads yet.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of. -/

/-- The Peano naturals: the recursive tagged union this file folds over. -/
inductive Peano where
  /-- Zero. -/
  | zero
  /-- The successor of a Peano natural. -/
  | succ (n : Peano)
  deriving LeanScriptTyWf

namespace Peano

/-- `fib`, on Peano naturals: it reads the answer two constructors down. -/
def fib : Peano → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ n) => fib n + fib (.succ n)

/-- The tribonacci numbers: three constructors down. -/
def trib : Peano → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 1
  | .succ (.succ (.succ n)) => trib n + trib (.succ n) + trib (.succ (.succ n))

/-- The tetranacci numbers: four constructors down. -/
def tetra : Peano → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 1
  | .succ (.succ (.succ (.succ n))) =>
      tetra n + tetra (.succ n) + tetra (.succ (.succ n)) + tetra (.succ (.succ (.succ n)))

/-- The pentanacci numbers: five constructors down. -/
def penta : Peano → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 0
  | .succ (.succ (.succ (.succ .zero))) => 1
  | .succ (.succ (.succ (.succ (.succ n)))) =>
      penta n + penta (.succ n) + penta (.succ (.succ n)) + penta (.succ (.succ (.succ n)))
        + penta (.succ (.succ (.succ (.succ n))))

/-- The hexanacci numbers: six constructors down. -/
def hexa : Peano → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 0
  | .succ (.succ (.succ (.succ .zero))) => 0
  | .succ (.succ (.succ (.succ (.succ .zero)))) => 1
  | .succ (.succ (.succ (.succ (.succ (.succ n))))) =>
      hexa n + hexa (.succ n) + hexa (.succ (.succ n)) + hexa (.succ (.succ (.succ n)))
        + hexa (.succ (.succ (.succ (.succ n))))
        + hexa (.succ (.succ (.succ (.succ (.succ n)))))

/-- The tail-recursive loop, with two accumulators (`@[inline]`, so that `fibTR` below
    translates to the loop itself, applied to `0` and `1`). -/
@[inline] def fibLoopTR : Peano → Nat → Nat → Nat
  | .zero, a, _ => a
  | .succ n, a, b => fibLoopTR n b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (n : Peano) : Nat := fibLoopTR n 0 1

/-- The pair recursion: the answer at `n` together with the answer at `n + 1`
    (`@[inline]`, so that `fibPairFst` below translates to the fold itself). -/
@[inline] def fibPair : Peano → Nat × Nat
  | .zero => (0, 1)
  | .succ n => let (a, b) := fibPair n; (b, a + b)

/-- `fib`, as the first component of the pair recursion. -/
def fibPairFst (n : Peano) : Nat := (fibPair n).1

/-- Zero, as a closed value. -/
def zeroVal : Peano := .zero

/-- The successor, as a function. -/
def succFn (n : Peano) : Peano := .succ n

/-- A Peano natural from a `Nat`, for the checks below. -/
def ofNat : Nat → Peano
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

-- The reference programs are the familiar sequences.
-- [SKIPPED BY PROFILE_LAKE] #guard fib (ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard fibTR (ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard fibPair (ofNat 10) = (55, 89)
-- [SKIPPED BY PROFILE_LAKE] #guard trib (ofNat 10) = 81
-- [SKIPPED BY PROFILE_LAKE] #guard tetra (ofNat 10) = 56
-- [SKIPPED BY PROFILE_LAKE] #guard penta (ofNat 10) = 31
-- [SKIPPED BY PROFILE_LAKE] #guard hexa (ofNat 10) = 16

/-- The Peano `fib` is the `fib` of `TermTests.FibWindow`, at **every** argument. -/
theorem fib_ofNat : (n : Nat) → fib (ofNat n) = TermTests.FibWindow.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show fib (ofNat n) + fib (ofNat (n + 1)) =
        TermTests.FibWindow.fib n + TermTests.FibWindow.fib (n + 1)
      rw [fib_ofNat n, fib_ofNat (n + 1)]

/-- Addition of Peano naturals, by recursion on the left argument. -/
def add : Peano → Peano → Peano
  | .zero, m => m
  | .succ n, m => .succ (add n m)

@[simp] theorem add_succ : (n m : Peano) → add n (.succ m) = .succ (add n m)
  | .zero, _ => rfl
  | .succ n, m => congrArg Peano.succ (add_succ n m)

/-- The pair recursion carries the answer at `n` and the answer at `n + 1`. -/
theorem fibPair_eq : (n : Peano) → fibPair n = (fib n, fib (.succ n))
  | .zero => rfl
  | .succ n => by
      show (let (a, b) := fibPair n; ((b, a + b) : Nat × Nat)) = _
      rw [fibPair_eq n]
      rfl

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (n : Peano) : (fibPair n).1 = fib n := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `m` and `m + 1`, answers at `n + m`. -/
theorem fibLoopTR_eq : (n m : Peano) →
    fibLoopTR n (fib m) (fib (.succ m)) = fib (add n m)
  | .zero, _ => rfl
  | .succ n, m => by
      show fibLoopTR n (fib (.succ m)) (fib m + fib (.succ m)) = fib (.succ (add n m))
      rw [show fib m + fib (.succ m) = fib (.succ (.succ m)) from rfl,
        fibLoopTR_eq n (.succ m), add_succ]

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (n : Peano) : fibTR n = fib n := by
  show fibLoopTR n (fib .zero) (fib (.succ .zero)) = fib n
  rw [fibLoopTR_eq n .zero]
  show fib (add n .zero) = fib n
  rw [show add n .zero = n from by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Peano.succ ih]

end Peano

/-! ## 1. The union, and what its branches bind

`zero` carries nothing and `succ` carries the union itself, which is `Ty.self`. -/

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-- A signature with two declarations, `add` and `mul`, both `nat ⇒ nat ⇒ nat`:
    arithmetic is external to the language. -/
def sigAdd : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"mul", natT ⇒ natT ⇒ natT⟩], by decide⟩

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ natT) : Term sigAdd Γ natT :=
  .ap (.ap (.global .here) a) b

/-- `mul a b`, for two terms in hand. -/
def mulT {Γ : Ctx} (a b : Term sigAdd Γ natT) : Term sigAdd Γ natT :=
  .ap (.ap (.global (.there .here)) a) b

/-- The schema of the Peano naturals: constructor `0` is `zero`, which has no fields;
    constructor `1` is `succ`, whose one field is the union itself. -/
def peanoSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨Ty.self.toTyWfIn, []⟩ [])

/-- The type of a Peano natural. -/
def peanoTy : TyWf := .recTaggedUnion peanoSchema

-- It is the tree `LeanScriptTyWf` derives for the Lean `Peano` of §0, so the Lean programs
-- there translate to terms of this type.
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf Peano = peanoTy := by kernel_rfl

-- The unfolding really is the schema with `Ty.self` replaced by the union, so the field
-- of `succ` takes a Peano natural.
-- [SKIPPED BY PROFILE_LAKE] example : (TyWf.recTaggedUnionUnfold peanoSchema).get 1 (by decide) = [peanoTy] := by kernel_rfl

/-- The fields of `succ`, as the branch families see them. -/
abbrev succFields : List (TyWfIn 1) := [Ty.self.toTyWfIn]

/-- How the value of a fold at motive `τ` reaches a branch. -/
abbrev pbind (τ : TyWf) : List (TyWfIn 1) → List TyWf := TyWf.recBinders peanoTy τ

-- What a branch binds: `zero` binds nothing, and `succ` binds its field — a Peano
-- natural — and then the value of the fold at that field.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : pbind τ [] = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : pbind τ succFields = [peanoTy, τ] := by kernel_rfl

-- So the branch of `succ` of a depth-zero fold over `Γ` is written in `peanoTy :: τ :: Γ`,
-- and a branch reached by descending once more is written in that context again with the
-- subvalue and the value of the fold at it in front of it.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) : pbind τ succFields ++ Γ = peanoTy :: τ :: Γ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) :
-- [SKIPPED BY PROFILE_LAKE]     pbind τ succFields ++ (pbind τ succFields ++ Γ) =
-- [SKIPPED BY PROFILE_LAKE]       peanoTy :: τ :: peanoTy :: τ :: Γ := by kernel_rfl

/-- The context every fold below is written in: the Peano natural it folds over, bound by
    the `fun` in front of it. -/
abbrev PCtx : Ctx := [peanoTy]

/-- Zero, as a term: `Peano.zeroVal`, translated. -/
def zeroTerm : Term sigAdd [] peanoTy := #leanscript_to_term Peano.zeroVal

/-- The successor of the variable in scope: `Peano.succFn`, translated. -/
def succTerm : Term sigAdd [] (peanoTy ⇒ peanoTy) := #leanscript_to_term Peano.succFn

end TermTests.RecUnionRecDepth
