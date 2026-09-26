module

public import LeanScript.Expr.Build
public import LeanScript.Eval
public import LeanScript.FamilyRecFacts
public import TermTests.FibWindowTest
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a mutual recursive family: `mutualRecursiveFamily_rec` at every depth

`TermTests/NatRecDepthTest/` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`; `TermTests/ArrayRecDepthTest.lean`,
`TermTests/RecUnionRecDepthTest.lean`, `TermTests/RecObjectRecDepthTest.lean` and
`TermTests/RecAliasRecDepthTest.lean` do the same for a fold over an array, over a recursive
tagged union, over a recursive record and over a recursive newtype.  This file is that
exercise for a fold over a **mutual recursive family**, which is
`LeanScript.Term.mutualRecursiveFamily_rec`.

The family is a `mutual` block of two declarations — the Peano naturals and a list of
naturals:

```lean
mutual
inductive Pe where
  | zero
  | succ (n : Pe)
inductive Ls where
  | nil
  | cons (a : Nat) (as : Ls)
end
```

so `fib` is the program the depth is for:

```lean
def Pe.fib : Pe → Nat
  | .zero            => 0
  | .succ .zero      => 1
  | .succ (.succ n)  => fib n + fib (.succ n)
```

Its `succ` branch does not answer: it **looks one constructor further down**, and only
then answers, using the value of the recursion at the value it descended past *and* at the
one it arrived at.  That is exactly the shape of a depth-one branch of the fold —
`LeanScript.FamilyFoldKBranch.deep`, which names the field descended into, says which
member of the family that field is an occurrence of, and dispatches on **that member**
again — and the nesting of the Lean `match` above is the nesting of the case tree below,
one for one.

| the program | the node it is | here |
| :-- | :-- | :-- |
| `Pe.fib` (reads two constructors down) | `mutualRecursiveFamily_rec 1` | `fibTerm` |
| `Pe.trib`, `Pe.tetra`, `Pe.penta`, `Pe.hexa` | `mutualRecursiveFamily_rec 2 … 5` | `tribTerm`, `tetraTerm`, `pentaTerm`, `hexaTerm` |
| `Pe.fibLoopTR` (tail-recursive, two accumulators) | `mutualRecursiveFamily_rec 0` **at a function type** | `fibTRTerm` |
| `Pe.fibPair` (pair recursion) | `mutualRecursiveFamily_rec 0` at a record type | `fibPairTerm` |
| `Ls.cont` (the continuant, over the **other member**) | `mutualRecursiveFamily_rec 1`, descending into the *second* field | `contTerm` |
| `Ev.fib` (over a family whose members mention **each other**) | `mutualRecursiveFamily_rec 1`, descending into the *other member* | `TermTests/FamilyRecDepthMembersTest.lean` |
| `Node.fib` (over a family of a record, a union and a newtype) | `mutualRecursiveFamily_rec 1`, both recursive members descending | `TermTests/FamilyRecDepthMembersTest.lean` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

A fold over a family always gives the branches of **every** member, whichever member the
value belongs to and wherever a deeper look lands, so each term below carries the branches
of both members of its family; §1 says what those branches bind.

**What is checked.**  Each definition states the type of the term it builds, so the file
fails to build if the branch a program needs cannot be written at that depth, or is written
in a context other than the documented one.  And since a member of a family denotes the
indexed W-tree of the family (`LeanScript.Ty.Den`), every term is also **run**, by the
kernel, against its Lean reference (§7 of `TermTests/FamilyRecDepthTest.lean`).
What the contexts are is pinned separately, by the `rfl` examples of §1, and the Lean
programs at the top of each section say what each term means.

Those Lean programs are themselves checked, in §0: their values at `10` by `#guard`, that
`Pe.fib` is the ordinary `fib` at *every* argument (`Pe.fib_ofNat`), and the three theorems
of the request — `Pe.fibPair_eq`, `Pe.fibPair_fst_eq_fib` and `Pe.fibTR_eq_fib`, that the
pair recursion and the tail-recursive loop both compute `fib`.

The depth-zero fold is the fold that was there before the depth was added: §8 checks that,
at `k = 0`, no branch can look down at all, and `LeanScript.FamilyRecFacts` proves that the
branches of a depth-zero fold are exactly the branches of the plain fold.

What a deeper look into **another member** looks like, and what the branches of a record
member and of a newtype member are, is the companion file
`TermTests/FamilyRecDepthMembersTest.lean`.

The terms are **written out**, not translated by `#leanscript_to_term`: `Pe` and `Ls` do
not mention each other, so `LeanScriptTyWf` models each as a recursive tagged union of its
own (a type has one model, and a `mutual` block is split into the groups of declarations
that mention each other), and no Lean type has the two-member family of §1 as its tree.
The folds over families that *are* translated — members that mention each other — are
`evFibTerm` in `TermTests/FamilyRecDepthMembersTest.lean` and
`TermTests/MutualFamilyToTermTest/`.
-/

namespace TermTests.FamilyRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of.
`Pe` and `Ls` are declared as one `mutual` block, which is the block the family of §1
describes. -/

mutual

/-- Member `0` of the family: the Peano naturals. -/
inductive Pe where
  /-- Zero. -/
  | zero
  /-- The successor of a Peano natural. -/
  | succ (n : Pe)

/-- Member `1` of the family: a list of naturals. -/
inductive Ls where
  /-- The empty list. -/
  | nil
  /-- One more element, at the front. -/
  | cons (a : Nat) (as : Ls)

end

namespace Pe

/-- `fib`, on Peano naturals: it reads the answer two constructors down. -/
def fib : Pe → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ n) => fib n + fib (.succ n)

/-- The tribonacci numbers: three constructors down. -/
def trib : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 1
  | .succ (.succ (.succ n)) => trib n + trib (.succ n) + trib (.succ (.succ n))

/-- The tetranacci numbers: four constructors down. -/
def tetra : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 1
  | .succ (.succ (.succ (.succ n))) =>
      tetra n + tetra (.succ n) + tetra (.succ (.succ n)) + tetra (.succ (.succ (.succ n)))

/-- The pentanacci numbers: five constructors down. -/
def penta : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 0
  | .succ (.succ (.succ (.succ .zero))) => 1
  | .succ (.succ (.succ (.succ (.succ n)))) =>
      penta n + penta (.succ n) + penta (.succ (.succ n)) + penta (.succ (.succ (.succ n)))
        + penta (.succ (.succ (.succ (.succ n))))

/-- The hexanacci numbers: six constructors down. -/
def hexa : Pe → Nat
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

/-- The tail-recursive loop, with two accumulators. -/
def fibLoopTR : Pe → Nat → Nat → Nat
  | .zero, a, _ => a
  | .succ n, a, b => fibLoopTR n b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (n : Pe) : Nat := fibLoopTR n 0 1

/-- The pair recursion: the answer at `n` together with the answer at `n + 1`. -/
def fibPair : Pe → Nat × Nat
  | .zero => (0, 1)
  | .succ n => let (a, b) := fibPair n; (b, a + b)

/-- A Peano natural from a `Nat`, for the checks below. -/
def ofNat : Nat → Pe
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
def add : Pe → Pe → Pe
  | .zero, m => m
  | .succ n, m => .succ (add n m)

@[simp] theorem add_succ : (n m : Pe) → add n (.succ m) = .succ (add n m)
  | .zero, _ => rfl
  | .succ n, m => congrArg Pe.succ (add_succ n m)

@[simp] theorem add_zero : (n : Pe) → add n .zero = n
  | .zero => rfl
  | .succ n => congrArg Pe.succ (add_zero n)

/-- The pair recursion carries the answer at `n` and the answer at `n + 1`. -/
theorem fibPair_eq : (n : Pe) → fibPair n = (fib n, fib (.succ n))
  | .zero => rfl
  | .succ n => by
      show (let (a, b) := fibPair n; ((b, a + b) : Nat × Nat)) = _
      rw [fibPair_eq n]
      rfl

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (n : Pe) : (fibPair n).1 = fib n := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `m` and `m + 1`, answers at `n + m`. -/
theorem fibLoopTR_eq : (n m : Pe) → fibLoopTR n (fib m) (fib (.succ m)) = fib (add n m)
  | .zero, _ => rfl
  | .succ n, m => by
      show fibLoopTR n (fib (.succ m)) (fib m + fib (.succ m)) = fib (.succ (add n m))
      rw [show fib m + fib (.succ m) = fib (.succ (.succ m)) from rfl,
        fibLoopTR_eq n (.succ m), add_succ]

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (n : Pe) : fibTR n = fib n := by
  show fibLoopTR n (fib .zero) (fib (.succ .zero)) = fib n
  rw [fibLoopTR_eq n .zero]
  show fib (add n .zero) = fib n
  rw [add_zero]

end Pe

namespace Ls

/-- The **continuant** over the other member of the family:
    `K [] = 1`, `K [a] = a`, `K (a :: b :: as) = a * K (b :: as) + K as`. -/
def cont : Ls → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a (.cons b as) => a * cont (.cons b as) + cont as

/-- A list of `n` ones. -/
def ones : Nat → Ls
  | 0 => .nil
  | n + 1 => .cons 1 (ones n)

-- [SKIPPED BY PROFILE_LAKE] #guard cont (.cons 3 (.cons 1 (.cons 4 .nil))) = 3 * (1 * 4 + 1) + 4

/-- The continuant of a list of `n` ones is `fib (n + 1)`: the continuant *is* the
    `fib`-shaped recursion, read over the second member of the family. -/
theorem cont_ones : (n : Nat) → cont (ones n) = TermTests.FibWindow.fib (n + 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show 1 * cont (ones (n + 1)) + cont (ones n) =
        TermTests.FibWindow.fib (n + 1) + TermTests.FibWindow.fib (n + 2)
      rw [cont_ones n, cont_ones (n + 1)]
      show 1 * TermTests.FibWindow.fib (n + 2) + TermTests.FibWindow.fib (n + 1) = _
      omega

end Ls

/-! ## 1. The family, and what its branches bind

The family has the two members of the `mutual` block above: member `0` has the
constructors `zero`, which carries nothing, and `succ`, whose one field is an occurrence of
member `0`; member `1` has `nil`, which carries nothing, and `cons`, which carries a
natural and an occurrence of member `1`.  A family is written in the scope of all of its
members, so a field is `Ty.familyMember i` rather than `Ty.self`. -/

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

/-- Member `0` of the family: the Peano naturals, `zero | succ (n : member 0)`. -/
def memPe : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 0).toTyWfIn, []⟩ []))

/-- Member `1` of the family: a list of naturals,
    `nil | cons (a : nat) (as : member 1)`. -/
def memLs : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.prim .nat).toTyWfIn, [(Ty.familyMember 1).toTyWfIn]⟩ []))

/-- The family, selecting member `0`. -/
def famPe : LeanMutualRecFamily (TyWfIn 2) := .selectedThenMore [] memPe memLs []

/-- The family, selecting member `1`. -/
def famLs : LeanMutualRecFamily (TyWfIn 2) := .selectedLast memPe [] memLs

-- Both are the same block of declarations: they differ only in which member is selected.
-- [SKIPPED BY PROFILE_LAKE] example : famPe.members = [memPe, memLs] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : famLs.members = [memPe, memLs] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : famPe.memberIdx = 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : famLs.memberIdx = 1 := by kernel_rfl

/-- That the family describes types: every member is mentioned, no occurrence is in the
    domain of a function, and every member has values. -/
theorem peWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famPe) := by ty_wf

/-- The same, for the family that selects member `1`. -/
theorem lsWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famLs) := by ty_wf

/-- The type of member `0`: a Peano natural. -/
def peTy : TyWf := .mutualRecursiveFamily famPe peWf

/-- The type of member `1`: a list of naturals. -/
def lsTy : TyWf := .mutualRecursiveFamily famLs lsWf

/-- The fields of `succ`, as the branch families see them. -/
abbrev succFields : List (TyWfIn 2) := [(Ty.familyMember 0).toTyWfIn]

/-- The fields of `cons`. -/
abbrev consFields : List (TyWfIn 2) :=
  [(Ty.prim .nat).toTyWfIn, (Ty.familyMember 1).toTyWfIn]

/-- How the value of a fold over member `0` at motive `τ` reaches a branch. -/
abbrev pbind (τ : TyWf) : List (TyWfIn 2) → List TyWf := TyWf.famRecBinders famPe peWf τ

-- What a branch binds: a field-less constructor binds nothing; `succ` binds its field — a
-- Peano natural — and then the value of the fold at that field; `cons` binds its natural,
-- its tail and the value of the fold at the tail, since the natural is not an occurrence
-- of a member.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : pbind τ [] = [] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : pbind τ succFields = [peTy, τ] := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : pbind τ consFields = [natT, lsTy, τ] := by kernel_rfl

-- So the branch of `succ` of a depth-zero fold over `Γ` is written in `peTy :: τ :: Γ`,
-- and a branch reached by descending once more is written in that context again with the
-- subvalue and the value of the fold at it in front of it.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) : pbind τ succFields ++ Γ = peTy :: τ :: Γ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) :
-- [SKIPPED BY PROFILE_LAKE]     pbind τ succFields ++ (pbind τ succFields ++ Γ) = peTy :: τ :: peTy :: τ :: Γ := by kernel_rfl

/-- The context every fold over member `0` below is written in: the Peano natural it folds
    over, bound by the `fun` in front of it. -/
abbrev PCtx : Ctx := [peTy]

/-- Zero, as a term. -/
def zeroTerm : Term sigAdd [] peTy :=
  .mutualRecursiveFamily_mk famPe peWf (value := .ctors _ 0 (fields := .nil))

/-- The successor of the variable in scope. -/
def succTerm : Term sigAdd [] (peTy ⇒ peTy) :=
  .lam (.mutualRecursiveFamily_mk famPe peWf
    (value := .ctors _ 1 (fields := .cons (.var (v♯0)) .nil)))

/-- **The branches of the member the fold does not descend into.**  Every fold over this
    family has to answer for member `1` as well, whatever it is folding: `nil` answers with
    the term given here, and `cons` answers with the value of the fold at its tail, which
    its branch binds at index `2`.  It is written once, for every motive and every depth,
    and used by every fold below. -/
def lsCases {τ : TyWf} {Γ : Ctx} {k : Nat} {outer : List (List (TyWfIn 2))}
    (nilAnswer : Term sigAdd Γ τ) :
    FamilyMemberFoldKCases sigAdd 0 famPe.members (pbind τ) Γ τ memLs k outer :=
  .ctors (.skip (.here nilAnswer) (.here (.here (.var (v♯2))) .nil))

end TermTests.FamilyRecDepth
