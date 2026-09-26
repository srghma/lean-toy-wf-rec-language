module

public import LeanScript.Expr.Build
public import LeanScript.Eval
public import LeanScript.RecAliasRecFacts
public import TermTests.FibWindowTest
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a recursive newtype: `recAlias_rec` at every depth

`TermTests/NatRecDepthTest/` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`; `TermTests/ArrayRecDepthTest.lean` does the same
for a fold over an array, `TermTests/RecUnionRecDepthTest.lean` for a fold over a recursive
tagged union and `TermTests/RecObjectRecDepthTest.lean` for a fold over a recursive record.
This file is that exercise for a fold over a **recursive newtype**, which is
`LeanScript.Term.recAlias_rec`.

## Why a newtype needed a window too

The body of a recursive newtype can never be *literally* an occurrence of it: `μX. X` is
the equation `T = T`, which no value satisfies (`LeanScript.Ty.not_wf_recAlias_self`).  So
`LeanScript.TyWf.recBinders`, which puts the value of the fold after a field that *is* an
occurrence, put nothing anywhere: the fold of a newtype handed its branch no answer at all
(`LeanScript.TyWf.recBinders_recAlias`, and the `rfl` example in §1).

What the fold hands the branch now is one **window** binder: the newtype's body with every
occurrence of the newtype replaced by the answer there (`LeanScript.TyWf.recAliasMap`),
and at depth `k` by the **answer tree** of depth `k` at that subvalue — the answer at it
beside, in the shape of the body, the depth-`k - 1` trees of its own subvalues
(`LeanScript.TyWf.recAliasAnswerTree`).  So a depth-`k` branch reads the answers at
everything `k + 1` levels down, along the path it descends, exactly as a depth-`k` branch
of `Term.recObject_rec` does.

## The newtype

```lean
inductive Chain where
  | mk (link : Option (Nat × Chain))

@[match_pattern] abbrev Chain.nil : Chain := .mk none
@[match_pattern] abbrev Chain.cons (label : Nat) (rest : Chain) : Chain :=
  .mk (some (label, rest))
```

a list of labels, written as the newtype `Chain = Option (Nat × Chain)`: one binder whose
body is a *union*, which is the shape a newtype has when it stands for a list.  Its `fib`
is the program the depth is for:

```lean
def Chain.fib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 1
  | .cons _ (.cons l r) => fib (.cons l r) + fib r
```

(the chain below is rebuilt rather than named with `t@…`, so that Lean compiles the
recursion structurally, which is what `#leanscript_to_term` translates).

| the program | the node | the term |
| --- | --- | --- |
| `Chain.fib` (reads two links down) | `recAlias_rec 1` | `fibTerm` |
| `Chain.trib`, `Chain.tetra`, `Chain.penta`, `Chain.hexa` | `recAlias_rec 2 … 5` | `tribTerm`, … |
| `Chain.fibLoopTR` (tail-recursive, two accumulators) | `recAlias_rec 0` **at a function type** | `fibTRTerm` |
| `Chain.fibPair` (pair recursion) | `recAlias_rec 0` at a record type | `fibPairTerm` |
| `Chain.cont` (the continuant, which reads the **label** too) | `recAlias_rec 1` | `contTerm` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

**What is checked.**  Each term of `TermTests.RecAliasRecDepthTest` is the Lean program
of §0 translated by `#leanscript_to_term`, at the type it states, so the file fails to
build if a program is not the fold at the documented depth; what the contexts of the
branches are is pinned separately, by the `rfl` examples of §1.  And `LeanScript.Ty.Den` gives a recursive
newtype its values — the W-tree of its body — so the terms also **run**: §7 of
`TermTests.RecAliasRecDepthTest` builds chains with the introduction form and checks, with
the kernel, that every term answers what its Lean reference does.

The Lean programs the terms transcribe are checked too, in §0: their values at a chain of
ten links by `#guard`, that `Chain.fib` is the ordinary `fib` of the chain's length, and
the request's own theorems — that the pair recursion carries `(fib n, fib (n + 1))`, that
its first component is `fib`, and that the tail-recursive loop computes `fib`.
-/

namespace TermTests.RecAliasRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of. -/

/-- A chain of labels: the recursive newtype this file folds over, `Option (Nat × Chain)`
    — one constructor of one field, which mentions the type itself inside a union. -/
inductive Chain where
  /-- The one constructor: the wrapper is erased. -/
  | mk (link : Option (Nat × Chain))
  deriving LeanScriptTyWf

namespace Chain

/-- The chain ends. -/
@[match_pattern] abbrev nil : Chain := .mk none

/-- A label, and the rest of the chain. -/
@[match_pattern] abbrev cons (label : Nat) (rest : Chain) : Chain := .mk (some (label, rest))

/-- How many links the chain has. -/
def len : Chain → Nat
  | .nil => 0
  | .cons _ r => len r + 1

/-- A chain of `n` links, all labelled `0`. -/
def ofNat : Nat → Chain
  | 0 => .nil
  | n + 1 => .cons 0 (ofNat n)

@[simp] theorem len_ofNat : (n : Nat) → len (ofNat n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (len_ofNat n)

/-- `fib`, on a chain: it reads the answer two links down. -/
def fib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 1
  | .cons _ (.cons l r) => fib (.cons l r) + fib r

/-- The tribonacci numbers: three links down. -/
def trib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 1
  | .cons _ (.cons l₂ (.cons l₃ r)) => trib (.cons l₂ (.cons l₃ r)) + trib (.cons l₃ r) + trib r

/-- The tetranacci numbers: four links down. -/
def tetra : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 1
  | .cons _ (.cons l₂ (.cons l₃ (.cons l₄ r))) =>
      tetra (.cons l₂ (.cons l₃ (.cons l₄ r))) + tetra (.cons l₃ (.cons l₄ r)) +
        tetra (.cons l₄ r) + tetra r

/-- The pentanacci numbers: five links down. -/
def penta : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => 1
  | .cons _ (.cons l₂ (.cons l₃ (.cons l₄ (.cons l₅ r)))) =>
      penta (.cons l₂ (.cons l₃ (.cons l₄ (.cons l₅ r)))) +
        penta (.cons l₃ (.cons l₄ (.cons l₅ r))) + penta (.cons l₄ (.cons l₅ r)) +
        penta (.cons l₅ r) + penta r

/-- The hexanacci numbers: six links down. -/
def hexa : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil)))) => 1
  | .cons _ (.cons l₂ (.cons l₃ (.cons l₄ (.cons l₅ (.cons l₆ r))))) =>
      hexa (.cons l₂ (.cons l₃ (.cons l₄ (.cons l₅ (.cons l₆ r))))) +
        hexa (.cons l₃ (.cons l₄ (.cons l₅ (.cons l₆ r)))) +
        hexa (.cons l₄ (.cons l₅ (.cons l₆ r))) + hexa (.cons l₅ (.cons l₆ r)) +
        hexa (.cons l₆ r) + hexa r

/-- The tail-recursive loop, with two accumulators (`@[inline]`, so that `fibTR` below
    translates to the loop itself, applied to `0` and `1`). -/
@[inline] def fibLoopTR : Chain → Nat → Nat → Nat
  | .nil, a, _ => a
  | .cons _ r, a, b => fibLoopTR r b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (t : Chain) : Nat := fibLoopTR t 0 1

/-- The pair recursion: the answer at the chain and the answer at one link more
    (`@[inline]`, so that `fibPairFst` below translates to the fold itself). -/
@[inline] def fibPair : Chain → Nat × Nat
  | .nil => (0, 1)
  | .cons _ r => let (a, b) := fibPair r; (b, a + b)

/-- `fib`, as the first component of the pair recursion. -/
def fibPairFst (t : Chain) : Nat := (fibPair t).1

/-- The **continuant** of the labels of a chain, the one program here that reads the
    newtype's own label as well as the answers: `K ⟨⟩ = 1`, `K ⟨a⟩ = a` and
    `K ⟨a, b, …⟩ = a * K ⟨b, …⟩ + K ⟨…⟩`. -/
def cont : Chain → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a (.cons l r) => a * cont (.cons l r) + cont r

-- The reference programs are the familiar sequences.
-- [SKIPPED BY PROFILE_LAKE] #guard fib (ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard fibTR (ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard fibPair (ofNat 10) = (55, 89)
-- [SKIPPED BY PROFILE_LAKE] #guard trib (ofNat 10) = 81
-- [SKIPPED BY PROFILE_LAKE] #guard tetra (ofNat 10) = 56
-- [SKIPPED BY PROFILE_LAKE] #guard penta (ofNat 10) = 31
-- [SKIPPED BY PROFILE_LAKE] #guard hexa (ofNat 10) = 16
-- [SKIPPED BY PROFILE_LAKE] #guard cont (.cons 3 (.cons 2 (.cons 1 .nil))) = 10

/-- **The chain's `fib` is the ordinary `fib`** of the number of links it has. -/
theorem fib_eq_fib_len : (t : Chain) → fib t = TermTests.FibWindow.fib (len t)
  | .nil => by simp [fib, len, TermTests.FibWindow.fib]
  | .cons _ .nil => by simp [fib, len, TermTests.FibWindow.fib]
  | .cons a (.cons b r) => by
      have he : fib (.cons a (.cons b r)) = fib (.cons b r) + fib r := by simp [fib]
      have hlen : len (.cons a (.cons b r)) = len r + 2 := by simp [len]
      have hl1 : len (.cons b r) = len r + 1 := by simp [len]
      have hw : TermTests.FibWindow.fib (len r + 2) =
          TermTests.FibWindow.fib (len r) + TermTests.FibWindow.fib (len r + 1) := by
        simp [TermTests.FibWindow.fib]
      rw [he, fib_eq_fib_len (.cons b r), fib_eq_fib_len r, hlen, hl1, hw]
      omega

/-- So on the chain of `n` links it is `fib n`. -/
theorem fib_ofNat (n : Nat) : fib (ofNat n) = TermTests.FibWindow.fib n := by
  rw [fib_eq_fib_len, len_ofNat]

/-- The pair recursion carries the answer at the chain and the answer at one link
    more. -/
theorem fibPair_eq : (t : Chain) → fibPair t = (fib t, fib (.cons 0 t))
  | .nil => by simp [fibPair, fib]
  | .cons l c => by
      have ih := fibPair_eq c
      have hfib : fib (.cons l c) = fib (.cons 0 c) := by
        rcases c with ⟨_ | ⟨_, _⟩⟩ <;> simp [fib]
      show (let (a, b) := fibPair c; ((b, a + b) : Nat × Nat)) = _
      rw [ih]
      have hup : fib (.cons 0 (.cons l c)) = fib (.cons l c) + fib c := by simp [fib]
      simp only [hup, hfib]
      exact Prod.ext rfl (Nat.add_comm _ _)

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (t : Chain) : (fibPair t).1 = fib t := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `k` and `k + 1`, answers at `k` plus the length
    of the chain. -/
theorem fibLoopTR_eq : (t : Chain) → (k : Nat) →
    fibLoopTR t (TermTests.FibWindow.fib k) (TermTests.FibWindow.fib (k + 1)) =
      TermTests.FibWindow.fib (k + len t)
  | .nil, _ => rfl
  | .cons _ c, k => by
      show fibLoopTR c (TermTests.FibWindow.fib (k + 1))
        (TermTests.FibWindow.fib k + TermTests.FibWindow.fib (k + 1)) = _
      rw [show TermTests.FibWindow.fib k + TermTests.FibWindow.fib (k + 1) =
        TermTests.FibWindow.fib (k + 2) from rfl, fibLoopTR_eq c (k + 1)]
      show TermTests.FibWindow.fib (k + 1 + len c) = TermTests.FibWindow.fib (k + (len c + 1))
      congr 1
      omega

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (t : Chain) : fibTR t = fib t := by
  show fibLoopTR t (TermTests.FibWindow.fib 0) (TermTests.FibWindow.fib 1) = _
  rw [fibLoopTR_eq t 0, fib_eq_fib_len, Nat.zero_add]

end Chain

/-! ## 1. The newtype, and what its branch binds -/

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

/-- `Option τ`, as a union of the language: `none` first, then `some`. -/
abbrev optTy (τ : TyWf) : TyWf := .taggedUnion (.skip (.here ⟨τ, []⟩ []))

/-- The schema of a **link**: a label, and whatever follows it. -/
abbrev linkSchema (τ : TyWf) : LeanRecordSchema TyWf := ⟨natT, τ, []⟩

/-- A link: `Nat × τ`. -/
abbrev linkTy (τ : TyWf) : TyWf := .record (linkSchema τ)

/-- `Nat × Ty.self`, written inside the binder. -/
def linkSelf : Ty := .record ⟨.prim .nat, Ty.self, []⟩

/-- The body of the newtype: `Option (Nat × Ty.self)`, written inside the binder.  The
    occurrence sits inside the `some` constructor, which is the only way a newtype can
    mention itself and still have values — the `none` constructor is the one that does
    not. -/
def chainBody : Ty := .taggedUnion (.skip (.here ⟨linkSelf, []⟩ []))

/-- That body, with the proof that it is well formed in the scope the binder opens. -/
def chainBodyW : TyWfIn 1 := chainBody.toTyWfIn

/-- The type of a chain. -/
def chainTy : TyWf := .recAlias chainBodyW

-- It is the tree `LeanScriptTyWf` derives for the Lean `Chain` of §0, so the Lean programs
-- there translate to terms of this type.
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf Chain = chainTy := by kernel_rfl

-- A value of it is an `Option` of a label and one more chain.
-- [SKIPPED BY PROFILE_LAKE] example : TyWf.recAliasUnfold chainBodyW = optTy (linkTy chainTy) := by kernel_rfl

-- **The old fold bound no answer**: the body of the newtype is not an occurrence of it,
-- so `TyWf.recBinders` — which is what the branch of every other fold uses — hands the
-- branch the body and nothing else (`LeanScript.TyWf.recBinders_recAlias`, at every
-- newtype).
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recBinders chainTy τ [chainBodyW] = [optTy (linkTy chainTy)] := by kernel_rfl

example (τ : TyWf) :
    TyWf.recBinders chainTy τ [chainBodyW] = [TyWf.recAliasUnfold chainBodyW] :=
  TyWf.recBinders_recAlias chainBodyW (by ty_wf) τ

/-- **The answer tree of depth `j` at a chain**, written out: at `0` the answer there, and
    at `j + 1` that answer beside the body's own shape — an `Option` of a label and the
    tree of depth `j` at the chain below. -/
abbrev treeTy (τ : TyWf) : Nat → TyWf
  | 0 => τ
  | j + 1 => .record ⟨τ, optTy (linkTy (treeTy τ j)), []⟩

/-- **The window a depth-`k` fold binds**, written out: the newtype's body with the chain
    below replaced by the answer tree of depth `k` at it. -/
abbrev winTy (τ : TyWf) (k : Nat) : TyWf := optTy (linkTy (treeTy τ k))

-- These two equations are the whole of the descent, and they are what the branches below
-- are written against: **taking a window apart** binds a link whose second field is the
-- answer tree at the chain below, and **taking an answer tree apart** binds the answer at
-- that chain and the window of one depth less at it.  So each level of descent pushes
-- `1 + 2 + 2` binders in front of the context, and the answers read so far sit at the
-- indices `1, 3, 8, 13, …`.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (k : Nat) : winTy τ k = optTy (linkTy (treeTy τ k)) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (j : Nat) : treeTy τ (j + 1) = .record ⟨τ, winTy τ j, []⟩ := by kernel_rfl

-- At depth `0` the branch binds the body — an `Option` of a label and a chain — and the
-- window, an `Option` of a label and the answer at the chain below: the plain fold of a
-- newtype.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 ++ Γ =
-- [SKIPPED BY PROFILE_LAKE]       optTy (linkTy chainTy) :: optTy (linkTy τ) :: Γ := by kernel_rfl

-- At depth `1` the window holds, for the chain below, the answer at it *and* the answers
-- at the chains below that one.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) (Γ : Ctx) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 1 ++ Γ =
-- [SKIPPED BY PROFILE_LAKE]       optTy (linkTy chainTy) ::
-- [SKIPPED BY PROFILE_LAKE]         optTy (linkTy (.record ⟨τ, optTy (linkTy τ), []⟩)) :: Γ := by kernel_rfl

/-- The context every fold below is written in: the chain it folds over, bound by the
    `fun` in front of it. -/
abbrev CCtx : Ctx := [chainTy]

/-- **The context a branch of a depth-`k` fold is written in**: the body, the window, and
    then the context the fold stands in. -/
abbrev branchCtx (τ : TyWf) (k : Nat) : Ctx :=
  optTy (linkTy chainTy) :: winTy τ k :: CCtx

-- That really is the context the grammar asks for, at each of the depths used below.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 ++ CCtx = branchCtx τ 0 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 1 ++ CCtx = branchCtx τ 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 2 ++ CCtx = branchCtx τ 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 3 ++ CCtx = branchCtx τ 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 4 ++ CCtx = branchCtx τ 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 5 ++ CCtx = branchCtx τ 5 := by kernel_rfl

/-- The union the body of the newtype is, once unfolded: what `Term.recAlias_mk` takes
    a value of. -/
abbrev chainUnion : LeanTaggedUnionSchema TyWf := .skip (.here ⟨linkTy chainTy, []⟩ [])

/-- The empty chain, as a term: `Chain.nil`, translated. -/
def nilTerm : Term sigAdd [] chainTy := #leanscript_to_term Chain.nil

/-- One more link on top of the chain in scope: `Chain.cons`, translated. -/
def consTerm : Term sigAdd [] (natT ⇒ chainTy ⇒ chainTy) := #leanscript_to_term Chain.cons


end TermTests.RecAliasRecDepth

end
