module

public import TermTests.RecUnionRecDepthTest.Programs
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TermTests.RecUnionRecDepthTest.Programs`; this file translates the programs to terms
of the language with `#leanscript_to_term` and checks the terms against the references.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`: the depth-one fold

`Peano.fib` reads the answer two constructors down, so it translates to
`recTaggedUnion_rec 1`.  The `zero` branch answers `0`.  The `succ` branch does not
answer: it descends into its field — the only occurrence of the union among its fields,
which is `SelfField`'s `.here rfl` — and dispatches on it.  In that dispatch the value is
`succ n` with `n` in hand, so:

* if `n` is `zero` the value is `succ zero`, and the answer is `1`;
* if `n` is `succ m`, the context binds `m` (index `0`), the answer at `m` (index `1`),
  `n` (index `2`) and the answer at `n` (index `3`), and the answer is `fib m + fib n` —
  which is the `fib n + fib (n + 1)` of the program. -/

/-- **`fib` over a recursive tagged union**: `Peano.fib`, translated to the depth-one
    fold. -/
def fibTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.fib

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

The `n + k` recursions of the request: at depth `k` the branch descends `k` times, and the
answers at the values it descended past are the odd indices `1, 3, …, 2k + 1` — nearest
last, since each descent pushes the subvalue and its answer in front of the context. -/

/-- `trib`, as a term: a depth-two fold. -/
def tribTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.trib

/-- `tetra`, as a term: a depth-three fold. -/
def tetraTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.tetra

/-- `penta`, as a term: a depth-four fold. -/
def pentaTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.penta

/-- `hexa`, as a term: a depth-five fold. -/
def hexaTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.hexa

mutual
/-- The depth of the `recTaggedUnion_rec` a translated function is: the fold under the
    `fun`s of its arguments, and under the applications and the case analysis around it.
    `none` if the translation is not of that shape. -/
def recUnionRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sigAdd Γ τ J → Option Nat
  | .recTaggedUnion_rec k _ _ _ => some k
  | .letE c body => (recUnionRecDepth?.comp c).orElse fun _ => recUnionRecDepth? body
  | .letJ jp body => (recUnionRecDepth? body).orElse fun _ => recUnionRecDepth? jp
  | _ => none

/-- `recUnionRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recUnionRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sigAdd Γ τ → Option Nat
  | .lam b => recUnionRecDepth? b
  | _ => none
end

-- Each program is the fold at the depth it reads.
-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? fibTerm = some 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? tribTerm = some 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? tetraTerm = some 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? pentaTerm = some 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? hexaTerm = some 5 := by kernel_rfl

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the immediate predecessor, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added.  `fibTR` is that loop
applied to `0` and `1`. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.fibTR

/-- The branches of the loop, read back out of `fibTRTerm`: `zero` answers
    `fun a b => a`, and `succ` answers `fun a b => ih b (a + b)`, where `ih` is the loop at
    the predecessor. -/
def fibTRCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind loopTy) PCtx peanoSchema loopTy 0 [] :=
  #leanscript_fold_branch fibTRTerm

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? fibTRTerm = some 0 := by kernel_rfl

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at `n + 1` alongside the
answer at `n`.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib n, fib (n + 1))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (peanoTy ⇒ natT) := #leanscript_to_term Peano.fibPairFst

/-- The branches of the pair recursion, read back out of `fibPairTerm`: `zero` answers
    `(0, 1)`, and `succ` takes the pair at the predecessor apart — binding `a` at index `0`
    and `b` at index `1` — and answers `(b, a + b)`. -/
def fibPairCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind pairTy) PCtx peanoSchema pairTy 0 [] :=
  #leanscript_fold_branch fibPairTerm

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? fibPairTerm = some 0 := by kernel_rfl

/-! ## 6. A constructor with more than one field: the continuant over a list

Every constructor above has at most one field, so a deeper look had only one field it
could descend into.  The **continuant** is the same `fib`-shaped recursion over a union
whose recursive constructor carries a payload first, a list (`contRef` below).

Its `cons` branch reads the answer at the tail *of the tail*, so it descends once, and
the field it descends into is the **second** — which is what `SelfField`'s `.there` says. -/

/-- The schema of a list of naturals: `nil` carries nothing, `cons` carries a natural and
    the list itself. -/
def natListSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.prim .nat).toTyWfIn, [Ty.self.toTyWfIn]⟩ [])

/-- The type of a list of naturals. -/
def natListTy : TyWf := .recTaggedUnion natListSchema

-- It is the tree of a Lean `List Nat`.
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf (List Nat) = natListTy := by kernel_rfl

/-- The fields of `cons`. -/
abbrev consFields : List (TyWfIn 1) := [(Ty.prim .nat).toTyWfIn, Ty.self.toTyWfIn]

/-- How the value of a fold over the list reaches a branch. -/
abbrev lbind (τ : TyWf) : List (TyWfIn 1) → List TyWf := TyWf.recBinders natListTy τ

/-- The context the fold below is written in. -/
abbrev LCtx : Ctx := [natListTy]

-- The `cons` branch binds the head, the tail, and the value of the fold at the tail —
-- the head is not an occurrence of the union, so no value of the fold follows it.
-- [SKIPPED BY PROFILE_LAKE] example (τ : TyWf) : lbind τ consFields = [natT, natListTy, τ] := by kernel_rfl

/-- The continuant, in Lean: `K [] = 1`, `K [a] = a` and `K (a :: b :: as) =
    a * K (b :: as) + K as`. -/
def contRef : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * contRef (b :: as) + contRef as

/-- The continuant, as a term: `contRef`, translated to the depth-one fold of a list.  Its
    `cons` branch descends into its **second** field, and then answers `a` for a
    one-element list and `a * K (b :: bs) + K bs` for a longer one. -/
def contTerm : Term sigAdd [] (natListTy ⇒ natT) := #leanscript_to_term contRef

-- [SKIPPED BY PROFILE_LAKE] example : recUnionRecDepth? contTerm = some 1 := by kernel_rfl

/-! ## 7. Running the terms

A recursive tagged union has values in the model (`LeanScript.Ty.Den` gives it the W-tree
of its constructors), so these terms run, and the kernel checks them against their Lean
references.  The depth-`k` folds are evaluated with every answer remembered
(`LeanScript.WType.memo`), so a deeper look reads answers that are already there. -/


/-- The values of `add` and `mul`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigAdd` (scoped: the checks in
    `TermTests/RecUnionRecDepthTest/Run*.lean` use it too). -/
scoped macro:max "runP" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- The Peano natural `n`, built by the terms `zeroTerm` and `succTerm`. -/
def peanoVal : Nat → TyWf.Den peanoTy
  | 0 => runP zeroTerm
  | n + 1 => runP succTerm (peanoVal n)

/-- The empty list. -/
def nilList : List Nat := []

/-- A natural on top of a list. -/
def consList (a : Nat) (as : List Nat) : List Nat := a :: as

/-- The empty list, as a term: `nilList`, translated. -/
def nilListTerm : Term sigAdd [] natListTy := #leanscript_to_term nilList

/-- A natural on top of a list, as a term: `consList`, translated. -/
def consListTerm : Term sigAdd [] (natT ⇒ natListTy ⇒ natListTy) :=
  #leanscript_to_term consList

/-- The list of naturals `l`, built by the introduction form. -/
def natListVal : List Nat → TyWf.Den natListTy
  | [] => runP nilListTerm
  | a :: as => runP consListTerm a (natListVal as)

-- [SKIPPED BY PROFILE_LAKE] example : runP fibTerm (peanoVal 10) = 55 := by decide +kernel
-- The checks of each term against its reference at the first ten arguments are in
-- `TermTests/RecUnionRecDepthTest/RunFibToPenta.lean` and
-- `TermTests/RecUnionRecDepthTest/RunHexaLoopPair.lean`: each takes a few seconds of
-- kernel time, and in two files of their own they are checked in parallel.
-- [SKIPPED BY PROFILE_LAKE] example : runP contTerm (natListVal [3, 1, 4, 1, 5]) = contRef [3, 1, 4, 1, 5] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP contTerm (natListVal []) = contRef [] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runP contTerm (natListVal [7]) = contRef [7] := by decide +kernel

/-! ## 8. A depth is needed: what cannot be written without one

At depth `0` a branch is an answer and nothing else — `LeanScript.FoldKBranch.deep` is a
branch of a depth `k + 1` fold — so the `succ` branch of `fib`, which has to look one
constructor further down before it can answer, is not a branch of the plain fold. -/

/--
error: Type mismatch
  FoldKBranch.deep (ListAnyT.here ?m.18)
    (TaggedUnionFoldKCases.skip (FoldKBranch.here (Term.nat_mk 1))
      (CtorsWithPayloadFoldKCases.here (FoldKBranch.here (Term.nat_mk 2)) TaggedUnionFoldKCasesRest.nil))
has type
  FoldKBranch ?m.60 (LeanTaggedUnionSchema.skip (CtorsWithPayload.here ?m.46 [])) ?m.62 ?m.7 (?m.14 :: ?m.15)
    (TyWf.prim LeanPrimTy.nat) (?m.65 + 1) ?m.11
but is expected to have type
  FoldKBranch sigAdd peanoSchema (pbind natT) PCtx succFields natT 0 []
-/
#guard_msgs (error) in
def succBranchTooShallow :
    FoldKBranch sigAdd peanoSchema (pbind natT) PCtx succFields natT 0 [] :=
  .deep (.here rfl)
    (.skip (.here (.nat_mk 1)) (.here (.here (.nat_mk 2)) .nil))

-- And a depth-zero fold *is* the fold that was there before the depth was added: the
-- branches of the loop of §4, read as branches of the plain fold and back, are the same
-- branches (`LeanScript.RecUnionRecFacts`, at every union and every motive).
example :
    TaggedUnionFoldCases.toFoldK (TaggedUnionFoldKCases.ofFoldK fibTRCases) = fibTRCases :=
  TaggedUnionFoldKCases.toFoldK_ofFoldK fibTRCases

example :
    TaggedUnionFoldCases.toFoldK (TaggedUnionFoldKCases.ofFoldK fibPairCases) =
      fibPairCases :=
  TaggedUnionFoldKCases.toFoldK_ofFoldK fibPairCases

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: `n / 2` is not `n` with a fixed number of constructors taken
off it, so there is no depth at which the branch is *given* the answer at it.  The same
is true of the union — a fold is given the answers on the path it descended, and a
recursion that jumps needs a measure and a proof, which a `Term` does not carry.  This is
the same boundary `TermTests/NatRecDepthTest/` records for `Nat`.
-/

end TermTests.RecUnionRecDepth
