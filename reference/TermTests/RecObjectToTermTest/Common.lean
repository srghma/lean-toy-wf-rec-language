module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `recObject_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci`, `pentanacci`, … and `TermTests/ArrayRecToTermTest/` does the
same for `LeanScript.Term.array_rec k`.  These files do it for
`LeanScript.Term.recObject_rec k`, the fold of a **recursive record** that reads `k + 1`
levels at a time.

**Which Lean program is a `recObject_rec`.**  A recursive record is an inductive type with
**one** constructor that mentions itself only *inside* another type — it has to, or it
would have no values.  The shortest one is a chain of labelled cells:

```lean
inductive Cell where
  | mk (label : Nat) (next : Option Cell)
  deriving LeanScriptTyWf
```

whose tree is `Ty.recObject ⟨nat, Option self⟩` (checked below).  Lean compiles an
ordinary structural recursion on it — pattern matching on `.mk a none` and
`.mk a (some c)`, calling itself on the cells below — into `Cell.brecOn` (Lean's
structural recursion on a nested inductive), and the translation reads that as
`recObject_rec k`.  The programs are written as ordinary Lean, with no `decreasing_by`
and nothing added for the translation.

The depth `k` is read off the compiled recursion: it is the smallest `k` for which every
branch reads only the labels and the values of the recursion at the cells at most
`k + 1` levels down, which is what the **window** of `recObject_rec k` holds
(`LeanScript.TyWf.recObjectRecBinders`).  So `Cell.sum` (reads the value one cell down)
is `k = 0`, `Cell.fib` (two cells down) is `k = 1`, the tribonacci numbers `k = 2`, and
so on.

The inputs are built by translated Lean programs too: `Cell.ofNat n` (a chain of `n + 1`
cells, a `nat_rec` whose branch builds a cell with `recObject_mk`) and `Cell.ofList a l`
(a chain labelled `a :: l`, a fold of a list).

Each program (one file per depth, so that they build in parallel) is checked:

* the translated term **is** a `recObject_rec` of the expected depth (`…_depth`);
* the term computes the expected numbers;
* the term computes what the Lean definition computes.

The equations are checked by `kernel_rfl` rather than `rfl`: the elaborator's own check
of such an equation runs out of heartbeats (every extern call goes through the case
splits of `Extern.eval`), while the kernel checks it quickly (see
`LeanScript/KernelRfl.lean`).  `kernel_rfl` is still a proof by `Eq.refl`, checked by the
kernel.
-/

namespace TermTests.RecObjectToTerm

open LeanScript

/-- A chain of labelled cells: the recursive record the programs fold over. -/
inductive Cell where
  /-- A label, and perhaps one more cell. -/
  | mk (label : Nat) (next : Option Cell)
  deriving LeanScriptTyWf

/-- The type of a cell, in the language. -/
abbrev cellT : TyWf := tyWfOf Cell

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

-- The derived tree is a recursive record: a `nat` and an `Option` of the record itself.
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Cell = .recObject ⟨.prim .nat, .taggedUnion (.skip (.here ⟨.self, []⟩ [])), []⟩ :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

/-- The empty signature: `+` and `*` are `Nat.add` and `Nat.mul`, implemented by the
    externs `lean_nat_add` and `lean_nat_mul`, so the signature needs no declaration. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0` (scoped, so it is available in every file that
    opens `TermTests.RecObjectToTerm`). -/
scoped macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

mutual
/-- The depth of the `recObject_rec` a translated function is: the fold under the `fun`s
    of its arguments, applied to the arguments that Lean put in the motive (a recursion
    with accumulators folds to a function).  `none` if the translation is not of that
    shape. -/
def recObjectRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sig0 Γ τ J → Option Nat
  | .recObject_rec k _ _ _ => some k
  | .letE c body => (recObjectRecDepth?.comp c).orElse fun _ => recObjectRecDepth? body
  | .letJ jp body => (recObjectRecDepth? body).orElse fun _ => recObjectRecDepth? jp
  | _ => none

/-- `recObjectRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recObjectRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sig0 Γ τ → Option Nat
  | .lam b => recObjectRecDepth? b
  | _ => none
end

namespace Cell

/-- A chain of `n + 1` cells, labelled `n, n - 1, …, 0` from the top. -/
def ofNat : Nat → Cell
  | 0 => .mk 0 none
  | n + 1 => .mk (n + 1) (some (ofNat n))

/-- The chain labelled `a :: l`, from the top. -/
def ofList : Nat → List Nat → Cell
  | a, [] => .mk a none
  | a, b :: bs => .mk a (some (ofList b bs))

end Cell

/-- `Cell.ofNat`, as a term: a `nat_rec` whose branch builds a cell with `recObject_mk`. -/
def ofNat_term : Term sig0 [] (natT ⇒ cellT) := #leanscript_to_term Cell.ofNat

/-- `Cell.ofList`, as a term: a fold of a list, building cells with `recObject_mk`. -/
def ofList_term : Term sig0 [] (natT ⇒ tyWfOf (List Nat) ⇒ cellT) :=
  #leanscript_to_term Cell.ofList

/-- The chain labelled `a :: l`, as a value of the language: `Cell.ofList` run by its
    translation, on the list `l` of the language (`LeanScript.Ty.DenRec.ofList`). -/
def cellOf (a : Nat) (l : List Nat) : TyWf.Den cellT :=
  run ofList_term a (Ty.DenRec.ofList (.prim .nat) l)

/-- The chain of `n + 1` cells `Cell.ofNat n`, as a value of the language: `Cell.ofNat`
    run by its translation. -/
def cellOfNat (n : Nat) : TyWf.Den cellT := run ofNat_term n

/-- A chain written out, as a closed Lean value. -/
def chain3 : Cell := .mk 3 (some (.mk 2 (some (.mk 1 none))))

/-- `chain3`, as a term: nested `recObject_mk`s. -/
def chain3_term : Term sig0 [] cellT := #leanscript_to_term chain3

end TermTests.RecObjectToTerm
