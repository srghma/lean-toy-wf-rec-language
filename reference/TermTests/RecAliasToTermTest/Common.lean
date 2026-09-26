module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `recAlias_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci`, `pentanacci`, … ; `TermTests/ArrayRecToTermTest/`,
`TermTests/RecUnionToTermTest/` and `TermTests/RecObjectToTermTest/` do the same for
`array_rec k`, `recTaggedUnion_rec k` and `recObject_rec k`.  These files do it for
`LeanScript.Term.recAlias_rec k`, the fold of a **recursive newtype** that reads `k + 1`
levels at a time.

**Which Lean program is a `recAlias_rec k`.**  A recursive newtype is an inductive type with
**one** constructor of **one** field that mentions the type itself inside another type (it
has to: `μX. X` has no values).  Its tree is `Ty.recAlias body`, the wrapper erased.  The
one used here is a chain of labelled links:

```lean
inductive Link (α : Type) where
  | stop
  | step (label : Nat) (rest : α)

inductive Chain where
  | mk (link : Link Chain)
```

whose tree is `Ty.recAlias (stop | step nat self)` (checked below).  Lean compiles an
ordinary structural recursion on `Chain` into `Chain.brecOn`, and the translation reads it
as `recAlias_rec k` (`LeanScript.ToTerm.TransRecObject`, which serves recursive records
and recursive newtypes alike).  The programs are written as ordinary Lean, with no
`decreasing_by` and nothing added for the translation.

The depth `k` is the smallest one for which every branch reads only the labels and the
values of the recursion at the links at most `k + 1` levels down, which is what the
**window** of `recAlias_rec k` holds (`LeanScript.TyWf.recAliasRecBinders`).

One file per depth, `K0.lean` … `K4.lean`.  Each program is checked three ways:

* the translated term **is** a `recAlias_rec` of the expected depth (`recAliasRecDepth?`);
* the term computes the expected numbers;
* the term computes what the Lean definition computes.

The inputs are built by translated Lean programs too: `Chain.ofNat n` (a chain of `n`
links, a `nat_rec` whose branch builds a link with `recAlias_mk`), `Chain.ofList l` (a
fold of a list) and a literal chain.

The equations are checked by `kernel_rfl` rather than `rfl`: the elaborator's own check of
such an equation runs out of heartbeats, while the kernel checks it quickly (see
`LeanScript/KernelRfl.lean`).  `kernel_rfl` is still a proof by `Eq.refl`, checked by the
kernel.
-/

namespace TermTests.RecAliasToTerm

open LeanScript TermTests.NatRecDepth

/-- One link of a chain: the end, or a label and the rest.  A non-recursive wrapper of its
    own, so that `Chain` below is a newtype whose body is a union. -/
inductive Link (α : Type) where
  /-- The end of the chain. -/
  | stop
  /-- A label, and the rest of the chain. -/
  | step (label : Nat) (rest : α)
  deriving LeanScriptTyWf

/-- A chain of labelled links: the recursive newtype the programs fold over. -/
inductive Chain where
  /-- The one constructor, of one field: the wrapper is erased. -/
  | mk (link : Link Chain)
  deriving LeanScriptTyWf

/-- The type of a chain, in the language. -/
abbrev chainT : TyWf := tyWfOf Chain

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

-- The derived tree is a recursive newtype whose body is the union `stop | step nat self`.
-- [SKIPPED BY PROFILE_LAKE] example :
-- [SKIPPED BY PROFILE_LAKE]     tyOf Chain = .recAlias (.taggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ []))) := rfl

mutual
/-- The depth of the `recAlias_rec` a translated function is: the fold under the `fun`s of
    its arguments, applied to the arguments that Lean put in the motive (a recursion with
    accumulators folds to a function).  `none` if the translation is not of that shape. -/
def recAliasRecDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term Sg Γ τ J → Option Nat
  | .recAlias_rec k _ _ _ => some k
  | .letE c body => (recAliasRecDepth?.comp c).orElse fun _ => recAliasRecDepth? body
  | .letJ jp body => (recAliasRecDepth? body).orElse fun _ => recAliasRecDepth? jp
  | _ => none

/-- `recAliasRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def recAliasRecDepth?.comp {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Comp Sg Γ τ → Option Nat
  | .lam b => recAliasRecDepth? b
  | _ => none
end

namespace Chain

/-- A chain of `n` links, labelled `n - 1, …, 1, 0` from the top. -/
def ofNat : Nat → Chain
  | 0 => .mk .stop
  | n + 1 => .mk (.step n (ofNat n))

/-- The chain labelled by the elements of `l`, from the top. -/
def ofList : List Nat → Chain
  | [] => .mk .stop
  | a :: as => .mk (.step a (ofList as))

end Chain

/-- `Chain.ofNat`, as a term: a `nat_rec` whose branch builds a link with `recAlias_mk`. -/
def ofNat_term : Term sigAdd [] (natT ⇒ chainT) := #leanscript_to_term Chain.ofNat

/-- `Chain.ofList`, as a term: a fold of a list, building links with `recAlias_mk`. -/
def ofList_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ chainT) :=
  #leanscript_to_term Chain.ofList

/-- The chain of `n` links `Chain.ofNat n`, as a value of the language. -/
def chainOfNat (n : Nat) : TyWf.Den chainT := runAdd ofNat_term n

/-- The chain labelled by `l`, as a value of the language: `Chain.ofList` run by its
    translation, on the list `l` of the language. -/
def chainOf (l : List Nat) : TyWf.Den chainT :=
  runAdd ofList_term (Ty.DenRec.ofList (.prim .nat) l)

/-- A chain written out, as a closed Lean value. -/
def chain3 : Chain := .mk (.step 3 (.mk (.step 2 (.mk (.step 1 (.mk .stop))))))

/-- `chain3`, as a term: nested `recAlias_mk`s. -/
def chain3_term : Term sigAdd [] chainT := #leanscript_to_term chain3

end TermTests.RecAliasToTerm

end
