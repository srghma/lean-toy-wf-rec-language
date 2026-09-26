module

public import LeanScript.Eval

@[expose] public section

/-!
# `array_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci` and `pentanacci`, which descend `k + 1 = 2, 3, 4, 5` steps.
These files do the same for `LeanScript.Term.array_rec k`, the fold of an array that
descends `k + 1` elements at a time.

**Which Lean program is an `array_rec`.**  Lean cannot recurse structurally on an
`Array`: a definition by the patterns `⟨x :: xs⟩ => … f ⟨xs⟩` is compiled by well-founded
recursion (and is irreducible, so none of the checks below could be stated about
it).  What Lean *does* compile structurally is a recursion on the list of the elements:

```lean
def f (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | …
```

The translation reads `go a.toList` — a structurally recursive function on lists applied
to the elements of an array — as `array_rec k` on `a`.  The depth `k` is read off the
compiled recursion exactly as for `nat_rec k`: it is the smallest `k` for which the branch
at `x :: y₁ :: … :: yₖ :: rest` reads only the head `x`, the elements `y₁ … yₖ` and the
values of `go` at the `k + 1` suffixes `y₁ :: … :: rest`, …, `rest`
(`TermTests/ArrayRecToTermTest/Elements.lean`).  The patterns for the lists of at most `k`
elements become the `LeanScript.ArrayRecBases`.

Each program (one file per program, so that they build in parallel) is written
as ordinary Lean, with nothing added for the translation,
and each block checks that

* the translated term **is** an `array_rec` of the expected depth (`…_depth`);
* the term computes the expected numbers, by `kernel_rfl`;
* the term computes what the Lean definition computes, by `kernel_rfl`.
-/

namespace TermTests.ArrayRecToTerm

open LeanScript

/-- The empty signature: `+` is `Nat.add`, which is implemented by the extern
    `lean_nat_add`, so the translation calls it as `Term.extern .lean_nat_add` and the
    signature needs no declaration for it. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0` (scoped, so it is available in every file that
    opens `TermTests.ArrayRecToTerm`). -/
scoped macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

mutual
/-- The depth of the `array_rec` a translated function `fun a => array_rec k …` is — the
    first fold under its `fun`s and `let`s — or `none` if the translation is not of that
    shape. -/
def arrayRecDepth? {Γ : Ctx} {τ : TyWf} {J : JCtx} : Term sig0 Γ τ J → Option Nat
  | .array_rec k _ _ _ _ => some k
  | .letE c body => (arrayRecDepth?.comp c).orElse fun _ => arrayRecDepth? body
  | .letJ jp body => (arrayRecDepth? body).orElse fun _ => arrayRecDepth? jp
  | _ => none

/-- `arrayRecDepth?`, in the computation a `let` binds: the body of a `fun`. -/
def arrayRecDepth?.comp {Γ : Ctx} {τ : TyWf} : Comp sig0 Γ τ → Option Nat
  | .lam b => arrayRecDepth? b
  | _ => none
end

end TermTests.ArrayRecToTerm
