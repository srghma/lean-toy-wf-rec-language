module

public import LeanScript.Eval

@[expose] public section

/-!
# A recursion that descends more than one step, written and translated

`LeanScript.Term.nat_rec k` is the fold of a natural number that descends `k + 1` steps.
Its base values are the answers at `k, …, 1, 0` — **nearest first** — and its branch, at
`n + k + 1`, binds `n` (de Bruijn index `0`) and then the answers at `n + k, …, n + 1, n`
(indices `1 … k + 1`).  The depth defaults to `0`, at which the node is `Nat.rec` with a
non-dependent motive.

These files check the node from both ends:

* **proved** (`TermTests/NatRecDepthTest/Written.lean`).  `fibTerm` is `fib` as a
  term of the grammar, at depth two (translated, and checked against the term written
  out), and `fibTerm_eval` proves that its value is `fib n`
  at **every** `n` — by the two equations of `LeanScript.NatRecFacts`, not by testing.
* **translated** (one file per program, so that they build in parallel).  Each of the
  Fibonacci programs of the request is handed to `#leanscript_to_term` as it is written,
  and the kernel checks the value of the term it produces: the two-step `fib`, the
  tail-recursive loop, the pair recursion, the `for` loop over a range, and the
  tribonacci … hexanacci numbers, which descend three to six steps.  The one program
  that is refused is `fibFast`, whose recursive call is at `n / 2`: that is not a
  descent by a fixed number of steps, and no fold of this kind can express it.
-/

namespace TermTests.NatRecDepth

open LeanScript

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`: arithmetic is external to
    the language, so every one of these programs calls it. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd` (scoped, so it is available in every file that
    opens `TermTests.NatRecDepth`). -/
scoped macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

end TermTests.NatRecDepth

end
