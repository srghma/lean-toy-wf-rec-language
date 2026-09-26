import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- Without the proof this function triples n at every step and diverges for every
-- input.  With h : Safe n the else-branch is dead code: omega derives False from
-- h (which unfolds to n = 1) and hn (n ≠ 1), so the impossible recursive call
-- `boom (3 * n)` never executes and Lean still accepts the termination proof.

/-- Only n = 1 is a safe starting point; every other value diverges. -/
def Safe (n : Nat) : Prop := n = 1

/-- Triples its argument at every step — obviously diverges for n ≠ 1.
    The proof `h : Safe n` rules out all other inputs:
    the else-branch is unreachable, proven by contradiction. -/
def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then
    0                              -- the one terminating case
  else
    boom (3 * n)                   -- blatant divergence: 1 → 3 → 9 → 27 → …
      (by simp [Safe] at h; omega) -- h : n = 1, hn : n ≠ 1 ⊢ False → anything
termination_by n
decreasing_by
  simp [Safe] at h  -- h : n = 1
  omega             -- n = 1 ∧ n ≠ 1 ⊢ False ⊢ 3 * n < n

example : boom 1 (by simp [Safe]) = 0 := by grind only [boom]


/-!
## The `LeanFunction` reports as an earlier iteration wrote them

The block below is kept exactly as it was written, but commented out.  Its expectations
were produced by an earlier iteration of `#leanjs_generate_term_and_ctx_for` and name
the constructors that iteration used (`Term.wfFix`, `Term.natRec`, …).  In this tree the
term language is `LeanScript.Expr`, whose one well-founded node is `Term.fixAcc` and
whose structural recursion is the datatype's own recursor, and the report says so — see
the live, checked report at the end of this file.
-/

/-
/-! ## Generated `LeanFunction`s

One report per public function of this file; see `LeanScript.Term.Elab`. -/

/--
info: LeanFunction boom
  signature   : (n : Nat) → Safe n → Nat
  argTy       : nat
  resTy       : nat
  recursion   : well-founded       (encoded as Term.wfFix: relation and Acc proof sealed inside)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for boom

-/

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction Safe
  signature   : Nat → Prop
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     : -
---
info: LeanFunction boom
  signature   : (n : Nat) → Safe n → Nat
  argTy       : nat
  resTy       : nat
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.decEq
    Nat.mul
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for_all

/-! ## The compiled terms

`#leanjs_compile_term_for_all` compiles every public function of this file into a
`LeanScript.Expr.Term`, bound to `<f>.leanTerm`, and `<f>.leanFn` is that term run by
`LeanScript.Term.evalClosed`.  The report says which functions were compiled and, for
the ones that were refused, why. -/

/--
info: LeanTerms of this module
  compiled  boom
-/
#guard_msgs in
#leanjs_compile_term_for_all

/-! ## The compiled term, run

`boom` is a well-founded definition, and Lean's own well-founded recursion does **not**
reduce in the kernel — its accessibility proof is a theorem — so the compiled term is
reduced to the literal, which `boom 1` is shown to equal above. -/

example : boom.leanFn 1 = 0 := by decide +kernel
