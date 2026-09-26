prelude
import Init.Data.Nat.Gcd
import Init.System.IO
import LeanScript.Term.Elab
import LeanScript.Term.Compile

def gcd2 (a b : Nat) : Nat := Nat.gcd a b

def run : Nat := gcd2 48 18

-- `main` is an IO action, which the backend refuses; see the note above.
-- def main : IO Unit := IO.println run

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction gcd2
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.gcd
  context     : -
---
info: LeanFunction run
  signature   : Nat
  argTy       : -                  (a constant, not a function)
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.gcd
  context     :
    ok  gcd2  [_current]
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
  compiled  gcd2
  compiled  run
-/
#guard_msgs in
#leanjs_compile_term_for_all

/-! ## The compiled terms, run

Each line below says that the compiled term and the Lean function answer with the same
thing, and is settled by `decide +kernel`: the **kernel** reduces
`LeanScript.Term.evalClosed` applied to the generated term, so each line checks the
whole pipeline — the type translation, the compiler and the evaluator of
`LeanScript.Eval` — against Lean's own answer.  The arguments are small on purpose: the
kernel reduces the evaluator by unfolding it, which is far slower than compiled code. -/

example : gcd2.leanFn 12 18 = gcd2 12 18 := by decide +kernel
example : gcd2.leanFn 7 0 = gcd2 7 0 := by decide +kernel
