
import LeanScript.Term.Elab
import LeanScript.Term.Compile
mutual
def go (n : Nat) : Nat :=
  if h1 : n = 0 then n
  else if h2 : n ≤ 100 then go (n - 1)
  else k (n - 1) (by omega)
termination_by n
decreasing_by all_goals omega

def k (m : Nat) (h : m ≥ 100) : Nat :=
  if h1 : m = 100 then go (m - 1)
  else if h2 : m = 900 then 42
  else k (m - 1) (by omega)
termination_by m
decreasing_by all_goals omega
end

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction go
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Nat.decEq
    Nat.decLe
    Nat.sub
  context     : -
---
info: LeanFunction k
  signature   : (m : Nat) → m ≥ 100 → Nat
  argTy       : nat
  resTy       : nat
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Nat.decEq
    Nat.decLe
    Nat.sub
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
  compiled  go
  compiled  k
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

example : go.leanFn 40 = go 40 := by decide +kernel
example : k.leanFn 103 = k 103 (by omega) := by decide +kernel
