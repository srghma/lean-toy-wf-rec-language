
import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- mutual
--   partial def f (a b : Int) : Int := g (a + b)
--   partial def g (a : Int) : Int := f a (a + 1)
-- end

mutual
  def f (fuel : Nat) (a b : Int) : Int :=
    match fuel with
    | 0 => a + b
    | fuel + 1 => g fuel (a + b)

  def g (fuel : Nat) (a : Int) : Int :=
    match fuel with
    | 0 => a
    | fuel + 1 => f fuel a (a + 1)
end

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction f
  signature   : Nat → Int → Int → Int
  argTy       : nat
  resTy       : (fn int (fn int int))
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  :
    Int.add
    Int.ofNat
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction g
  signature   : Nat → Int → Int
  argTy       : nat
  resTy       : (fn int int)
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  :
    Int.add
    Int.ofNat
  context     :
    ok  Unit.unit  [Init.Prelude]
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
  compiled  f
  compiled  g
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

example : f.leanFn 5 1 2 = f 5 1 2 := by decide +kernel
example : g.leanFn 5 1 = g 5 1 := by decide +kernel
