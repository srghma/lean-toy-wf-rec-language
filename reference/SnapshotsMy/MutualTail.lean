
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
Mutually tail-recursive functions: each of these calls the next in tail position, so
none of them may grow the JavaScript stack. The group is compiled into a single
function with a dispatch loop (`_mut$…`), and each member keeps a declaration of its
own that enters it with the member's tag.

`test1`/`test2` are a two-member group of one argument each; `test3`/`test4`/`test5`
are a three-member group of *different* arities, so the merged function takes as many
arguments as the widest member.
-/

mutual

def test1 : Nat → Bool
  | 0 => true
  | n + 1 => test2 n

def test2 : Nat → Bool
  | 0 => false
  | n + 1 => test1 n

end

mutual

def test3 (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test4 n (acc + 1) 2

def test4 (n acc k : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test5 n (acc + k)

def test5 (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test3 n (acc + 3)

end

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : Nat → Bool
  argTy       : nat
  resTy       : bool
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  : -
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test2
  signature   : Nat → Bool
  argTy       : nat
  resTy       : bool
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  : -
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test3
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test4
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test5
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Nat.add
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
  compiled  test1
  compiled  test2
  compiled  test3
  compiled  test4
  compiled  test5
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

example : test1.leanFn 7 = test1 7 := by decide +kernel
example : test2.leanFn 7 = test2 7 := by decide +kernel
example : test3.leanFn 9 0 = test3 9 0 := by decide +kernel
example : test4.leanFn 7 1 5 = test4 7 1 5 := by decide +kernel
example : test5.leanFn 8 2 = test5 8 2 := by decide +kernel
