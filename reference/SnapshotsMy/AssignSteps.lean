
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
The step of a loop the backend makes out of a tail call: the assignments are written
one after another, and a value that is *in the way* — one that a later assignment's
target still has to be read for — is bound to a `const` first
(`LakeJs.Backend.Analysis.assignStep`, `assignWithTemps`). No iteration builds the
array a destructuring assignment `[a, b] = [b, a]` would.
-/

/-- The parameters are permuted: the step needs one temporary. -/
def test1 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a
  | fuel + 1 => if b == 0 then a else test1 fuel b (a % b)

/-- A three-way rotation: two of the three values are in the way. -/
def test2 (fuel a b c : Nat) : Nat :=
  match fuel with
  | 0 => a * 100 + b * 10 + c
  | fuel + 1 => test2 fuel b c (a + 1)

/-- The values are calls, so they may not be reordered; they are bound in the order
    the call evaluates them in and the variables are assigned afterwards. -/
def test3 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a * 1000 + b
  | fuel + 1 => test3 fuel (Nat.gcd b (a + 7)) (Nat.gcd a (b + 3))

/-- Nothing is in the way here: every assignment can be written where it stands. -/
def test4 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a + b
  | fuel + 1 => test4 fuel (a + 1) (b + 2)

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.decEq
    Nat.mod
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test2
  signature   : Nat → Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat (fn nat nat)))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.mul
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test3
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.gcd
    Nat.mul
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test4
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
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

example : test1.leanFn 5 1 2 = test1 5 1 2 := by decide +kernel
example : test2.leanFn 4 1 2 3 = test2 4 1 2 3 := by decide +kernel
example : test3.leanFn 4 2 3 = test3 4 2 3 := by decide +kernel
example : test4.leanFn 4 2 3 = test4 4 2 3 := by decide +kernel
