
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
Scalar replacement of a constructor a helper is only ever handed
(`LakeJs.Backend.ScalarRepl`): a parameter every caller builds for the call and that
the callee only projects becomes that constructor's *fields*, so nothing is allocated
at the call and nothing is loaded out of it in the loop. What is left is then finished
by the parameter plan (`LakeJs.Backend.ParamElim`): a field nothing reads goes, and one
every caller passes the same literal in becomes that literal.

The cases that must *not* be split are here too: a value the callee answers with, one
that is handed on to something the analysis cannot see through, and a parameter whose
callers do not agree on one constructor.
-/

/-- A counted loop: the `Std.Range` is built at the call and only projected in the
    loop, so the loop takes its fields — and its step is `1`. -/
def test1 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

/-- Two loops, one inside the other. -/
def test2 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    for j in [0:i] do
      s := s + j
  return s

/-- A helper that only takes its argument apart: the pair is not built. -/
@[noinline] private def dist (p : Nat × Nat) : Nat :=
  if p.1 < p.2 then p.2 - p.1 else p.1 - p.2

def test3 (a b : Nat) : Nat := dist (a, b) + dist (b, a + 1)

/-- A helper that answers *with* what it is given: the pair escapes, so it stays a
    pair. -/
@[noinline] private def bigger (p : Nat × Nat) : Nat × Nat :=
  if p.1 < p.2 then p else (p.2, p.1)

def test4 (a b : Nat) : Nat × Nat := bigger (a, b)

/-- A helper whose callers do not agree on one constructor: it is handed a `some` at
    one call site and a `none` at another, so its parameter stays what it is. -/
@[noinline] private def sumOpt (o : Option (Nat × Nat)) : Nat :=
  match o with
  | some (a, b) => a + b
  | none => 0

def test5 (a b : Nat) : Nat := sumOpt (some (a, b)) + sumOpt none

/-- A recursion that carries a structure it only reads: the fields travel through the
    recursive call instead of the object. -/
private structure Bounds where
  lo : Nat
  hi : Nat

@[noinline] private def clampSum (b : Bounds) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => clampSum b n (acc + (if n < b.lo then b.lo else if b.hi < n then b.hi else n))

def test6 (n : Nat) : Nat := clampSum ⟨n % 3, n % 7 + 3⟩ n 0

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.emptyWithCapacity
    Array.push
    Nat.add
    Nat.decLt
    Nat.mod
    Nat.sub
  context     :
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  Std.Legacy.Range.forIn'  [Init.Data.Range.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test2
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.emptyWithCapacity
    Array.push
    Nat.add
    Nat.decLt
    Nat.mod
    Nat.sub
  context     :
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  Std.Legacy.Range.forIn'  [Init.Data.Range.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test3
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.sub
  context     : -
---
info: LeanFunction test4
  signature   : Nat → Nat → Nat × Nat
  argTy       : nat
  resTy       : (fn nat (record nat nat))
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.decLt
  context     : -
---
info: LeanFunction test5
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test6
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.mod
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
  refused   test1: the type `Type u_1 → Type u_2` has no `Ty`: a type or a proposition, which carries no value
  refused   test2: the type `Type u_1 → Type u_2` has no `Ty`: a type or a proposition, which carries no value
  compiled  test3
  compiled  test4
  compiled  test5
  compiled  test6
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

example : test3.leanFn 3 8 = test3 3 8 := by decide +kernel
example : test5.leanFn 3 8 = test5 3 8 := by decide +kernel
example : test6.leanFn 9 = test6 9 := by decide +kernel
