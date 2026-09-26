
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
A program made of the loops whose compiled shape the backend's *parameter elimination*
and loop rewriting are about.

`for m in messages do IO.println m` compiles, through `List.forIn'.loop`, to a
tail-recursive function of four parameters: the state token of `IO` (erased at every
call), the list, the `Unit` the loop accumulates, and the `Unit` the body answers with.
Only the list carries anything, so the emitted function takes only the list, answers
with one shared constant, and is a `while` over the list rather than a `while (true)`
that tests and `continue`s.

`countUp` is the same thing written by hand: a tail-recursive function with a parameter
nothing reads and one that never changes.

`scripts/test-programs.sh` runs the generated program under Node and requires it to
print exactly what Lean prints, so what the snapshot pins is an *optimization*, not a
change of meaning.
-/

def messages : List String := ["one", "two", "three"]

def printAll : IO Unit := do
  for m in messages do
    IO.println m

def countUp (unused : String) (step n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => countUp unused step n (acc + step)

def countdown : Nat → Nat
  | 0     => 0
  | n + 1 => countdown n

-- def main : IO Unit := do
--   printAll
--   IO.println (toString (countUp "ignored" 2 5 0))
--   for m in messages do
--     IO.println (m ++ "!")

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction countUp
  signature   : String → Nat → Nat → Nat → Nat
  argTy       : string
  resTy       : (fn nat (fn nat (fn nat nat)))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction countdown
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  : -
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction messages
  signature   : List String
  argTy       : -                  (a constant, not a function)
  resTy       : (recTaggedUnion [] [string self])
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  : -
  context     : -
---
info: LeanFunction printAll
  signature   : IO Unit
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (not a constant type)
  primitives  :
    Char.ofNatAux
    IO.getStdout
    Nat.decLt
    Nat.pow
    String.push
    UInt32.ofBitVec
  context     :
    ok  EST.bind  [Init.System.ST]
    ok  EST.pure  [Init.System.ST]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  IO.println  [Init.System.IO]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
    ok  messages  [_current]
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
  compiled  countUp
  compiled  countdown
  compiled  messages
  refused   printAll: the type `Void IO.RealWorld` has no `Ty`: not a constant type
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

example : countdown.leanFn 12 = countdown 12 := by decide +kernel
example : countUp.leanFn "ab" 0 3 0 = countUp "ab" 0 3 0 := by decide +kernel
