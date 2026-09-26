
import LeanScript.Term.Elab
import LeanScript.Term.Compile
def span (p : Int → Bool) (arr : Array Int) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then go (i + 1) else some i
    else
      none
  go 0

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction span
  signature   : (Int → Bool) → Array Int → Option Nat
  argTy       : (fn int bool)
  resTy       : (fn (array int) (taggedUnion [] [nat]))
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.size
    Nat.add
    Nat.decLt
    Nat.sub
  context     :
    ok  span.go  [_current]
---
info: LeanFunction span.go
  signature   : (Int → Bool) → Array Int → Nat → Option Nat
  argTy       : (fn int bool)
  resTy       : (fn (array int) (fn nat (taggedUnion [] [nat])))
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.size
    Nat.add
    Nat.decLt
    Nat.sub
  context     :
    ok  Bool.decEq  [Init.Prelude]
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
  compiled  span  (no leanFn: its Lean type is not the denotation of its Ty)
  compiled  span.go  (no leanFn: its Lean type is not the denotation of its Ty)
-/
#guard_msgs in
#leanjs_compile_term_for_all
