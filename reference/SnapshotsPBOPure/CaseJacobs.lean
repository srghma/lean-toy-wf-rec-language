
import LeanScript.Term.Elab
import LeanScript.Term.Compile
inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero


def renderExpr : Expr → String
  | .add a b => "Add(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .mul a b => "Mul(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .succ a => "Succ(" ++ renderExpr a ++ ")"
  | .zero => "Zero"

instance : ToString Expr where
  toString a := renderExpr a -- will be inlined

-- #print instToStringExpr

def test1 : Expr → String
  | .add .zero .zero => "e1"
  | .mul .zero x => "e2: " ++ toString x -- though toString is used - will use renderExpr anyway, tnx to optimization
  | .add (.succ x) y => "e3: " ++ toString x ++ " " ++ toString y
  | .mul x .zero => "e4: " ++ toString x
  | .mul (.add x y) z => "e5: " ++ toString x ++ " " ++ toString y ++ " " ++ toString z
  | .add x .zero => "e6: " ++ toString x
  | x => "e7: " ++ toString x

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction renderExpr
  signature   : Expr → String
  argTy       : (recTaggedUnion [self self] [self self] [self] [])
  resTy       : string
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    String.append
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction test1
  signature   : Expr → String
  argTy       : (recTaggedUnion [self self] [self self] [self] [])
  resTy       : string
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.land
    Nat.shiftRight
    String.append
  context     :
    ok  Expr.ctorIdx  [_current]
    ok  Unit.unit  [Init.Prelude]
    ok  renderExpr  [_current]
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
  compiled  renderExpr  (no leanFn: its Lean type is not the denotation of its Ty)
  compiled  test1  (no leanFn: its Lean type is not the denotation of its Ty)
-/
#guard_msgs in
#leanjs_compile_term_for_all
