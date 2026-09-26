
import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- @js_export: ExprF, Add, Lit, Mul, functorExprF, test1, test2
inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α
  | Mul : α → α → ExprF α

def mapExprF {α β : Type} (f : α → β) : ExprF α → ExprF β
  | .Lit n   => .Lit n
  | .Add a b => .Add (f a) (f b)
  | .Mul a b => .Mul (f a) (f b)

instance : Functor ExprF where
  map := mapExprF

structure FixExpr where
  unFix : ExprF FixExpr

-- Total, non-partial cata using mutual recursion
mutual
  def cata {α : Type} (alg : ExprF α → α) : FixExpr → α
    | ⟨f⟩ => alg (cataMap alg f)

  def cataMap {α : Type} (alg : ExprF α → α) : ExprF FixExpr → ExprF α
    | .Lit n   => .Lit n
    | .Add a b => .Add (cata alg a) (cata alg b)
    | .Mul a b => .Mul (cata alg a) (cata alg b)
end

def eval : ExprF Int → Int
  | .Lit n   => n
  | .Add a b => a + b
  | .Mul a b => a * b

def bump : ExprF Int → ExprF Int
  | .Lit n => .Lit (n + 1)
  | other  => other

def test1 (e : FixExpr) : Int :=
  cata eval e

def test2 (e : FixExpr) : Int :=
  cata (eval ∘ bump) e

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction bump
  signature   : ExprF Int → ExprF Int
  argTy       : (taggedUnion [int] [int int] [int int])
  resTy       : (taggedUnion [int] [int int] [int int])
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
    Int.ofNat
    Nat.land
    Nat.shiftRight
  context     :
    ok  ExprF.ctorIdx  [_current]
---
info: LeanFunction cata
  signature   : {α : Type} → (ExprF α → α) → FixExpr → α
  argTy       : -
  resTy       : -
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     : -
---
info: LeanFunction cataMap
  signature   : {α : Type} → (ExprF α → α) → ExprF FixExpr → ExprF α
  argTy       : -
  resTy       : -
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     :
    ok  FixExpr.brecOn_1  [_current]
---
info: LeanFunction eval
  signature   : ExprF Int → Int
  argTy       : (taggedUnion [int] [int int] [int int])
  resTy       : int
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
    Int.mul
  context     : -
---
info: LeanFunction mapExprF
  signature   : {α β : Type} → (α → β) → ExprF α → ExprF β
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     : -
---
info: LeanFunction test1
  signature   : FixExpr → Int
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (nested too deeply)
  primitives  :
    Int.add
    Int.mul
  context     :
    ok  cata  [_current]
    ok  eval  [_current]
---
info: LeanFunction test2
  signature   : FixExpr → Int
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (nested too deeply)
  primitives  :
    Int.add
    Int.mul
    Int.ofNat
    Nat.land
    Nat.shiftRight
  context     :
    ok  Function.comp  [Init.Prelude]
    ok  bump  [_current]
    ok  cata  [_current]
    ok  eval  [_current]
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
  compiled  bump  (no leanFn: its Lean type is not the denotation of its Ty)
  refused   cata: the type `ExprF α → α` has no `Ty`: not a constant type
  refused   cataMap: the type `ExprF α → α` has no `Ty`: not a constant type
  compiled  eval  (no leanFn: its Lean type is not the denotation of its Ty)
  refused   mapExprF: the type `α → β` has no `Ty`: not a constant type
  refused   test1: the type `FixExpr` has no `Ty`: nested too deeply
  refused   test2: the type `FixExpr` has no `Ty`: nested too deeply
-/
#guard_msgs in
#leanjs_compile_term_for_all
