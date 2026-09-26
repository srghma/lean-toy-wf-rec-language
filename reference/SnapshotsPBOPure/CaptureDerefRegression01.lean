prelude
import Init.Data.Int.Basic
import LeanScript.Term.Elab
import LeanScript.Term.Compile

-- Should be optimized out, bc its newtype
private inductive Box (α : Type) where
  | mk : α → Box α

-- all non-recursive types should be passed as just fields to functions
def test1 (v : Int × Int) (b : Int) : Int :=
  v.1 + b

def test2 (v : Int × Int) : Int → Int :=
  fun b => v.1 + b

def test3 (v : Int × Int) : Box (Int → Int) :=
  .mk (fun b => v.1 + b)

-------------------------------------
private inductive Box2 (α : Type) where
  | mk : α → α → Box2 α

-- in both test4 and test5 arguments will be unboxed and then reboxed on return.
-- Why? Bc we assume user will use actually

-- TODO: Detect The "Re-Boxing" Trap (Where Unboxing Hurts)
-- ```
-- Caller (has Boxed { _1, _2 })
--   ↳ Unpacks to call f(v_1, v_2)
--       ↳ f needs to store v in an Array or pass to a generic function
--           ↳ f must RE-BOX: const v = { _1: v_1, _2: v_2 };
-- ```

def test4 (v : Int × Int) : Box2 (Int → Int) :=
  .mk (fun b => v.1 + b) (fun b => v.2 + b)

def test5 (v : Box2 Int) : Box2 (Int → Int) :=
  .mk (fun b => v.1 + b) (fun b => v.2 + b)

-- set_option trace.compiler.ir.result true

-- Mutual Tail-Recursion Passing and Unpacking Box2
-- NOTE: even lean doesnt perform TCO for these two, so can overflow
mutual
  def testEven (n : Nat) (b : Box2 Int) : Box2 Int :=
    match n with
    | 0 => b
    | n + 1 =>
      match b with
      | .mk x y => testOdd n (.mk (y + 1) (x + 2))

  def testOdd (n : Nat) (b : Box2 Int) : Box2 Int :=
    match n with
    | 0 => b
    | n + 1 =>
      match b with
      | .mk x y => testEven n (.mk (y + 3) (x + 4))
end

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : Int × Int → Int → Int
  argTy       : (record int int)
  resTy       : (fn int int)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
  context     : -
---
info: LeanFunction test2
  signature   : Int × Int → Int → Int
  argTy       : (record int int)
  resTy       : (fn int int)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
  context     : -
---
info: LeanFunction test3
  signature   : Int × Int → Box (Int → Int)
  argTy       : (record int int)
  resTy       : (fn int int)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
  context     : -
---
info: LeanFunction test4
  signature   : Int × Int → Box2 (Int → Int)
  argTy       : (record int int)
  resTy       : (record (fn int int) (fn int int))
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
  context     : -
---
info: LeanFunction test5
  signature   : Box2 Int → Box2 (Int → Int)
  argTy       : (record int int)
  resTy       : (record (fn int int) (fn int int))
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Int.add
  context     : -
---
info: LeanFunction testEven
  signature   : Nat → Box2 Int → Box2 Int
  argTy       : nat
  resTy       : (fn (record int int) (record int int))
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  :
    Int.add
    Int.ofNat
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction testOdd
  signature   : Nat → Box2 Int → Box2 Int
  argTy       : nat
  resTy       : (fn (record int int) (record int int))
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
  compiled  test1
  compiled  test2
  compiled  test3
  compiled  test4
  compiled  test5
  compiled  testEven
  compiled  testOdd
-/
#guard_msgs in
#leanjs_compile_term_for_all
