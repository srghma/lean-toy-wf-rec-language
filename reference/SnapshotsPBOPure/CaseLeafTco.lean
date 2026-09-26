
import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- partial def test1 (b : Bool) (arr : Array Int) : Array Int :=
--   let head? : Option Int := arr[0]?
--   let last? : Option Int := arr.back?
--   match head?, last? with
--   | some 1, some 2 => arr
--   | none, some y => arr.push y
--   | none, none => arr
--   | some x, none => arr.push x
--   | some x, some y =>
--     if b then
--       #[]
--     else
--       test1 b (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)

def test1Fuel : Nat → Bool → Array Int → Array Int
  | 0,     _, arr => arr
  | n + 1, b, arr =>
    match (arr[0]? : Option Int), arr.back? with
    | some 1, some 2 => arr
    | none,   some y => arr.push y
    | none,   none   => arr
    | some x, none   => arr.push x
    | some x, some y =>
      if b then
        #[]
      else
        test1Fuel n b
          (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)

def test1FuelCalled (b : Bool) (arr : Array Int) : Array Int :=
  test1Fuel 1000000 b arr

-- this approach doesnt work
--
-- def test1 (b : Bool) (arr : Array Int) (h : arr = #[]) : Array Int :=
--   let head? : Option Int := arr[0]?
--   let last? : Option Int := arr.back?
--   match head?, last? with
--   | some 1, some 2 => arr
--   | none, some y => arr.push y
--   | none, none => arr
--   | some x, none => arr.push x
--   | some x, some y =>
--     if b then
--       #[]
--     else
--       test1 b (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1Fuel
  signature   : Nat → Bool → Array Int → Array Int
  argTy       : nat
  resTy       : (fn bool (fn (array int) (array int)))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Array.get!Internal
    Array.getInternal
    Array.mk
    Array.push
    Array.size
    Int.decEq
    Int.ofNat
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.sub
  context     :
    ok  Array.append  [Init.Data.Array.Basic]
    ok  Array.back?  [Init.Data.Array.Basic]
    ok  Bool.decEq  [Init.Prelude]
    ok  Eq.ndrec_symm  [Init.Prelude]
    ok  List.toArray  [Init.Prelude]
    ok  Unit.unit  [Init.Prelude]
    ok  decidableGetElem?  [Init.GetElem]
---
info: LeanFunction test1FuelCalled
  signature   : Bool → Array Int → Array Int
  argTy       : bool
  resTy       : (fn (array int) (array int))
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.get!Internal
    Array.getInternal
    Array.mk
    Array.push
    Array.size
    Int.decEq
    Int.ofNat
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.sub
  context     :
    ok  test1Fuel  [_current]
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
  compiled  test1Fuel
  compiled  test1FuelCalled
-/
#guard_msgs in
#leanjs_compile_term_for_all

/-! ## The compiled terms, run

Each line says that the compiled term and the Lean function answer with the same thing,
and is settled by `decide +kernel`: the kernel reduces `LeanScript.Term.evalClosed`
applied to the generated term, so each line checks the type translation, the compiler
and the evaluator against Lean's own answer.  The fuel is small on purpose — the kernel
reduces the evaluator by unfolding it. -/

example : test1Fuel.leanFn 2 true #[1, 2] = test1Fuel 2 true #[1, 2] := by decide +kernel
example : test1Fuel.leanFn 1 false #[3] = test1Fuel 1 false #[3] := by decide +kernel
example : test1Fuel.leanFn 0 false #[7] = test1Fuel 0 false #[7] := by decide +kernel
