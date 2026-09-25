import LeanScript.Term.Elab
import LeanScript.Term.Compile
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def ack999 := ack 999 1 -- XXX: DONT TRY TO EVALUATE!!! only build Term

-- def ackRev : Nat → Nat → Nat
--   | n,     0     => n + 1
--   | 0,     m + 1 => ackRev 1 m
--   | n + 1, m + 1 => ackRev (ackRev n (m + 1)) m
-- termination_by n m => (m, n)
-- decreasing_by all_goals omega

-- Inner recursion: structurally recursive on `n`
private def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)
-- Outer recursion: structurally recursive on `m`
def ack2 : Nat → (Nat → Nat)
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack2 m)

def ackWhile (m n : Nat) : Nat := Id.run do
  let mut stack : List Nat := [m]
  let mut curN : Nat := n
  while !stack.isEmpty do
    match stack with
    | [] => break
    | top :: rest =>
      stack := rest
      if top == 0 then
        -- A(0, n) = n + 1
        curN := curN + 1
      else if curN == 0 then
        -- A(m, 0) = A(m - 1, 1)
        stack := (top - 1) :: stack
        curN := 1
      else
        -- A(m, n) = A(m - 1, A(m, n - 1))
        stack := (top - 1) :: top :: stack
        curN := curN - 1
  return curN

-- #eval ackWhile 2 2  -- 7
-- #eval ackWhile 3 2  -- 29
-- #eval ackWhile 3 3  -- 61

namespace AckWithoutStackButUsingCantorPairing

-- Cantor pairing function: encodes two Nats into one Nat
def pair (x y : Nat) : Nat :=
  ((x + y) * (x + y + 1)) / 2 + y

-- Integer square root helper to invert Cantor pairing
def isqrt (n : Nat) : Nat := Id.run do
  let mut x := n
  let mut y := (x + 1) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

-- Decode the first element from a Cantor pair
def unpairLeft (z : Nat) : Nat :=
  let w := (isqrt (8 * z + 1) - 1) / 2
  let t := (w * (w + 1)) / 2
  let y := z - t
  w - y

-- Decode the second element from a Cantor pair
def unpairRight (z : Nat) : Nat :=
  let w := (isqrt (8 * z + 1) - 1) / 2
  let t := (w * (w + 1)) / 2
  z - t

-- Ackermann using ONLY a while loop and Nat variables:
def ackNoDataStructure (m n : Nat) : Nat := Id.run do
  -- 0 represents the empty stack.
  -- A non-empty stack is represented as pair(top, rest) + 1
  let mut s : Nat := pair m 0 + 1
  let mut curN : Nat := n

  while s != 0 do
    let code := s - 1
    let top := unpairLeft code
    s := unpairRight code

    if top == 0 then
      curN := curN + 1
    else if curN == 0 then
      -- Push top - 1
      s := pair (top - 1) s + 1
      curN := 1
    else
      -- Push top - 1, then push top
      s := pair (top - 1) s + 1
      s := pair top s + 1
      curN := curN - 1

  return curN

-- #eval ackNoDataStructure 2 2  -- 7
-- #eval ackNoDataStructure 3 2  -- 29

end AckWithoutStackButUsingCantorPairing

-- Equivalence theorem: ack2 m n = ack m n
theorem ack2_eq_ack (m n : Nat) : ack2 m n = ack m n := by
  induction m, n using ack.induct with
  | case1 n =>
    -- ack 0 n = n + 1
    simp [ack2, ack]
  | case2 m ih =>
    -- ack (m + 1) 0 = ack m 1
    -- ack2 (m + 1) 0 = ackInner (ack2 m) 0 = ack2 m 1
    have h : ack2 (m + 1) 0 = ack2 m 1 := by rfl
    rw [h, ih]
    simp [ack]
  | case3 m n ih1 ih2 =>
    -- ack (m + 1) (n + 1) = ack m (ack (m + 1) n)
    -- ack2 (m + 1) (n + 1) = ack2 m (ack2 (m + 1) n)
    have h : ack2 (m + 1) (n + 1) = ack2 m (ack2 (m + 1) n) := by rfl
    grind [= ack, = ack2]


/-!
## The `LeanFunction` reports as an earlier iteration wrote them

The block below is kept exactly as it was written, but commented out.  Its expectations
were produced by an earlier iteration of `#leanjs_generate_term_and_ctx_for` and name
the constructors that iteration used (`Term.wfFix`, `Term.natRec`, …).  In this tree the
term language is `LeanScript.Expr`, whose one well-founded node is `Term.fixAcc` and
whose structural recursion is the datatype's own recursor, and the report says so — see
the live, checked report at the end of this file.
-/

/-
/-! ## Generated `LeanFunction`s

One report per public function of this file; see `LeanScript.Term.Elab`. -/

/--
info: LeanFunction ack
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : well-founded       (encoded as Term.wfFix: relation and Acc proof sealed inside)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for ack

/--
info: LeanFunction ack999
  signature   : Nat
  argTy       : -                  (a constant, not a function)
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  : -
  context     :
    ok  ack  [_current]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for ack999

/--
info: LeanFunction ack2
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : structural         (encoded as Term.natRec / Term.listRec)
  status      : representable in Term
  primitives  : -
  context     :
    ok  _private.SnapshotsMy.TcoAck.0.ackInner  [_current]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for ack2

/--
info: LeanFunction ackWhile
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : partial fixpoint   NOT REPRESENTABLE in Term
  status      : rejected
  primitives  : -
  context     :
    ok  Bool.not  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.isEmpty  [Init.Data.List.Basic]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for ackWhile

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.pair
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for AckWithoutStackButUsingCantorPairing.pair

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.isqrt
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : partial fixpoint   NOT REPRESENTABLE in Term
  status      : rejected
  primitives  :
    Nat.decLt
  context     :
    ok  Id.run  [Init.Control.Id]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for AckWithoutStackButUsingCantorPairing.isqrt

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.unpairLeft
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.decLt
  context     :
    BAD AckWithoutStackButUsingCantorPairing.isqrt  [_current]
    ok  Id.run  [Init.Control.Id]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for AckWithoutStackButUsingCantorPairing.unpairLeft

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.unpairRight
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.decLt
  context     :
    BAD AckWithoutStackButUsingCantorPairing.isqrt  [_current]
    ok  Id.run  [Init.Control.Id]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for AckWithoutStackButUsingCantorPairing.unpairRight

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.ackNoDataStructure
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : partial fixpoint   NOT REPRESENTABLE in Term
  status      : rejected
  primitives  :
    Nat.decLt
  context     :
    BAD AckWithoutStackButUsingCantorPairing.isqrt  [_current]
    ok  AckWithoutStackButUsingCantorPairing.pair  [_current]
    ok  AckWithoutStackButUsingCantorPairing.unpairLeft  [_current]
    ok  AckWithoutStackButUsingCantorPairing.unpairRight  [_current]
    ok  Bool.not  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  bne  [Init.Core]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for AckWithoutStackButUsingCantorPairing.ackNoDataStructure

-/

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction AckWithoutStackButUsingCantorPairing.ackNoDataStructure
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decEq
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
  context     :
    ok  AckWithoutStackButUsingCantorPairing.pair  [_current]
    BAD AckWithoutStackButUsingCantorPairing.unpairLeft  [_current]
    BAD AckWithoutStackButUsingCantorPairing.unpairRight  [_current]
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    BAD Lean.Loop.forIn  [Init.While]
    ok  Unit.unit  [Init.Prelude]
    ok  bne  [Init.Core]
---
info: LeanFunction AckWithoutStackButUsingCantorPairing.isqrt
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decLt
    Nat.div
  context     :
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    BAD Lean.Loop.forIn  [Init.While]
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction AckWithoutStackButUsingCantorPairing.pair
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.div
    Nat.mul
  context     : -
---
info: LeanFunction AckWithoutStackButUsingCantorPairing.unpairLeft
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
  context     :
    BAD AckWithoutStackButUsingCantorPairing.isqrt  [_current]
---
info: LeanFunction AckWithoutStackButUsingCantorPairing.unpairRight
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
  context     :
    BAD AckWithoutStackButUsingCantorPairing.isqrt  [_current]
---
info: LeanFunction ack
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.add
  context     : -
---
info: LeanFunction ack2
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction ack999
  signature   : Nat
  argTy       : -                  (a constant, not a function)
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  ack  [_current]
---
info: LeanFunction ackWhile
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decEq
    Nat.sub
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Bool.not  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    BAD Lean.Loop.forIn  [Init.While]
    ok  List.isEmpty  [Init.Data.List.Basic]
    ok  Unit.unit  [Init.Prelude]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for_all

/-! ## The compiled terms

`#leanjs_compile_term_for_all` compiles every public function of this file into a
`LeanScript.Expr.Term`, bound to `<f>.leanTerm`, and `<f>.leanFn` is that term run by
`LeanScript.Term.evalClosed`.  The report says which functions were compiled and, for
the ones that were refused, why. -/

-- The measure of this recursion is not one of its arguments, so it is given to the
-- compiler: `LeanScript.Term.Compile` descends in `<` on a `Nat`, or lexicographically
-- on a pair of them.
#leanjs_compile_term_for ack measure fun m n => (m, n)

/--
info: LeanTerms of this module
  refused   AckWithoutStackButUsingCantorPairing.ackNoDataStructure: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  refused   AckWithoutStackButUsingCantorPairing.isqrt: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  compiled  AckWithoutStackButUsingCantorPairing.pair
  refused   AckWithoutStackButUsingCantorPairing.unpairLeft: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  refused   AckWithoutStackButUsingCantorPairing.unpairRight: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  compiled  ack  (above, with a measure of its own)
  compiled  ack2
  compiled  ack999
  refused   ackWhile: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
-/
#guard_msgs in
#leanjs_compile_term_for_all

/-! ## The compiled terms, run

Each line below says that the compiled term and the Lean function answer with the same
thing, and is settled by `decide +kernel`: the **kernel** reduces
`LeanScript.Term.evalClosed` applied to the generated term, so each line checks the
whole pipeline — the type translation, the compiler and the evaluator of
`LeanScript.Eval` — against Lean's own answer.  The arguments are small on purpose: the
kernel reduces the evaluator by unfolding it, which is far slower than compiled code.

`ack` is a well-founded definition, and Lean's own well-founded recursion does **not**
reduce in the kernel — its accessibility proof is a theorem — so the compiled term is
reduced to the literal and the Lean function is shown to equal the same literal by its
own unfolding lemmas. -/

example : ack.leanFn 2 2 = 7 := by decide +kernel
example : ack 2 2 = 7 := by simp [ack]
example : ack2.leanFn 2 2 = ack2 2 2 := by decide +kernel
example : AckWithoutStackButUsingCantorPairing.pair.leanFn 3 4
    = AckWithoutStackButUsingCantorPairing.pair 3 4 := by decide +kernel
