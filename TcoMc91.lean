import Aesop
import LeanScript.Term.Elab
import LeanScript.Term.Compile

-- ============================================================================
-- 1. Reference Specification
-- ============================================================================

def mc91 (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    91

-- Closed-form characterization of McCarthy 91
theorem mc91_spec (n : Nat) : mc91 n = if n > 100 then n - 10 else 91 := by
  rfl

-- ============================================================================
-- 2. Tail-Recursive Implementation
-- ============================================================================

-- Tail-recursive loop helper:
-- `c` is the number of pending calls to evaluate.
-- When c = 0, all calls have completed.
def mc91Loop : Nat → Nat → Nat
  | 0,     n => n
  | c + 1, n =>
    if h : n > 100 then
      mc91Loop c (n - 10)
    else
      mc91Loop (c + 1 + 1) (n + 11)
termination_by c n => 2 * (111 - n) + 21 * c
decreasing_by
  all_goals omega

-- Tail-recursive entry point (starts with 1 pending call)
def mc91TR (n : Nat) : Nat :=
  mc91Loop 1 n

-- ============================================================================
-- 3. While-loop / Imperative Implementation
-- ============================================================================

def mc91While (n : Nat) : Nat := Id.run do
  let mut c : Nat := 1
  let mut cur : Nat := n

  while c != 0 do
    if cur > 100 then
      cur := cur - 10
      c := c - 1
    else
      cur := cur + 11
      c := c + 1

  return cur

-- ============================================================================
-- 4. Equivalence Proof: mc91TR n = mc91 n
-- ============================================================================

-- Simple function iteration helper without Mathlib
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | c + 1, x => iter f c (f x)

-- Step 1: Characterize single step when n > 100
theorem mc91_step_gt {n : Nat} (h : n > 100) : mc91 n = n - 10 := by
  unfold mc91
  split
  · rfl
  · omega

-- Step 2: Characterize nested double-step when n ≤ 100
-- `repeat (first | split | omega)` safely splits ifs and closes arithmetic leaves
theorem mc91_step_le {n : Nat} (h : n ≤ 100) : mc91 (mc91 (n + 11)) = mc91 n := by
  unfold mc91
  repeat (first | split | omega)

-- Step 3: Loop invariant for arbitrary pending call count `c`
theorem mc91Loop_eq (c n : Nat) : mc91Loop c n = iter mc91 c n := by
  induction c, n using mc91Loop.induct with
  | case1 n =>
    grind => instantiate only [mc91Loop, iter]
  | case2 c n hgt ih =>
    unfold mc91Loop
    split
    · rw [ih, ← mc91_step_gt hgt]
      rfl
    · omega
  | case3 c n hle ih =>
    unfold mc91Loop
    split
    · omega
    · rw [ih]
      dsimp [iter]
      simp_all only [gt_iff_lt, not_false_eq_true, Nat.not_lt]
      grind [= iter, = mc91]

-- Main Theorem: mc91TR n = mc91 n
theorem mc91TR_eq_mc91 (n : Nat) : mc91TR n = mc91 n := by
  unfold mc91TR
  rw [mc91Loop_eq 1 n]
  rfl

-- ============================================================================
-- Sanity Checks
-- ============================================================================

-- #eval mc91TR 99     -- 91
-- #eval mc91While 99  -- 91
-- #eval mc91TR 105    -- 95
-- #eval mc91While 105 -- 95


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
info: LeanFunction mc91
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.decLt
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for mc91

/--
info: LeanFunction mc91Loop
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : well-founded       (encoded as Term.wfFix: relation and Acc proof sealed inside)
  status      : representable in Term
  primitives  :
    Nat.decLt
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for mc91Loop

/--
info: LeanFunction mc91TR
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.decLt
  context     :
    ok  mc91Loop  [_current]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for mc91TR

/--
info: LeanFunction mc91While
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : partial fixpoint   NOT REPRESENTABLE in Term
  status      : rejected
  primitives  :
    Nat.decLt
  context     :
    ok  Bool.not  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  bne  [Init.Core]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for mc91While

/--
info: LeanFunction iter
  signature   : (Nat → Nat) → Nat → Nat → Nat
  argTy       : (fn nat nat)
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded as Term.natRec / Term.listRec)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for iter

-/

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction iter
  signature   : (Nat → Nat) → Nat → Nat → Nat
  argTy       : (fn nat nat)
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  : -
  context     : -
---
info: LeanFunction mc91
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.decLt
    Nat.sub
  context     : -
---
info: LeanFunction mc91Loop
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.mul
    Nat.sub
  context     : -
---
info: LeanFunction mc91TR
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.mul
    Nat.sub
  context     :
    ok  mc91Loop  [_current]
---
info: LeanFunction mc91While
  signature   : Nat → Nat
  argTy       : nat
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : rejected           (a definition it calls is not representable)
  primitives  :
    Nat.add
    Nat.decEq
    Nat.decLt
    Nat.sub
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    BAD Lean.Loop.forIn  [Init.While]
    ok  Unit.unit  [Init.Prelude]
    ok  bne  [Init.Core]
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
#leanjs_compile_term_for mc91Loop measure fun c n => 2 * (111 - n) + 21 * c

/--
info: LeanTerms of this module
  compiled  iter
  compiled  mc91
  compiled  mc91Loop  (above, with a measure of its own)
  compiled  mc91TR
  refused   mc91While: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
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

example : mc91.leanFn 99 = mc91 99 := by decide +kernel
example : mc91TR.leanFn 99 = mc91TR 99 := by decide +kernel
example : mc91Loop.leanFn 1 99 = mc91Loop 1 99 := by decide +kernel
example : iter.leanFn (fun x => x + 2) 3 1 = iter (fun x => x + 2) 3 1 := by decide +kernel
