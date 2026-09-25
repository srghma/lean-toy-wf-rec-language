import Aesop
import LeanScript.Term.Elab
import LeanScript.Term.Compile

-- 1. Original recursive definition
def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

-- Base value for each operation level at b = 0
def hyperBase : Nat → Nat → Nat
  | 0,     _ => 1
  | 1,     a => a
  | 2,     _ => 0
  | _ + 3, _ => 1

-- 2. Tail-recursive loop helper: applies `f` to `acc`, `b` times.
-- Automatically verified terminating structurally on `b`.
def hyperLoop (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | b + 1, acc => hyperLoop f b (f acc)

-- 2. Staged TCO evaluator: structurally recursive on `n`.
def hyperTCO : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a)

-- 3. Imperative evaluator using a stateful loop over level n
def hyperWhile : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => Id.run do
    let mut acc := hyperBase (n + 1) a
    for _ in [0:b] do
      acc := hyperWhile n a acc
    return acc

-------------------------------------------------------------------------------
-- Verification / Proofs
-------------------------------------------------------------------------------

-- Key property of `hyperLoop`: pulling `f` outside the loop
theorem hyperLoop_step (f : Nat → Nat) (b acc : Nat) :
    hyperLoop f (b + 1) acc = f (hyperLoop f b acc) := by
  induction b generalizing acc with
  | zero => rfl
  | succ b ih => exact ih (f acc)

-- Base values match at b = 0
theorem hyperBase_eq (n a : Nat) : hyperBase (n + 1) a = hyper (n + 1) a 0 := by
  cases n with
  | zero => simp [hyperBase, hyper]
  | succ n =>
    cases n with
    | zero => simp [hyperBase, hyper]
    | succ n => simp [hyperBase, hyper]

-- Main equivalence theorem: hyperTCO n a b = hyper n a b
theorem hyperTCO_eq : ∀ n a b, hyperTCO n a b = hyper n a b := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp [hyperTCO, hyper]
  | succ n ih =>
    intro a b
    have hfun : hyperTCO n a = hyper n a := funext fun x => ih a x
    have hbase : hyperBase (n + 1) a = hyper (n + 1) a 0 := hyperBase_eq n a
    have hloop : ∀ b, hyperLoop (hyper n a) b (hyper (n + 1) a 0) = hyper (n + 1) a b := by
      intro b
      induction b with
      | zero => rfl
      | succ b ihb =>
        rw [hyperLoop_step, ihb]
        simp [hyper]
    show hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a) = hyper (n + 1) a b
    rw [hfun, hbase, hloop]

-------------------------------------------------------------------------------
-- Sanity Checks
-------------------------------------------------------------------------------

-- #eval hyper 3 2 4      -- 2^4 = 16
-- #eval hyperTCO 3 2 4   -- 16
-- #eval hyperWhile 3 2 4 -- 16


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
info: LeanFunction hyper
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : well-founded       (encoded as Term.wfFix: relation and Acc proof sealed inside)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for hyper

/--
info: LeanFunction hyperBase
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for hyperBase

/--
info: LeanFunction hyperLoop
  signature   : (Nat → Nat) → Nat → Nat → Nat
  argTy       : (fn nat nat)
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded as Term.natRec / Term.listRec)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for hyperLoop

/--
info: LeanFunction hyperTCO
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded as Term.natRec / Term.listRec)
  status      : representable in Term
  primitives  : -
  context     :
    ok  hyperBase  [_current]
    ok  hyperLoop  [_current]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for hyperTCO

/--
info: LeanFunction hyperWhile
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded as Term.natRec / Term.listRec)
  status      : representable in Term
  primitives  : -
  context     :
    ok  Id.run  [Init.Control.Id]
    ok  hyperBase  [_current]
    ok  inferInstance  [Init.Prelude]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for hyperWhile

-/

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction hyper
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.add
  context     : -
---
info: LeanFunction hyperBase
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  : -
  context     : -
---
info: LeanFunction hyperLoop
  signature   : (Nat → Nat) → Nat → Nat → Nat
  argTy       : (fn nat nat)
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  : -
  context     : -
---
info: LeanFunction hyperTCO
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : representable in Term
  primitives  :
    Nat.add
  context     :
    ok  hyperBase  [_current]
    ok  hyperLoop  [_current]
---
info: LeanFunction hyperWhile
  signature   : Nat → Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat (fn nat nat))
  recursion   : structural         (encoded with the recursor of the datatype)
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
    ok  hyperBase  [_current]
    ok  inferInstance  [Init.Prelude]
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
#leanjs_compile_term_for hyper measure fun n _a b => (n, b)

/--
info: LeanTerms of this module
  compiled  hyper  (above, with a measure of its own)
  compiled  hyperBase
  compiled  hyperLoop
  compiled  hyperTCO
  refused   hyperWhile: the type `Type u_1 → Type u_2` has no `Ty`: a type or a proposition, which carries no value
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

example : hyperBase.leanFn 2 3 = hyperBase 2 3 := by decide +kernel
example : hyperTCO.leanFn 2 2 2 = hyperTCO 2 2 2 := by decide +kernel
example : hyperLoop.leanFn (fun x => x + 1) 3 2 = hyperLoop (fun x => x + 1) 3 2 := by
  decide +kernel
