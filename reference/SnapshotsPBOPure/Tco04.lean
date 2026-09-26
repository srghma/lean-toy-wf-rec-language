
import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- mutual
--   def test1 (n : Nat) : Nat :=
--     if n ≤ 1 then n else test2 (n - 1)

--   def test2 (m : Nat) : Nat :=
--     if m ≤ 2 then m else test1 (m - 2)
-- end

def Valid1 (n : Int) : Prop := n ≥ 1 ∧ (n % 3 = 0 ∨ n % 3 = 1)
def Valid2 (m : Int) : Prop := m ≥ 2 ∧ (m % 3 = 0 ∨ m % 3 = 2)

theorem test1_step {n : Int} (h : Valid1 n) (hn : n ≠ 1) : Valid2 (n - 1) := by
  unfold Valid1 Valid2 at *
  omega

theorem test2_step {m : Int} (h : Valid2 m) (hm : m ≠ 2) : Valid1 (m - 2) := by
  unfold Valid1 Valid2 at *
  omega

mutual
def test1 (n : Int) (h : Valid1 n) : Int :=
  if hn : n = 1 then
    n
  else
    test2 (n - 1) (test1_step h hn)
termination_by n.toNat
decreasing_by
  simp_wf
  grind only [Valid1]

def test2 (m : Int) (h : Valid2 m) : Int :=
  if hm : m = 2 then
    m
  else
    test1 (m - 2) (test2_step h hm)
termination_by m.toNat
decreasing_by
  simp_wf
  grind only [Valid2, = Int.max_def]
end

example : test1 7 (by grind only [Valid1]) = 1 := by
  grind only [test1, test2]

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction Valid1
  signature   : Int → Prop
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Int.emod
    Int.ofNat
  context     : -
---
info: LeanFunction Valid2
  signature   : Int → Prop
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Int.emod
    Int.ofNat
  context     : -
---
info: LeanFunction test1
  signature   : (n : Int) → Valid1 n → Int
  argTy       : int
  resTy       : int
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Int.decEq
    Int.negSucc
    Int.ofNat
    Int.sub
  context     :
    ok  Int.toNat  [Init.Data.Int.Basic]
---
info: LeanFunction test2
  signature   : (m : Int) → Valid2 m → Int
  argTy       : int
  resTy       : int
  recursion   : mutual well-founded(encoded as Term.fixAcc over the whole block)
  status      : representable in Term
  primitives  :
    Int.decEq
    Int.negSucc
    Int.ofNat
    Int.sub
  context     :
    ok  Int.toNat  [Init.Data.Int.Basic]
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

example : test1.leanFn 4 = test1 4 (by unfold Valid1; omega) := by decide +kernel
example : test2.leanFn 5 = test2 5 (by unfold Valid2; omega) := by decide +kernel
