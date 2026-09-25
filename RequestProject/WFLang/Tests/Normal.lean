import RequestProject.WFLang.Tests.MoreChecks

/-!
# Optimised normal form

The statements of `PCL.Expr` only accept call-free expressions in optimised normal form
(`PExpr.isNF`, `Core/Normal.lean`) and `if` tests that are conditions (`PExpr.isCond`): no
constant subexpression left to fold, no algebraic identity left to apply (`x + 0`, `x * 1`,
`b && true`, `l ++ []`, …), no `!!b`, `- - i`, `(a, b).1`, no `if` on a literal or on a negation,
no `if c then true else false`.  The capture simplifies while it translates
(`Capture/Optimize.lean`), so its programs satisfy these checks; a program that could still be
simplified does not type-check.

* `optEx` and `listEx` are written with many simplifiable subterms; their captures are small
  (sizes pinned below) and agree with the Lean functions.
* The normal-form checks reject the unsimplified forms (`decide` below), and a hand-written
  unsimplified program is rejected by the type checker (`#expect_reject`).
-/

namespace NormalEx

/-- Constant folding (`0 * n + (2 + 3)`), a dead branch (`3 < 2`), a negated test (`n ≠ 1`),
identities (`+ 0`, `* 1`, `- 0`) and an `if true`. -/
def optEx (n : Nat) : Nat :=
  if n = 0 then 0 * n + (2 + 3)
  else if 3 < 2 then optEx (n - 1)
  else if n ≠ 1 then optEx (n - 1) + 0
  else (n * 1 + 0) - 0 + (if true then 1 else n)
termination_by n

/-- List literals folded (`[1] ++ [2, 3]`), `l ++ []`, `Int` arithmetic on literals, and a
negated test inside a value (`if !b then 1 else 2`). -/
def listEx (l : List Nat) (b : Bool) : List Nat × Int :=
  ((l ++ []) ++ ([1] ++ [2, 3]), (-3 : Int) + 5 * 1 + (if !b then 1 else 2))

/-- `b && true`, `xor b false`, `!!b`, `(x, y).1`, `if c then true else false`, `min` of a literal. -/
def boolEx (b c : Bool) (x y : Nat) : Bool × Nat :=
  ((b && true) || (xor c false && !!b), (x, y).1 + min 3 5 + (if (if c then true else false) then 1 else 0))

end NormalEx

namespace ExNormal
open WFLang PCL NormalEx

def optEx_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term optEx
theorem optEx_agree : ∀ n, Term.eval optEx_term n = optEx n := by wf_agree

def listEx_term : Term ⟨[.list .nat, .bool], .prod (.list .nat) .int⟩ :=
  #lean_wf_func_to_term listEx
theorem listEx_agree : ∀ l b, Term.eval listEx_term l b = listEx l b := by wf_agree

def boolEx_term : Term ⟨[.bool, .bool, .nat, .nat], .prod .bool .nat⟩ :=
  #lean_wf_func_to_term boolEx
theorem boolEx_agree : ∀ b c x y, Term.eval boolEx_term b c x y = boolEx b c x y := by wf_agree

-- `optEx` is captured as the global function
-- `f n := if n == 0 then ret 5 else if n == 1 then ret (n + 1) else let v := f (n - 1) in ret v`
-- and the main statement `let v := f n in ret v` (8 nodes: the call `f n`, its `ret`, and the
-- 6 nodes of the body); `listEx` and `boolEx` are a single `ret`.
/-- info: [8, 1, 1] -/
#guard_msgs in
#eval [optEx_term.size, listEx_term.size, boolEx_term.size]

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun n => Term.eval optEx_term n == optEx n

/-- info: true -/
#guard_msgs in
#eval [[], [4], [5, 6]].all fun l => [true, false].all fun b =>
  Term.eval listEx_term l b == listEx l b

/-- info: true -/
#guard_msgs in
#eval [true, false].all fun b => [true, false].all fun c => (List.range 5).all fun x =>
  Term.eval boolEx_term b c x 7 == boolEx b c x 7

/-! ## The normal-form checks -/

example : (PExpr.bin .add (.lit .nat 2) (.lit .nat 3) : PExpr [] .nat).isNF = false := by decide
example : (PExpr.lit .nat 5 : PExpr [] .nat).isNF = true := by decide
example : (PExpr.bin .add (.var .here) (.lit .nat 0) : PExpr (.nat :: []) .nat).isNF = false := by
  decide
example : (PExpr.bin .mul (.lit .nat 1) (.var .here) : PExpr (.nat :: []) .nat).isNF = false := by
  decide
example : (PExpr.bin .add (.var .here) (.lit .nat 1) : PExpr (.nat :: []) .nat).isNF = true := by
  decide
example : (PExpr.bin .and (.var .here) (.lit .bool true) : PExpr (.bool :: []) .bool).isNF =
    false := by decide
example : (PExpr.not (.not (.var .here)) : PExpr (.bool :: []) .bool).isNF = false := by decide
example : (PExpr.un (.fst .nat .nat) (.bin (.pair .nat .nat) (.var .here) (.lit .nat 1)) :
    PExpr (.nat :: []) .nat).isNF = false := by decide
example : (PExpr.bin (.append .nat) (.var .here) (.lit (.list .nat) []) :
    PExpr (.list .nat :: []) (.list .nat)).isNF = false := by decide
example : (PExpr.ite (.var .here) (.lit .bool true) (.lit .bool false) :
    PExpr (.bool :: []) .bool).isNF = false := by decide
example : (PExpr.ite (.var .here) (.lit .nat 1) (.lit .nat 2) : PExpr (.bool :: []) .nat).isNF =
    true := by decide
example : (PExpr.lit .bool true : PExpr [] .bool).isCond = false := by decide
example : (PExpr.not (.var .here) : PExpr (.bool :: []) .bool).isCond = false := by decide
example : (PExpr.var .here : PExpr (.bool :: []) .bool).isCond = true := by decide

/-! ## Unsimplified programs are ill-typed -/

/-- The simplified program `fun n => n` is accepted. -/
example : Term ⟨[.nat], .nat⟩ := ⟨.nil, .ret (.var .here) (by decide) (fun _ _ => trivial)⟩

-- `fun n => n + 0` is rejected: its `ret` needs a proof that `n + 0` is in normal form.
/-- info: rejected: Tactic `decide` proved that the proposition -/
#guard_msgs in
#expect_reject (⟨.nil, .ret (.bin .add (.var .here) (.lit .nat 0)) (by decide)
  (fun _ _ => trivial)⟩ : Term ⟨[.nat], .nat⟩)

-- `if true then 1 else 2` is rejected: the test of an `if` must not be a literal.
/-- info: rejected: Tactic `decide` proved that the proposition -/
#guard_msgs in
#expect_reject (⟨.nil, .ite (.lit .bool true) (by decide)
  (.ret (.lit .nat 1) rfl (fun _ _ => trivial))
  (.ret (.lit .nat 2) rfl (fun _ _ => trivial))⟩ : Term ⟨[.nat], .nat⟩)

end ExNormal
