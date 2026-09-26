import RequestProject.WFLang.Tests.MoreChecks

/-!
# Sharing: the pure `let` statement

`let v := p in k` (`PCL.Expr.plet`) computes the call-free value `p` once and binds it to a new
variable `v`; `k` runs under the path condition extended by `v = p`.  The capture uses it for a
Lean `let x := v; b` whose value is call-free, not atomic once simplified, and used at least
twice in `b` (`shareLet?`, `Capture/Stmt/Basic.lean`); other call-free `let`s are substituted,
as before.  `set_option wfLang.shareLets false` substitutes every call-free `let`.

* `sq2`, `pow4`, `nested`, `letList`, `letBool`: `let`s in call-free code, in tail position.
* `sumSq`: a shared value next to a recursive call; `inArg`: a `let` inside the argument of an
  operator whose other argument calls (the `let` is lifted, like a call).
* `gcdL`: the decrease proof of the recursive call needs the value of the `let`
  (`gcdL n r` with `r := m % n`): it is found in the path condition (`wf_subst_lets`).
* `sumLoop`: a `let` in the body of a loop (an inlined tail-recursive `@[inlinable]` function).
* `doLet`: a `let` in `do` notation.
* `once`, `atom`, `folded`: not shared (used once; a variable; a constant after folding).

Each capture agrees with its Lean function (`wf_agree`); the number of pure `let`s (`lets`) and
of expression nodes (`exprNodes`), with and without sharing, are pinned below.
-/

namespace SharingEx

def sq2 (n : Nat) : Nat := let x := n * n + 1; x + x

def pow4 (a b c : Nat) : Nat := let x := a * b + c; x * x * x * x

def nested (n : Nat) : Nat :=
  let a := n + 1
  let b := a * a
  b + b + a

def letList (l : List Nat) (n : Nat) : List Nat × Nat :=
  let l2 := l ++ [n]
  (l2, l2.length)

def letBool (n : Nat) : Nat :=
  let c := n % 3 == 0
  if c then (if c && n > 5 then 1 else 2) else 3

def sumSq (n : Nat) : Nat :=
  if n = 0 then 0 else
  let y := n * n
  y + y * y + sumSq (n - 1)
termination_by n

def inArg (n : Nat) : Nat :=
  if n = 0 then 1 else n + (let y := n * n + 2; y * inArg (n - 1) + y)
termination_by n

def gcdL (m n : Nat) : Nat :=
  if n = 0 then m else
  let r := m % n
  if r = 0 then n else gcdL n r
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

@[inlinable] def sumLoopGo (i acc : Nat) : Nat :=
  if i = 0 then acc else
  let s := i * i + 1
  sumLoopGo (i - 1) (acc + s * s)
termination_by i

def sumLoop (n : Nat) : Nat := sumLoopGo n 0 + 1

/-- `do` notation: `x` is shared, the mutable `s` (used once after its update) is substituted. -/
def doLet (n : Nat) : Nat := Id.run do
  let x := n * 3 + 1
  let mut s := x
  s := s * x
  return s + x

def once (n : Nat) : Nat := let x := n * n; x + 1

def atom (n : Nat) : Nat := let x := n; x * x

def folded (n : Nat) : Nat := let y := 2 + 3; y * n + y

end SharingEx

namespace ExSharing
open WFLang PCL SharingEx

def sq2_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sq2
theorem sq2_agree : ∀ n, Term.eval sq2_term n = sq2 n := by wf_agree

def pow4_term : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term pow4
theorem pow4_agree : ∀ a b c, Term.eval pow4_term a b c = pow4 a b c := by wf_agree

def nested_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term nested
theorem nested_agree : ∀ n, Term.eval nested_term n = nested n := by wf_agree

def letList_term : Term ⟨[.list .nat, .nat], .prod (.list .nat) .nat⟩ :=
  #lean_wf_func_to_term letList
theorem letList_agree : ∀ l n, Term.eval letList_term l n = letList l n := by wf_agree

def letBool_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term letBool
theorem letBool_agree : ∀ n, Term.eval letBool_term n = letBool n := by wf_agree

def sumSq_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumSq
theorem sumSq_agree : ∀ n, Term.eval sumSq_term n = sumSq n := by wf_agree

def inArg_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term inArg
theorem inArg_agree : ∀ n, Term.eval inArg_term n = inArg n := by wf_agree

def gcdL_term : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdL
theorem gcdL_agree : ∀ m n, Term.eval gcdL_term m n = gcdL m n := by wf_agree

def sumLoop_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumLoop
theorem sumLoop_agree : ∀ n, Term.eval sumLoop_term n = sumLoop n := by wf_agree

def doLet_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term doLet
theorem doLet_agree : ∀ n, Term.eval doLet_term n = doLet n := by wf_agree

def once_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term once
theorem once_agree : ∀ n, Term.eval once_term n = once n := by wf_agree

def atom_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term atom
theorem atom_agree : ∀ n, Term.eval atom_term n = atom n := by wf_agree

def folded_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term folded
theorem folded_agree : ∀ n, Term.eval folded_term n = folded n := by wf_agree

/-! ### The same functions, captured without sharing -/

set_option wfLang.shareLets false in
def sq2_subst : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sq2
set_option wfLang.shareLets false in
def pow4_subst : Term ⟨[.nat, .nat, .nat], .nat⟩ := #lean_wf_func_to_term pow4
set_option wfLang.shareLets false in
def nested_subst : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term nested
set_option wfLang.shareLets false in
def sumSq_subst : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term sumSq
set_option wfLang.shareLets false in
def gcdL_subst : Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcdL
theorem pow4_subst_agree : ∀ a b c, Term.eval pow4_subst a b c = pow4 a b c := by wf_agree

/-! ### Shapes -/

-- the number of pure `let`s: one per shared value; none for `once`, `atom`, `folded`
/-- info: [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0] -/
#guard_msgs in
#eval [sq2_term.lets, pow4_term.lets, nested_term.lets, letList_term.lets, letBool_term.lets,
  sumSq_term.lets, inArg_term.lets, gcdL_term.lets, sumLoop_term.lets, doLet_term.lets,
  once_term.lets, atom_term.lets, folded_term.lets]

-- nodes of call-free expressions, with sharing (first row) and without (second row):
-- e.g. `pow4` has `a * b + c` (5 nodes) once instead of four times: 5 + 7 against 4 * 5 + 3
/-- info: [[8, 12, 11, 19, 17], [11, 23, 19, 22, 18]] -/
#guard_msgs in
#eval [[sq2_term.exprNodes, pow4_term.exprNodes, nested_term.exprNodes, sumSq_term.exprNodes,
    gcdL_term.exprNodes],
  [sq2_subst.exprNodes, pow4_subst.exprNodes, nested_subst.exprNodes, sumSq_subst.exprNodes,
    gcdL_subst.exprNodes]]

/-! ### Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 30).all fun n =>
  Term.eval sq2_term n == sq2 n && Term.eval nested_term n == nested n &&
  Term.eval letBool_term n == letBool n && Term.eval sumSq_term n == sumSq n &&
  Term.eval inArg_term n == inArg n && Term.eval sumLoop_term n == sumLoop n &&
  Term.eval doLet_term n == doLet n &&
  Term.eval once_term n == once n && Term.eval atom_term n == atom n &&
  Term.eval folded_term n == folded n

/-- info: true -/
#guard_msgs in
#eval (List.range 12).all fun a => (List.range 12).all fun b =>
  Term.eval pow4_term a b 3 == pow4 a b 3 && Term.eval gcdL_term a b == gcdL a b

/-- info: true -/
#guard_msgs in
#eval [[], [1], [2, 3]].all fun l => Term.eval letList_term l 7 == letList l 7

/-! ### Hand-written programs -/

/-- `fun n => let x := n * n in x + x`. -/
def dbl : Term ⟨[.nat], .nat⟩ :=
  ⟨.nil, .plet .nat (.bin .mul (.var .here) (.var .here)) (by decide)
    (.ret (.bin .add (.var .here) (.var .here)) (by decide) (fun _ _ => trivial))⟩

theorem dbl_eval : ∀ n, Term.eval dbl n = n * n + n * n := by
  intro n; rfl

-- the path condition of the rest knows the value of the variable: here the postcondition
-- `r = n * n + n * n` of the program is proved from `x = n * n`
/-- `fun n => let x := n * n in x + x`, with the postcondition `r = n * n + n * n`. -/
def dblPost : Term ⟨[.nat], .nat⟩ (fun e r => r = e.1 * e.1 + e.1 * e.1) :=
  ⟨.nil, .plet .nat (.bin .mul (.var .here) (.var .here)) (by decide)
    (.ret (.bin .add (.var .here) (.var .here)) (by decide)
      (fun e h => by simp only [PExpr.eval, BinOp.eval, Var.get] at h ⊢; rw [h.2]))⟩

-- binding a variable (or a literal) is rejected: it is substituted instead
/-- info: rejected: Tactic `decide` proved that the proposition -/
#guard_msgs in
#expect_reject (⟨.nil, .plet .nat (.var .here) (by decide)
  (.ret (.bin .add (.var .here) (.var .here)) rfl (fun _ _ => trivial))⟩ :
  Term ⟨[.nat], .nat⟩)

end ExSharing
