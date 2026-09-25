import RequestProject.WFLang.Capture.Elab
import RequestProject.WFLang.Tests.Functions

/-!
# Join points: non-tail `if`/`match` containing calls

A Lean `if`/`match` in non-tail position whose branches call a recursive function is captured
as

```
join j (v) := ⟦rest of the computation⟧ in
if c then (…; jump j a) else (…; jump j b)
```

so the rest of the computation is written once.  (Copying it into both branches instead would
give a program of size exponential in the number of such `if`s: `seq4` below would contain 16
copies of its last addition.)

* `alt`: one non-tail `if` with a recursive call in each branch;
* `seq4`: four non-tail `if`s in sequence (four join points, each one's body defining the next:
  the jumps go through `wk`);
* `nested`: a non-tail `if` inside a branch of a non-tail `if` (the inner join point's body jumps
  to the outer one);
* `viaMatch`: a non-tail `match`;
* `mixed`: a call of another recursive function (`gcd`) in one branch.

Each program is checked to contain `join` nodes (`Expr.joins`), its size is pinned
(`Expr.size`), its agreement theorem is proved by `wf_agree`, and it is run on sample inputs.
-/

open WFLang

namespace JoinEx

def alt (n : Nat) : Nat :=
  if n < 2 then n else (if n % 2 == 0 then alt (n - 1) else alt (n - 2)) + 1
termination_by n

def seq4 (n : Nat) : Nat :=
  if n = 0 then 0 else
    (if n % 2 == 0 then seq4 (n - 1) else 1) +
    (if n % 3 == 0 then seq4 (n - 1) else 2) +
    (if n % 5 == 0 then seq4 (n - 1) else 3) +
    (if n % 7 == 0 then seq4 (n - 1) else 4)
termination_by n

def seq2 (n : Nat) : Nat :=
  if n = 0 then 0 else
    (if n % 2 == 0 then seq2 (n - 1) else 1) +
    (if n % 3 == 0 then seq2 (n - 1) else 2)
termination_by n

def seq3 (n : Nat) : Nat :=
  if n = 0 then 0 else
    (if n % 2 == 0 then seq3 (n - 1) else 1) +
    (if n % 3 == 0 then seq3 (n - 1) else 2) +
    (if n % 5 == 0 then seq3 (n - 1) else 3)
termination_by n

def nested (n : Nat) : Nat :=
  if n < 3 then n else
    (if n % 2 == 0 then (if n % 3 == 0 then nested (n - 1) else nested (n - 2)) * 2
     else nested (n - 3)) + 1
termination_by n

def viaMatch (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (match k % 3 with
    | 0 => viaMatch k
    | _ => viaMatch (k / 2)) + 1

def mixed (n : Nat) : Nat :=
  if n = 0 then 0 else (if n % 2 == 0 then gcd n 6 else mixed (n - 1)) + mixed (n - 1)
termination_by n

end JoinEx


namespace ExJoin
open PCL

def alt_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.alt
theorem alt_agree : ∀ n, Term.eval alt_term n = JoinEx.alt n := by wf_agree

def seq4_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq4
theorem seq4_agree : ∀ n, Term.eval seq4_term n = JoinEx.seq4 n := by wf_agree

def nested_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.nested
theorem nested_agree : ∀ n, Term.eval nested_term n = JoinEx.nested n := by wf_agree

def viaMatch_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.viaMatch
theorem viaMatch_agree : ∀ n, Term.eval viaMatch_term n = JoinEx.viaMatch n := by wf_agree

def mixed_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.mixed
theorem mixed_agree : ∀ n, Term.eval mixed_term n = JoinEx.mixed n := by wf_agree

/-! ## The programs use join points, and stay small -/

/-- info: [1, 4, 2, 1, 1] -/
#guard_msgs in
#eval [alt_term.joins, seq4_term.joins, nested_term.joins, viaMatch_term.joins, mixed_term.joins]

/-- info: [11, 25, 16, 11, 16] -/
#guard_msgs in
#eval [alt_term.size, seq4_term.size, nested_term.size, viaMatch_term.size, mixed_term.size]

/-! ## Without join points

`set_option wfLang.joinPoints false` restores the previous behaviour: the rest of the
computation is copied into both branches.  With `k` non-tail `if`s in sequence
(`seq2`, `seq3`, `seq4`), the programs with join points have 15, 20, 25 nodes (5 more per `if`),
the programs with copies 14, 26, … nodes (the copies double with each `if`; the capture of
`seq4` with copies did not finish elaborating within 4 000 000 heartbeats when tried, so it is
not in this file).  When the continuation is tiny, copying is smaller: `nested` has 16 nodes
with join points and 12 with copies. -/

def seq2_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq2
def seq3_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq3
set_option wfLang.joinPoints false in
def seq2_dup_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq2
set_option wfLang.joinPoints false in
def seq3_dup_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.seq3
set_option wfLang.joinPoints false in
def nested_dup_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term JoinEx.nested

theorem seq3_agree : ∀ n, Term.eval seq3_term n = JoinEx.seq3 n := by wf_agree
theorem seq3_dup_agree : ∀ n, Term.eval seq3_dup_term n = JoinEx.seq3 n := by wf_agree

/-- info: [15, 20, 25] -/
#guard_msgs in
#eval [seq2_term.size, seq3_term.size, seq4_term.size]

/-- info: [14, 26, 12] -/
#guard_msgs in
#eval [seq2_dup_term.size, seq3_dup_term.size, nested_dup_term.size]

/-- info: [0, 0, 0] -/
#guard_msgs in
#eval [seq2_dup_term.joins, seq3_dup_term.joins, nested_dup_term.joins]

/-! ## Runtime checks -/

/-- info: true -/
#guard_msgs in
#eval (List.range 40).all fun n =>
  Term.eval alt_term n == JoinEx.alt n && Term.eval seq4_term n == JoinEx.seq4 n &&
  Term.eval nested_term n == JoinEx.nested n && Term.eval viaMatch_term n == JoinEx.viaMatch n

/-- info: true -/
#guard_msgs in
#eval (List.range 14).all fun n => Term.eval mixed_term n == JoinEx.mixed n

end ExJoin
