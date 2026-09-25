import RequestProject.WFLang.Tests.MoreChecks

/-!
# What is still not supported (`UNSUPPORTED.md`)

Each function below is an ordinary Lean definition that `#lean_wf_func_to_term` does **not**
capture today.  The rejection (or the failed decrease proof) is pinned by `#guard_msgs`, so if
the capture starts accepting one of them, the build fails and `UNSUPPORTED.md` must be updated.
`#expect_reject` (from `MoreChecks.lean`) succeeds only if the capture fails, and reports the
first line of its error.
-/

open WFLang

namespace Unsupported

/-! ## Types outside `Ty` (`Nat`, `Bool`, `Int`, pairs, lists, subtypes of them) -/

def optDown : Nat → Option Nat
  | 0 => none
  | n + 1 => optDown n

def strLen (s : String) : Nat := s.length

structure Pt where
  a : Nat
  b : Nat

def ptSum (p : Pt) : Nat := p.a + p.b

/-- An `Option` only as an intermediate value (neither parameter nor result). -/
def optInside (n : Nat) : Nat :=
  match (if n > 3 then some n else none) with
  | some k => k
  | none => 0

/-- `Array` (here only through its size). -/
def arrSize (n : Nat) : Nat := (Array.range n).size

/-- `match` on the constructors of `Int`. -/
def intCases : Int → Nat
  | .ofNat n => n
  | .negSucc n => n

/-! ## Library functions on lists, and higher-order combinators -/

def mapSq (n : Nat) : List Nat := (List.range n).map (fun i => i * i)
def listGetD (l : List Nat) (i : Nat) : Nat := l.getD i 0
def listIdx (l : List Nat) (i : Nat) : Nat := l[i]!
def listHas3 (l : List Nat) : Bool := l.contains 3
def listFoldl (l : List Nat) : Nat := l.foldl (· + ·) 0

/-- A bounded quantifier decided by `decide`. -/
def boundedAll (n : Nat) : Bool := decide (∀ i < n, i * i ≠ 7)

/-! ## `do` notation beyond "for over a range, always continuing" -/

def forList (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do s := s + x
  return s

def forBreak (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    if s > 100 then break
    s := s + i
  return s

def forReturn (n : Nat) : Nat := Id.run do
  for i in [0:n] do
    if i * i > n then return i
  return n

def forStep (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n:2] do s := s + i
  return s

/-! ## Definitions that are not well-founded recursion -/

def pfix (n : Nat) : Nat := if n = 0 then 0 else pfix (n - 1)
partial_fixpoint

/-! ## Mutual recursion with different signatures -/

mutual
def mA : Nat → Nat
  | 0 => 0
  | n + 1 => mB n true
def mB : Nat → Bool → Nat
  | 0, _ => 1
  | n + 1, b => if b then mA n else mA n + 1
end

mutual
def rA : Nat → Nat
  | 0 => 0
  | n + 1 => if rB n then 1 else 2
def rB : Nat → Bool
  | 0 => true
  | n + 1 => rA n == 0
end

/-! ## A decrease proof that Lean finds but the capture does not

`nestMin (n+1) = nestMin (min n (nestMin n)) + 1` terminates because `min n _ ≤ n`, and Lean's
`omega` proves it without knowing anything about the inner call.  The capture translates `min`
into an `if`, and its decrease goal (with the `if`) is not closed by Lean's proof term, which
mentions `n ⊓ x n ⋯`.  The goal is true: this is a gap in the capture's automation, not in the
language. -/

def nestMin : Nat → Nat
  | 0 => 0
  | n + 1 => nestMin (min n (nestMin n)) + 1
termination_by n => n
decreasing_by all_goals omega

end Unsupported

/-- info: rejected: #lean_wf_func_to_term: unsupported type Option ℕ (only Nat, Bool, Int, pairs, lists and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.optDown : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type String (only Nat, Bool, Int, pairs, lists and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.strLen : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported type Unsupported.Pt (only Nat, Bool, Int, pairs, lists and subtypes of them) -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.ptSum : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.optInside : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.arrSize : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.intCases : PCL.Term ⟨[.int], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.mapSq : PCL.Term ⟨[.nat], .list .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.listGetD : PCL.Term ⟨[.list .nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.listIdx : PCL.Term ⟨[.list .nat, .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.listHas3 : PCL.Term ⟨[.list .nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.listFoldl : PCL.Term ⟨[.list .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported condition -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.boundedAll : PCL.Term ⟨[.nat], .bool⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.forList : PCL.Term ⟨[.list .nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.forBreak : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.forReturn : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: unsupported expression -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.forStep : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: recursive call of Unsupported.pfix outside its definition -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.pfix : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: the mutually recursive functions [Unsupported.mA, -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.mA : PCL.Term ⟨[.nat], .nat⟩)

/-- info: rejected: #lean_wf_func_to_term: the mutually recursive functions [Unsupported.rA, -/
#guard_msgs in
#expect_reject (#lean_wf_func_to_term Unsupported.rA : PCL.Term ⟨[.nat], .nat⟩)

/--
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
this✝¹ : ∀ (n : ℕ), InvImage (fun x1 x2 => x1 < x2) (fun x => x) n n.succ
this✝ :
  ∀ (n : ℕ) (x : (y : ℕ) → InvImage (fun x1 x2 => x1 < x2) (fun x => x) y n.succ → ℕ),
    InvImage (fun x1 x2 => x1 < x2) (fun x => x) (n ⊓ x n ⋯) n.succ
e✝ : Env [Ty.nat, Ty.nat]
g✝ : ¬e✝.snd.fst = 0
⊢ (if e✝.snd.fst ≤ e✝.fst + 1 then e✝.snd.fst - 1 else e✝.fst) < e✝.snd.fst
-/
#guard_msgs in
example : PCL.Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term Unsupported.nestMin
