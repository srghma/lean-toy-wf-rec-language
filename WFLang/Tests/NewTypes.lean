import RequestProject.WFLang

/-!
# `Option`, `Sum`, `Except`, `String`, `Char`, `Array`, `Unit`; list indexing; `match` on `Int`

Each function below was rejected before these types were added to `Ty` (see `UNSUPPORTED.md`).
Each is captured with `#lean_wf_func_to_term`, and its agreement theorem is proved by `wf_agree`.
The `#guard`s compare the program with the Lean function on sample inputs.
-/

open WFLang PCL

namespace NewTypes

/-- `Option` as a result. -/
def optDown : Nat → Option Nat
  | 0 => none
  | n + 1 => optDown n

/-- An `Option` only as an intermediate value. -/
def optInside (n : Nat) : Nat :=
  match (if n > 3 then some n else none) with
  | some k => k
  | none => 0

/-- `Option` as the result of a recursive search. -/
def optFind (l : List Nat) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => if x % 2 = 0 then some x else optFind xs

/-- A `String` parameter. -/
def strLen (s : String) : Nat := s.length

/-- Strings and characters. -/
def shout (s : String) : String := s ++ "!"
def charCode (c : Char) : Nat := c.toNat

/-- An `Array` (here only through its size). -/
def arrSize (n : Nat) : Nat := (Array.range n).size

/-- `match` on the constructors of `Int`. -/
def intCases : Int → Nat
  | .ofNat n => n
  | .negSucc n => n

/-- List indexing with a default, and `l[i]!`. -/
def listGetD (l : List Nat) (i : Nat) : Nat := l.getD i 0
def listIdx (l : List Nat) (i : Nat) : Nat := l[i]!

/-- `match` on a `Sum`. -/
def sumCase (x : Nat ⊕ Bool) : Nat :=
  match x with
  | .inl n => n + 1
  | .inr b => if b then 1 else 0

/-- `match` on an `Except`. -/
def excCase (x : Except String Nat) : Nat :=
  match x with
  | .ok n => n
  | .error s => s.length

/-- `Except` as a result. -/
def safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then .error "div by zero" else .ok (a / b)

/-- `Unit` in a result. -/
def unitPair (n : Nat) : Unit × Nat := ((), n + 1)

end NewTypes

def optDown_term : Term ⟨[.nat], .option .nat⟩ := #lean_wf_func_to_term NewTypes.optDown
theorem optDown_agree : ∀ n, Term.eval optDown_term n = NewTypes.optDown n := by wf_agree

def optInside_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term NewTypes.optInside
theorem optInside_agree : ∀ n, Term.eval optInside_term n = NewTypes.optInside n := by wf_agree

def optFind_term : Term ⟨[.list .nat], .option .nat⟩ := #lean_wf_func_to_term NewTypes.optFind
theorem optFind_agree : ∀ l, Term.eval optFind_term l = NewTypes.optFind l := by wf_agree

def strLen_term : Term ⟨[.string], .nat⟩ := #lean_wf_func_to_term NewTypes.strLen
theorem strLen_agree : ∀ s, Term.eval strLen_term s = NewTypes.strLen s := by wf_agree

def shout_term : Term ⟨[.string], .string⟩ := #lean_wf_func_to_term NewTypes.shout
theorem shout_agree : ∀ s, Term.eval shout_term s = NewTypes.shout s := by wf_agree

def charCode_term : Term ⟨[.char], .nat⟩ := #lean_wf_func_to_term NewTypes.charCode
theorem charCode_agree : ∀ c, Term.eval charCode_term c = NewTypes.charCode c := by wf_agree

def arrSize_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term NewTypes.arrSize
theorem arrSize_agree : ∀ n, Term.eval arrSize_term n = NewTypes.arrSize n := by wf_agree

def intCases_term : Term ⟨[.int], .nat⟩ := #lean_wf_func_to_term NewTypes.intCases
theorem intCases_agree : ∀ i, Term.eval intCases_term i = NewTypes.intCases i := by wf_agree

def listGetD_term : Term ⟨[.list .nat, .nat], .nat⟩ := #lean_wf_func_to_term NewTypes.listGetD
theorem listGetD_agree : ∀ l i, Term.eval listGetD_term l i = NewTypes.listGetD l i := by
  wf_agree

def listIdx_term : Term ⟨[.list .nat, .nat], .nat⟩ := #lean_wf_func_to_term NewTypes.listIdx
theorem listIdx_agree : ∀ l i, Term.eval listIdx_term l i = NewTypes.listIdx l i := by wf_agree

def sumCase_term : Term ⟨[.sum .nat .bool], .nat⟩ := #lean_wf_func_to_term NewTypes.sumCase
theorem sumCase_agree : ∀ x, Term.eval sumCase_term x = NewTypes.sumCase x := by wf_agree

def excCase_term : Term ⟨[.except .string .nat], .nat⟩ := #lean_wf_func_to_term NewTypes.excCase
theorem excCase_agree : ∀ x, Term.eval excCase_term x = NewTypes.excCase x := by wf_agree

def safeDiv_term : Term ⟨[.nat, .nat], .except .string .nat⟩ :=
  #lean_wf_func_to_term NewTypes.safeDiv
theorem safeDiv_agree : ∀ a b, Term.eval safeDiv_term a b = NewTypes.safeDiv a b := by wf_agree

def unitPair_term : Term ⟨[.nat], .prod .unit .nat⟩ := #lean_wf_func_to_term NewTypes.unitPair
theorem unitPair_agree : ∀ n, Term.eval unitPair_term n = NewTypes.unitPair n := by wf_agree

#guard (List.range 10).all fun n =>
  Term.eval optDown_term n == NewTypes.optDown n &&
  Term.eval optInside_term n == NewTypes.optInside n &&
  Term.eval arrSize_term n == NewTypes.arrSize n &&
  Term.eval unitPair_term n == NewTypes.unitPair n
#guard [[], [1, 3], [1, 4, 5], [2]].all fun l =>
  Term.eval optFind_term l == NewTypes.optFind l &&
  (List.range 5).all (fun i => Term.eval listGetD_term l i == NewTypes.listGetD l i) &&
  -- (in range only: out of range, Lean's `l[i]!` panics at run time before returning `0`)
  (List.range l.length).all fun i => Term.eval listIdx_term l i == NewTypes.listIdx l i
#guard ["", "ab", "héllo"].all fun s =>
  Term.eval strLen_term s == NewTypes.strLen s && Term.eval shout_term s == NewTypes.shout s
#guard ['a', 'Z', '0'].all fun c => Term.eval charCode_term c == NewTypes.charCode c
#guard ([-3, 0, 5] : List Int).all fun i => Term.eval intCases_term i == NewTypes.intCases i
#guard [.inl 3, .inr true, .inr false].all fun x => Term.eval sumCase_term x == NewTypes.sumCase x
#guard [.ok 4, .error "bad"].all fun x => Term.eval excCase_term x == NewTypes.excCase x
#guard [(7, 2), (7, 0)].all fun (a, b) =>
  NewTypes.excCase (Term.eval safeDiv_term a b) == NewTypes.excCase (NewTypes.safeDiv a b)
