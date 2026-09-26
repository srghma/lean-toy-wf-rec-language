import RequestProject.WFLang

/-!
# List combinators, bounded quantifiers, and `for` loops that stop early or step

Each function below was rejected before (see `UNSUPPORTED.md`).  The library combinators with a
function argument (`List.foldl`, `foldr`, `any`, `all`, `contains`, `elem`, `find?`, `filter`,
`for x in l`) are rewritten into the first-order recursive functions of `Core/ListLoops.lean`,
specialised to their function argument at the call site.  `for` loops whose body may `break` or
`return`, and loops over ranges with a step `[a:b:s]`, become `rangeLoopN` / `listLoopN`.
Each function is captured with `#lean_wf_func_to_term`, and its agreement theorem is proved by
`wf_agree`.
-/

open WFLang PCL

namespace ListComb

def listHas3 (l : List Nat) : Bool := l.contains 3
def listFoldl (l : List Nat) : Nat := l.foldl (· + ·) 0
def forList (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do s := s + x
  return s
def anyBig (l : List Nat) (k : Nat) : Bool := l.any (fun x => x > k)
def allSmall (l : List Nat) : Bool := l.all (fun x => x < 10)
def firstEven (l : List Nat) : Option Nat := l.find? (fun x => x % 2 == 0)
def evens (l : List Nat) : List Nat := l.filter (fun x => x % 2 == 0)
def sumR (l : List Nat) : Nat := l.foldr (fun x acc => x + 2 * acc) 0

/-! Bounded quantifiers, decided by `decide` or in the test of an `if`. -/

def boundedAll (n : Nat) : Bool := decide (∀ i < n, i * i ≠ 7)
def boundedEx (n : Nat) : Nat := if ∃ i < n, i * i = 49 then 1 else 0
def memAll (l : List Nat) : Bool := decide (∀ x ∈ l, x % 2 = 0)
def memEx (l : List Nat) (k : Nat) : Bool := decide (∃ x ∈ l, x > k)

/-! `for` loops with `break`, early `return`, a step, and over a list with `break`. -/

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

def forListBreak (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in l do
    if x = 0 then break
    s := s + x
  return s

/-! A recursive call inside the function given to a combinator. -/

def fsum (n : Nat) : Nat :=
  if n = 0 then 0 else (List.range n).foldl (fun acc i => acc + i * fsum (n - 1)) 1
termination_by n
decreasing_by omega

def anyRec (n : Nat) : Bool :=
  if n = 0 then false else (List.range 3).any (fun i => i == n || anyRec (n - 1))
termination_by n
decreasing_by omega

end ListComb

def listHas3_term : Term ⟨[.list .nat], .bool⟩ := #lean_wf_func_to_term ListComb.listHas3
theorem listHas3_agree : ∀ l, Term.eval listHas3_term l = ListComb.listHas3 l := by wf_agree
def listFoldl_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term ListComb.listFoldl
theorem listFoldl_agree : ∀ l, Term.eval listFoldl_term l = ListComb.listFoldl l := by wf_agree
def forList_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term ListComb.forList
theorem forList_agree : ∀ l, Term.eval forList_term l = ListComb.forList l := by wf_agree
def anyBig_term : Term ⟨[.list .nat, .nat], .bool⟩ := #lean_wf_func_to_term ListComb.anyBig
theorem anyBig_agree : ∀ l k, Term.eval anyBig_term l k = ListComb.anyBig l k := by wf_agree
def allSmall_term : Term ⟨[.list .nat], .bool⟩ := #lean_wf_func_to_term ListComb.allSmall
theorem allSmall_agree : ∀ l, Term.eval allSmall_term l = ListComb.allSmall l := by wf_agree
def firstEven_term : Term ⟨[.list .nat], .option .nat⟩ := #lean_wf_func_to_term ListComb.firstEven
theorem firstEven_agree : ∀ l, Term.eval firstEven_term l = ListComb.firstEven l := by wf_agree
def evens_term : Term ⟨[.list .nat], .list .nat⟩ := #lean_wf_func_to_term ListComb.evens
theorem evens_agree : ∀ l, Term.eval evens_term l = ListComb.evens l := by wf_agree
def sumR_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term ListComb.sumR
theorem sumR_agree : ∀ l, Term.eval sumR_term l = ListComb.sumR l := by wf_agree

def boundedAll_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term ListComb.boundedAll
theorem boundedAll_agree : ∀ n, Term.eval boundedAll_term n = ListComb.boundedAll n := by
  wf_agree
def boundedEx_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ListComb.boundedEx
theorem boundedEx_agree : ∀ n, Term.eval boundedEx_term n = ListComb.boundedEx n := by wf_agree
def memAll_term : Term ⟨[.list .nat], .bool⟩ := #lean_wf_func_to_term ListComb.memAll
theorem memAll_agree : ∀ l, Term.eval memAll_term l = ListComb.memAll l := by wf_agree
def memEx_term : Term ⟨[.list .nat, .nat], .bool⟩ := #lean_wf_func_to_term ListComb.memEx
theorem memEx_agree : ∀ l k, Term.eval memEx_term l k = ListComb.memEx l k := by wf_agree

def forBreak_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ListComb.forBreak
theorem forBreak_agree : ∀ n, Term.eval forBreak_term n = ListComb.forBreak n := by wf_agree
def forReturn_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ListComb.forReturn
theorem forReturn_agree : ∀ n, Term.eval forReturn_term n = ListComb.forReturn n := by wf_agree
def forStep_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ListComb.forStep
theorem forStep_agree : ∀ n, Term.eval forStep_term n = ListComb.forStep n := by wf_agree
def forListBreak_term : Term ⟨[.list .nat], .nat⟩ := #lean_wf_func_to_term ListComb.forListBreak
theorem forListBreak_agree : ∀ l, Term.eval forListBreak_term l = ListComb.forListBreak l := by
  wf_agree

def fsum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term ListComb.fsum
theorem fsum_agree : ∀ n, Term.eval fsum_term n = ListComb.fsum n := by wf_agree
def anyRec_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term ListComb.anyRec
theorem anyRec_agree : ∀ n, Term.eval anyRec_term n = ListComb.anyRec n := by wf_agree

#guard [[], [3], [1, 2, 3, 4], [5, 0, 7], [2, 4, 12]].all fun l =>
  Term.eval listHas3_term l == ListComb.listHas3 l &&
  Term.eval listFoldl_term l == ListComb.listFoldl l &&
  Term.eval forList_term l == ListComb.forList l &&
  Term.eval anyBig_term l 3 == ListComb.anyBig l 3 &&
  Term.eval allSmall_term l == ListComb.allSmall l &&
  Term.eval firstEven_term l == ListComb.firstEven l &&
  Term.eval evens_term l == ListComb.evens l &&
  Term.eval sumR_term l == ListComb.sumR l &&
  Term.eval memAll_term l == ListComb.memAll l &&
  Term.eval memEx_term l 4 == ListComb.memEx l 4 &&
  Term.eval forListBreak_term l == ListComb.forListBreak l
#guard (List.range 30).all fun n =>
  Term.eval boundedAll_term n == ListComb.boundedAll n &&
  Term.eval boundedEx_term n == ListComb.boundedEx n &&
  Term.eval forBreak_term n == ListComb.forBreak n &&
  Term.eval forReturn_term n == ListComb.forReturn n &&
  Term.eval forStep_term n == ListComb.forStep n
#guard (List.range 6).all fun n =>
  Term.eval fsum_term n == ListComb.fsum n && Term.eval anyRec_term n == ListComb.anyRec n
