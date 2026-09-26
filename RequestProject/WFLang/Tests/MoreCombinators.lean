import RequestProject.WFLang

/-!
# More combinators: `zipWith`, `partition`, `countP`, and the array combinators

Each function below uses a library function with a function argument that was not supported
before (see `UNSUPPORTED.md`, §3): `List.zipWith`, `List.partition`, `List.countP`,
`Array.foldl`, `Array.foldr`, `Array.map`, `Array.any`, `Array.all`, `Array.contains`.  They are
rewritten into the first-order recursive functions of `Core/MoreCombinators.lean` (or of
`Core/ListLoops.lean`), specialised to the function argument at the call site.  Each function is
captured with `#lean_wf_func_to_term`, and its agreement theorem is proved by `wf_agree`.
-/

open WFLang PCL

namespace MoreComb

def dot (a b : List Nat) : Nat := (List.zipWith (· * ·) a b).foldl (· + ·) 0
def addK (a b : List Nat) (k : Nat) : List Nat := List.zipWith (fun x y => x + y + k) a b
def split (l : List Nat) : List Nat × List Nat := l.partition (fun x => x % 2 == 0)
def countBig (l : List Nat) (k : Nat) : Nat := l.countP (fun x => x > k)
def arrSum (a : Array Nat) : Nat := a.foldl (· + ·) 0
def arrSumR (a : Array Nat) : Nat := a.foldr (fun x acc => x + 2 * acc) 0
def arrDouble (a : Array Nat) : Array Nat := a.map (· * 2)
def arrAnyBig (a : Array Nat) (k : Nat) : Bool := a.any (fun x => x > k)
def arrAllSmall (a : Array Nat) : Bool := a.all (fun x => x < 10)
def arrHas3 (a : Array Nat) : Bool := a.contains 3

/-- A recursive call inside the function given to `Array.map`. -/
def arrRec (n : Nat) : Array Nat :=
  if n = 0 then #[] else (Array.range n).map (fun i => i + (arrRec (n - 1)).size)
termination_by n
decreasing_by omega

end MoreComb

def dot_term : Term ⟨[.list .nat, .list .nat], .nat⟩ := #lean_wf_func_to_term MoreComb.dot
theorem dot_agree : ∀ a b, Term.eval dot_term a b = MoreComb.dot a b := by wf_agree
def addK_term : Term ⟨[.list .nat, .list .nat, .nat], .list .nat⟩ :=
  #lean_wf_func_to_term MoreComb.addK
theorem addK_agree : ∀ a b k, Term.eval addK_term a b k = MoreComb.addK a b k := by wf_agree
def split_term : Term ⟨[.list .nat], .prod (.list .nat) (.list .nat)⟩ :=
  #lean_wf_func_to_term MoreComb.split
theorem split_agree : ∀ l, Term.eval split_term l = MoreComb.split l := by wf_agree
def countBig_term : Term ⟨[.list .nat, .nat], .nat⟩ := #lean_wf_func_to_term MoreComb.countBig
theorem countBig_agree : ∀ l k, Term.eval countBig_term l k = MoreComb.countBig l k := by
  wf_agree
def arrSum_term : Term ⟨[.array .nat], .nat⟩ := #lean_wf_func_to_term MoreComb.arrSum
theorem arrSum_agree : ∀ a, Term.eval arrSum_term a = MoreComb.arrSum a := by wf_agree
def arrSumR_term : Term ⟨[.array .nat], .nat⟩ := #lean_wf_func_to_term MoreComb.arrSumR
theorem arrSumR_agree : ∀ a, Term.eval arrSumR_term a = MoreComb.arrSumR a := by wf_agree
def arrDouble_term : Term ⟨[.array .nat], .array .nat⟩ := #lean_wf_func_to_term MoreComb.arrDouble
theorem arrDouble_agree : ∀ a, Term.eval arrDouble_term a = MoreComb.arrDouble a := by wf_agree
def arrAnyBig_term : Term ⟨[.array .nat, .nat], .bool⟩ := #lean_wf_func_to_term MoreComb.arrAnyBig
theorem arrAnyBig_agree : ∀ a k, Term.eval arrAnyBig_term a k = MoreComb.arrAnyBig a k := by
  wf_agree
def arrAllSmall_term : Term ⟨[.array .nat], .bool⟩ := #lean_wf_func_to_term MoreComb.arrAllSmall
theorem arrAllSmall_agree : ∀ a, Term.eval arrAllSmall_term a = MoreComb.arrAllSmall a := by
  wf_agree
def arrHas3_term : Term ⟨[.array .nat], .bool⟩ := #lean_wf_func_to_term MoreComb.arrHas3
theorem arrHas3_agree : ∀ a, Term.eval arrHas3_term a = MoreComb.arrHas3 a := by wf_agree
def arrRec_term : Term ⟨[.nat], .array .nat⟩ := #lean_wf_func_to_term MoreComb.arrRec
theorem arrRec_agree : ∀ n, Term.eval arrRec_term n = MoreComb.arrRec n := by wf_agree

#guard [([], []), ([1, 2, 3], [4, 5, 6]), ([1, 2], [3, 4, 5]), ([7, 0, 3], [2])].all fun (a, b) =>
  Term.eval dot_term a b == MoreComb.dot a b &&
  Term.eval addK_term a b 10 == MoreComb.addK a b 10
#guard [[], [3], [1, 2, 3, 4], [5, 0, 7], [2, 4, 12]].all fun l =>
  Term.eval split_term l == MoreComb.split l &&
  Term.eval countBig_term l 2 == MoreComb.countBig l 2 &&
  Term.eval arrSum_term l.toArray == MoreComb.arrSum l.toArray &&
  Term.eval arrSumR_term l.toArray == MoreComb.arrSumR l.toArray &&
  Term.eval arrDouble_term l.toArray == MoreComb.arrDouble l.toArray &&
  Term.eval arrAnyBig_term l.toArray 4 == MoreComb.arrAnyBig l.toArray 4 &&
  Term.eval arrAllSmall_term l.toArray == MoreComb.arrAllSmall l.toArray &&
  Term.eval arrHas3_term l.toArray == MoreComb.arrHas3 l.toArray
#guard (List.range 6).all fun n => Term.eval arrRec_term n == MoreComb.arrRec n
