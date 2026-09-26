import RequestProject.WFLang

/-!
# Recursive calls inside `List.foldl` / `List.any` / `List.all` over `List.attach`

The membership proof `x ∈ l` provided by `List.attach` is what proves the decrease of the
recursive call.  These folds are captured by the PCL statement `Expr.foldl`, whose body is
evaluated under the path condition `x ∈ l`, so the termination proof of the call can use it.
`l.attach.any p` and `l.attach.all p` are first rewritten into `List.foldl` with `||` / `&&`, and
`for` loops that use the membership proof (`for h : x in l`, or `for ⟨x, h⟩ in l.attach`), whose
body always continues, into `List.foldl` over `l.attach`.
Each function is captured with `#lean_wf_func_to_term`, and its agreement theorem is proved by
`wf_agree`.
-/

open WFLang PCL

namespace AttachComb

def depthSum (n : Nat) : Nat :=
  if n = 0 then 0 else (List.range n).attach.foldl (fun acc ⟨i, _h⟩ => acc + depthSum i) 1
termination_by n
decreasing_by simp at _h; omega

def depthSum' (n : Nat) : Nat :=
  if n = 0 then 1
  else (List.range n).attach.foldl
    (fun acc (x : {i // i ∈ List.range n}) => have : x.1 < n := List.mem_range.mp x.2; acc + 2 * depthSum' x.1) 0
termination_by n

def anyA (n : Nat) : Bool :=
  if n = 0 then true
  else (List.range n).attach.any (fun ⟨i, h⟩ => have : i < n := List.mem_range.mp h; !anyA i)
termination_by n

def allA (n : Nat) : Bool :=
  if n = 0 then true
  else (List.range n).attach.all (fun ⟨i, h⟩ => have : i < n := List.mem_range.mp h; allA i)
termination_by n

def depthSum_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term depthSum
theorem depthSum_agree : ∀ n, Term.eval depthSum_term n = depthSum n := by wf_agree

def depthSum'_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term depthSum'
theorem depthSum'_agree : ∀ n, Term.eval depthSum'_term n = depthSum' n := by wf_agree

def anyA_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term anyA
theorem anyA_agree : ∀ n, Term.eval anyA_term n = anyA n := by wf_agree

def allA_term : Term ⟨[.nat], .bool⟩ := #lean_wf_func_to_term allA
theorem allA_agree : ∀ n, Term.eval allA_term n = allA n := by wf_agree

#guard Term.eval depthSum_term 5 == depthSum 5
#guard Term.eval depthSum'_term 4 == depthSum' 4
#guard (List.range 6).all fun n => Term.eval anyA_term n == anyA n
#guard (List.range 6).all fun n => Term.eval allA_term n == allA n

def forAttach (n : Nat) : Nat := Id.run do
  if n = 0 then return 1
  let mut s := 0
  for ⟨i, h⟩ in (List.range n).attach do
    have : i < n := List.mem_range.mp h
    s := s + forAttach i
  return s
termination_by n

def forMem (n : Nat) : Nat := Id.run do
  let mut s := 1
  for h : i in List.range n do
    have : i < n := List.mem_range.mp h
    s := s + 2 * forMem i
  return s
termination_by n

def forMemIf (n : Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in List.range n do
    have : i < n := List.mem_range.mp h
    if i % 2 == 0 then s := s + forMemIf i else s := s + 1
  return s + 1
termination_by n

def forAttach_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term forAttach
theorem forAttach_agree : ∀ n, Term.eval forAttach_term n = forAttach n := by wf_agree

def forMem_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term forMem
theorem forMem_agree : ∀ n, Term.eval forMem_term n = forMem n := by wf_agree

def forMemIf_term : Term ⟨[.nat], .nat⟩ := #lean_wf_func_to_term forMemIf
theorem forMemIf_agree : ∀ n, Term.eval forMemIf_term n = forMemIf n := by wf_agree

#guard Term.eval forAttach_term 5 == forAttach 5
#guard Term.eval forMem_term 4 == forMem 4
#guard Term.eval forMemIf_term 6 == forMemIf 6

end AttachComb
