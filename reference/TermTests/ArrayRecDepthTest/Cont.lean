module

public import TermTests.ArrayRecKTest
public import TermTests.FibWindowTest
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over arrays: the continuant at depths one to three

The signature `sigArith` the suite runs in, and the first two sections of
`TermTests/ArrayRecDepthTest.lean`: `cont` at depth one, and `cont3`, `cont4` at depths two and
three.  The overview of the suite is in `TermTests/ArrayRecDepthTest.lean`.
-/

namespace TermTests.ArrayRecDepth

open LeanScript
open TermTests.ArrayRecK (natT cont cont3 cont4 listFoldK_eq_cont listFoldK_eq_cont3
  listFoldK_eq_cont4)
open TermTests.FibWindow (fib)

/-- A signature with two declarations, `add` and `mul`, both `nat ⇒ nat ⇒ nat`. -/
def sigArith : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"mul", natT ⇒ natT ⇒ natT⟩], by decide⟩

/-- The values of the declarations of `sigArith`. -/
def envArith : GlobalEnv sigArith.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigArith`. -/
local macro:max "runArith" t:term:max : term => `(Term.run (Sg := sigArith) envArith $t)

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigArith Γ natT) : Term sigArith Γ natT :=
  .ap (.ap (.global .here) a) b

/-- `mul a b`, for two terms in hand. -/
def mulT {Γ : Ctx} (a b : Term sigArith Γ natT) : Term sigArith Γ natT :=
  .ap (.ap (.global (.there .here)) a) b

/-- The context the folds below are written in: the array they fold over. -/
abbrev ArrCtx : Ctx := [TyWf.array natT]

/-! ## 0. The programs

Each term of the suite is a Lean program on the elements of an array — a structurally
recursive function on `List Nat`, applied to `a.toList` — translated by
`#leanscript_to_term`, which reads such a recursion as `array_rec k` (see
`TermTests/ArrayRecToTermTest/Common.lean`).  The bases and the branch the proofs name are
read back out of the translated term with `#leanscript_fold_bases` and
`#leanscript_fold_branch`. -/

/-- The continuant of the elements of an array. -/
def contArr (a : Array Nat) : Nat := cont a.toList

/-- `cont3` of the elements of an array. -/
def cont3Arr (a : Array Nat) : Nat := cont3 a.toList

/-- `cont4` of the elements of an array. -/
def cont4Arr (a : Array Nat) : Nat := cont4 a.toList

/-! ## 1. `cont` at depth one

The lists of at most one element are answered by the `ArrayRecBases`: the empty list by
`1`, and a one-element list by its element, which the block **binds**.  The branch, at
`a :: as` with `as` non-empty, binds `a` (index `0`), `as` (index `1`), the answer at `as`
(index `2`) and the answer at `as.drop 1` (index `3`). -/

/-- The continuant, as a term of the grammar: the depth-one fold of an array,
    `.lam (.array_rec' 1 (.var (v♯0)) contBases contBranch)`. -/
def contTerm : Term sigArith [] (TyWf.array natT ⇒ natT) := #leanscript_to_term contArr

/-- The answers for the short lists: `K [] = 1` and `K [a] = a`, that is
    `.cons (.nat_mk 1) (.nil (.var (v♯0)))`. -/
def contBases : ArrayRecBases sigArith ArrCtx natT natT 1 := #leanscript_fold_bases contTerm

/-- The branch: `a * K as + K (as.drop 1)`, that is
    `addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))`. -/
def contBranch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 2 ArrCtx) natT :=
  #leanscript_fold_branch contTerm

-- [SKIPPED BY PROFILE_LAKE] example : contTerm = .lam (.array_rec' 1 (.var (v♯0)) contBases contBranch) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contBases = .cons (.nat_mk 1) (.nil (.var (v♯0))) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : contBranch = addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3)) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runArith contTerm #[] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTerm #[3] = 3 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTerm #[3, 4] = 13 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTerm #[1, 2, 3] = 10 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith contTerm #[1, 1, 1, 1, 1, 1] = 13 := by kernel_rfl

/-- The fold `Term.eval` runs for `contTerm`, in an arbitrary environment: the short
    lists go to `contBases` and the branch runs with the window in front of the
    environment. -/
def contEvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 1)
    (fun m => ArrayRecBases.eval envArith contBases env m)
    (fun hd tl w => Term.eval envArith contBranch ((hd, tl.toArray, Env.ofWin w env)))

/-- That fold is the continuant — by the two equations of `LeanScript.ArrayRecFacts`,
    whatever the environment is. -/
theorem contEvalFold_eq (env : Env ArrCtx) (l : List Nat) : contEvalFold env l = cont l :=
  listFoldK_eq_cont _ _ rfl (fun _ => rfl) (fun _ _ _ => rfl) l

/-- **The term computes the continuant, at every list** — not only at the ones checked by
    `rfl` above. -/
theorem contTerm_eval (l : List Nat) : runArith contTerm l.toArray = cont l :=
  contEvalFold_eq (l.toArray, Env.nil) l

/-! ### The continuant is `fib`

On a list of `n` ones every coefficient is `1`, so the recursion is `fib`'s own. -/

/-- `K (1, …, 1)` with `n` ones is `fib (n + 1)`. -/
theorem cont_replicate_one : (n : Nat) → cont (List.replicate n 1) = fib (n + 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show 1 * cont (List.replicate (n + 1) 1) + cont (List.replicate n 1) = fib (n + 3)
      rw [cont_replicate_one (n + 1), cont_replicate_one n,
        show fib (n + 3) = fib (n + 1) + fib (n + 2) from rfl,
        show n + 1 + 1 = n + 2 from rfl]
      omega

/-- So the term of the grammar computes `fib`, on the arrays of ones. -/
theorem contTerm_eval_ones (n : Nat) :
    runArith contTerm (List.replicate n 1).toArray = fib (n + 1) := by
  rw [contTerm_eval, cont_replicate_one]

/-! ## 2. Three and four suffixes: the same node at depth two and three

`cont3` and `cont4` are to `cont` what the tribonacci and tetranacci numbers are to
`fib`.  Nothing changes but the depth: one more short list to answer, and one more entry
in the window. -/

/-- `cont3`, as a term: the depth-two fold of an array. -/
def cont3Term : Term sigArith [] (TyWf.array natT ⇒ natT) := #leanscript_to_term cont3Arr

/-- The answers for the short lists of the depth-two fold: `1`, `a`, `a * b`.  In the
    last one the first element is bound outermost, so `a` is index `1` and `b` index
    `0`. -/
def cont3Bases : ArrayRecBases sigArith ArrCtx natT natT 2 := #leanscript_fold_bases cont3Term

/-- The branch of the depth-two fold: `a * K as + K (as.drop 1) + K (as.drop 2)`. -/
def cont3Branch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 3 ArrCtx) natT :=
  #leanscript_fold_branch cont3Term

-- [SKIPPED BY PROFILE_LAKE] example : cont3Term = .lam (.array_rec' 2 (.var (v♯0)) cont3Bases cont3Branch) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont3Bases =
-- [SKIPPED BY PROFILE_LAKE]     .cons (.nat_mk 1) (.cons (.var (v♯0)) (.nil (mulT (.var (v♯1)) (.var (v♯0))))) := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont3Branch =
-- [SKIPPED BY PROFILE_LAKE]     addT (addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))) (.var (v♯4)) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runArith cont3Term #[] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith cont3Term #[5, 6] = 30 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith cont3Term #[1, 1, 1, 1, 1, 1] = 17 := by kernel_rfl

/-- The fold `Term.eval` runs for `cont3Term`. -/
def cont3EvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 2)
    (fun m => ArrayRecBases.eval envArith cont3Bases env m)
    (fun hd tl w => Term.eval envArith cont3Branch ((hd, tl.toArray, Env.ofWin w env)))

theorem cont3EvalFold_eq (env : Env ArrCtx) (l : List Nat) : cont3EvalFold env l = cont3 l :=
  listFoldK_eq_cont3 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) l

/-- The depth-two term computes `cont3`, at every list. -/
theorem cont3Term_eval (l : List Nat) : runArith cont3Term l.toArray = cont3 l :=
  cont3EvalFold_eq (l.toArray, Env.nil) l

/-- `cont4`, as a term: the depth-three fold of an array. -/
def cont4Term : Term sigArith [] (TyWf.array natT ⇒ natT) := #leanscript_to_term cont4Arr

/-- The answers for the short lists of the depth-three fold: `1`, `a`, `a * b`,
    `a * b * c`. -/
def cont4Bases : ArrayRecBases sigArith ArrCtx natT natT 3 := #leanscript_fold_bases cont4Term

/-- The branch of the depth-three fold: the head times the nearest answer, plus the other
    three the window holds. -/
def cont4Branch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 4 ArrCtx) natT :=
  #leanscript_fold_branch cont4Term

-- [SKIPPED BY PROFILE_LAKE] example : cont4Term = .lam (.array_rec' 3 (.var (v♯0)) cont4Bases cont4Branch) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont4Bases =
-- [SKIPPED BY PROFILE_LAKE]     .cons (.nat_mk 1)
-- [SKIPPED BY PROFILE_LAKE]       (.cons (.var (v♯0))
-- [SKIPPED BY PROFILE_LAKE]         (.cons (mulT (.var (v♯1)) (.var (v♯0)))
-- [SKIPPED BY PROFILE_LAKE]           (.nil (mulT (mulT (.var (v♯2)) (.var (v♯1))) (.var (v♯0)))))) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : cont4Branch =
-- [SKIPPED BY PROFILE_LAKE]     addT (addT (addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))) (.var (v♯4)))
-- [SKIPPED BY PROFILE_LAKE]       (.var (v♯5)) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] example : runArith cont4Term #[] = 1 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith cont4Term #[2, 3, 4] = 24 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : runArith cont4Term #[1, 1, 1, 1, 1, 1] = 13 := by kernel_rfl

/-- The fold `Term.eval` runs for `cont4Term`. -/
def cont4EvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 3)
    (fun m => ArrayRecBases.eval envArith cont4Bases env m)
    (fun hd tl w => Term.eval envArith cont4Branch ((hd, tl.toArray, Env.ofWin w env)))

theorem cont4EvalFold_eq (env : Env ArrCtx) (l : List Nat) : cont4EvalFold env l = cont4 l :=
  listFoldK_eq_cont4 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) l

/-- The depth-three term computes `cont4`, at every list. -/
theorem cont4Term_eval (l : List Nat) : runArith cont4Term l.toArray = cont4 l :=
  cont4EvalFold_eq (l.toArray, Env.nil) l

end TermTests.ArrayRecDepth

end
