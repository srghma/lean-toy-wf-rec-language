import RequestProject.WFLang.Core.Loops
import RequestProject.WFLang.Core.EvalSimpAttr

/-!
# List combinators as first-order recursive functions

The library combinators on lists that take a function argument (`List.foldl`, `List.foldr`,
`List.any`, `List.all`, `List.contains`, `List.elem`, `List.find?`, `List.filter`, and `for x in l`
loops in `Id` that always continue) are rewritten by the capture into the well-founded
functions below, whose function argument is then specialised to the (known) argument of the call,
exactly as `rangeLoop` is for loops over ranges.  A tail-recursive one becomes a loop (a recursive
join point) at the call site, the others (`listFoldr`, `listFilter`) global functions.

The equations `List.foldl f b l = listFoldl f b l`, … are in the simp set `wflang_eval` used by the
agreement proofs.  `foldl_eq_listFoldl` has a low priority, so that a `for` loop over a range,
which the simplifier turns into a `List.foldl` over `List.range'`, still becomes a `rangeLoop`
(`foldl_range'_eq_rangeLoop`); the others are pre-rewriting lemmas (`↓`) with a high priority, so that they
apply before the library's simp lemmas turn e.g. `l.contains a` into `decide (a ∈ l)`.
-/

namespace WFLang

/-- `List.foldl`, by well-founded recursion. -/
def listFoldl {α β : Type} (f : β → α → β) (b : β) (l : List α) : β :=
  match l with
  | [] => b
  | x :: xs => listFoldl f (f b x) xs
termination_by l.length

/-- `List.foldr`, by well-founded recursion. -/
def listFoldr {α β : Type} (f : α → β → β) (b : β) (l : List α) : β :=
  match l with
  | [] => b
  | x :: xs => f x (listFoldr f b xs)
termination_by l.length

/-- `List.any`, by well-founded recursion. -/
def listAny {α : Type} (p : α → Bool) (l : List α) : Bool :=
  match l with
  | [] => false
  | x :: xs => if p x then true else listAny p xs
termination_by l.length

/-- `List.all`, by well-founded recursion. -/
def listAll {α : Type} (p : α → Bool) (l : List α) : Bool :=
  match l with
  | [] => true
  | x :: xs => if p x then listAll p xs else false
termination_by l.length

/-- `List.find?`, by well-founded recursion. -/
def listFind? {α : Type} (p : α → Bool) (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: xs => if p x then some x else listFind? p xs
termination_by l.length

/-- `List.filter`, by well-founded recursion. -/
def listFilter {α : Type} (p : α → Bool) (l : List α) : List α :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: listFilter p xs else listFilter p xs
termination_by l.length

theorem foldl_eq_listFoldl {α β : Type} (f : β → α → β) (b : β) (l : List α) :
    List.foldl f b l = listFoldl f b l := by
  induction l generalizing b with
  | nil => rw [listFoldl]; rfl
  | cons x xs ih => rw [listFoldl, List.foldl_cons, ih]

theorem foldr_eq_listFoldr {α β : Type} (f : α → β → β) (b : β) (l : List α) :
    List.foldr f b l = listFoldr f b l := by
  induction l with
  | nil => rw [listFoldr]; rfl
  | cons x xs ih => rw [listFoldr, List.foldr_cons, ih]

theorem any_eq_listAny {α : Type} (l : List α) (p : α → Bool) : l.any p = listAny p l := by
  induction l with
  | nil => rw [listAny]; rfl
  | cons x xs ih => rw [listAny, List.any_cons, ih]; cases p x <;> simp

theorem all_eq_listAll {α : Type} (l : List α) (p : α → Bool) : l.all p = listAll p l := by
  induction l with
  | nil => rw [listAll]; rfl
  | cons x xs ih => rw [listAll, List.all_cons, ih]; cases p x <;> simp

theorem contains_eq_listAny {α : Type} [BEq α] (l : List α) (a : α) :
    l.contains a = listAny (fun x => a == x) l := by
  rw [List.contains_eq_any_beq, any_eq_listAny]

theorem elem_eq_listAny {α : Type} [BEq α] (a : α) (l : List α) :
    l.elem a = listAny (fun x => a == x) l := by
  rw [List.elem_eq_contains, contains_eq_listAny]

theorem find?_eq_listFind? {α : Type} (p : α → Bool) (l : List α) :
    l.find? p = listFind? p l := by
  induction l with
  | nil => rw [listFind?]; rfl
  | cons x xs ih => rw [listFind?, List.find?_cons, ih]; cases p x <;> simp

theorem filter_eq_listFilter {α : Type} (p : α → Bool) (l : List α) :
    l.filter p = listFilter p l := by
  induction l with
  | nil => rw [listFilter]; rfl
  | cons x xs ih => rw [listFilter, List.filter_cons, ih]

/-! ## Bounded quantifiers

A decidable proposition with a bounded quantifier (`∀ i < n, P i`, `∃ i < n, P i`, `∀ x ∈ l, P x`,
`∃ x ∈ l, P x`), in `decide` or in the test of an `if`, is captured as a call of `listAll` or
`listAny` (on `List.range n`, resp. on `l`). -/

theorem forall_lt_iff_listAll {P : Nat → Prop} [DecidablePred P] (n : Nat) :
    (∀ i, i < n → P i) ↔ listAll (fun i => decide (P i)) (List.range n) = true := by
  rw [← all_eq_listAll]; simp

theorem exists_lt_iff_listAny {P : Nat → Prop} [DecidablePred P] (n : Nat) :
    (∃ i, i < n ∧ P i) ↔ listAny (fun i => decide (P i)) (List.range n) = true := by
  rw [← any_eq_listAny]; simp

theorem forall_mem_iff_listAll {α : Type} {P : α → Prop} [DecidablePred P] (l : List α) :
    (∀ x, x ∈ l → P x) ↔ listAll (fun x => decide (P x)) l = true := by
  rw [← all_eq_listAll]; simp

theorem exists_mem_iff_listAny {α : Type} {P : α → Prop} [DecidablePred P] (l : List α) :
    (∃ x, x ∈ l ∧ P x) ↔ listAny (fun x => decide (P x)) l = true := by
  rw [← any_eq_listAny]; simp

/-! The agreement proofs rewrite the bounded quantifiers only where the capture does: in
`decide` and in the test of an `if` (a proposition elsewhere in a proof is left alone). -/

section
variable {α β : Type} {P : α → Prop} [DecidablePred P] {Q : Nat → Prop} [DecidablePred Q]

theorem decide_forall_lt (n : Nat) [Decidable (∀ i, i < n → Q i)] :
    decide (∀ i, i < n → Q i) = listAll (fun i => decide (Q i)) (List.range n) := by
  simp only [forall_lt_iff_listAll, Bool.decide_eq_true]

theorem decide_exists_lt (n : Nat) [Decidable (∃ i, i < n ∧ Q i)] :
    decide (∃ i, i < n ∧ Q i) = listAny (fun i => decide (Q i)) (List.range n) := by
  simp only [exists_lt_iff_listAny, Bool.decide_eq_true]

theorem decide_forall_mem (l : List α) [Decidable (∀ x, x ∈ l → P x)] :
    decide (∀ x, x ∈ l → P x) = listAll (fun x => decide (P x)) l := by
  simp only [forall_mem_iff_listAll, Bool.decide_eq_true]

theorem decide_exists_mem (l : List α) [Decidable (∃ x, x ∈ l ∧ P x)] :
    decide (∃ x, x ∈ l ∧ P x) = listAny (fun x => decide (P x)) l := by
  simp only [exists_mem_iff_listAny, Bool.decide_eq_true]

theorem ite_forall_lt (n : Nat) [Decidable (∀ i, i < n → Q i)] (a b : β) :
    (if ∀ i, i < n → Q i then a else b) =
      if listAll (fun i => decide (Q i)) (List.range n) = true then a else b := by
  simp only [forall_lt_iff_listAll]

theorem ite_exists_lt (n : Nat) [Decidable (∃ i, i < n ∧ Q i)] (a b : β) :
    (if ∃ i, i < n ∧ Q i then a else b) =
      if listAny (fun i => decide (Q i)) (List.range n) = true then a else b := by
  simp only [exists_lt_iff_listAny]

theorem ite_forall_mem (l : List α) [Decidable (∀ x, x ∈ l → P x)] (a b : β) :
    (if ∀ x, x ∈ l → P x then a else b) =
      if listAll (fun x => decide (P x)) l = true then a else b := by
  simp only [forall_mem_iff_listAll]

theorem ite_exists_mem (l : List α) [Decidable (∃ x, x ∈ l ∧ P x)] (a b : β) :
    (if ∃ x, x ∈ l ∧ P x then a else b) =
      if listAny (fun x => decide (P x)) l = true then a else b := by
  simp only [exists_mem_iff_listAny]
end

attribute [wflang_eval ↓ high] decide_forall_lt decide_exists_lt decide_forall_mem
  decide_exists_mem ite_forall_lt ite_exists_lt ite_forall_mem ite_exists_mem

attribute [wflang_eval low] foldl_eq_listFoldl
attribute [wflang_eval ↓ high] foldr_eq_listFoldr any_eq_listAny all_eq_listAll contains_eq_listAny
  elem_eq_listAny find?_eq_listFind? filter_eq_listFilter

end WFLang

/-! ## Loops that may stop early, and loops over ranges with a step

`for` loops (in `Id`) whose body may stop (`break`, `return`, i.e. `ForInStep.done`), and loops over
ranges with a step `[a:b:s]`, are captured as the following loops.  The body `f` returns a
`ForInStep`: `.yield b` goes on with `b`, `.done b` stops with `b`.  The capture pushes the case
split on `f i b` into the branches of the body (`Translate.pushCases?`), so that no `ForInStep`
value remains in the program. -/

namespace WFLang

/-- `n` iterations at `i, i + s, i + 2s, …` of a body that may stop early. -/
def rangeLoopN {β : Type} (f : Nat → β → ForInStep β) (n s i : Nat) (b : β) : β :=
  match n with
  | 0 => b
  | n + 1 =>
    match f i b with
    | .done b' => b'
    | .yield b' => rangeLoopN f n s (i + s) b'
termination_by n

/-- A loop over the elements of a list, with a body that may stop early. -/
def listLoopN {α β : Type} (f : α → β → ForInStep β) (l : List α) (b : β) : β :=
  match l with
  | [] => b
  | x :: xs =>
    match f x b with
    | .done b' => b'
    | .yield b' => listLoopN f xs b'
termination_by l.length

theorem forIn_range'_eq_rangeLoopN {β : Type} (i n s : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn (List.range' i n s) init f = pure (rangeLoopN (fun a b => (f a b).run) n s i init) := by
  induction n generalizing i init with
  | zero => rw [rangeLoopN]; rfl
  | succ n ih =>
    rw [rangeLoopN, List.range'_succ, List.forIn_cons]
    change (match (f i init).run with
      | .done b => pure b
      | .yield b => forIn (List.range' (i + s) n s) b f : Id β) = _
    cases (f i init).run with
    | done b => rfl
    | yield b => exact ih (i + s) b

theorem forIn_eq_listLoopN {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) :
    forIn l init f = pure (listLoopN (fun a b => (f a b).run) l init) := by
  induction l generalizing init with
  | nil => rw [listLoopN]; rfl
  | cons x xs ih =>
    rw [listLoopN, List.forIn_cons]
    change (match (f x init).run with
      | .done b => pure b
      | .yield b => forIn xs b f : Id β) = _
    cases (f x init).run with
    | done b => rfl
    | yield b => exact ih b

theorem foldl_range'_eq_rangeLoopN {β : Type} (g : β → Nat → β) (i n s : Nat) (b : β) :
    List.foldl g b (List.range' i n s) = rangeLoopN (fun a b => .yield (g b a)) n s i b := by
  induction n generalizing i b with
  | zero => rw [rangeLoopN]; rfl
  | succ n ih => rw [rangeLoopN, List.range'_succ, List.foldl_cons, ih]

attribute [wflang_eval 500] forIn_range'_eq_rangeLoopN foldl_range'_eq_rangeLoopN
attribute [wflang_eval low] forIn_eq_listLoopN

end WFLang
