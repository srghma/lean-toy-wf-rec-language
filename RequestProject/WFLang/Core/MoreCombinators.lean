import RequestProject.WFLang.Core.ListLoops

/-!
# More combinators with a function argument: `zipWith`, `partition`, `countP`, and arrays

Like the list combinators of `Core/ListLoops.lean`, the following library functions with a
function argument are rewritten by the capture into first-order recursive functions (or into
the list combinators already supported), whose function argument is then specialised at the
call site:

* `List.zipWith f l₁ l₂`   ↦ `listZipWith f l₁ l₂` (a global function);
* `List.partition p l`     ↦ `(listFilter p l, listFilter (fun x => !p x) l)`;
* `List.countP p l`        ↦ `listFoldl (fun n x => if p x then n + 1 else n) 0 l` (a loop);
* `Array.foldl f b a`      ↦ `listFoldl f b a.toList`, `Array.foldr f b a` ↦ `listFoldr f b a.toList`;
* `Array.map f a`          ↦ `(List.map f a.toList).toArray` (a `map` statement);
* `Array.any a p`, `Array.all a p`, `Array.contains a x` ↦ `listAny`/`listAll` on `a.toList`.

The array combinators are recognised only on the whole array (the default bounds `start = 0`,
`stop = a.size`).  The equations below are in the simp set `wflang_eval` used by the agreement
proofs.
-/

namespace WFLang

/-- `List.zipWith`, by well-founded recursion. -/
def listZipWith {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) : List γ :=
  match l₁ with
  | [] => []
  | x :: xs =>
    match l₂ with
    | [] => []
    | y :: ys => f x y :: listZipWith f xs ys
termination_by l₁.length

theorem zipWith_eq_listZipWith {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) :
    List.zipWith f l₁ l₂ = listZipWith f l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rw [listZipWith]; rfl
  | cons x xs ih =>
    cases l₂ with
    | nil => rw [listZipWith]; rfl
    | cons y ys => rw [listZipWith, List.zipWith_cons_cons, ih]

theorem partition_eq_listFilter {α : Type} (p : α → Bool) (l : List α) :
    l.partition p = (listFilter p l, listFilter (fun x => !p x) l) := by
  rw [List.partition_eq_filter_filter, filter_eq_listFilter, filter_eq_listFilter]
  rfl

theorem countP_eq_listFoldl {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = listFoldl (fun n x => if p x then n + 1 else n) 0 l := by
  rw [← foldl_eq_listFoldl]
  suffices h : ∀ k, List.foldl (fun n x => if p x = true then n + 1 else n) k l = k + l.countP p by
    rw [h]; simp
  induction l with
  | nil => intro k; simp
  | cons x xs ih =>
    intro k
    rw [List.foldl_cons, ih, List.countP_cons]
    cases p x <;> simp <;> omega

theorem array_foldl_eq_listFoldl {α β : Type} (f : β → α → β) (b : β) (a : Array α) :
    a.foldl f b = listFoldl f b a.toList := by
  rw [← foldl_eq_listFoldl, Array.foldl_toList]

theorem array_foldr_eq_listFoldr {α β : Type} (f : α → β → β) (b : β) (a : Array α) :
    a.foldr f b = listFoldr f b a.toList := by
  rw [← foldr_eq_listFoldr, Array.foldr_toList]

theorem array_map_eq_list_map {α β : Type} (f : α → β) (a : Array α) :
    a.map f = (a.toList.map f).toArray := by
  rcases a with ⟨l⟩
  simp

theorem array_any_eq_listAny {α : Type} (p : α → Bool) (a : Array α) :
    a.any p = listAny p a.toList := by
  rw [← any_eq_listAny, Array.any_toList]

theorem array_all_eq_listAll {α : Type} (p : α → Bool) (a : Array α) :
    a.all p = listAll p a.toList := by
  rw [← all_eq_listAll, Array.all_toList]

theorem array_contains_eq_listAny {α : Type} [BEq α] (a : Array α) (x : α) :
    a.contains x = listAny (fun y => x == y) a.toList := by
  rw [← any_eq_listAny]
  rcases a with ⟨l⟩
  simp only [List.contains_toArray, List.contains_eq_any_beq]

attribute [wflang_eval ↓ high] zipWith_eq_listZipWith partition_eq_listFilter countP_eq_listFoldl
  array_foldl_eq_listFoldl array_foldr_eq_listFoldr array_map_eq_list_map array_any_eq_listAny
  array_all_eq_listAll array_contains_eq_listAny

end WFLang
