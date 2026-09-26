module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# The answers a fold of a family binds inside a field

The fold of a family (`Term.mutualRecursiveFamily_rec`) binds, right after a field that
holds occurrences of members only **inside** it — `Array (familyMember i)`, a function
into a member, a delay of one — the answers at those occurrences, in the field's own
shape (`TyWf.famAnswerBinders`, evaluated by `famAnswerEnv`).  This is what lets
`#leanscript_to_term` translate a recursion through an array inside a family
(`List (Array T)`, `Array (List T)`, an array of another member of a `mutual` block).

This file proves what that binder holds:

* `TyWf.famAnswerBinders_of_hasMemberOcc`, `TyWf.famAnswerBinders_of_not_hasMemberOcc`:
  the binder is there exactly when the field holds an occurrence of a member.
* `famBindField_array`, `famAnswerField_array`: at a field `Array (familyMember i)`, the
  field is the array of the subtrees in its holes, and the binder beside it the array of
  the answers stored with them — the same memos, in the same order.
* `famAnswerField_array_memo`, `famBindField_array_memo`: at a node as the evaluator builds
  it (each hole holding the memo of its subtree, `IWType.memo`), the binder is, element by
  element, the value of the fold (`IWType.memoFold`) at the corresponding element of the
  field.
-/

namespace LeanScript

open IPFunctor

/-- The binder after a field is there when the field holds an occurrence of a member. -/
theorem TyWf.famAnswerBinders_of_hasMemberOcc {n : Nat} (τ : TyWf) (a : TyWfIn (n + 2))
    (rest : List TyWf) (h : Ty.hasMemberOcc a.toTy = true) :
    TyWf.famAnswerBinders τ a rest = TyWf.famAnswerMap τ a :: rest := by
  simp [TyWf.famAnswerBinders, h]

/-- … and absent when it does not. -/
theorem TyWf.famAnswerBinders_of_not_hasMemberOcc {n : Nat} (τ : TyWf) (a : TyWfIn (n + 2))
    (rest : List TyWf) (h : Ty.hasMemberOcc a.toTy = false) :
    TyWf.famAnswerBinders τ a rest = rest := by
  simp [TyWf.famAnswerBinders, h]

/-- The binder after an array of a member is the array of the motive. -/
example {n : Nat} (τ : TyWf) (i : Nat)
    (h : Ty.WfIn (n + 2) (.shape (.primCovariant (.array (.familyMember i))))) :
    (TyWf.famAnswerMap τ ⟨_, h⟩).toTy = .shape (.primCovariant (.array τ.toTy)) := rfl

/-- Reading the list of a changed extension is reading the list with the change. -/
theorem IPFunctor.Obj.toList_map_holes {c : IPFunctor} {X Y : Nat → Type} {α : Type}
    (h : c.Obj Y → α) (g : ∀ j, X j → Y j) :
    ∀ (xs : List c.A) (k : (p : PFunctor.ListPos c.B xs) → X (listTgt c xs p)),
      Obj.toList h xs (fun p => g _ (k p)) = Obj.toList (fun y => h (y.map g)) xs k
  | [], _ => rfl
  | s :: ss, k => by
      simp only [Obj.toList]
      exact congrArg _ (IPFunctor.Obj.toList_map_holes h g ss (fun q => k (.inr q)))

/-- Reading the list through a function after the reading is mapping that function. -/
theorem IPFunctor.Obj.toList_map_list {c : IPFunctor} {X : Nat → Type} {α β : Type}
    (h : c.Obj X → α) (g : α → β) :
    ∀ (xs : List c.A) (k : (p : PFunctor.ListPos c.B xs) → X (listTgt c xs p)),
      Obj.toList (fun y => g (h y)) xs k = (Obj.toList h xs k).map g
  | [], _ => rfl
  | s :: ss, k => by
      simp only [Obj.toList, List.map_cons]
      exact congrArg _ (IPFunctor.Obj.toList_map_list h g ss (fun q => k (.inr q)))

/-- `IPFunctor.Obj.toList_map_holes`, for an array. -/
theorem IPFunctor.Obj.toArray_map {c : IPFunctor} {X Y : Nat → Type} {α : Type}
    (h : c.Obj Y → α) (g : ∀ j, X j → Y j) (x : (array c).Obj X) :
    Obj.toArray h (x.map g) = Obj.toArray (fun y => h (y.map g)) x :=
  congrArg Array.mk (IPFunctor.Obj.toList_map_holes h g _ _)

/-- `IPFunctor.Obj.toList_map_list`, for an array. -/
theorem IPFunctor.Obj.toArray_comp {c : IPFunctor} {X : Nat → Type} {α β : Type}
    (h : c.Obj X → α) (g : α → β) (x : (array c).Obj X) :
    (Obj.toArray (fun y => g (h y)) x).toList = (Obj.toArray h x).toList.map g :=
  IPFunctor.Obj.toList_map_list h g _ _

/-- `Obj.toArray` of an array with its holes changed, read through another reading of the
    elements. -/
theorem IPFunctor.Obj.toArray_map_comp {c : IPFunctor} {X Y : Nat → Type} {α β : Type}
    (h : c.Obj Y → α) (g : ∀ j, X j → Y j) (k : c.Obj X → β) (l : β → α)
    (hk : ∀ y, h (y.map g) = l (k y)) (x : (array c).Obj X) :
    (Obj.toArray h (x.map g)).toList = (Obj.toArray k x).toList.map l := by
  rw [IPFunctor.Obj.toArray_map, show (fun y => h (y.map g)) = fun y => l (k y) from funext hk]
  exact IPFunctor.Obj.toArray_comp k l x

section
variable {n : Nat} (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)) (τ : TyWf) (i : Nat)
    (h : Ty.WfIn (n + 2) (.shape (.primCovariant (.array (.familyMember i)))))
    (e : (IPFunctor.array (Ty.toIPF (.familyMember i))).Obj (FamMemoAt f.members τ))

/-- The memo in the one hole of an occurrence `Ty.familyMember i`. -/
def famHoleMemo (y : (Ty.toIPF (.familyMember i)).Obj (FamMemoAt f.members τ)) :
    FamMemoAt f.members τ i :=
  y.2 PUnit.unit

/-- The memos of the elements of an array field. -/
def famArrayMemos : List (FamMemoAt f.members τ i) :=
  (Obj.toArray (famHoleMemo f τ i) e).toList

/-- At a field `Array (familyMember i)`, the field is the array of the subtrees in its
    holes. -/
theorem famBindField_array : Array.toList (α := TyWf.Den (TyWf.famMemberTy f hwf i)) (famBindField f hwf τ ⟨_, h⟩ e) =
    (famArrayMemos f τ i e).map (famSubtree f hwf τ i) := by
  simp only [famBindField, Ty.famUnroll, Ty.famUnrollShape, Ty.famUnrollCov]
  exact IPFunctor.Obj.toArray_map_comp _ _ (famHoleMemo f τ i) (famSubtree f hwf τ i)
    (fun _ => rfl) e

/-- At a field `Array (familyMember i)`, the binder beside it is the array of the answers
    stored with the same memos. -/
theorem famAnswerField_array : Array.toList (α := TyWf.Den τ) (famAnswerField τ f.members ⟨_, h⟩ e) =
    (famArrayMemos f τ i e).map FamMemo.answer := by
  simp only [famAnswerField, Ty.famUnroll, Ty.famUnrollShape, Ty.famUnrollCov]
  exact IPFunctor.Obj.toArray_map_comp _ _ (famHoleMemo f τ i) FamMemo.answer (fun _ => rfl) e

/-- The subtree in the one hole of an occurrence `Ty.familyMember i`. -/
def famHoleTree
    (y : (Ty.toIPF (.familyMember i)).Obj
      (fun j => FamW (famFs f.members) (selIdx (famFs f.members).length j))) :
    FamW (famFs f.members) (selIdx (famFs f.members).length i) :=
  y.2 PUnit.unit

/-- The elements of an array field of a node, as subtrees. -/
def famArrayTrees (e₀ : (IPFunctor.array (Ty.toIPF (.familyMember i))).Obj
      (fun j => FamW (famFs f.members) (selIdx (famFs f.members).length j))) :
    List (FamW (famFs f.members) (selIdx (famFs f.members).length i)) :=
  (Obj.toArray (famHoleTree f i) e₀).toList

/-- At a node as the evaluator builds it, the memos in the holes of an array field are the
    memos of its elements. -/
theorem famArrayMemos_memo
    (step : (j : Nat) → (a : (IPFunctor.at (famFs f.members) j).A) →
      ((b : (IPFunctor.at (famFs f.members) j).B a) →
        FamMemo (famFs f.members) (TyWf.Den τ)
          (selIdx (famFs f.members).length ((IPFunctor.at (famFs f.members) j).tgt a b))) →
      TyWf.Den τ)
    (e₀ : (IPFunctor.array (Ty.toIPF (.familyMember i))).Obj
      (fun j => FamW (famFs f.members) (selIdx (famFs f.members).length j))) :
    famArrayMemos f τ i (e₀.map fun _ t => IWType.memo step t) =
      (famArrayTrees f i e₀).map (IWType.memo step) :=
  IPFunctor.Obj.toArray_map_comp _ _ (famHoleTree f i) (IWType.memo step) (fun _ => rfl) e₀

/-- **The answers bound beside an array field are the fold's values at its elements.**  At a
    node of the fold of a family, whose holes hold the memos of the subtrees (as the
    evaluator builds them, `IWType.memo`), the array the fold binds after a field
    `Array (familyMember i)` is, element by element, the value of the fold
    (`IWType.memoFold`) at the corresponding element of the field. -/
theorem famAnswerField_array_memo
    (step : (j : Nat) → (a : (IPFunctor.at (famFs f.members) j).A) →
      ((b : (IPFunctor.at (famFs f.members) j).B a) →
        FamMemo (famFs f.members) (TyWf.Den τ)
          (selIdx (famFs f.members).length ((IPFunctor.at (famFs f.members) j).tgt a b))) →
      TyWf.Den τ)
    (e₀ : (IPFunctor.array (Ty.toIPF (.familyMember i))).Obj
      (fun j => FamW (famFs f.members) (selIdx (famFs f.members).length j))) :
    Array.toList (α := TyWf.Den τ)
        (famAnswerField τ f.members ⟨_, h⟩ (e₀.map fun _ t => IWType.memo step t)) =
      (famArrayTrees f i e₀).map (IWType.memoFold step) := by
  rw [famAnswerField_array, famArrayMemos_memo, List.map_map]
  rfl

/-- The field itself, at such a node, is the array of those same elements, each read as a
    value of member `i`. -/
theorem famBindField_array_memo
    (step : (j : Nat) → (a : (IPFunctor.at (famFs f.members) j).A) →
      ((b : (IPFunctor.at (famFs f.members) j).B a) →
        FamMemo (famFs f.members) (TyWf.Den τ)
          (selIdx (famFs f.members).length ((IPFunctor.at (famFs f.members) j).tgt a b))) →
      TyWf.Den τ)
    (e₀ : (IPFunctor.array (Ty.toIPF (.familyMember i))).Obj
      (fun j => FamW (famFs f.members) (selIdx (famFs f.members).length j))) :
    Array.toList (α := TyWf.Den (TyWf.famMemberTy f hwf i))
        (famBindField f hwf τ ⟨_, h⟩ (e₀.map fun _ t => IWType.memo step t)) =
      (famArrayTrees f i e₀).map (fun t => cast (den_famMemberTy f hwf i).symm t) := by
  rw [famBindField_array, famArrayMemos_memo, List.map_map]
  refine congrArg (List.map · _) (funext fun t => ?_)
  show cast _ (IWType.Memo.tree (IWType.memo step t)) = _
  rw [IWType.memo_tree]

end


end LeanScript

end
