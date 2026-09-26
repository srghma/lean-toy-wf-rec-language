module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# What `Term.array_rec k` means

`LeanScript.Term.array_rec k` is the fold of an array that descends `k + 1` elements: at
a list `a :: as` whose tail is at least `k` long its branch is given the head, the tail,
and the answers at the `k + 1` suffixes `as`, `as.drop 1`, …, `as.drop k` — nearest
first — while the lists of at most `k` elements are answered by
`LeanScript.ArrayRecBases`, which binds their elements.  `LeanScript.Eval` evaluates the
node with `LeanScript.listFoldK`, which carries those `k + 1` answers as a **window** and
shifts a new one in at each element.

This file says what that fold computes, in full generality and at every depth:

* `listFoldK_base` — below the depth, the answer at `l` is the short-list answer for `l`;
* `listFoldK_step` — at and above it, the answer at `a :: as` is the branch applied to
  the window of the answers at the suffixes of `as`;
* `listFoldKAux_eq_ofFunList` — the invariant that makes the second statement say what it
  should: the window the fold carries **is** the tuple of the answers at the suffixes,
  which is why the fold is linear and no answer is ever recomputed;
* `listFoldK_eq_listFold` — the depth-zero instance **is** the one-element fold
  `LeanScript.listFold`, so the node's default depth is the old `List.rec`;
* `Term.eval_array_rec`, `Term.eval_array_rec_base` and `Term.eval_array_rec_step` — the
  same facts for the grammar's node, stated of `Term.eval`.  An array of the language
  denotes a Lean `Array`; the node folds the list of its elements (`Array.toList`), and
  gives its branch the tail as an array again (`List.toArray`).
-/

variable {α : Type} {τ : TyWf}

/-! ## Reading a window of suffix answers -/

/-- The window of a *function of a list*: the answers at `l`, `l.drop 1`, …, `l.drop
    (k - 1)`, nearest first. -/
def NatWin.ofFunList (f : List α → TyWf.Den τ) : (k : Nat) → List α → NatWin τ k
  | 0, _ => PUnit.unit
  | k + 1, l => (f l, NatWin.ofFunList f k (l.drop 1))

@[simp] theorem NatWin.ofFunList_zero (f : List α → TyWf.Den τ) (l : List α) :
    NatWin.ofFunList f 0 l = PUnit.unit := rfl

@[simp] theorem NatWin.ofFunList_succ (f : List α → TyWf.Den τ) (k : Nat) (l : List α) :
    NatWin.ofFunList f (k + 1) l = (f l, NatWin.ofFunList f k (l.drop 1)) := rfl

/-- The window of the empty list is the constant window: every suffix of the empty list
    is the empty list. -/
theorem NatWin.ofFunList_nil (f : List α → TyWf.Den τ) :
    (k : Nat) → NatWin.ofFunList (τ := τ) f k ([] : List α) = NatWin.const (f []) k
  | 0 => rfl
  | k + 1 => by
      show ((f [], NatWin.ofFunList f k ([] : List α)) : TyWf.Den τ × NatWin τ k) = _
      rw [NatWin.ofFunList_nil f k]
      rfl

/-- Shifting a new answer into a window of suffix answers drops the oldest one, which is
    the one the shorter window no longer holds. -/
theorem NatWin.push_ofFunList (f : List α → TyWf.Den τ) (a : TyWf.Den τ) :
    (k : Nat) → (l : List α) →
      NatWin.push a (NatWin.ofFunList f (k + 1) l) = (a, NatWin.ofFunList f k l)
  | 0, _ => rfl
  | k + 1, l => by
      show ((a, NatWin.push (f l) (NatWin.ofFunList f (k + 1) (l.drop 1))) :
          TyWf.Den τ × NatWin τ (k + 1)) = _
      rw [NatWin.push_ofFunList f (f l) k (l.drop 1)]
      rfl

/-- The newest answer a window holds is the one just shifted in. -/
theorem NatWin.push_fst {k : Nat} (a : TyWf.Den τ) (w : NatWin τ (k + 1)) :
    (NatWin.push a w).1 = a := by
  cases k <;> rfl

/-! ## The two equations of the fold -/

variable {k : Nat} (z : List α → TyWf.Den τ)
    (s : α → List α → NatWin τ (k + 1) → TyWf.Den τ)

/-- The head of the window at `l` is the answer at `l` — the fold itself. -/
theorem listFoldKAux_fst (l : List α) : (listFoldKAux z s l).1 = listFoldK z s l := rfl

/-- One element of the fold: a list of at most `k` elements takes the short-list answer,
    and a longer one takes the branch. -/
theorem listFoldK_cons (a : α) (as : List α) :
    listFoldK z s (a :: as) =
      if as.length < k then z (a :: as) else s a as (listFoldKAux z s as) :=
  NatWin.push_fst _ _

/-- **The base equation.**  A list of at most `k` elements is answered by the short-list
    answers, and by them alone. -/
theorem listFoldK_base : (l : List α) → l.length ≤ k → listFoldK z s l = z l
  | [], _ => rfl
  | a :: as, h => by
      have hlt : as.length < k := by
        have : as.length + 1 ≤ k := h
        omega
      rw [listFoldK_cons]
      simp [hlt]

/-- **The window is the history.**  At every list, the window the fold carries is the
    tuple of the answers at that list and its `k` next suffixes, nearest first — which is
    what makes the fold linear rather than exponential. -/
theorem listFoldKAux_eq_ofFunList :
    (l : List α) → listFoldKAux z s l = NatWin.ofFunList (listFoldK z s) (k + 1) l
  | [] => by
      show NatWin.const (z []) (k + 1) = _
      rw [NatWin.ofFunList_nil]
      rfl
  | a :: as => by
      have hw : listFoldKAux z s as = NatWin.ofFunList (listFoldK z s) (k + 1) as :=
        listFoldKAux_eq_ofFunList as
      show NatWin.push
          (if as.length < k then z (a :: as) else s a as (listFoldKAux z s as))
          (listFoldKAux z s as) = _
      rw [hw, NatWin.push_ofFunList]
      show ((if as.length < k then z (a :: as)
          else s a as (NatWin.ofFunList (listFoldK z s) (k + 1) as),
          NatWin.ofFunList (listFoldK z s) k as) : TyWf.Den τ × NatWin τ k) =
        (listFoldK z s (a :: as), NatWin.ofFunList (listFoldK z s) k as)
      rw [listFoldK_cons, hw]

/-- **The step equation.**  At `a :: as` with a tail of at least `k` elements — the first
    lists at which all `k + 1` suffixes the branch reads exist — the answer is the branch
    applied to the head, the tail and the window of the answers at `as`, `as.drop 1`, …,
    `as.drop k`. -/
theorem listFoldK_step (a : α) (as : List α) (h : k ≤ as.length) :
    listFoldK z s (a :: as) =
      s a as (NatWin.ofFunList (listFoldK z s) (k + 1) as) := by
  have hlt : ¬ as.length < k := by omega
  rw [listFoldK_cons, listFoldKAux_eq_ofFunList]
  simp [hlt]

/-! ## Depth zero is the one-element fold -/

/-- The depth-zero instance **is** `LeanScript.listFold`: the only short list is the
    empty one, and the window holds the single answer at the tail. -/
theorem listFoldK_eq_listFold (z0 : TyWf.Den τ) (s0 : α → List α → TyWf.Den τ → TyWf.Den τ) :
    (l : List α) →
      listFoldK (τ := τ) (k := 0) (fun _ => z0) (fun a as w => s0 a as w.1) l =
        listFold z0 s0 l
  | [] => rfl
  | a :: as => by
      show s0 a as (listFoldK (τ := τ) (k := 0) (fun _ => z0) (fun a as w => s0 a as w.1) as) =
        s0 a as (listFold z0 s0 as)
      rw [listFoldK_eq_listFold z0 s0 as]

/-! ## The node, evaluated -/

section Node

variable {Sg : Sig} {Γ : Ctx} {σ : TyWf} (G : GlobalEnv Sg.decls)
    (arr : Atom Γ (.array σ)) (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ)
    (env : Env Γ)

/-- The value of the node — answering with the term's own value, `Dest.ret` — **is** the
    fold: the short lists are answered by its
    `ArrayRecBases`, and its step runs the branch with the head, the tail and the window
    in front of the environment. -/
theorem Term.eval_array_rec :
    Term.eval G (Term.array_rec k arr bases branch .ret) env =
      listFoldK (fun l => ArrayRecBases.eval G bases env l)
        (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
        (show Array _ from Atom.eval arr env).toList :=
  rfl

/-- Below the depth, the node answers with its `ArrayRecBases`. -/
theorem Term.eval_array_rec_base (l : List (TyWf.Den σ)) (hl : l.length ≤ k)
    (harr : (show Array (TyWf.Den σ) from Atom.eval arr env).toList = l) :
    Term.eval G (Term.array_rec k arr bases branch .ret) env =
      ArrayRecBases.eval G bases env l := by
  rw [Term.eval_array_rec, harr, listFoldK_base _ _ l hl]

/-- At and above the depth, the node answers with its branch, given the head, the tail
    and the window of the answers at the `k + 1` suffixes of the tail. -/
theorem Term.eval_array_rec_step (a : TyWf.Den σ) (as : List (TyWf.Den σ))
    (hk : k ≤ as.length)
    (harr : (show Array (TyWf.Den σ) from Atom.eval arr env).toList = a :: as) :
    Term.eval G (Term.array_rec k arr bases branch .ret) env =
      Term.eval G branch
        (a, as.toArray, Env.ofWin
          (NatWin.ofFunList
            (listFoldK (fun l => ArrayRecBases.eval G bases env l)
              (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env)))
            (k + 1) as)
          env)
        := by
  rw [Term.eval_array_rec, harr, listFoldK_step _ _ a as hk]

end Node

end LeanScript

end
