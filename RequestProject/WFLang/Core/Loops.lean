module

/-!
# Bounded loops as a first-order recursive function

`rangeLoop f stop i b` runs `b := f i b` for `i = i, i + 1, …, stop - 1`.  It is the target of
the capture of bounded loops: `for i in [a:b] do …` (in `Id`) and `Nat.fold n (fun i _ acc => …)`
are rewritten into `rangeLoop` (`forIn_range_eq_rangeLoop`, `fold_eq_rangeLoop`), whose function
argument is then specialised to the (known) loop body.  The lemmas below are also used by the
agreement proofs, in the form the simplifier produces (`List.foldl … (List.range' …)`).
-/

@[expose] public section

namespace WFLang

/-- `b := f i b` for `i` from `i` to `stop - 1`. -/
def rangeLoop {β : Type} (f : Nat → β → β) (stop i : Nat) (b : β) : β :=
  if i < stop then rangeLoop f stop (i + 1) (f i b) else b
termination_by stop - i

theorem foldl_range'_eq_rangeLoop {β : Type} (g : β → Nat → β) (i n : Nat) (b : β) :
    List.foldl g b (List.range' i n) = rangeLoop (fun a b => g b a) (i + n) i b := by
  induction n generalizing i b with
  | zero => rw [rangeLoop]; simp
  | succ n ih =>
    rw [rangeLoop, if_pos (by omega), List.range'_succ, List.foldl_cons, ih]
    congr 1; omega

/-- A loop body whose branches all continue: one `ForInStep.yield` of an `if`. -/
theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem rangeLoop_add_sub {β : Type} (f : Nat → β → β) (a b : Nat) (x : β) :
    rangeLoop f (a + (b - a)) a x = rangeLoop f b a x := by
  by_cases h : a ≤ b
  · rw [Nat.add_sub_cancel' h]
  · rw [rangeLoop, if_neg (by omega), rangeLoop, if_neg (by omega)]

theorem fold_eq_rangeLoop {β : Type} (f : Nat → β → β) (n : Nat) (b : β) :
    Nat.fold n (fun i _ acc => f i acc) b = rangeLoop f n 0 b := by
  have h (m : Nat) : rangeLoop f m 0 b =
      List.foldl (fun b a => f a b) b (List.range' 0 m) := by
    rw [foldl_range'_eq_rangeLoop, Nat.zero_add]
  induction n with
  | zero => rw [h]; simp
  | succ n ih => rw [Nat.fold_succ, ih, h, h, List.range'_concat, List.foldl_append]; simp

end WFLang

end
