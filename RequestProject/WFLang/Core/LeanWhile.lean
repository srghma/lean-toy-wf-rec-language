module

/-!
# Lean's own `while` loop: its unfolding law

In `do` notation, `while c do body` (and `repeat`) expands to `for _ in Lean.Loop.mk do …`, i.e.
`forIn Lean.Loop.mk init step` where `step : Unit → β → Id (ForInStep β)` runs one iteration on
the tuple `β` of the mutable variables and returns `ForInStep.yield b'` (go on with `b'`) or
`ForInStep.done b'` (stop, `break` or the test is false).  `forIn` for `Lean.Loop` is
`Lean.Loop.forIn`, a **`partial def`**: in the logic it is an opaque constant, so no theorem
about a function using `while` can be proved without an assumption about it.

`LoopLaw` is that assumption: the unfolding equation that `Lean.Loop.forIn` satisfies by its
definition (it is the equation of its compiled code, `Init/While.lean`):

```
forIn Loop.mk b f = match f () b with
  | .done b'  => pure b'
  | .yield b' => forIn Loop.mk b' f
```

It is used as an explicit **hypothesis** (never as an axiom) of the agreement theorems of the
functions using `while` that `#lean_wf_func_to_term` captures.

* `loopLaw_satisfiable`: the equation has a solution (for every `β` and body at once), so a
  hypothesis `h : LoopLaw` is not contradictory in shape;
* `LoopLaw.forIn_of_exit`: under the law, a loop that stops after `n` iterations computes the
  value it stops with — the law determines `forIn Loop.mk` on every terminating loop.
-/

@[expose] public section

namespace WFLang

/-- **The unfolding law of Lean's `while` loop** (in the `Id` monad): the equation of
`Lean.Loop.forIn`'s compiled code.  Lean's `partial def` gives no proof of it, so it is an
explicit hypothesis of every theorem about a function using `while`. -/
def LoopLaw : Prop :=
  ∀ (β : Type) (b : β) (f : Unit → β → Id (ForInStep β)),
    (forIn Lean.Loop.mk b f : Id β) =
      match f () b with
      | .done b' => pure b'
      | .yield b' => forIn Lean.Loop.mk b' f

/-- `n` iterations of the loop body `f` from `b`, as long as it yields (`none` if it stopped
before). -/
def loopIter {β : Type} (f : Unit → β → Id (ForInStep β)) : Nat → β → Option β
  | 0, b => some b
  | n + 1, b =>
    match f () b with
    | .done _ => none
    | .yield b' => loopIter f n b'

/-- The loop body `f` started from `b` stops after `n` iterations with the value `v`: it yields
`n` times and then returns `ForInStep.done v`. -/
def LoopStops {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) (n : Nat) (v : β) : Prop :=
  ∃ b', loopIter f n b = some b' ∧ f () b' = ForInStep.done v

theorem loopStops_zero {β : Type} {f : Unit → β → Id (ForInStep β)} {b v : β} :
    LoopStops f b 0 v ↔ f () b = ForInStep.done v := by
  constructor
  · rintro ⟨b', h, hv⟩
    cases h
    exact hv
  · intro h
    exact ⟨b, rfl, h⟩

theorem loopStops_succ {β : Type} {f : Unit → β → Id (ForInStep β)} {b v : β} {n : Nat} :
    LoopStops f b (n + 1) v ↔ ∃ b', f () b = ForInStep.yield b' ∧ LoopStops f b' n v := by
  unfold LoopStops
  simp only [loopIter]
  constructor
  · rintro ⟨b'', h, hv⟩
    revert h
    cases hf : f () b with
    | done _ => intro h; cases h
    | yield b' => intro h; exact ⟨b', rfl, b'', h, hv⟩
  · rintro ⟨b', hf, b'', h, hv⟩
    refine ⟨b'', ?_, hv⟩
    rw [hf]
    exact h

/-- **The law determines `while` on terminating loops**: a loop that stops after `n` iterations
with the value `v` computes `v`. -/
theorem LoopLaw.forIn_of_exit (h : LoopLaw) {β : Type} (f : Unit → β → Id (ForInStep β)) :
    ∀ (n : Nat) (b v : β), LoopStops f b n v → (forIn Lean.Loop.mk b f : Id β) = v := by
  intro n
  induction n with
  | zero =>
    intro b v hs
    rw [h, loopStops_zero.mp hs]
    rfl
  | succ n ih =>
    intro b v hs
    obtain ⟨b', hf, hs'⟩ := loopStops_succ.mp hs
    rw [h, hf]
    exact ih b' v hs'

theorem loopStops_unique {β : Type} {f : Unit → β → Id (ForInStep β)} :
    ∀ {n m : Nat} {b v w : β}, LoopStops f b n v → LoopStops f b m w → v = w := by
  intro n
  induction n with
  | zero =>
    intro m b v w hv hw
    have hv := loopStops_zero.mp hv
    cases m with
    | zero =>
      have hw := loopStops_zero.mp hw
      rw [hv] at hw
      cases hw
      rfl
    | succ m =>
      obtain ⟨b', hf, _⟩ := loopStops_succ.mp hw
      rw [hv] at hf
      cases hf
  | succ n ih =>
    intro m b v w hv hw
    obtain ⟨b', hf, hv'⟩ := loopStops_succ.mp hv
    cases m with
    | zero =>
      have hw := loopStops_zero.mp hw
      rw [hf] at hw
      cases hw
    | succ m =>
      obtain ⟨b'', hf', hw'⟩ := loopStops_succ.mp hw
      rw [hf] at hf'
      cases hf'
      exact ih hv' hw'

open Classical in
/-- A solution of the loop equation: the value the loop stops with if it stops, and an
arbitrary value (the same along the whole run) if it runs forever. -/
noncomputable def loopSolution (β : Type) (b : β) (f : Unit → β → Id (ForInStep β)) : β :=
  if hs : ∃ n v, LoopStops f b n v then Classical.choose (Classical.choose_spec hs)
  else Classical.choice ⟨b⟩

/-- **The loop equation has a solution**, for every type and body at once: a hypothesis
`LoopLaw` asks `Lean.Loop.forIn` to be such a solution, which it is not contradictory to ask. -/
theorem loopLaw_satisfiable :
    ∃ F : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β,
      ∀ (β : Type) (b : β) (f : Unit → β → Id (ForInStep β)),
        F β b f = match f () b with
          | .done b' => b'
          | .yield b' => F β b' f := by
  refine ⟨loopSolution, fun β b f => ?_⟩
  have spec : ∀ {b : β} (hs : ∃ n v, LoopStops f b n v),
      LoopStops f b (Classical.choose hs) (Classical.choose (Classical.choose_spec hs)) :=
    fun hs => Classical.choose_spec (Classical.choose_spec hs)
  cases hf : f () b with
  | done v =>
    have hs : ∃ n v, LoopStops f b n v := ⟨0, v, loopStops_zero.mpr hf⟩
    show loopSolution β b f = v
    rw [loopSolution, dif_pos hs]
    exact loopStops_unique (spec hs) (loopStops_zero.mpr hf)
  | yield b' =>
    show loopSolution β b f = loopSolution β b' f
    by_cases hs : ∃ n v, LoopStops f b n v
    · have hs' : ∃ n v, LoopStops f b' n v := by
        obtain ⟨n, v, hnv⟩ := hs
        cases n with
        | zero => rw [loopStops_zero, hf] at hnv; cases hnv
        | succ n =>
          obtain ⟨b'', hf', h''⟩ := loopStops_succ.mp hnv
          rw [hf] at hf'
          cases hf'
          exact ⟨n, v, h''⟩
      rw [loopSolution, dif_pos hs, loopSolution, dif_pos hs']
      obtain ⟨n', hn'⟩ := hs'
      exact loopStops_unique (spec hs)
        (loopStops_succ.mpr ⟨b', hf, spec ⟨_, _, hn'.choose_spec⟩⟩ :)
    · have hs' : ¬ ∃ n v, LoopStops f b' n v := by
        rintro ⟨n, v, hnv⟩
        exact hs ⟨n + 1, v, loopStops_succ.mpr ⟨b', hf, hnv⟩⟩
      rw [loopSolution, dif_neg hs, loopSolution, dif_neg hs']

end WFLang

end
