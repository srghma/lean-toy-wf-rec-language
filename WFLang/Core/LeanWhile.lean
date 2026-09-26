module

/-!
# Lean's own `while` loop: its unfolding law

In `do` notation, `while c do body` (and `repeat`) expands to `for _ in Lean.Loop.mk do …`, i.e.
`forIn Lean.Loop.mk init step` where `step : Unit → β → Id (ForInStep β)` runs one iteration on
the tuple `β` of the mutable variables and returns `ForInStep.yield b'` (go on with `b'`) or
`ForInStep.done b'` (stop, `break` or the test is false).

Since Lean v4.34, `Lean.Loop.forIn` is defined in the logic (through `repeatM`, whose value is
pinned to the least fixed point of its body in every monad with a `Lean.Order.MonadTail`
instance, e.g. `Id`), and Lean proves its one-step unfolding
(`Lean.Loop.forIn_eq_of_monadTail`).  `LoopLaw` states that unfolding in the `Id` monad:

```
forIn Loop.mk b f = match f () b with
  | .done b'  => pure b'
  | .yield b' => forIn Loop.mk b' f
```

* `loopLaw`: **the law holds** (a theorem, from Lean's own unfolding lemma).  It is what the
  generated equations `f.eq_wf : ∀ xs, f xs = f.wf xs` of the functions using `while` are proved
  with, so the agreement theorems of these functions have no hypothesis;
* `forIn_loop_of_exit`: a loop that stops after `n` iterations computes the value it stops
  with (`LoopLaw.forIn_of_exit`: the same from any function satisfying the law).
-/

@[expose] public section

namespace WFLang

/-- **The unfolding law of Lean's `while` loop** (in the `Id` monad).  It holds: `loopLaw`. -/
def LoopLaw : Prop :=
  ∀ (β : Type) (b : β) (f : Unit → β → Id (ForInStep β)),
    (forIn Lean.Loop.mk b f : Id β) =
      match f () b with
      | .done b' => pure b'
      | .yield b' => forIn Lean.Loop.mk b' f

/-- **Lean's `while` loop satisfies its unfolding law** (Lean's `Lean.Loop.forIn_eq_of_monadTail`,
in the `Id` monad). -/
theorem loopLaw : LoopLaw := by
  intro β b f
  show Lean.Loop.forIn _ b f = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

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

/-- **The law determines `while` on terminating loops**: for any function satisfying the law, a
loop that stops after `n` iterations with the value `v` computes `v`. -/
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

/-- **`while` computes the value it stops with**: a loop that stops after `n` iterations with the
value `v` computes `v`. -/
theorem forIn_loop_of_exit {β : Type} (f : Unit → β → Id (ForInStep β)) (n : Nat) (b v : β)
    (h : LoopStops f b n v) : (forIn Lean.Loop.mk b f : Id β) = v :=
  loopLaw.forIn_of_exit f n b v h

end WFLang

end
