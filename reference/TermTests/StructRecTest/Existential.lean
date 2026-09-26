module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public import LeanScript.CtorFn
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # Structures with an **existentially quantified type field**

```lean
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x
```

hides the type of its state: two values of `Unfold Nat` may choose different `State`s, so
`Unfold Nat` has no one tree of the language and no `LeanScriptTyWf` instance.  It is
translated anyway (`LeanScript.ToTerm.ExistentialArgs`):

* **a value** of it is built by the constructor function of `#leanscript_ctor`, whose type
  is the layout `Unfold.mk.leanScriptLayout α State` at the `State` the value chose (the
  proof `decreasing` is erased, as every proof is);
* **a call on a value that is written out** (`countdown.take n`, `(countFrom k).take n`)
  is specialized to that value: the value is substituted, so its `State`, `seed` and `step`
  are known, and the call is an ordinary term — here, the `nat_rec` of `Unfold.take.go`.
  This holds for any function on it, `@[inline]` or not (`firstOut`), since a function of
  a type without a tree cannot be declared in the signature;
* **a function of such a value** (`Unfold.take`, `firstOut`, `Pipe.run`, …) translates to a
  term **for every choice of the hidden type**: a Lean function
  `fun (State : TyWf) => (… : Term Sg Γ (Unfold.mk.leanScriptLayout α State ⇒ …))`, which
  is what a function out of an existential is.  Given the tree a value chose, it is a term
  that can be applied to that value; the tree is found by unification (`take_term _`).

Covered below: `Unfold` with a state of `Nat`, of a pair and of a list; a structure with
two hidden types (`Pipe`); a structure whose recursion answers a value of the hidden type
(`Boxed.iter`); two existential arguments at once; and a function that builds a new value of
the existential structure (`Boxed.bump`).  Each is checked by running the term, against fixed
numbers and against the Lean definition. -/

namespace TermTests.StructRec.Existential

open LeanScript TermTests.NatRecDepth

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-- A list of natural numbers of the language. -/
abbrev listT : TyWf := tyWfOf (List Nat)

/-- A list of the language, read back as a Lean list. -/
abbrev toL (v : TyWf.Den listT) : List Nat := Ty.DenRec.toList (.prim .nat) v

noncomputable section

/-! ## `Unfold`: a generator with a hidden state -/

/-- A generator: a seed, a step, and a measure that each step decreases. -/
structure Unfold (α : Type) where
  /-- The hidden type of the state. -/
  State      : Type
  /-- The first state. -/
  seed       : State
  /-- The next state and an output, or the end. -/
  step       : State → Option (State × α)
  /-- A measure of a state. -/
  measure    : State → Nat
  /-- Each step decreases the measure. -/
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

-- `Unfold` has no tree of the language: its instance is refused.
/--
error: the type `TermTests.StructRec.Existential.Unfold` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Unfold

/-- The first `fuel` outputs of a generator: a structural recursion on the fuel, whose state
    has the hidden type. -/
def Unfold.take {α : Type} (u : Unfold α) (fuel : Nat) : List α :=
  go fuel u.seed
where
  /-- The outputs from the state `s` on. -/
  go : Nat → u.State → List α
    | 0, _ => []
    | n + 1, s =>
      match u.step s with
      | none => []
      | some (s', a) => a :: go n s'

/-- The first output of a generator, or `0`: not `@[inline]`, and not recursive. -/
def firstOut (u : Unfold Nat) : Nat :=
  match u.step u.seed with
  | none => 0
  | some (_, a) => a

/-- `5, 4, 3, 2, 1`: the state is a `Nat`. -/
def countdown : Unfold Nat where
  State := Nat
  seed := 5
  step n := match n with | 0 => none | k + 1 => some (k, n)
  measure n := n
  decreasing := by
    intro x x' a h
    cases x with
    | zero => cases h
    | succ k => simp at h; obtain ⟨rfl, -⟩ := h; simp

/-- `k, k - 1, …, 1`: a generator built from a number. -/
def countFrom (k : Nat) : Unfold Nat where
  State := Nat
  seed := k
  step n := match n with | 0 => none | m + 1 => some (m, n)
  measure n := n
  decreasing := by
    intro x x' a h
    cases x with
    | zero => cases h
    | succ k => simp at h; obtain ⟨rfl, -⟩ := h; simp

/-- The Fibonacci numbers, `n` of them: the state is a triple. -/
def fibsUpTo (n : Nat) : Unfold Nat where
  State := Nat × Nat × Nat
  seed := (0, 1, n)
  step s := match s with
    | (_, _, 0) => none
    | (a, b, k + 1) => some ((b, a + b, k), a)
  measure s := s.2.2
  decreasing := by
    intro x x' a h
    obtain ⟨p, q, _ | k⟩ := x
    · cases h
    · simp at h; obtain ⟨rfl, -⟩ := h; simp

/-- Ten times each element of a list: the state is a list. -/
def ofList (xs : List Nat) : Unfold Nat where
  State := List Nat
  seed := xs
  step l := match l with | [] => none | a :: as => some (as, a * 10)
  measure l := l.length
  decreasing := by
    intro x x' a h
    cases x with
    | nil => cases h
    | cons b bs => simp at h; obtain ⟨rfl, -⟩ := h; simp

/-! ### A value: the constructor function, at the state it chose -/

/-- `countdown`, as a value of the language: its type is the layout at `State := Nat`. -/
def countdown_term := #leanscript_to_term (sig := sigAdd) countdown

example : Term sigAdd [] (Unfold.mk.leanScriptLayout natT natT) := countdown_term

/-- `fibsUpTo 8`, whose state is a triple. -/
def fibs8_term := #leanscript_to_term (sig := sigAdd) (fibsUpTo 8)

/-! ### Specialized to a value that is written out -/

/-- A structural recursion (`Unfold.take.go`) called through a wrapper, on a closed value. -/
def takeCountdown (n : Nat) : List Nat := countdown.take n

def takeCountdown_term : Term sigAdd [] (natT ⇒ listT) := #leanscript_to_term takeCountdown

-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd takeCountdown_term 3) = [5, 4, 3] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd takeCountdown_term 10) = [5, 4, 3, 2, 1] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd takeCountdown_term 10) = takeCountdown 10 := by decide +kernel

/-- The same on a triple state. -/
def takeFibs (n : Nat) : List Nat := (fibsUpTo 7).take n

def takeFibs_term : Term sigAdd [] (natT ⇒ listT) := #leanscript_to_term takeFibs

-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd takeFibs_term 20) = [0, 1, 1, 2, 3, 5, 8] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd takeFibs_term 4) = takeFibs 4 := by decide +kernel

/-- Values built from the arguments (`countFrom k`, `ofList xs`), a list state, and a call
    of the non-inline `firstOut` on two values. -/
def mixed (k n : Nat) (xs : List Nat) : List Nat :=
  (countFrom k).take n ++ (ofList xs).take n ++ [firstOut (ofList xs), firstOut countdown]

def mixed_term : Term sigAdd [] (natT ⇒ natT ⇒ listT ⇒ listT) := #leanscript_to_term mixed

/-- `[7, 8]`. -/
@[inline] def l78L : List Nat := [7, 8]

/-- `[7, 8]`, as a value of the language. -/
def l78 : TyWf.Den listT := runAdd (#leanscript_to_term l78L : Term sigAdd [] listT)

-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd mixed_term 3 2 l78) = [3, 2, 70, 80, 70, 5] := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd mixed_term 4 5 l78) = mixed 4 5 [7, 8] := by decide +kernel

/-! ### Generic in the hidden type -/

/-- `Unfold.take`, for every choice of `State`. -/
def take_term := #leanscript_to_term (sig := sigAdd) (Unfold.take (α := Nat))

example (S : TyWf) : Term sigAdd [] (Unfold.mk.leanScriptLayout natT S ⇒ natT ⇒ listT) :=
  take_term S

-- at `State := Nat`, applied to `countdown`
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd ((take_term natT).ap countdown_term) 3) = [5, 4, 3] := by decide +kernel
-- at the triple state of `fibsUpTo 8`, the tree found by unification
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd ((take_term _).ap fibs8_term) 10) = (fibsUpTo 8).take 10 := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-- `firstOut`, for every choice of `State`. -/
def firstOut_term := #leanscript_to_term (sig := sigAdd) firstOut

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((firstOut_term _).ap countdown_term) = 5 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((firstOut_term _).ap fibs8_term) = firstOut (fibsUpTo 8) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

/-- Two generators, each with its own hidden state. -/
def both (u v : Unfold Nat) (n : Nat) : List Nat := u.take n ++ v.take n

def both_term := #leanscript_to_term (sig := sigAdd) both

example (S T : TyWf) :
    Term sigAdd [] (Unfold.mk.leanScriptLayout natT S ⇒ Unfold.mk.leanScriptLayout natT T ⇒
      natT ⇒ listT) :=
  both_term S T

-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd (((both_term _ _).ap countdown_term).ap fibs8_term) 3) =
-- [SKIPPED BY PROFILE_LAKE]     [5, 4, 3, 0, 1, 1] := by decide +kernel

/-! ## Two hidden types -/

/-- A value, a map to a second hidden type, and a score of the result. -/
structure Pipe where
  /-- The hidden type of the source. -/
  In : Type
  /-- The hidden type of the result. -/
  Out : Type
  /-- The source. -/
  src : In
  /-- The map. -/
  f : In → Out
  /-- The score of a result. -/
  score : Out → Nat

/-- The score of the source's image. -/
def Pipe.run (p : Pipe) : Nat := p.score (p.f p.src)

def pipeRun_term := #leanscript_to_term (sig := sigAdd) Pipe.run

example (I O : TyWf) : Term sigAdd [] (Pipe.mk.leanScriptLayout I O ⇒ natT) := pipeRun_term I O

/-- `In := Nat`, `Out := Bool`. -/
def isFive : Pipe := ⟨Nat, Bool, 5, fun n => n == 5, fun b => if b then 1 else 0⟩

def isFive_term := #leanscript_to_term (sig := sigAdd) isFive

-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((pipeRun_term _ _).ap isFive_term) = 1 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((pipeRun_term _ _).ap isFive_term) = isFive.run := by decide +kernel

/-! ## A recursion that answers a value of the hidden type -/

/-- A value of a hidden type and a way to step it. -/
structure Boxed where
  /-- The hidden type. -/
  T : Type
  /-- The value. -/
  val : T
  /-- The step, given the number of the step. -/
  fn : T → Nat → T

/-- `n` steps from the value: a structural recursion whose answer has the hidden type. -/
def Boxed.iter (b : Boxed) (n : Nat) : b.T := go n
where
  /-- The value after `k` steps. -/
  go : Nat → b.T
    | 0 => b.val
    | k + 1 => b.fn (go k) k

def iter_term := #leanscript_to_term (sig := sigAdd) Boxed.iter

example (T : TyWf) : Term sigAdd [] (Boxed.mk.leanScriptLayout T ⇒ natT ⇒ T) := iter_term T

/-- A new value of the structure, with the same hidden type, one step further. -/
def Boxed.bump (b : Boxed) : Boxed := { b with val := b.fn b.val 1 }

def bump_term := #leanscript_to_term (sig := sigAdd) Boxed.bump

example (T : TyWf) : Term sigAdd [] (Boxed.mk.leanScriptLayout T ⇒ Boxed.mk.leanScriptLayout T) :=
  bump_term T

/-- `T := Nat`: add the number of the step. -/
def addBox : Boxed := ⟨Nat, 3, fun t k => t + k⟩

def addBox_term := #leanscript_to_term (sig := sigAdd) addBox

/-- `T := List Nat`: push the number of the step. -/
def listBox : Boxed := ⟨List Nat, [], fun t k => k :: t⟩

def listBox_term := #leanscript_to_term (sig := sigAdd) listBox

-- `3 + 0 + 1 + 2 + 3`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((iter_term _).ap addBox_term) 4 = 9 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((iter_term _).ap addBox_term) 6 = addBox.iter 6 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : toL (runAdd ((iter_term _).ap listBox_term) 3) = [2, 1, 0] := by decide +kernel
-- bumped once, then iterated: `3 + 1 + 0 + 1 + 2`
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((iter_term _).ap ((bump_term _).ap addBox_term)) 3 = 7 := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : runAdd ((iter_term _).ap ((bump_term _).ap addBox_term)) 3 = addBox.bump.iter 3 := by
-- [SKIPPED BY PROFILE_LAKE]   kernel_rfl

end

end TermTests.StructRec.Existential
