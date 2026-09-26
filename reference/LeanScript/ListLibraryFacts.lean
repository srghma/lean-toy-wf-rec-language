module

public import LeanScript.Ty.Instances
public import LeanScript.RangeFacts

@[expose] public section

/-!
# Why the translations of the `List` library functions are sound

`#leanscript_to_term` translates a few functions of Lean's library by a rule rather than
by reading their definition (see `LeanScript/ToTerm/Overview.lean` and
`TermTests/ToTermTest/ListLibrary.lean`).  Each rule replaces a Lean expression by
another one, which is then translated as usual.  This file proves, for every input, that
each replacement is an equation of Lean's logic:

* `panic! msg` becomes the `default` of its `Inhabited` instance (`panic_eq_default`,
  and the same for the variants `l[i]!` and `a[i]!` reach);
* `l[i]!` becomes `l.getD i default` (`getElem!_eq_getD`);
* `l[i]` on a list, with its proof, becomes `l.getD i d`, for any default `d`
  (`getElem_eq_getD`);
* `l.getD i d` is `l[i]?.getD d` (`getD_eq_getElem?_getD`), and `l[i]?` is the recursion
  `nth?` with a catch-all pattern (`getElem?_eq_nth?`);
* `l.attach` and `l.attachWith P h` become `l`: a subtype has the tree of its values
  (`tyWfOf_subtype`), and reading the values of the attached list gives back `l`
  (`attach_unattach`, `attachWith_unattach`), so any `map` or `foldl` that reads only
  the values is the same function of `l` (`map_attach_val`, `foldl_attach_val`, …);
* `for x in l do body` in `Id`, whose body always yields, becomes `l.foldl` of the body
  (`forIn_id_yield_eq_foldl`), and `for h : x in l` a `foldl` over `l.attach`
  (`forIn'_id_yield_eq_foldl_attach`, or over `l` when `h` is not read:
  `forIn'_id_yield_eq_foldl`);
* such a loop whose body can `break` (or `return`) folds the step `ForInStep β` instead
  of the state, and reads the state of the last step (`forIn_id_eq_foldl_step`,
  `forIn'_id_eq_foldl_attach_step`, `forIn'_id_eq_foldl_step`, and for `for i in [:n]`,
  `forIn_range_id_eq_natRec_step`);
* `for i in [start:stop:step]` is the loop over `[:size]` whose body reads the index
  `start + j * step` (`forIn_range_step_eq`);
* `for h : i in r` over a range, which names the membership proof `h : i ∈ r`, is the loop
  over `[:r.size]` whose body, guarded by `if hj : j < r.size`, reads the index
  `r.start + j * r.step` with the proof `r.mem_start_add_mul_step hj`
  (`forIn'_range_eq_forIn_guard`), and the loop `for i in r` when the body does not read
  `h` (`forIn'_range_eq_forIn`).
-/

namespace LeanScript.ListLibrary

/-! ## `panic!` is `default` -/

/-- `panic msg` is, in Lean's logic, the `default` of the instance it is handed. -/
theorem panic_eq_default {α : Sort u} [Inhabited α] (msg : String) :
    (panic msg : α) = default := rfl

/-- The same for `panicWithPos`, which `panic!` expands to. -/
theorem panicWithPos_eq_default {α : Sort u} [Inhabited α] (modName : String)
    (line col : Nat) (msg : String) :
    (panicWithPos modName line col msg : α) = default := rfl

/-- The same for `panicWithPosWithDecl`, which `panic!` inside a definition expands to
    (`List.get!Internal`'s out-of-range branch is one). -/
theorem panicWithPosWithDecl_eq_default {α : Sort u} [Inhabited α]
    (modName declName : String) (line col : Nat) (msg : String) :
    (panicWithPosWithDecl modName declName line col msg : α) = default := rfl

/-- The same for `outOfBounds`, which `a[i]!` on an array reaches. -/
theorem outOfBounds_eq_default {α : Sort u} [Inhabited α] :
    (outOfBounds : α) = default := rfl

/-! ## Indexing a list -/

/-- `l[i]!` is `l.getD i default`: in range the element, out of range `default`. -/
theorem getElem!_eq_getD {α : Type u} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = l.getD i default := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

/-- `l[i]` with its proof is `l.getD i d`, whatever the default `d`: the default is never
    reached when the index is in range. -/
theorem getElem_eq_getD {α : Type u} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l[i] = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `l.getD i d` is `l[i]?.getD d`, by definition. -/
theorem getD_eq_getElem?_getD {α : Type u} (l : List α) (i : Nat) (d : α) :
    l.getD i d = l[i]?.getD d := rfl

/-- `l[i]?` written by hand as a recursion whose `match` has a catch-all pattern — the
    shape of `List.get?Internal`, which `l[i]?` is. -/
def nth? {α : Type u} : List α → Nat → Option α
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n
  | _, _ => none

/-- `l[i]?` is `nth? l i`, for every list and index. -/
theorem getElem?_eq_nth? {α : Type u} (l : List α) (i : Nat) : l[i]? = nth? l i := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ n => simp only [List.getElem?_cons_succ, ih, nth?]

/-! ## `List.attach` is the list itself -/

/-- A subtype `{x // p x}` has the tree of `α`: its proof is erased. -/
theorem tyWfOf_subtype {α : Type u} (p : α → Prop) [LeanScriptTyWf α] :
    tyWfOf (Subtype p) = tyWfOf α := rfl

/-- So `List {x // p x}` has the tree of `List α`. -/
theorem tyWfOf_list_subtype {α : Type u} (p : α → Prop) [LeanScriptTyWf α] :
    tyWfOf (List (Subtype p)) = tyWfOf (List α) := rfl

/-- The values of `l.attach` are `l`. -/
theorem attach_unattach {α : Type u} (l : List α) : l.attach.map Subtype.val = l :=
  List.attach_map_subtype_val l

/-- The values of `l.attachWith P h` are `l`. -/
theorem attachWith_unattach {α : Type u} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) : (l.attachWith P h).map Subtype.val = l :=
  List.attachWith_map_subtype_val h

/-- A `map` over `l.attach` that reads only the values is a `map` over `l`. -/
theorem map_attach_val {α : Type u} {β : Type v} (l : List α) (g : α → β) :
    l.attach.map (fun x => g x.1) = l.map g := by
  have h := congrArg (List.map g) (attach_unattach l)
  rwa [List.map_map] at h

/-- The same over `l.attachWith P h`. -/
theorem map_attachWith_val {α : Type u} {β : Type v} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) (g : α → β) :
    (l.attachWith P h).map (fun x => g x.1) = l.map g := by
  have h' := congrArg (List.map g) (attachWith_unattach l P h)
  rwa [List.map_map] at h'

/-- A `foldl` over `l.attach` that reads only the values is a `foldl` over `l`. -/
theorem foldl_attach_val {α : Type u} {β : Type v} (l : List α) (f : β → α → β) (b : β) :
    l.attach.foldl (fun acc x => f acc x.1) b = l.foldl f b := by
  rw [← List.foldl_map (f := Subtype.val) (g := f), attach_unattach]

/-- The same over `l.attachWith P h`. -/
theorem foldl_attachWith_val {α : Type u} {β : Type v} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) (f : β → α → β) (b : β) :
    (l.attachWith P h).foldl (fun acc x => f acc x.1) b = l.foldl f b := by
  rw [← List.foldl_map (f := Subtype.val) (g := f), attachWith_unattach]

/-- The pattern `(List.range n).attach.map fun ⟨i, h⟩ => l[i]'…`: indexing with the proof
    that membership in `List.range l.length` gives is `l.getD i d` at every `i`, so the
    whole map is a map of `getD` over `List.range l.length`, which is `l` mapped. -/
theorem map_range_attach_getElem {α : Type u} {β : Type v} (l : List α) (g : α → β)
    (d : α) :
    (List.range l.length).attach.map (fun x => g (l[x.1]'(List.mem_range.mp x.2))) =
      (List.range l.length).map (fun i => g (l.getD i d)) := by
  have h : ∀ x ∈ (List.range l.length).attach,
      g (l[x.1]'(List.mem_range.mp x.2)) = g (l.getD x.1 d) := fun x _ => by
    rw [getElem_eq_getD l x.1 _ d]
  rw [List.map_congr_left h]
  exact map_attach_val _ (fun i => g (l.getD i d))

/-! ## `for x in l` in `Id`

`for x in l do body` in the identity monad, whose body always yields, is translated as
`l.foldl` of the body read as the next state (`LeanScript.ToTerm.listForInAsFoldl`); with
`for h : x in l`, when the body reads `h`, as a `foldl` over `l.attach`.  Reading the next
state pushes `pure (.yield ·)` inside every `if`, `if h :` and `match` of the body; the
first two are `ite_pure_yield` and `dite_pure_yield` (a `match` is the same, one
constructor at a time), and `let`s and join points are definitional. -/

/-- A `for` over a list in `Id` whose body always yields is the `foldl` of the body. -/
theorem forIn_id_yield_eq_foldl {α : Type u} {β : Type v} (l : List α) (init : β)
    (g : α → β → β) :
    (forIn (m := Id) l init fun x s => pure (ForInStep.yield (g x s))) =
      l.foldl (fun s x => g x s) init :=
  List.forIn_pure_yield_eq_foldl g init

/-- `for h : x in l` in `Id`, whose body always yields, is the `foldl` of the body over
    `l.attach`, whose elements carry the proof `h`. -/
theorem forIn'_id_yield_eq_foldl_attach {α : Type u} {β : Type v} (l : List α) (init : β)
    (g : (x : α) → x ∈ l → β → β) :
    (forIn' (m := Id) l init fun x h s => pure (ForInStep.yield (g x h s))) =
      l.attach.foldl (fun s p => g p.1 p.2 s) init := by
  rw [List.forIn'_pure_yield_eq_foldl]
  rfl

/-- When the body of `for h : x in l` does not read `h`, the fold over `l.attach` is the
    fold over `l`. -/
theorem forIn'_id_yield_eq_foldl {α : Type u} {β : Type v} (l : List α) (init : β)
    (g : α → β → β) :
    (forIn' (m := Id) l init fun x _ s => pure (ForInStep.yield (g x s))) =
      l.foldl (fun s x => g x s) init := by
  rw [forIn'_id_yield_eq_foldl_attach (g := fun x _ s => g x s)]
  exact foldl_attach_val l (fun s x => g x s) init

/-- A yield under an `if` is the `if` of the yielded states. -/
theorem ite_pure_yield {β : Type v} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

/-- A yield under an `if h :` is the `if h :` of the yielded states. -/
theorem dite_pure_yield {β : Type v} (c : Prop) [Decidable c] (a : c → β) (b : ¬c → β) :
    (if h : c then pure (ForInStep.yield (a h)) else pure (ForInStep.yield (b h)) :
        Id (ForInStep β)) =
      pure (ForInStep.yield (if h : c then a h else b h)) := by
  split <;> rfl

/-! ## `for` loops that `break`

A `for` in `Id` whose body can leave the loop (`break`, or `return` out of it, which `do`
compiles to `ForInStep.done`) is translated with the **step** `ForInStep β` as the state of
the fold (`LeanScript.ToTerm.listForInAsFoldl`, `LeanScript.ToTerm.rangeForInBreakAsNatRec`):
the fold starts from `ForInStep.yield init`; each element either keeps a `done` step as it is
or, from `yield s`, takes the step of the body at `s`; and the answer is the state the last
step carries.  The translator writes the case analysis as `ForInStep.casesOn` and reads the
state with `ForInStep.casesOn` too, which are these `match`es and `ForInStep.value`
definitionally.  The body itself needs no rewriting: in `Id`, `pure` is the identity. -/

/-- Once a loop has stopped, the remaining elements keep the step as it is. -/
theorem foldl_forInStep_done {α : Type u} {β : Type v} (f : α → β → Id (ForInStep β))
    (l : List α) (s : β) :
    l.foldl (fun st x => match st with
      | .done s => .done s
      | .yield s => Id.run (f x s)) (ForInStep.done s) = ForInStep.done s := by
  induction l with
  | nil => rfl
  | cons a as ih => exact ih

/-- A `for` over a list in `Id`, whose body may `break`, is the `foldl` of the step. -/
theorem forIn_id_eq_foldl_step {α : Type u} {β : Type v} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) :
    forIn (m := Id) l init f =
      (l.foldl (fun st x => match st with
        | .done s => .done s
        | .yield s => Id.run (f x s)) (ForInStep.yield init)).value := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, List.foldl_cons]
    show _ = (List.foldl _ (Id.run (f a init)) as).value
    cases h : Id.run (f a init) with
    | done b =>
      rw [foldl_forInStep_done]
      simp [Id.run] at h
      simp [h]; rfl
    | yield b =>
      simp [Id.run] at h
      simp [h]
      exact ih b

/-- `for h : x in l` in `Id`, whose body may `break`, is the `foldl` of the step over
    `l.attach`. -/
theorem forIn'_id_eq_foldl_attach_step {α : Type u} {β : Type v} (l : List α) (init : β)
    (f : (x : α) → x ∈ l → β → Id (ForInStep β)) :
    forIn' (m := Id) l init f =
      (l.attach.foldl (fun st p => match st with
        | .done s => .done s
        | .yield s => Id.run (f p.1 p.2 s)) (ForInStep.yield init)).value := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn'_cons, List.attach_cons, List.foldl_cons, List.foldl_map]
    show _ = (List.foldl _ (Id.run (f a List.mem_cons_self init)) _).value
    cases h : Id.run (f a List.mem_cons_self init) with
    | done b =>
      rw [foldl_forInStep_done
        (fun (p : {x // x ∈ as}) s => f p.1 (List.mem_cons_of_mem a p.2) s)]
      simp [Id.run] at h
      simp [h]; rfl
    | yield b =>
      simp [Id.run] at h
      simp [h]
      exact ih b (fun x hx s => f x (List.mem_cons_of_mem a hx) s)

/-- When the body of `for h : x in l` does not read `h`, the fold of the step over
    `l.attach` is the fold over `l`. -/
theorem forIn'_id_eq_foldl_step {α : Type u} {β : Type v} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) :
    forIn' (m := Id) l init (fun x _ s => f x s) =
      (l.foldl (fun st x => match st with
        | .done s => .done s
        | .yield s => Id.run (f x s)) (ForInStep.yield init)).value := by
  rw [forIn'_id_eq_foldl_attach_step (f := fun x _ s => f x s)]
  exact congrArg ForInStep.value (foldl_attach_val l (fun st x => match st with
    | .done s => .done s
    | .yield s => Id.run (f x s)) (ForInStep.yield init))

/-- `for i in [:n]` in `Id`, whose body may `break`, is the recursion on `n` whose value
    is the step after `n` iterations. -/
theorem forIn_range_id_eq_natRec_step {β : Type v} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id) [:n] init f =
      (Nat.rec (motive := fun _ => ForInStep β) (ForInStep.yield init)
        (fun i st => match st with
          | .done s => .done s
          | .yield s => Id.run (f i s)) n).value := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl_step]
  congr 1
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← List.range_eq_range']
  induction n with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/-- `List.range' s n step` is the list of the `s + j * step` for `j < n`. -/
theorem range'_eq_map_range_step (s n step : Nat) :
    List.range' s n step = (List.range n).map (fun j => s + j * step) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ_eq_map, List.range', ih, List.map_cons, List.map_map]
    simp only [Nat.zero_mul, Nat.add_zero, List.cons.injEq, true_and]
    apply List.map_congr_left; intro j _; simp only [Function.comp, Nat.succ_mul]; omega

/-- `for i in [start:stop:step]` in `Id` is the loop over `[:size]`, with
    `size = (stop - start + step - 1) / step` the number of its indices, whose body reads
    the index `start + j * step`.  This is how a range other than `[:n]` is translated. -/
theorem forIn_range_step_eq {β : Type v} (start stop step : Nat) (hs : 0 < step) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn (m := Id)
        ({ start := start, stop := stop, step := step, step_pos := hs } : Std.Legacy.Range)
        init f =
      forIn (m := Id) [:(stop - start + step - 1) / step] init
        (fun j s => f (start + j * step) s) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize (stop - start + step - 1) / step = n
  rw [range'_eq_map_range_step, range'_eq_map_range_step, List.forIn_map, List.forIn_map]
  simp

/-- A loop over a list whose body reads a proof of `P a` from the membership proof is the
    loop that does not name the membership proof and tests `P a` instead: the test always
    holds on the elements of the list. -/
theorem forIn'_eq_forIn_dite {α : Type w} {β : Type v} {m : Type v → Type x} [Monad m]
    (l : List α) (P : α → Prop) [DecidablePred P] (hP : ∀ a, a ∈ l → P a) (init : β)
    (g : (a : α) → P a → β → m (ForInStep β)) :
    forIn' l init (fun a h s => g a (hP a h) s) =
      forIn l init (fun a s => if h : P a then g a h s else pure (ForInStep.yield s)) := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    have ha : P a := hP a List.mem_cons_self
    rw [List.forIn'_cons, List.forIn_cons]
    simp only [ha, ↓reduceDIte]
    congr 1; funext st
    cases st with
    | done => rfl
    | yield s' => exact ih (fun a h => hP a (List.mem_cons_of_mem _ h)) s'

/-- `for h : i in r` in `Id`, over a range `r`, is the loop over `[:r.size]` whose body, at
    `j`, reads the index `r.start + j * r.step` with the proof that it is a member of `r`,
    built from the test `j < r.size` (which always holds).  This is how such a loop is
    translated when its body reads `h`. -/
theorem forIn'_range_eq_forIn_guard {β : Type v} (r : Std.Legacy.Range) (init : β)
    (f : (i : Nat) → i ∈ r → β → Id (ForInStep β)) :
    forIn' (m := Id) r init f =
      forIn (m := Id) [:r.size] init (fun j s =>
        if hj : j < r.size then f (r.start + j * r.step) (r.mem_start_add_mul_step hj) s
        else pure (ForInStep.yield s)) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : ([:r.size] : Std.Legacy.Range).size = r.size := by
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [hs]
  rw [← List.range_eq_range', ← forIn'_eq_forIn_dite (List.range r.size) (· < r.size)
    (fun a h => List.mem_range.1 h)]
  rw [List.forIn'_congr (range'_eq_map_range_step _ _ _) rfl (fun _ _ _ => rfl),
    List.forIn'_map]

/-- `for h : i in r` whose body does not read `h` is the loop `for i in r`.  This is how
    such a loop is translated. -/
theorem forIn'_range_eq_forIn {β : Type v} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    forIn' (m := Id) r init (fun i _ s => f i s) = forIn (m := Id) r init f := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range']
  generalize List.range' r.start r.size r.step = l
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn'_cons, List.forIn_cons]
    congr 1

end LeanScript.ListLibrary

end
