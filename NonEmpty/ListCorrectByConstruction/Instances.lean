module
import Init.Data.List.Lemmas
public import NonEmpty.ListCorrectByConstruction.Ops

@[expose] public section

/-!
Membership, `ForIn`, and the `Functor`/`Applicative`/`Monad` instances of `NonEmptyList`, with their lawfulness proofs.
-/

namespace NonEmpty.ListCorrectByConstruction

namespace NonEmptyList

structure Mem (as : NonEmptyList α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (NonEmptyList α) where
  mem := Mem

def toArray (xs : NonEmptyList α) : Array α := xs.toList.toArray

@[simp] theorem toList_toArray (xs : NonEmptyList α) : xs.toArray.toList = xs.toList := by
  simp [toArray]

@[simp] def forInImpl [Monad m] (xs : NonEmptyList α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn xs.toList init f

instance [Monad m] : ForIn m (NonEmptyList α) α where
  forIn := forInImpl

theorem mem_def {a : α} {as : NonEmptyList α} : a ∈ as ↔ a ∈ as.toList := by
  constructor
  · intro ⟨h⟩; exact h
  · intro h; exact ⟨h⟩

theorem mem_head_or_tail {a : α} {as : NonEmptyList α} : a ∈ as ↔ a = as.head ∨ a ∈ as.tail := by
  constructor
  · intro ⟨h⟩; exact List.mem_cons.1 h
  · intro h; exact ⟨List.mem_cons.2 h⟩

theorem mem_iff_getElem {a : α} {as : NonEmptyList α} :
    a ∈ as ↔ ∃ (i : Nat) (h : i < as.length), as[i] = a := by
  simp only [mem_def, List.mem_iff_getElem, length_toList]
  simp_all only [toList, length, toList_getElem]

theorem mem_iff_exists_getElem {a : α} {as : NonEmptyList α} :
    a ∈ as ↔ ∃ (i : Fin as.length), as[i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, h⟩, rfl⟩
  · rintro ⟨⟨i, h⟩, rfl⟩; exact ⟨i, h, rfl⟩

def forIn'Impl [Monad m] (xs : NonEmptyList α) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β := forIn' xs.toList init (fun a h => f a ⟨h⟩)

instance [Monad m] : ForIn' m (NonEmptyList α) α inferInstance where
  forIn' := forIn'Impl

end NonEmptyList

instance : Functor NonEmptyList where
  map := NonEmptyList.map

namespace NonEmptyList


@[simp] theorem id_map (x : NonEmptyList α) : id <$> x = x := by
  ext <;> simp only [Functor.map, map, id_eq, List.map_id_fun]

@[simp] theorem map_id (as : NonEmptyList α) : map id as = as := id_map as

@[simp] theorem comp_map (g : α → β) (h : β → γ) (x : NonEmptyList α) : (h ∘ g) <$> x = h <$> g <$> x := by
  ext <;> simp only [Functor.map, map, Function.comp_apply, _root_.List.map_map]

@[simp] theorem map_comp {α β γ : Type u} (g : α → β) (h : β → γ) (as : NonEmptyList α) : map (h ∘ g) as = map h (map g as) := comp_map g h as

@[simp] def seq (fs : NonEmptyList (α → β)) (xs : NonEmptyList α) : NonEmptyList β :=
  ⟨fs.head xs.head,
   (fs.head <$> xs.tail).append (fs.tail.mapNonEmptyList (fun f => xs.map f))⟩

end NonEmptyList

instance : Seq NonEmptyList where
  seq fs x := NonEmptyList.seq fs (x ())

instance : Applicative NonEmptyList where
  pure := NonEmptyList.singleton

instance : LawfulFunctor NonEmptyList where
  id_map := NonEmptyList.id_map
  comp_map := NonEmptyList.comp_map
  map_const := rfl

namespace NonEmptyList

-- Helps prove seq_pure and seq_assoc
@[simp] theorem map_tail (f : α → β) (xs : NonEmptyList α) : (Functor.map f xs).tail = xs.tail.map f := rfl
@[simp] theorem map_head (f : α → β) (xs : NonEmptyList α) : (Functor.map f xs).head = f xs.head := rfl

/--
Helper lemmas
-/

@[simp] theorem NonEmptyList.toList_flatten (xs : NonEmptyList (NonEmptyList α)) :
    xs.flatten.toList = (xs.toList.map toList).flatten := by
  simp_all only [toList, flatten, List.mapNonEmptyList, id_eq, List.map_cons, List.flatten_cons, List.cons_append,
    List.cons.injEq, List.append_cancel_left_eq, true_and]
  rfl

@[simp] theorem NonEmptyList.flatten_flatten_eq (xs : NonEmptyList (NonEmptyList (NonEmptyList α))) :
    NonEmptyList.flatten (NonEmptyList.flatten xs) =
    NonEmptyList.flatten (Functor.map NonEmptyList.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all only [flatten, List.map_append, List.map_map, List.map_flatten, List.flatten_append,
    mk.injEq, List.mapNonEmptyList_id]
  congr 2
  rw [List.flatten_flatten]
  have : (List.map List.flatten (List.map (List.map toList ∘ toList) t)) = List.map (toList ∘ flatten) t := by
    simp only [List.map_map, Function.comp_def]
    congr 1
  rw [this]
  simp_all only [List.map_map, List.map_inj_left, Function.comp_apply, toList, List.map_cons, List.flatten_cons,
    List.cons_append, flatten, List.mapNonEmptyList, id_eq, List.cons.injEq, List.append_cancel_left_eq, true_and,
    map_head, map_tail, List.append_assoc, List.append_cancel_right_eq]
  rfl

/-- `as.attach` returns a NonEmptyList where each element is paired with a proof that it is in `as`. -/
@[simp] def attach (as : NonEmptyList α) : NonEmptyList { x // x ∈ as } :=
  ⟨⟨as.head, by
    solve_by_elim
  ⟩, as.tail.attach.map fun ⟨x, h⟩ => ⟨x, by
    solve_by_elim
  ⟩⟩

@[simp] theorem length_attach (as : NonEmptyList α) : as.attach.length = as.length := by
  simp only [length, attach, List.length_map, List.length_attach]

@[simp] theorem getElem_attach (as : NonEmptyList α) (i : Nat) (h : i < as.attach.length) :
    as.attach[i] = ⟨as[i]'(by simpa only [length, attach, List.length_map, List.length_attach] using h), by
      have h' : i < as.length := by simpa only [length, attach, List.length_map, List.length_attach] using
        h
      rw [mem_def, ← toList_getElem (h := h')]
      exact List.getElem_mem ..⟩ := by
  apply Subtype.ext
  cases i with
  | zero => rfl
  | succ i =>
    cases as with | mk head tail =>
    have h' : i + 1 < tail.length + 1 := by
      simp only [length, attach, List.length_map, List.length_attach] at h
      omega
    -- The goal should now have concrete structure
    simp_all only [Nat.add_lt_add_iff_right, length, attach]
    simp only [getElem]
    simp_all only [List.get_eq_getElem, List.getElem_map, List.getElem_attach]

@[simp] theorem attach_map (as : NonEmptyList α) (f : α → β) : as.attach.map (fun x => f x.val) = as.map f := by
  ext <;> simp

@[simp] theorem attach_map_val (as : NonEmptyList α) : as.attach.map (fun x => x.val) = as := by
  simp_all only [map, attach, List.map_map, Function.comp_apply, List.map_subtype, List.unattach_attach,
    List.map_id_fun', id_eq]

@[simp] theorem toList_attach (as : NonEmptyList α) :
    as.attach.toList = as.toList.attach.map fun ⟨x, h⟩ => ⟨x, by
    solve_by_elim
  ⟩ := by
  simp_all only [toList, attach, List.attach_cons, List.map_cons, List.map_map, List.cons.injEq, List.map_inj_left,
    List.mem_attach, Function.comp_apply, imp_self, implies_true, and_self]

@[simp] theorem sizeOf_get [SizeOf α] (as : NonEmptyList α) (i : Fin as.length) : sizeOf (as[i]) < sizeOf as := by
  obtain ⟨idx, h_idx⟩ := i
  cases idx with
  | zero =>
    -- 'as.get ⟨0, _⟩' is definitionally 'as.head'
    change sizeOf as.head < sizeOf as

    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega

  | succ n =>
    have hn : n < as.tail.length := by
      simp_all only [length]
      grind only

    -- 'as.get ⟨n + 1, _⟩' is definitionally 'as.tail[n]' (proof irrelevance handles the exact proof match)
    change sizeOf (as.tail[n]'hn) < sizeOf as

    -- Extract the array theorem BEFORE breaking apart 'as'
    have step := List.sizeOf_get as.tail ⟨n, hn⟩

    -- Now safely break apart 'as'
    cases as with | mk hd tl =>

    -- Expose the raw sizeOf math to the goal
    change sizeOf (tl[n]'hn) < 1 + sizeOf hd + sizeOf tl

    -- Clean up `step` so `omega` recognizes it!
    change sizeOf (tl[n]'hn) < sizeOf tl at step

    omega

@[simp] theorem sizeOf_getElem [SizeOf α] (as : NonEmptyList α) (i : Nat) (h : i < as.length) :
    sizeOf (as[i]'h) < sizeOf as :=
  sizeOf_get as ⟨i, h⟩

@[simp] theorem sizeOf_lt_of_mem [SizeOf α] {as : NonEmptyList α} {a : α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  rw [NonEmptyList.mem_head_or_tail] at h
  rcases h with rfl | h_tail
  · -- case 1: 'a' is the head
    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega
  · -- case 2: 'a' is in the tail
    have step := List.sizeOf_lt_of_mem h_tail
    cases as with | mk hd tl =>
    change sizeOf a < 1 + sizeOf hd + sizeOf tl
    change sizeOf a < sizeOf tl at step
    omega

@[simp] theorem sizeOf_attach_elem [SizeOf α] (as : NonEmptyList α) (x : { x // x ∈ as }) : sizeOf x.val < sizeOf as :=
  sizeOf_lt_of_mem x.property

@[simp] theorem sizeOf_head [SizeOf α] (as : NonEmptyList α) : sizeOf as.head < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf hd < 1 + sizeOf hd + sizeOf tl
      omega

@[simp] theorem sizeOf_tail [SizeOf α] (as : NonEmptyList α) : sizeOf as.tail < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf tl < 1 + sizeOf hd + sizeOf tl
      omega

end NonEmptyList

private theorem flatMap_flatMap_aux {α β γ} (l : List α) (h1 : α → List β) (h2 : β → List γ) :
    (l.flatMap h1).flatMap h2 = l.flatMap (fun a => (h1 a).flatMap h2) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]

instance : LawfulApplicative NonEmptyList where
  map_pure g x := by
    rfl

  pure_seq g x := by
    cases x; simp [Seq.seq, NonEmptyList.seq, pure, NonEmptyList.singleton, Functor.map, NonEmptyList.map, List.mapNonEmptyList]

  seq_pure f x := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyList.seq, pure, NonEmptyList.singleton, Functor.map, NonEmptyList.map, List.map_nil]
      exact List.mapNonEmptyList_singleton ft (fun h => h x)

  seq_assoc x g f := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      obtain ⟨gh, gt⟩ := g
      obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map, List.mapNonEmptyList,
        NonEmptyList.toList, List.append_eq]
      simp_all only [List.map_append, List.flatMap_append, List.append_assoc, List.flatMap_map, List.map_flatMap, List.map_map, List.flatMap_cons, List.map_cons, Function.comp_apply, flatMap_flatMap_aux, List.cons_append]

  seqLeft_eq x y := by
    simp only [SeqLeft.seqLeft, Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map,
      Function.const, List.map_const, List.mapNonEmptyList, NonEmptyList.toList]

  seqRight_eq x y := by
    simp only [SeqRight.seqRight, Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map,
      Function.const, List.map_const, id_eq, List.map_id_fun, List.mapNonEmptyList,
      NonEmptyList.toList]


instance : Monad NonEmptyList where
  bind xs f := NonEmptyList.flatten (xs.map f)

instance : LawfulMonad NonEmptyList where
  pure_bind x f := by
    apply NonEmptyList.ext
    · rfl
    · simp only [bind, NonEmptyList.flatten, pure, NonEmptyList.singleton,
        List.mapNonEmptyList, NonEmptyList.toList, id_eq, List.map_nil,
        List.flatMap_nil, List.append_nil]

  bind_pure_comp f x := by
    apply NonEmptyList.ext
    · rfl
    · simp_all only [NonEmptyList.map_tail]
      simp only [bind, pure, NonEmptyList.singleton, NonEmptyList.flatten, List.mapNonEmptyList,
        NonEmptyList.toList, id_eq, List.map_eq_flatMap, flatMap_flatMap_aux, List.nil_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

  bind_map f x := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
        Seq.seq, NonEmptyList.seq, List.flatMap_map, Functor.map, NonEmptyList.map]
      rfl

  bind_assoc x f g := by
    apply NonEmptyList.ext
    · simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
      List.map_append, List.flatMap_append, List.append_assoc]
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
        List.map_append, List.flatMap_append, List.append_assoc]
      simp_all only [List.append_cancel_left_eq]
      simp only [List.map_eq_flatMap, flatMap_flatMap_aux]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append]

end NonEmpty.ListCorrectByConstruction
