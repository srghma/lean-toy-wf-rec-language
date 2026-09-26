module
import Init.Data.Array.Lemmas
public import NonEmpty.ArrayCorrectByConstruction.Ops

@[expose] public section

/-!
Membership, `ForIn`, and the `Functor`/`Applicative`/`Monad` instances of `NonEmptyArray`, with their lawfulness proofs.
-/

namespace NonEmpty.ArrayCorrectByConstruction

namespace NonEmptyArray

structure Mem (as : NonEmptyArray α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (NonEmptyArray α) where
  mem := Mem

@[simp] theorem toArr_toList (xs : NonEmptyArray α) : xs.toArr.toList = xs.toList := by
  simp only [Array.toList_append]
  rfl

@[simp] def forInImpl [Monad m] (xs : NonEmptyArray α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn xs.toArr init f

instance [Monad m] : ForIn m (NonEmptyArray α) α where
  forIn := forInImpl

theorem mem_def {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a ∈ as.toArr := by
  constructor
  · intro ⟨h⟩; rw [Array.mem_def, toArr_toList]; exact h
  · intro h; rw [Array.mem_def, toArr_toList] at h; exact ⟨h⟩

theorem mem_head_or_tail {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a = as.head ∨ a ∈ as.tail := by
  constructor
  · intro ⟨h⟩; exact (List.mem_cons.1 h).imp id (Array.mem_def.2)
  · intro h; exact ⟨List.mem_cons.2 (h.imp id (Array.mem_def.1))⟩

theorem mem_iff_getElem {a : α} {as : NonEmptyArray α} :
    a ∈ as ↔ ∃ (i : Nat) (h : i < as.size), as[i] = a := by
  simp only [mem_def, Array.mem_iff_getElem, size_toArr]
  simp_all only [toArr, size, toArr_getElem]

theorem mem_iff_exists_getElem {a : α} {as : NonEmptyArray α} :
    a ∈ as ↔ ∃ (i : Fin as.size), as[i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, h⟩, rfl⟩
  · rintro ⟨⟨i, h⟩, rfl⟩; exact ⟨i, h, rfl⟩

def forIn'Impl [Monad m] (xs : NonEmptyArray α) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β := forIn' xs.toArr init (fun a h => f a ⟨by
    rw [Array.mem_def, toArr_toList] at h
    exact h
  ⟩)

instance [Monad m] : ForIn' m (NonEmptyArray α) α inferInstance where
  forIn' := forIn'Impl

end NonEmptyArray

instance : Functor NonEmptyArray where
  map := NonEmptyArray.map

namespace NonEmptyArray


@[simp] theorem id_map (x : NonEmptyArray α) : id <$> x = x := by
  ext <;> simp only [Functor.map, map, id_eq, Array.map_id_fun]

@[simp] theorem map_id (as : NonEmptyArray α) : map id as = as := id_map as

@[simp] theorem comp_map (g : α → β) (h : β → γ) (x : NonEmptyArray α) : (h ∘ g) <$> x = h <$> g <$> x := by
  ext <;> simp only [Functor.map, map, Function.comp_apply, _root_.Array.map_map]

@[simp] theorem map_comp {α β γ : Type u} (g : α → β) (h : β → γ) (as : NonEmptyArray α) : map (h ∘ g) as = map h (map g as) := comp_map g h as

@[simp] def seq (fs : NonEmptyArray (α → β)) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨fs.head xs.head,
   (fs.head <$> xs.tail).append (fs.tail.mapNonEmptyArray (fun f => xs.map f))⟩

end NonEmptyArray

instance : Seq NonEmptyArray where
  seq fs x := NonEmptyArray.seq fs (x ())

instance : Applicative NonEmptyArray where
  pure := NonEmptyArray.singleton

instance : LawfulFunctor NonEmptyArray where
  id_map := NonEmptyArray.id_map
  comp_map := NonEmptyArray.comp_map
  map_const := rfl

namespace NonEmptyArray

-- Helps prove seq_pure and seq_assoc
@[simp] theorem map_tail (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).tail = xs.tail.map f := rfl
@[simp] theorem map_head (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).head = f xs.head := rfl

/--
Helper lemmas
-/

@[simp] theorem NonEmptyArray.toArr_flatten (xs : NonEmptyArray (NonEmptyArray α)) :
    xs.flatten.toArr = (xs.toArr.map toArr).flatten := by
  cases xs with | mk h t =>
  simp only [toArr, flatten, Array.map_append, List.map_toArray, List.map_cons, List.map_nil,
    Array.flatten_append, Array.flatten_singleton, Array.append_assoc, Array.mapNonEmptyArray_id]

@[simp] theorem NonEmptyArray.flatten_flatten_eq (xs : NonEmptyArray (NonEmptyArray (NonEmptyArray α))) :
    NonEmptyArray.flatten (NonEmptyArray.flatten xs) =
    NonEmptyArray.flatten (Functor.map NonEmptyArray.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all only [flatten, Array.map_append, Array.map_map, Array.map_flatten, Array.flatten_append,
    mk.injEq, Array.mapNonEmptyArray_id]
  congr 2
  rw [Array.flatten_flatten]
  have : (Array.map Array.flatten (Array.map (Array.map toArr ∘ toArr) t)) = Array.map (toArr ∘ flatten) t := by
    simp only [Array.map_map, Function.comp_def]
    congr 1
    funext x
    exact (toArr_flatten x).symm
  rw [this]
  simp_all only [Array.map_map, Array.map_inj_left, Function.comp_apply, toArr, Array.map_append, List.map_toArray,
    List.map_cons, List.map_nil, Array.flatten_append, Array.flatten_singleton, Array.append_assoc, flatten,
    Array.mapNonEmptyArray, id_eq, map_head, map_tail, true_and]
  congr 1
  congr 1
  simp [Array.flatMap_def]

/-- `as.attach` returns a NonEmptyArray where each element is paired with a proof that it is in `as`. -/
@[simp] def attach (as : NonEmptyArray α) : NonEmptyArray { x // x ∈ as } :=
  ⟨⟨as.head, by simp only [mem_def, toArr, Array.mem_append, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false, true_or]⟩, as.tail.attach.map fun ⟨x, h⟩ => ⟨x, by simp only [mem_def,
      toArr, Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, h,
      or_true]⟩⟩

@[simp] theorem size_attach (as : NonEmptyArray α) : as.attach.size = as.size := by
  simp only [size, attach, Array.size_map, Array.size_attach]

@[simp] theorem getElem_attach (as : NonEmptyArray α) (i : Nat) (h : i < as.attach.size) :
    as.attach[i] = ⟨as[i]'(by simpa only [size, attach, Array.size_map, Array.size_attach] using h), by
      have h' : i < as.size := by simpa only [size, attach, Array.size_map, Array.size_attach] using
        h
      rw [mem_def, ← toArr_getElem (h := h')]
      exact Array.getElem_mem ..⟩ := by
  apply Subtype.ext
  cases i with
  | zero => rfl
  | succ i =>
    cases as with | mk head tail =>
    have h' : i + 1 < tail.size + 1 := by
      simp only [size, attach, Array.size_map, Array.size_attach] at h
      omega
    -- The goal should now have concrete structure
    simp_all only [Nat.add_lt_add_iff_right, size, attach]
    simp only [getElem]
    simp_all only [Array.getInternal_eq_getElem, Array.getElem_map, Array.getElem_attach]

@[simp] theorem attach_map (as : NonEmptyArray α) (f : α → β) : as.attach.map (fun x => f x.val) = as.map f := by
  ext <;> simp

@[simp] theorem attach_map_val (as : NonEmptyArray α) : as.attach.map (fun x => x.val) = as := by
  simp_all only [map, attach, Array.map_map, Function.comp_apply, Array.map_subtype, Array.unattach_attach,
    Array.map_id_fun', id_eq]

@[simp] theorem toArr_attach (as : NonEmptyArray α) :
    as.attach.toArr = as.toArr.attach.map fun ⟨x, h⟩ => ⟨x, by simpa only [mem_def, toArr,
      Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] using h⟩ := by
  apply Array.ext
  · simp only [toArr, attach, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Array.size_map, Array.size_attach, Array.attach_append,
    List.attach_toArray, List.attachWith_mem_toArray, List.attach_cons, List.attach_nil,
    List.map_nil, List.map_cons, List.map_toArray, Array.map_append, Array.map_map]
  · intro i h1 h2
    apply Subtype.ext
    simp only [toArr, attach, Array.getElem_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Array.getElem_map, Array.getElem_attach]
    split <;> simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, size_attach, size, Array.attach_append, List.attach_toArray, List.attachWith_mem_toArray,
      List.attach_cons, List.attach_nil, List.map_nil, List.map_cons, List.map_toArray, Array.map_append,
      Array.map_map, Array.size_map, Array.size_attach, List.getElem_toArray, List.getElem_singleton]

@[simp] theorem sizeOf_get [SizeOf α] (as : NonEmptyArray α) (i : Fin as.size) : sizeOf (as[i]) < sizeOf as := by
  obtain ⟨idx, h_idx⟩ := i
  cases idx with
  | zero =>
    -- 'as.get ⟨0, _⟩' is definitionally 'as.head'
    change sizeOf as.head < sizeOf as

    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega

  | succ n =>
    have hn : n < as.tail.size := by
      simp only [size] at h_idx
      omega

    -- 'as.get ⟨n + 1, _⟩' is definitionally 'as.tail[n]' (proof irrelevance handles the exact proof match)
    change sizeOf (as.tail[n]'hn) < sizeOf as

    -- Extract the array theorem BEFORE breaking apart 'as'
    have step := Array.sizeOf_getElem as.tail n hn

    -- Now safely break apart 'as'
    cases as with | mk hd tl =>

    -- Expose the raw sizeOf math to the goal
    change sizeOf (tl[n]'hn) < 1 + sizeOf hd + sizeOf tl

    -- Clean up `step` so `omega` recognizes it!
    change sizeOf (tl[n]'hn) < sizeOf tl at step

    omega

@[simp] theorem sizeOf_getElem [SizeOf α] (as : NonEmptyArray α) (i : Nat) (h : i < as.size) :
    sizeOf (as[i]'h) < sizeOf as :=
  sizeOf_get as ⟨i, h⟩

@[simp] theorem sizeOf_lt_of_mem [SizeOf α] {as : NonEmptyArray α} {a : α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  rw [NonEmptyArray.mem_head_or_tail] at h
  rcases h with rfl | h_tail
  · -- case 1: 'a' is the head
    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega
  · -- case 2: 'a' is in the tail
    have step := Array.sizeOf_lt_of_mem h_tail
    cases as with | mk hd tl =>
    change sizeOf a < 1 + sizeOf hd + sizeOf tl
    change sizeOf a < sizeOf tl at step
    omega

@[simp] theorem sizeOf_attach_elem [SizeOf α] (as : NonEmptyArray α) (x : { x // x ∈ as }) : sizeOf x.val < sizeOf as :=
  sizeOf_lt_of_mem x.property

@[simp] theorem sizeOf_head [SizeOf α] (as : NonEmptyArray α) : sizeOf as.head < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf hd < 1 + sizeOf hd + sizeOf tl
      omega

@[simp] theorem sizeOf_tail [SizeOf α] (as : NonEmptyArray α) : sizeOf as.tail < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf tl < 1 + sizeOf hd + sizeOf tl
      omega

end NonEmptyArray

instance : LawfulApplicative NonEmptyArray where
  map_pure g x := by
    simp only [Functor.map, NonEmptyArray.map, pure, NonEmptyArray.singleton, List.map_toArray,
      List.map_nil]

  pure_seq g x := by
    simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
      Array.mapNonEmptyArray, NonEmptyArray.toArr, List.flatMap_toArray, Array.toList_append,
      Array.toList_map, List.cons_append, List.nil_append, List.flatMap_nil, Array.append_eq_append,
      Array.append_empty, NonEmptyArray.map]

  seq_pure f x := by
    apply NonEmptyArray.ext
    · simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
      List.map_toArray, List.map_nil, Array.mapNonEmptyArray, NonEmptyArray.toArr,
      Array.append_empty, ← Array.map_eq_flatMap, Array.append_eq_append,
      Array.empty_append, NonEmptyArray.map]
    · obtain ⟨g, gt⟩ := f
      simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
        List.map_toArray, List.map_nil, Array.mapNonEmptyArray, NonEmptyArray.toArr,
        Array.append_empty, ← Array.map_eq_flatMap, Array.append_eq_append,
        Array.empty_append, NonEmptyArray.map]

  seq_assoc x g f := by
    apply NonEmptyArray.ext
    · simp only [Seq.seq, NonEmptyArray.seq, Functor.map, Array.mapNonEmptyArray,
      NonEmptyArray.toArr, Array.append_eq_append, Array.map_append, Array.map_map,
      Array.append_assoc, NonEmptyArray.map, Function.comp_apply, Array.flatMap_append]
    · obtain ⟨xh, xt⟩ := x
      obtain ⟨gh, gt⟩ := g
      obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyArray.seq, Functor.map, Array.mapNonEmptyArray,
        NonEmptyArray.toArr, Array.append_eq_append, Array.map_append, Array.map_map,
        Array.append_assoc, NonEmptyArray.map, Function.comp_apply, Array.flatMap_append]
      cases xt with | mk l =>
      induction l generalizing gh gt fh ft
      · simp only [Function.comp_def, List.map_toArray, List.map_nil, Array.append_empty,
        ← Array.map_eq_flatMap, Array.map_map, Array.empty_append, Array.flatMap_map,
        Function.comp_apply, Array.flatMap_assoc, Array.flatMap_append, List.flatMap_toArray,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · rename_i a as ih
        simp only [Function.comp_def, List.map_toArray, List.append_toArray, List.cons_append,
          List.nil_append, Array.map_flatMap, List.map_cons, List.map_map, Array.flatMap_map,
          Function.comp_apply, Array.flatMap_assoc, Array.flatMap_append, List.flatMap_toArray,
          List.flatMap_cons, List.flatMap_nil, List.append_nil] at *
        simp only [← Array.append_assoc, List.append_toArray, List.cons_append, List.nil_append]

  seqLeft_eq x y := by
    simp only [SeqLeft.seqLeft, Seq.seq, NonEmptyArray.seq, Functor.map, NonEmptyArray.map,
      Function.const, Array.map_const, Array.mapNonEmptyArray, NonEmptyArray.toArr,
      Array.append_eq_append]

  seqRight_eq x y := by
    simp only [SeqRight.seqRight, Seq.seq, NonEmptyArray.seq, Functor.map, NonEmptyArray.map,
      Function.const, Array.map_const, id_eq, Array.map_id_fun, Array.mapNonEmptyArray,
      NonEmptyArray.toArr, Array.append_eq_append]


instance : Monad NonEmptyArray where
  bind xs f := NonEmptyArray.flatten (xs.map f)

instance : LawfulMonad NonEmptyArray where
  pure_bind x f := by
    apply NonEmptyArray.ext
    · rfl
    · simp only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.singleton,
      Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq, List.map_toArray, List.map_nil,
      List.flatMap_toArray, Array.toList_append, List.cons_append, List.nil_append,
      List.flatMap_nil, Array.append_empty]

  bind_pure_comp f x := by
    apply NonEmptyArray.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.singleton, Array.mapNonEmptyArray,
        NonEmptyArray.toArr, id_eq, Array.flatMap_map, Array.append_empty,
        ← Array.map_eq_flatMap, Array.empty_append, NonEmptyArray.map_tail]

  bind_map f x := by
    apply NonEmptyArray.ext
    · rfl
    · obtain ⟨fh, ft⟩ := f
      obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, NonEmptyArray.map_head, NonEmptyArray.map_tail,
        Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq, Seq.seq, NonEmptyArray.seq,
        Array.append_eq_append, Array.flatMap_map]
      -- Simplify the remaining Functor.map and unify Array operations
      rfl


  bind_assoc x f g := by
    apply NonEmptyArray.ext
    · simp only [bind, NonEmptyArray.flatten, Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq,
      Array.map_append, Array.flatMap_append, Array.append_assoc]
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq,
        Array.map_append, Array.flatMap_append, Array.append_assoc]
      cases xt with | mk l =>
      induction l generalizing f g
      · simp only [Array.flatMap_map, List.map_toArray, List.map_nil, List.flatMap_toArray,
        Array.toList_append, List.cons_append, List.nil_append, List.flatMap_nil,
        Array.append_empty]
      · rename_i a as ih
        simp_all only [Array.flatMap_map, List.map_toArray, List.flatMap_toArray,
          Array.toList_append, List.cons_append, List.nil_append, List.flatMap_map,
          List.flatMap_assoc, List.flatMap_cons, Array.toList_flatMap, implies_true, List.map_cons,
          List.map_append, List.flatMap_append, List.append_assoc]

end NonEmpty.ArrayCorrectByConstruction
