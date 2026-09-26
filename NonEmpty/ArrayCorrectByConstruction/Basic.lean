module
import Init.Data.Array.Lemmas
public import NonEmpty.ArrayUtil

@[expose] public section

-- why this is needed? for https://github.com/leanprover/lean4/issues/4964#issuecomment-4337841019
namespace NonEmpty.ArrayCorrectByConstruction

@[ext]
structure NonEmptyArray (α : Type u) where
  head : α
  tail : Array α
  deriving Hashable, Ord, Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

instance [ToString α] : ToString (NonEmptyArray α) where
  toString a := "#!" ++ toString (#[a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := ⟨default, #[]⟩

namespace NonEmptyArray

@[simp] abbrev toArr (xs : NonEmptyArray α) : Array α :=
  #[xs.head] ++ xs.tail

@[simp] protected def _root_.Array.mapNonEmptyArray (as : Array α) (f : α → NonEmptyArray β) : Array β :=
  as.flatMap (fun a => (f a).toArr)

@[simp] protected theorem _root_.Array.mapNonEmptyArray_id (as : Array (NonEmptyArray α)) :
    as.mapNonEmptyArray id = (as.map toArr).flatten := by
  simp only [Array.mapNonEmptyArray, Array.flatMap_def, id_def]

@[simp] abbrev size (xs : NonEmptyArray α) : Nat := 1 + xs.tail.size

-- @[inline_if_reduce] abbrev getElem (as : NonEmptyArray α) (i : Nat) (h : i < as.size) : α :=
--   match i with
--   | 0 => as.head
--   | n + 1 =>
--     have : n < as.tail.size := by
--       -- h is n + 1 < size xs
--       -- size xs is 1 + xs.tail.size
--       simp only [size] at h
--       omega
--     as.tail[n]'this

-- @[always_inline] abbrev getElem? (as : NonEmptyArray α) (i : Nat) : Option α :=
--   if h : i < as.size then some (as.getElem i h) else none

instance : GetElem (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  getElem as i h :=
    match i with
  | 0 => as.head
  | n + 1 =>
    have : n < as.tail.size := by
      -- h is n + 1 < size xs
      -- size xs is 1 + xs.tail.size
      simp only [size] at h
      omega
    as.tail[n]'this

instance : GetElem? (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  getElem? as i := if h : i < as.size then as[i]'h else none

-- @[simp] theorem getElem?_def (as : NonEmptyArray α) (i : Nat) [Decidable (i < as.size)] :
--     as[i]? = if h : i < as.size then some as[i] else none := by
--   simp_all only [size]
--   split
--   next h => simp_all only [size, getElem?_pos]
--   next h => simp_all only [Nat.not_lt, size, getElem?_neg]

-- @[simp] theorem getElem!_def [Inhabited α] (as : NonEmptyArray α) (i : Nat) :
--     as[i]! = match as[i]? with | some e => e | none => default := rfl

-- @[simp] theorem getElem!_def_if [Inhabited α] (as : NonEmptyArray α) (i : Nat) [Decidable (i < as.size)] :
--     as[i]! = if h : i < as.size then as[i] else default := by
--   simp_all only [size, getElem!_def, getElem?_def]
--   split
--   next x e heq =>
--     simp_all only [Option.dite_none_right_eq_some, Option.some.injEq]
--     obtain ⟨w, h⟩ := heq
--     subst h
--     simp_all only [↓reduceDIte]
--   next x heq =>
--     simp_all only [dif_neg_iff, reduceCtorEq, imp_false, Nat.not_lt, right_eq_dite_iff]
--     intro h
--     grind only

instance : LawfulGetElem (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  -- getElem?_def := getElem?_def
  -- getElem!_def := getElem!_def

@[simp] theorem size_toArr (as : NonEmptyArray α) : as.toArr.size = as.size := by
  simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, size]

@[simp] theorem toArr_getElem (as : NonEmptyArray α) (i : Nat) (h : i < as.size) :
    as.toArr[i]'(by simp only [size_toArr]; exact h) = as[i] := by
  simp only [GetElem.getElem];
  simp_all only [toArr, Array.getInternal_eq_getElem, size]
  split
  next i h h_1 =>
    simp_all only [size, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
      Array.getElem_append_left, List.getElem_toArray, List.getElem_cons_zero]
  next i h n h_1 =>
    simp_all only [size, Nat.succ_eq_add_one, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.le_add_left, Array.getElem_append_right, Nat.add_one_sub_one]

@[simp] theorem getElem?_eq_toArr_getElem? (as : NonEmptyArray α) (i : Nat) :
    as[i]? = as.toArr[i]? := by
  rw [getElem?_def]
  split
  · next h =>
    have h' : i < as.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, h]
    rw [getElem?_pos as.toArr i h', toArr_getElem]
  · next h =>
    have h' : ¬i < as.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, h, not_false_eq_true]
    rw [getElem?_neg as.toArr i h']

@[simp] abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs[0]'h, xs[1:]⟩ else none

@[simp] abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty array"

@[simp] abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨a, #[xs.head] ++ xs.tail⟩

@[simp] abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyArray (NonEmptyArray α)) : NonEmptyArray α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ t.mapNonEmptyArray id⟩

-- not needed ever
-- @[simp] def foldl (f : β → α → β) (init : β) (xs : NonEmptyArray α) : β :=
--   xs.tail.foldl f (f init xs.head)

@[inline]
def foldlM1 [Monad m] (f : β → α → m β) (g : α → m β) (as : NonEmptyArray α) : m β := do
  as.tail.foldlM f (← g as.head)

def foldrM1 [Monad m] (f : α → β → m β) (g : α → m β) (as : NonEmptyArray α) : m β := do
  let sz := as.tail.size
  if h : 0 < sz then
    -- Use the last element of the tail as the initial seed.
    -- .back h is a safe way to get as.tail[sz-1]
    let init ← g (as.tail.back h)
    -- foldrM with start := sz - 1 begins folding from index sz - 2 down to 0.
    let accumulated ← as.tail.foldrM f init (start := sz - 1)
    -- Combine the result with the head
    f as.head accumulated
  else
    -- Tail is empty, just transform the head
    g as.head

@[simp, inline] def foldl1 (f : b -> a -> b) (g : a -> b) (as : NonEmptyArray a) : b :=
  as.tail.foldl f (g as.head)

/--
Pure right fold for non-empty arrays.
`foldr1 f g [a, b, c]` is `f a (f b (g c))`
-/
@[inline]
def foldr1 (f : α → β → β) (g : α → β) (as : NonEmptyArray α) : β :=
  Id.run <| as.foldrM1 (fun a b => pure (f a b)) (fun a => pure (g a))

@[simp] def mapM [Monad m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) := do
  return ⟨← f as.head, ← as.tail.mapM f⟩

def mapM' [Monad m] (f : α → m β) (as : NonEmptyArray α) :
    m { bs : NonEmptyArray β // bs.size = as.size } := do
  let tail ← as.tail.mapM' f
  return ⟨⟨← f as.head, tail⟩, by
    simp_all only [size, Nat.add_left_cancel_iff]
    obtain ⟨val, property⟩ := tail
    simp_all only
  ⟩


@[simp] def mapFinIdxM [Monad m] (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (NonEmptyArray β) :=
  return ⟨← f 0 as.head (by simp only [size]; omega),
          ← as.tail.mapFinIdxM (fun i a h => f (i + 1) a (by simp only [size] at h ⊢; omega))⟩

@[simp] def mapIdxM [Monad m] (f : Nat → α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  as.mapFinIdxM (fun i a _ => f i a)

/-- Map a function over a NonEmptyArray, passing the index. -/
@[simp] def mapFinIdx (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → β) : NonEmptyArray β :=
  ⟨f 0 as.head (by simp only [size]; omega),
   as.tail.mapFinIdx (fun i a h => f (i + 1) a (by simp only [size] at h ⊢; omega))⟩

/-- Map a function over a NonEmptyArray, passing the index. -/
@[simp] def mapIdx (f : Nat → α → β) (as : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f 0 as.head,
   as.tail.mapIdx (fun i => f (i + 1))⟩


--------------------------------------------------------------------------------
-- API Mapped from standard `Array`
--------------------------------------------------------------------------------

@[simp] def toList (xs : NonEmptyArray α) : List α := xs.head :: xs.tail.toList
def toListAppend (xs : NonEmptyArray α) (l : List α) : List α := xs.toList ++ l

@[simp] def isEmpty (_xs : NonEmptyArray α) : Bool := false

def back (xs : NonEmptyArray α) : α := if h : xs.tail.size > 0 then xs.tail.back h else xs.head
def back! [Inhabited α] (xs : NonEmptyArray α) : α := xs.back
def back? (xs : NonEmptyArray α) : Option α := some xs.back

@[simp] theorem toArr_back (xs : NonEmptyArray α) : xs.toArr.back (by simp only [toArr,
  Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]; omega) = xs.back := by
  obtain ⟨h, t⟩ := xs
  simp only [toArr, Array.back_append, Array.isEmpty_iff, List.back_toArray, List.getLast_singleton,
    back, gt_iff_lt]
  split <;> simp_all only [left_eq_dite_iff, Nat.not_lt, Nat.le_zero_eq, Array.size_eq_zero_iff,
    false_implies, List.size_toArray, List.length_nil, Nat.lt_irrefl, ↓reduceDIte]

@[simp] theorem toArr_back? (xs : NonEmptyArray α) : xs.toArr.back? = xs.back? := by
  obtain ⟨h, t⟩ := xs
  rw [toArr, Array.back?_append, back?, back]
  split
  · next h_size =>
    rw [Array.back?_eq_getElem?, getElem?_pos (c := t) (i := t.size - 1) (h := Nat.sub_lt h_size (by decide))]
    simp only [List.back?_toArray, List.getLast?_singleton, Option.or_some, Option.getD_some,
      Array.back_eq_getElem]
  · next h_size =>
    have : t = #[] := Array.size_eq_zero_iff.1 (by simpa only [Array.size_eq_zero_iff, gt_iff_lt,
      Nat.not_lt, Nat.le_zero_eq] using h_size)
    simp only [this, List.back?_toArray, List.getLast?_nil, List.getLast?_singleton, Option.or_some,
      Option.getD_none]

@[simp] def singleton (a : α) : NonEmptyArray α := ⟨a, #[]⟩

@[simp] theorem _root_.Array.mapNonEmptyArray_singleton (as : Array α) (f : α → β) :
    as.mapNonEmptyArray (fun a => singleton (f a)) = as.map f := by
  simp only [Array.mapNonEmptyArray, toArr, singleton, Array.append_empty,
    ← Array.map_eq_flatMap]

@[simp] def ofFn {n : Nat} (f : Fin (n + 1) → α) : NonEmptyArray α :=
  ⟨f ⟨0, by omega⟩, Array.ofFn (fun (i : Fin n) => f ⟨i.val + 1, by omega⟩)⟩

@[simp] theorem size_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).size = n + 1 := by
  simp only [size, ofFn, Fin.zero_eta, Array.size_ofFn]; omega

@[simp] theorem getElem_ofFn {n : Nat} (f : Fin (n + 1) → α) (i : Nat) (h : i < (ofFn f).size) :
    (ofFn f)[i] = f ⟨i, by simp only [size, size_ofFn] at h; exact h⟩ := by
  simp only [ofFn, GetElem.getElem]
  simp_all only [Fin.zero_eta, size, Array.getInternal_eq_getElem, Array.getElem_ofFn]
  split
  next i h h_1 => simp_all only [size, Array.size_ofFn, Fin.zero_eta]
  next i h n_1 h_1 => simp_all only [size, Array.size_ofFn, Nat.succ_eq_add_one]

-- Modifications returning NonEmptyArray
def push (xs : NonEmptyArray α) (a : α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail.push a⟩

def set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.tail⟩
  else
    have : i - 1 < xs.tail.size := by simp only [size] at h; omega
    ⟨xs.head, xs.tail.set (i - 1) a this⟩

def set! (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i < xs.size then xs.set i a h else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def modify (xs : NonEmptyArray α) (i : Nat) (f : α → α) : NonEmptyArray α :=
  if h : i < xs.size then
    if h0 : i = 0 then ⟨f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp only [size] at h; omega
      ⟨xs.head, xs.tail.modify (i - 1) f⟩
  else xs

def modifyM [Monad m] (xs : NonEmptyArray α) (i : Nat) (f : α → m α) : m (NonEmptyArray α) := do
  if h : i < xs.size then
    if h0 : i = 0 then return ⟨← f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp only [size] at h; omega
      return ⟨xs.head, ← xs.tail.modifyM (i - 1) f⟩
  else return xs

def swap (xs : NonEmptyArray α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 ∧ j = 0 then xs
  else if h1 : i = 0 then
    let j' := j - 1; have : j' < xs.tail.size := by simp only [size] at hj; omega
    ⟨xs.tail[j'], xs.tail.set j' xs.head this⟩
  else if h2 : j = 0 then
    let i' := i - 1; have : i' < xs.tail.size := by simp only [size] at hi; omega
    ⟨xs.tail[i'], xs.tail.set i' xs.head this⟩
  else
    let i' := i - 1; have hi' : i' < xs.tail.size := by simp only [size] at hi; omega
    let j' := j - 1; have hj' : j' < xs.tail.size := by simp only [size] at hj; omega
    ⟨xs.head, xs.tail.swap i' j' hi' hj'⟩

def swap! (xs : NonEmptyArray α) (i j : Nat) : NonEmptyArray α :=
  if hi : i < xs.size then
    if hj : j < xs.size then xs.swap i j hi hj
    else
      have : Inhabited (NonEmptyArray α) := ⟨xs⟩
      panic! "invalid index"
  else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def swapAt (xs : NonEmptyArray α) (i : Nat) (v : α) (hi : i < xs.size) : α × NonEmptyArray α :=
  (xs[i]'hi, xs.set i v hi)

def swapAt! (xs : NonEmptyArray α) (i : Nat) (v : α) : α × NonEmptyArray α :=
  if hi : i < xs.size then xs.swapAt i v hi
  else
    have : Inhabited (α × NonEmptyArray α) := ⟨(v, xs)⟩
    panic! "invalid index"

end NonEmptyArray

end NonEmpty.ArrayCorrectByConstruction
