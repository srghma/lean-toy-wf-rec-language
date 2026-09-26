module
import Init.Data.List.Lemmas
-- public import NonEmpty.ListUtil

@[expose] public section

-- why this is needed? for https://github.com/leanprover/lean4/issues/4964#issuecomment-4337841019
namespace NonEmpty.ListCorrectByConstruction

@[ext]
structure NonEmptyList (α : Type u) where
  head : α
  tail : List α
  deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

instance [ToString α] : ToString (NonEmptyList α) where
  toString a := "!" ++ toString ([a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyList α) where
  default := ⟨default, []⟩

namespace NonEmptyList

@[simp] abbrev toList (xs : NonEmptyList α) : List α :=
  List.cons xs.head xs.tail

@[simp] protected def _root_.List.mapNonEmptyList (as : List α) (f : α → NonEmptyList β) : List β :=
  as.flatMap (fun a => (f a).toList)

@[simp] protected theorem _root_.List.mapNonEmptyList_id (as : List (NonEmptyList α)) :
    as.mapNonEmptyList id = (as.map toList).flatten := by
  simp only [List.mapNonEmptyList, List.flatMap_def, id_def]

@[simp] abbrev length (xs : NonEmptyList α) : Nat := 1 + xs.tail.length

-- @[inline_if_reduce] abbrev getElem (as : NonEmptyList α) (i : Nat) (h : i < as.length) : α :=
--   match i with
--   | 0 => as.head
--   | n + 1 =>
--     have : n < as.tail.length := by
--       -- h is n + 1 < length xs
--       -- length xs is 1 + xs.tail.length
--       simp only [length] at h
--       omega
--     as.tail[n]'this

-- @[always_inline] abbrev getElem? (as : NonEmptyList α) (i : Nat) : Option α :=
--   if h : i < as.length then some (as.getElem i h) else none

instance : GetElem (NonEmptyList α) Nat α (fun as i => i < as.length) where
  getElem as i h :=
    match i with
  | 0 => as.head
  | n + 1 =>
    have : n < as.tail.length := by
      -- h is n + 1 < length xs
      -- length xs is 1 + xs.tail.length
      simp only [length] at h
      omega
    as.tail[n]'this

instance : GetElem? (NonEmptyList α) Nat α (fun as i => i < as.length) where
  getElem? as i := if h : i < as.length then as[i]'h else none

-- @[simp] theorem getElem?_def (as : NonEmptyList α) (i : Nat) [Decidable (i < as.length)] :
--     as[i]? = if h : i < as.length then some as[i] else none := by
--   simp_all only [length]
--   split
--   next h => simp_all only [length, getElem?_pos]
--   next h => simp_all only [Nat.not_lt, length, getElem?_neg]

-- @[simp] theorem getElem!_def [Inhabited α] (as : NonEmptyList α) (i : Nat) :
--     as[i]! = match as[i]? with | some e => e | none => default := rfl

-- @[simp] theorem getElem!_def_if [Inhabited α] (as : NonEmptyList α) (i : Nat) [Decidable (i < as.length)] :
--     as[i]! = if h : i < as.length then as[i] else default := by
--   simp_all only [length, getElem!_def, getElem?_def]
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

instance : LawfulGetElem (NonEmptyList α) Nat α (fun as i => i < as.length) where
  -- getElem?_def := getElem?_def
  -- getElem!_def := getElem!_def

@[simp] theorem length_toList (as : NonEmptyList α) : as.toList.length = as.length := by
  simp_all only [toList, List.length_cons, length]
  simp +arith only

@[simp] theorem toList_getElem (as : NonEmptyList α) (i : Nat) (h : i < as.length) :
    as.toList[i]'(by simp only [length_toList]; exact h) = as[i] := by
  cases as with
  | mk hd tl => cases i with
    | zero => rfl
    | succ n => rfl

@[simp] theorem getElem?_eq_toList_getElem? (as : NonEmptyList α) (i : Nat) :
    as[i]? = as.toList[i]? := by
  have : as.length = as.toList.length := by simp only [length_toList]
  if h : i < as.length then
    have h' : i < as.toList.length := by omega
    simp only [getElem?_pos as i h, getElem?_pos as.toList i h']
    simp_all only [length, toList, List.length_cons, Option.some.injEq]
    exact Eq.symm (toList_getElem as i h)
  else
    have h' : ¬(i < as.toList.length) := by omega
    simp only [getElem?_neg as i h, getElem?_neg as.toList i h']

@[simp] abbrev fromList? (xs : List α) : Option (NonEmptyList α) :=
  match xs with
  | [] => none
  | x :: xs => some ⟨x, xs⟩

@[simp] abbrev fromList! [Inhabited α] (xs : List α) : NonEmptyList α :=
  match fromList? xs with
  | some xs => xs
  | none => panic! "Expected non-empty list"

@[simp] abbrev cons (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  ⟨a, [xs.head] ++ xs.tail⟩

@[simp] abbrev map (f : α → β) (xs : NonEmptyList α) : NonEmptyList β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyList (NonEmptyList α)) : NonEmptyList α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ t.mapNonEmptyList id⟩

-- not needed ever
-- @[simp] def foldl (f : β → α → β) (init : β) (xs : NonEmptyList α) : β :=
--   xs.tail.foldl f (f init xs.head)

@[inline]
def foldlM1 [Monad m] (f : β → α → m β) (g : α → m β) (as : NonEmptyList α) : m β := do
  as.tail.foldlM f (← g as.head)

def foldrM1 [Monad m] (f : α → β → m β) (g : α → m β) (as : NonEmptyList α) : m β :=
  let rec go (x : α) (xs : List α) : m β :=
    match xs with
    | [] => g x
    | y :: ys => do f x (← go y ys)
  go as.head as.tail

@[simp, inline] def foldl1 (f : b -> a -> b) (g : a -> b) (as : NonEmptyList a) : b :=
  as.tail.foldl f (g as.head)

/--
Pure right fold for non-empty arrays.
`foldr1 f g [a, b, c]` is `f a (f b (g c))`
-/
@[inline]
def foldr1 (f : α → β → β) (g : α → β) (as : NonEmptyList α) : β :=
  Id.run <| as.foldrM1 (fun a b => pure (f a b)) (fun a => pure (g a))

@[simp] def mapM [Monad m] (f : α → m β) (as : NonEmptyList α) : m (NonEmptyList β) := do
  return ⟨← f as.head, ← as.tail.mapM f⟩

def mapM' [Monad m] (f : α → m β) (as : NonEmptyList α) :
    m { bs : NonEmptyList β // bs.length = as.length } := do
  let rec go (xs : List α) : m { bs : List β // bs.length = xs.length } :=
    match xs with
    | [] => return ⟨[], rfl⟩
    | x :: xs => do
      let x' ← f x
      let ⟨xs', h_xs'⟩ ← go xs
      return ⟨x' :: xs', by simp only [List.length_cons, h_xs']⟩
  let head' ← f as.head
  let ⟨tail', h_tail'⟩ ← go as.tail
  return ⟨⟨head', tail'⟩, by simp only [length, h_tail']⟩


@[simp] def mapFinIdxM [Monad m] (as : NonEmptyList α) (f : (i : Nat) → α → (h : i < as.length) → m β) : m (NonEmptyList β) :=
  return ⟨← f 0 as.head (by simp only [length]; omega),
          ← as.tail.mapFinIdxM (fun i a h => f (i + 1) a (by simp only [length] at h ⊢; omega))⟩

@[simp] def mapIdxM [Monad m] (f : Nat → α → m β) (as : NonEmptyList α) : m (NonEmptyList β) :=
  as.mapFinIdxM (fun i a _ => f i a)

/-- Map a function over a NonEmptyList, passing the index. -/
@[simp] def mapFinIdx (as : NonEmptyList α) (f : (i : Nat) → α → (h : i < as.length) → β) : NonEmptyList β :=
  ⟨f 0 as.head (by simp only [length]; omega),
   as.tail.mapFinIdx (fun i a h => f (i + 1) a (by simp only [length] at h ⊢; omega))⟩

/-- Map a function over a NonEmptyList, passing the index. -/
@[simp] def mapIdx (f : Nat → α → β) (as : NonEmptyList α) : NonEmptyList β :=
  ⟨f 0 as.head,
   as.tail.mapIdx (fun i => f (i + 1))⟩


--------------------------------------------------------------------------------
-- API Mapped from standard `List`
--------------------------------------------------------------------------------

def toListAppend (xs : NonEmptyList α) (l : List α) : List α := xs.toList ++ l

@[simp] def isEmpty (_xs : NonEmptyList α) : Bool := false

def back (xs : NonEmptyList α) : α := xs.tail.getLast? |>.getD xs.head
def back! [Inhabited α] (xs : NonEmptyList α) : α := xs.back
def back? (xs : NonEmptyList α) : Option α := some xs.back

@[simp] theorem toList_back (xs : NonEmptyList α) : xs.toList.getLast (by simp_all only [toList, ne_eq, reduceCtorEq,
  not_false_eq_true]) = xs.back := by
  obtain ⟨h, t⟩ := xs
  simp_all only [toList]
  grind [= back]

@[simp] theorem toList_back? (xs : NonEmptyList α) : xs.toList.getLast? = xs.back? := by
  obtain ⟨h, t⟩ := xs
  simp only [toList, back?, back, List.getLast?_cons]

@[simp] def singleton (a : α) : NonEmptyList α := ⟨a, []⟩

@[simp] theorem _root_.List.mapNonEmptyList_singleton (as : List α) (f : α → β) :
    as.mapNonEmptyList (fun a => singleton (f a)) = as.map f := by
  simp_all only [List.mapNonEmptyList, toList, singleton]
  exact Eq.symm List.map_eq_flatMap

@[simp] def ofFn {n : Nat} (f : Fin (n + 1) → α) : NonEmptyList α :=
  ⟨f ⟨0, by omega⟩, List.ofFn (fun (i : Fin n) => f ⟨i.val + 1, by omega⟩)⟩

@[simp] theorem length_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).length = n + 1 := by
  simp only [length, ofFn, Fin.zero_eta, List.length_ofFn]; omega

@[simp] theorem getElem_ofFn {n : Nat} (f : Fin (n + 1) → α) (i : Nat) (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp only [length, length_ofFn] at h; exact h⟩ := by
  simp only [ofFn, GetElem.getElem]
  simp_all only [Fin.zero_eta, length, List.get_eq_getElem, List.getElem_ofFn]
  split
  next i h h_1 => simp_all only [length, List.length_ofFn, Fin.zero_eta]
  next i h n_1 h_1 => simp_all only [length, List.length_ofFn, Nat.succ_eq_add_one]

-- Modifications returning NonEmptyList
def concat (xs : NonEmptyList α) (a : α) : NonEmptyList α :=
  ⟨xs.head, xs.tail.concat a⟩

def set (xs : NonEmptyList α) (i : Nat) (a : α) (h : i < xs.length) : NonEmptyList α :=
  if h0 : i = 0 then
    ⟨a, xs.tail⟩
  else
    have : i - 1 < xs.tail.length := by simp only [length] at h; omega
    ⟨xs.head, xs.tail.set (i - 1) a⟩

def set! (xs : NonEmptyList α) (i : Nat) (a : α) : NonEmptyList α :=
  if h : i < xs.length then xs.set i a h else
    have : Inhabited (NonEmptyList α) := ⟨xs⟩
    panic! "invalid index"

def modify (xs : NonEmptyList α) (i : Nat) (f : α → α) : NonEmptyList α :=
  if h : i < xs.length then
    if h0 : i = 0 then ⟨f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.length := by simp only [length] at h; omega
      ⟨xs.head, xs.tail.modify (i - 1) f⟩
  else xs

-- commented out bc List dont have modifyM (weirdly)
-- def modifyM [Monad m] (xs : NonEmptyList α) (i : Nat) (f : α → m α) : m (NonEmptyList α) := do
--   if h : i < xs.length then
--     if h0 : i = 0 then return ⟨← f xs.head, xs.tail⟩
--     else
--       have : i - 1 < xs.tail.length := by simp only [length] at h; omega
--       return ⟨xs.head, ← xs.tail.modifyM (i - 1) f⟩
--   else return xs

-- def swap (xs : NonEmptyList α) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) : NonEmptyList α :=
--   if h0 : i = 0 ∧ j = 0 then xs
--   else if h1 : i = 0 then
--     let j' := j - 1; have : j' < xs.tail.length := by simp only [length] at hj; omega
--     ⟨xs.tail[j'], xs.tail.set j' xs.head this⟩
--   else if h2 : j = 0 then
--     let i' := i - 1; have : i' < xs.tail.length := by simp only [length] at hi; omega
--     ⟨xs.tail[i'], xs.tail.set i' xs.head this⟩
--   else
--     let i' := i - 1; have hi' : i' < xs.tail.length := by simp only [length] at hi; omega
--     let j' := j - 1; have hj' : j' < xs.tail.length := by simp only [length] at hj; omega
--     ⟨xs.head, xs.tail.swap i' j' hi' hj'⟩

-- def swap! (xs : NonEmptyList α) (i j : Nat) : NonEmptyList α :=
--   if hi : i < xs.length then
--     if hj : j < xs.length then xs.swap i j hi hj
--     else
--       have : Inhabited (NonEmptyList α) := ⟨xs⟩
--       panic! "invalid index"
--   else
--     have : Inhabited (NonEmptyList α) := ⟨xs⟩
--     panic! "invalid index"

-- def swapAt (xs : NonEmptyList α) (i : Nat) (v : α) (hi : i < xs.length) : α × NonEmptyList α :=
--   (xs[i]'hi, xs.set i v hi)

-- def swapAt! (xs : NonEmptyList α) (i : Nat) (v : α) : α × NonEmptyList α :=
--   if hi : i < xs.length then xs.swapAt i v hi
--   else
--     have : Inhabited (α × NonEmptyList α) := ⟨(v, xs)⟩
--     panic! "invalid index"

end NonEmptyList

end NonEmpty.ListCorrectByConstruction
