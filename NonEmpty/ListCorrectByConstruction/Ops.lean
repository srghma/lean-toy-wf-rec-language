module
import Init.Data.List.Lemmas
public import NonEmpty.ListCorrectByConstruction.Basic

@[expose] public section

/-!
Further operations on `NonEmptyList` (conversion from a list, reversal, appending, zipping, searching, folds) and their `toList`/size lemmas.
-/

namespace NonEmpty.ListCorrectByConstruction

namespace NonEmptyList

def fromList (xs : List α) (h : xs.length > 0) : NonEmptyList α :=
  ⟨xs[0]'h, xs.extract 1 xs.length⟩


@[simp] theorem toList_fromList (xs : List α) (h : xs.length > 0) :
  (fromList xs h).toList = xs := by
  simp only [toList, fromList]
  cases xs with
  | nil => contradiction
  | cons x xs' =>
    simp only [List.extract_eq_take_drop, List.drop_succ_cons, List.drop_zero, List.length_cons,
      Nat.add_sub_cancel, List.take_length, List.getElem_cons_zero]

@[simp] theorem length_fromList (xs : List α) (h : xs.length > 0) :
  (fromList xs h).length = xs.length := by
  simp_all only [length]
  grind [= tail.eq_def, = fromList.eq_def]

@[simp] theorem getElem_fromList (xs : List α) (h : xs.length > 0) (i : Nat) (hi : i < (fromList xs h).length) :
  (fromList xs h)[i] = xs[i]'(by simpa only [length, length_fromList] using hi) := by
  cases i with
  | zero => rfl
  | succ i =>
    cases xs with
    | nil => contradiction
    | cons x xs' =>
      have eq1 : (x :: xs').length - 1 = xs'.length := rfl
      simp only [fromList, GetElem.getElem]
      simp_all only [List.length_cons, Nat.add_one_sub_one, List.get_eq_getElem,
        List.getElem_cons_succ]
      simp only [List.extract_eq_take_drop, Nat.add_one_sub_one, List.drop_succ_cons,
        List.drop_zero, List.take_length]

def reverse (xs : NonEmptyList α) : NonEmptyList α :=
  let arr := xs.toList.reverse
  have : arr.length > 0 := by
    simp_all only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil,
      Nat.zero_add, gt_iff_lt, Nat.zero_lt_succ, arr]
  fromList arr this

def append (xs ys : NonEmptyList α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ ys.toList⟩

def appendList (xs : NonEmptyList α) (ys : List α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ ys⟩

def insertIdx (xs : NonEmptyList α) (i : Nat) (a : α) (h : i ≤ xs.length) : NonEmptyList α :=
  if h0 : i = 0 then
    ⟨a, xs.toList⟩
  else
    have : i - 1 ≤ xs.tail.length := by simp only [length] at h; omega
    ⟨xs.head, xs.tail.insertIdx (i - 1) a⟩

def insertIdxIfInBounds (xs : NonEmptyList α) (i : Nat) (a : α) : NonEmptyList α :=
  if h : i ≤ xs.length then xs.insertIdx i a h else xs

def replace [BEq α] (xs : NonEmptyList α) (a b : α) : NonEmptyList α :=
  if xs.head == a then ⟨b, xs.tail⟩
  else ⟨xs.head, xs.tail.replace a b⟩

def zipWith (f : α → β → γ) (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList γ :=
  ⟨f as.head bs.head, as.tail.zipWith f bs.tail⟩

def zipWithAll (f : Option α → Option β → γ) (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList γ :=
  match fromList? (as.toList.zipWithAll f bs.toList) with
  | some res => res
  | none => ⟨f (some as.head) (some bs.head), []⟩

def zipWithM [Monad m] (f : α → β → m γ) (as : NonEmptyList α) (bs : NonEmptyList β) : m (NonEmptyList γ) := do
  return ⟨← f as.head bs.head, ← as.tail.zipWithM f bs.tail⟩

def zip (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList (α × β) :=
  as.zipWith Prod.mk bs

def zipIdx (xs : NonEmptyList α) (start := 0) : NonEmptyList (α × Nat) :=
  ⟨(xs.head, start), xs.tail.zipIdx (start + 1)⟩

@[simp] theorem toList_zipIdx (xs : NonEmptyList α) (start := 0) :
    (xs.zipIdx start).toList = xs.toList.zipIdx start := by
  obtain ⟨head, tail⟩ := xs
  simp_all only [toList, List.zipIdx_cons, List.cons.injEq]
  apply And.intro
  · rfl
  · rfl

def unzip (as : NonEmptyList (α × β)) : NonEmptyList α × NonEmptyList β :=
  let (a, b) := as.toList.unzip
  (match fromList? a with | some a => a | none => ⟨as.head.1, []⟩,
   match fromList? b with | some b => b | none => ⟨as.head.2, []⟩)

def flatMap (f : α → List β) (xs : NonEmptyList α) : List β := xs.toList.flatMap f
def flatMapNonEmpty (f : α → NonEmptyList β) (xs : NonEmptyList α) : NonEmptyList β := flatten (xs.map f)

def leftpad (n : Nat) (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? (xs.toList.leftpad n a) with
  | some res => res
  | none => xs

def rightpad (n : Nat) (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? (xs.toList.rightpad n a) with
  | some res => res
  | none => xs

-- Functions returning potentially empty List
-- def pop (xs : NonEmptyList α) : List α := xs.toList.pop
-- def shrink (xs : NonEmptyList α) (n : Nat) : List α := xs.toList.shrink n
def take (xs : NonEmptyList α) (i : Nat) : List α := xs.toList.take i
def takeWhile (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.takeWhile p
def drop (xs : NonEmptyList α) (i : Nat) : List α := xs.toList.drop i
def filter (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.filter p
def filterMap (f : α → Option β) (xs : NonEmptyList α) : List β := xs.toList.filterMap f

def eraseIdx (xs : NonEmptyList α) (i : Nat) : List α :=
  if i = 0 then
    xs.tail
  else
    xs.head :: xs.tail.eraseIdx (i - 1)

-- def eraseIdxIfInBounds (xs : NonEmptyList α) (i : Nat) : List α :=
--   xs.toList.eraseIdxIfInBounds i

def erase [BEq α] (xs : NonEmptyList α) (a : α) : List α := xs.toList.erase a
def eraseP (xs : NonEmptyList α) (p : α → Bool) : List α := xs.toList.eraseP p
-- def popWhile (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.popWhile p
def reduceOption (xs : NonEmptyList (Option α)) : List α := xs.toList.reduceOption
def partition (p : α → Bool) (xs : NonEmptyList α) : List α × List α := xs.toList.partition p

-- def getEvenElems (xs : NonEmptyList α) : NonEmptyList α :=
--   match fromList? xs.toList.getEvenElems with
--   | some res => res
--   | none => ⟨xs.head, []⟩

def eraseReps [BEq α] (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? xs.toList.eraseReps with
  | some res => res
  | none => ⟨xs.head, []⟩

-- Queries / Searches
def foldr {β} (f : α → β → β) (init : β) (xs : NonEmptyList α) : β := xs.toList.foldr f init
def any (xs : NonEmptyList α) (p : α → Bool) : Bool := xs.toList.any p
def all (xs : NonEmptyList α) (p : α → Bool) : Bool := xs.toList.all p
def contains [BEq α] (xs : NonEmptyList α) (a : α) : Bool := xs.toList.contains a
def elem [BEq α] (a : α) (xs : NonEmptyList α) : Bool := xs.toList.elem a
def countP (p : α → Bool) (xs : NonEmptyList α) : Nat := xs.toList.countP p
def count [BEq α] (a : α) (xs : NonEmptyList α) : Nat := xs.toList.count a
def sum [Add α] [Zero α] (xs : NonEmptyList α) : α := xs.toList.sum
def find? (p : α → Bool) (xs : NonEmptyList α) : Option α := xs.toList.find? p
def findSome? {β} (f : α → Option β) (xs : NonEmptyList α) : Option β := xs.toList.findSome? f
def findRev? (p : α → Bool) (xs : NonEmptyList α) : Option α := xs.toList.findRev? p
def findIdx? (p : α → Bool) (xs : NonEmptyList α) : Option Nat := xs.toList.findIdx? p
def findIdx (p : α → Bool) (xs : NonEmptyList α) : Nat := xs.toList.findIdx p
def findFinIdx? (p : α → Bool) (xs : NonEmptyList α) : Option (Fin xs.length) :=
  xs.toList.findFinIdx? p |>.map (fun ⟨i, h⟩ => ⟨i, by
  simp only [toList, List.length_cons, length] at h ⊢; omega⟩)
def finIdxOf? [BEq α] (xs : NonEmptyList α) (a : α) : Option (Fin xs.length) :=
  xs.toList.finIdxOf? a |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toList, List.length_cons, length] at h ⊢; omega⟩)
def idxOf? [BEq α] (xs : NonEmptyList α) (a : α) : Option Nat := xs.toList.idxOf? a
def idxOf [BEq α] (a : α) (xs : NonEmptyList α) : Nat := xs.toList.idxOf a
def getMax (xs : NonEmptyList α) (lt : α → α → Bool) : α := xs.tail.foldl (fun best a => if lt best a then a else best) xs.head
def isEqv (xs ys : NonEmptyList α) (p : α → α → Bool) : Bool := xs.toList.isEqv ys.toList p
def isPrefixOf [BEq α] (xs ys : NonEmptyList α) : Bool := xs.toList.isPrefixOf ys.toList
-- def allDiff [BEq α] (xs : NonEmptyList α) : Bool := xs.toList.allDiff

-- Monadic operations
def forM [Monad m] (xs : NonEmptyList α) (f : α → m PUnit) : m PUnit := xs.toList.forM f
-- def forRevM [Monad m] (xs : NonEmptyList α) (f : α → m PUnit) : m PUnit := xs.toList.forRevM f
def foldlM [Monad m] {β} (f : β → α → m β) (init : β) (xs : NonEmptyList α) : m β := xs.toList.foldlM f init
def foldrM [Monad m] {β} (f : α → β → m β) (init : β) (xs : NonEmptyList α) : m β := xs.toList.foldrM f init
def anyM [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m Bool := xs.toList.anyM p
def allM [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m Bool := xs.toList.allM p
def findM? [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m (Option α) := xs.toList.findM? p
def findSomeM? [Monad m] {β} (f : α → m (Option β)) (xs : NonEmptyList α) : m (Option β) := xs.toList.findSomeM? f
def findIdxM? [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m (Option Nat) :=
  let rec go (i : Nat) (ys : List α) : m (Option Nat) :=
    match ys with
    | [] => return none
    | y :: ys' => do
      if ← p y then return some i else go (i + 1) ys'
  go 0 xs.toList

/--
Maps each element of the non-empty array to `ω`, and combines them using the
provided binary operation `op`.
Because the array is non-empty, no initial `mempty` or `init` value is required.
-/
@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (as : NonEmptyList α) : ω :=
  as.tail.foldl (fun acc x => op acc (f x)) (f as.head)

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : NonEmptyList α) : m (NonEmptyList β) :=
  (NonEmptyList.mk · ·) <$> f as.head <*> as.tail.mapA f

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : NonEmptyList (m α)) : m (NonEmptyList α) :=
  as.mapA id

instance : Append (NonEmptyList α) := ⟨append⟩
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) := ⟨appendList⟩
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) := ⟨appendList⟩

@[simp] theorem toList_singleton (a : α) : (singleton a).toList = [a] := by
  simp_all only [toList, singleton]
@[simp] theorem toList_concat (xs : NonEmptyList α) (a : α) : (xs.concat a).toList = xs.toList.concat a := by
  simp_all only [toList, List.concat_eq_append, List.cons_append, List.cons.injEq]
  apply And.intro
  · rfl
  · grind only [concat, = List.concat_eq_append]
@[simp] theorem toList_map (f : α → β) (xs : NonEmptyList α) : (xs.map f).toList = xs.toList.map f := by
  simp_all only [toList, List.map_cons]

@[simp] theorem toList_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).toList = List.ofFn f := by
  simp only [toList, ofFn, Fin.zero_eta]
  simp_all only [List.ofFn_succ, List.cons.injEq, true_and]
  rfl
@[simp] theorem length_append (xs ys : NonEmptyList α) : (xs ++ ys).length = xs.length + ys.length := by
  show (append xs ys).length = xs.length + ys.length
  unfold append
  simp_all only [length, toList, List.length_append, List.length_cons]
  simp +arith only
@[simp] theorem toList_append (xs ys : NonEmptyList α) : (xs ++ ys).toList = xs.toList ++ ys.toList := by
  show (append xs ys).toList = xs.toList ++ ys.toList
  unfold append
  show [xs.head] ++ (xs.tail ++ ys.toList) = ([xs.head] ++ xs.tail) ++ ys.toList
  rw [List.append_assoc]
@[simp] theorem toList_set (xs : NonEmptyList α) (i : Nat) (a : α) (h : i < xs.length) :
    (xs.set i a h).toList = xs.toList.set i a := by
  unfold set; split
  · rename_i h_1
    subst h_1
    simp_all only [length, toList, List.set_cons_zero]
  · cases i with
    | zero => contradiction
    | succ i' => rfl

@[simp] theorem length_reverse (xs : NonEmptyList α) : xs.reverse.length = xs.length := by
  simp only [reverse, length_fromList, List.length_reverse, length_toList]

@[simp] theorem toList_reverse (xs : NonEmptyList α) : xs.reverse.toList = xs.toList.reverse := by
  simp only [reverse, toList_fromList]

end NonEmptyList

end NonEmpty.ListCorrectByConstruction
