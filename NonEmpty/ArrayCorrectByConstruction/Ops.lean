module
import Init.Data.Array.Lemmas
public import NonEmpty.ArrayCorrectByConstruction.Basic

@[expose] public section

/-!
Further operations on `NonEmptyArray` (conversion from a array, reversal, appending, zipping, searching, folds) and their `toList`/size lemmas.
-/

namespace NonEmpty.ArrayCorrectByConstruction

namespace NonEmptyArray

def fromArray (xs : Array α) (h : xs.size > 0) : NonEmptyArray α :=
  ⟨xs[0]'h, xs.extract 1 xs.size⟩


@[simp] theorem toArr_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).toArr = xs := by
  simp only [toArr, fromArray]
  have : #[xs[0]] = xs.extract 0 1 := by
    apply Array.ext
    · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Array.size_extract, Nat.sub_zero]; omega
    · intro i h1 h2
      have : i = 0 := by simp_all only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.lt_one_iff, Array.size_extract, Nat.sub_zero]
      subst i; simp only [List.getElem_toArray, List.getElem_cons_zero, Array.getElem_extract,
        Nat.add_zero]
  rw [this, Array.extract_append_extract]
  simp only [Nat.zero_le, Nat.min_eq_left, Array.extract_eq_self_iff, Array.size_eq_zero_iff,
    true_and]
  omega

@[simp] theorem size_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).size = xs.size := by
  simp_all only [size, fromArray, Array.size_extract, Std.le_refl, Nat.min_eq_left]
  omega

@[simp] theorem getElem_fromArray (xs : Array α) (h : xs.size > 0) (i : Nat) (hi : i < (fromArray xs h).size) :
  (fromArray xs h)[i] = xs[i]'(by simpa only [size, size_fromArray] using hi) := by
  cases i with
  | zero => rfl
  | succ i =>
    have hi' : i + 1 < (fromArray xs h).size := by simpa only [size, size_fromArray] using hi
    let elem := (fromArray xs h)[i + 1]'hi'
    have step : elem = (xs.extract 1)[i]'(by
      simp_all only [size, size_fromArray, Array.size_extract, Std.le_refl, Nat.min_eq_left];
      omega) := rfl
    have : (fromArray xs h)[i + 1] = elem := rfl
    rw [this, step, Array.getElem_extract]
    congr 1; omega

def reverse (xs : NonEmptyArray α) : NonEmptyArray α :=
  let arr := xs.toArr.reverse
  have : arr.size > 0 := by simp only [Array.reverse_append, List.reverse_toArray,
    List.reverse_cons, List.reverse_nil, List.nil_append, Array.append_singleton, Array.size_push,
    Array.size_reverse, gt_iff_lt, Nat.zero_lt_succ, arr]
  fromArray arr this

def append (xs ys : NonEmptyArray α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArr⟩

def appendArray (xs : NonEmptyArray α) (ys : Array α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys⟩

def appendList (xs : NonEmptyArray α) (ys : List α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArray⟩

def insertIdx (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i ≤ xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.toArr⟩
  else
    have : i - 1 ≤ xs.tail.size := by simp only [size] at h; omega
    ⟨xs.head, xs.tail.insertIdx (i - 1) a this⟩

def insertIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i ≤ xs.size then xs.insertIdx i a h else xs

def replace [BEq α] (xs : NonEmptyArray α) (a b : α) : NonEmptyArray α :=
  if xs.head == a then ⟨b, xs.tail⟩
  else ⟨xs.head, xs.tail.replace a b⟩

def zipWith (f : α → β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  ⟨f as.head bs.head, as.tail.zipWith f bs.tail⟩

def zipWithAll (f : Option α → Option β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  match fromArray? (as.toArr.zipWithAll f bs.toArr) with
  | some res => res
  | none => ⟨f (some as.head) (some bs.head), #[]⟩

def zipWithM [Monad m] (f : α → β → m γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : m (NonEmptyArray γ) := do
  return ⟨← f as.head bs.head, ← as.tail.zipWithM f bs.tail⟩

def zip (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray (α × β) :=
  as.zipWith Prod.mk bs

def zipIdx (xs : NonEmptyArray α) (start := 0) : NonEmptyArray (α × Nat) :=
  ⟨(xs.head, start), xs.tail.zipIdx (start + 1)⟩

@[simp] theorem toArr_zipIdx (xs : NonEmptyArray α) (start := 0) :
    (xs.zipIdx start).toArr = xs.toArr.zipIdx start := by
  obtain ⟨head, tail⟩ := xs
  apply Array.ext
  · simp only [toArr, zipIdx, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Array.size_zipIdx]
  · intro i h1 h2
    simp only [toArr, zipIdx, Array.getElem_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
      Array.getElem_zipIdx]
    split <;> simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Array.size_zipIdx, Nat.add_zero, Prod.mk.injEq, true_and]
    · omega

def unzip (as : NonEmptyArray (α × β)) : NonEmptyArray α × NonEmptyArray β :=
  let (a, b) := as.toArr.unzip
  (match fromArray? a with | some a => a | none => ⟨as.head.1, #[]⟩,
   match fromArray? b with | some b => b | none => ⟨as.head.2, #[]⟩)

def flatMap (f : α → Array β) (xs : NonEmptyArray α) : Array β := xs.toArr.flatMap f
def flatMapNonEmpty (f : α → NonEmptyArray β) (xs : NonEmptyArray α) : NonEmptyArray β := flatten (xs.map f)

def leftpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.leftpad n a) with
  | some res => res
  | none => xs

def rightpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.rightpad n a) with
  | some res => res
  | none => xs

-- Functions returning potentially empty Array
def pop (xs : NonEmptyArray α) : Array α := xs.toArr.pop
def shrink (xs : NonEmptyArray α) (n : Nat) : Array α := xs.toArr.shrink n
def take (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.take i
def takeWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.takeWhile p
def drop (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.drop i
def filter (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.filter p
def filterMap (f : α → Option β) (xs : NonEmptyArray α) : Array β := xs.toArr.filterMap f

def eraseIdx (xs : NonEmptyArray α) (i : Nat) (h : i < xs.size) : Array α :=
  if h0 : i = 0 then
    xs.tail
  else
    have : i - 1 < xs.tail.size := by simp only [size] at h; omega
    #[xs.head] ++ xs.tail.eraseIdx (i - 1) this

def eraseIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) : Array α :=
  xs.toArr.eraseIdxIfInBounds i

def erase [BEq α] (xs : NonEmptyArray α) (a : α) : Array α := xs.toArr.erase a
def eraseP (xs : NonEmptyArray α) (p : α → Bool) : Array α := xs.toArr.eraseP p
def popWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.popWhile p
def reduceOption (xs : NonEmptyArray (Option α)) : Array α := xs.toArr.reduceOption
def partition (p : α → Bool) (xs : NonEmptyArray α) : Array α × Array α := xs.toArr.partition p

def getEvenElems (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.getEvenElems with
  | some res => res
  | none => ⟨xs.head, #[]⟩

def eraseReps [BEq α] (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.eraseReps with
  | some res => res
  | none => ⟨xs.head, #[]⟩

-- Queries / Searches
def foldr {β} (f : α → β → β) (init : β) (xs : NonEmptyArray α) : β := xs.toArr.foldr f init
def any (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.any p
def all (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.all p
def contains [BEq α] (xs : NonEmptyArray α) (a : α) : Bool := xs.toArr.contains a
def elem [BEq α] (a : α) (xs : NonEmptyArray α) : Bool := xs.toArr.elem a
def countP (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.countP p
def count [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.count a
def sum [Add α] [Zero α] (xs : NonEmptyArray α) : α := xs.toArr.sum
def find? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.find? p
def findSome? {β} (f : α → Option β) (xs : NonEmptyArray α) : Option β := xs.toArr.findSome? f
def findRev? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.findRev? p
def findIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option Nat := xs.toArr.findIdx? p
def findIdx (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.findIdx p
def findFinIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option (Fin xs.size) :=
  xs.toArr.findFinIdx? p |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toArr, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size] at h ⊢; omega⟩)
def finIdxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option (Fin xs.size) :=
  xs.toArr.finIdxOf? a |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toArr, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size] at h ⊢; omega⟩)
def idxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option Nat := xs.toArr.idxOf? a
def idxOf [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.idxOf a
def getMax (xs : NonEmptyArray α) (lt : α → α → Bool) : α := xs.tail.foldl (fun best a => if lt best a then a else best) xs.head
def isEqv (xs ys : NonEmptyArray α) (p : α → α → Bool) : Bool := xs.toArr.isEqv ys.toArr p
def isPrefixOf [BEq α] (xs ys : NonEmptyArray α) : Bool := xs.toArr.isPrefixOf ys.toArr
def allDiff [BEq α] (xs : NonEmptyArray α) : Bool := xs.toArr.allDiff

-- Monadic operations
def forM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forM f
def forRevM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forRevM f
def foldlM [Monad m] {β} (f : β → α → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldlM f init
def foldrM [Monad m] {β} (f : α → β → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldrM f init
def anyM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.anyM p
def allM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.allM p
def findM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option α) := xs.toArr.findM? p
def findSomeM? [Monad m] {β} (f : α → m (Option β)) (xs : NonEmptyArray α) : m (Option β) := xs.toArr.findSomeM? f
def findIdxM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option Nat) := xs.toArr.findIdxM? p

/--
Maps each element of the non-empty array to `ω`, and combines them using the
provided binary operation `op`.
Because the array is non-empty, no initial `mempty` or `init` value is required.
-/
@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (as : NonEmptyArray α) : ω :=
  as.tail.foldl (fun acc x => op acc (f x)) (f as.head)

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  (NonEmptyArray.mk · ·) <$> f as.head <*> NonEmpty.ArrayUtil.mapA f as.tail

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : NonEmptyArray (m α)) : m (NonEmptyArray α) :=
  as.mapA id

instance : Append (NonEmptyArray α) := ⟨append⟩
instance : HAppend (NonEmptyArray α) (Array α) (NonEmptyArray α) := ⟨appendArray⟩
instance : HAppend (NonEmptyArray α) (List α) (NonEmptyArray α) := ⟨appendList⟩

@[simp] theorem toArr_singleton (a : α) : (singleton a).toArr = #[a] := by
  simp_all only [toArr, Array.append_eq_toArray_iff, List.cons_append, List.nil_append, List.cons.injEq, Array.toList_eq_nil_iff]
  apply And.intro
  · rfl
  · rfl
@[simp] theorem toArr_push (xs : NonEmptyArray α) (a : α) : (xs.push a).toArr = xs.toArr.push a := by
  simp_all only [toArr, Array.push_append]
  rfl
@[simp] theorem toArr_map (f : α → β) (xs : NonEmptyArray α) : (xs.map f).toArr = xs.toArr.map f := by
  simp_all only [toArr, Array.map_append, List.map_toArray, List.map_cons, List.map_nil]

@[simp] theorem toArr_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).toArr = Array.ofFn f := by
  simp only [toArr, ofFn, Fin.zero_eta]
  apply Array.ext
  · simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Array.size_ofFn]; omega
  · intro i h1 h2
    simp only [Array.getElem_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
      Array.getElem_ofFn]
    split <;> rename_i h_i
    · subst h_i
      simp_all only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Array.size_ofFn, Fin.zero_eta]
    · congr; omega
@[simp] theorem size_append (xs ys : NonEmptyArray α) : (xs ++ ys).size = xs.size + ys.size := by
  show (append xs ys).size = xs.size + ys.size
  unfold append
  simp only [size, toArr, Array.append_singleton_assoc, Array.size_append, Array.size_push]
  omega
@[simp] theorem toArr_append (xs ys : NonEmptyArray α) : (xs ++ ys).toArr = xs.toArr ++ ys.toArr := by
  show (append xs ys).toArr = xs.toArr ++ ys.toArr
  unfold append
  show #[xs.head] ++ (xs.tail ++ ys.toArr) = (#[xs.head] ++ xs.tail) ++ ys.toArr
  rw [Array.append_assoc]
@[simp] theorem toArr_set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) :
    (xs.set i a h).toArr = xs.toArr.set i a (by simp only [toArr, Array.size_append,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]; exact h) := by
  unfold set; split
  · subst i; simp only [toArr, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_add_one, Array.set_append_left, List.set_toArray, List.set_cons_zero]
  · have h' : i < xs.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add]; exact h
    rw [Array.set_append_right h' (by simp only [List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add]; omega)]
    simp only [toArr, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]

@[simp] theorem size_reverse (xs : NonEmptyArray α) : xs.reverse.size = xs.size := by
  simp only [size, reverse, toArr, Array.reverse_append, List.reverse_toArray, List.reverse_cons,
    List.reverse_nil, List.nil_append, Array.append_singleton, size_fromArray, Array.size_push,
    Array.size_reverse]
  omega

@[simp] theorem toArr_reverse (xs : NonEmptyArray α) : xs.reverse.toArr = xs.toArr.reverse := by
  simp only [toArr, reverse, Array.reverse_append, List.reverse_toArray, List.reverse_cons,
    List.reverse_nil, List.nil_append, Array.append_singleton, toArr_fromArray]

end NonEmptyArray

end NonEmpty.ArrayCorrectByConstruction
