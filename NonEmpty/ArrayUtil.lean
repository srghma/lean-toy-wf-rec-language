module

@[expose] public section

namespace NonEmpty.ArrayUtil

@[simp] theorem flatten_map_singleton (t : Array α) (f : α → β) :
    (t.map (fun a => #[f a])).flatten = t.map f := by
  simp [← Array.flatMap_def, ← Array.map_eq_flatMap]

@[simp] theorem append_flatten_assoc (a : Array α) (b : Array (Array α)) (c : Array (Array α)) :
    a ++ (b ++ c).flatten = a ++ b.flatten ++ c.flatten := by
  simp only [Array.flatten_append, Array.append_assoc]

@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (init : ω) (as : Array α) : ω :=
  as.foldl (fun acc x => op acc (f x)) init

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : Array α) : m (Array β) :=
  as.foldl (fun macc x => (fun acc y => acc.push y) <$> macc <*> f x) (pure (Array.emptyWithCapacity as.size))

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : Array (m α)) : m (Array α) :=
  mapA id as

end NonEmpty.ArrayUtil
