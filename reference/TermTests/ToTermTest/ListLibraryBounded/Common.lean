module

public import TermTests.ToTermTest.ListLibrary
public meta import LeanScript.KernelRfl

@[expose] public section

/-! # The translated `List` library programs, checked on every small input

`TermTests/ToTermTest/ListLibrary.lean` runs each translated program on a few inputs.
The modules of `TermTests/ToTermTest/ListLibraryBounded/` check each one against the Lean
function it came from on **every** input of a bounded size: every list of length at most
`3` whose entries are below `4` (85 lists), every index below `5`, every natural number
below `12`.  Each statement is a theorem, closed by `decide +kernel` (the kernel evaluates
the terms; no `native_decide`).

The statements are written with ordinary bounds (`l.length ≤ 3 → (∀ x ∈ l, x < 4) → …`);
`mem_smallLists` (proved for every `b` and `len`) turns them into a check over the
explicit list `smallLists 4 3`. -/

namespace TermTests.ToTerm.ListLibrary

/-- Every list of length at most `len` whose entries are below `b`. -/
def smallLists (b : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | len + 1 => [] :: (smallLists b len).flatMap fun l => (List.range b).map (· :: l)

/-- `smallLists b len` holds exactly the lists of length at most `len` with entries below
    `b`. -/
theorem mem_smallLists (b len : Nat) (l : List Nat) :
    l ∈ smallLists b len ↔ l.length ≤ len ∧ ∀ x ∈ l, x < b := by
  induction len generalizing l with
  | zero =>
      cases l with
      | nil => simp [smallLists]
      | cons x t => simp [smallLists]
  | succ len ih =>
      cases l with
      | nil => simp [smallLists]
      | cons x t =>
          simp only [smallLists, List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap,
            List.mem_map, List.mem_range, List.cons.injEq, List.length_cons,
            Nat.add_le_add_iff_right, ih]
          constructor
          · rintro ⟨l', ⟨hlen, ht⟩, y, hy, rfl, rfl⟩
            refine ⟨hlen, fun z hz => ?_⟩
            rcases hz with rfl | hz
            · exact hy
            · exact ht z hz
          · rintro ⟨hlen, h⟩
            exact ⟨t, ⟨hlen, fun z hz => h z (Or.inr hz)⟩, x, h x (Or.inl rfl), rfl, rfl⟩

/-- There are 85 of them for `b = 4`, `len = 3`: `1 + 4 + 16 + 64`. -/
theorem smallLists_length : (smallLists 4 3).length = 85 := by decide

/-- A check over `smallLists 4 3`, as a statement about every small list. -/
theorem forall_small (P : List Nat → Prop) (h : ∀ l ∈ smallLists 4 3, P l) (l : List Nat)
    (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) : P l :=
  h l ((mem_smallLists 4 3 l).mpr ⟨hlen, hx⟩)

end TermTests.ToTerm.ListLibrary
