module

@[expose] public section

/-!
# The indices of a range are its members

`for h : i in r` over a range `r : Std.Legacy.Range` hands the body a proof `h : i ∈ r`.
`#leanscript_to_term` translates such a loop as the loop over `[:r.size]` whose body, at
`j`, reads the index `r.start + j * r.step` (see `LeanScript/ToTerm/ForIn.lean`), and the
proof it hands the body at that index is `Std.Legacy.Range.mem_start_add_mul_step`: every
`r.start + j * r.step` with `j < r.size` is a member of `r`.

The module is imported by the translator's command (`LeanScript/ToTerm/Elab.lean`), so the
lemma is in scope wherever `#leanscript_to_term` is.
-/

namespace Std.Legacy.Range

/-- The `j`-th index of a range, `r.start + j * r.step` for `j < r.size`, is a member of
    it. -/
theorem mem_start_add_mul_step (r : Std.Legacy.Range) {j : Nat} (h : j < r.size) :
    r.start + j * r.step ∈ r :=
  mem_of_mem_range' (List.mem_range'.2 ⟨j, h, by rw [Nat.mul_comm]⟩)

end Std.Legacy.Range

end
