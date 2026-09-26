module

public import TermTests.RecUnionRecDepthTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: running the terms, part 2

The terms of `TermTests/RecUnionRecDepthTest.lean`, checked by the kernel against their
Lean references at the first ten arguments.  This file: the hexanacci numbers, the
tail-recursive loop and the pair recursion.  The checks are split over two
files so that they build in parallel.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP hexaTerm (peanoVal n) = Peano.hexa (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP fibTRTerm (peanoVal n) = Peano.fibTR (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP fibPairTerm (peanoVal n) = (Peano.fibPair (Peano.ofNat n)).1 := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

end TermTests.RecUnionRecDepth
