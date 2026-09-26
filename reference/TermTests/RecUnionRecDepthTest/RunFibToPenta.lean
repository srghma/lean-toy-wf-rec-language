module

public import TermTests.RecUnionRecDepthTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: running the terms, part 1

The terms of `TermTests/RecUnionRecDepthTest.lean`, checked by the kernel against their
Lean references at the first ten arguments.  This file: `fib` and the tribonacci,
tetranacci and pentanacci numbers.  The checks are split over two
files so that they build in parallel.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP fibTerm (peanoVal n) = Peano.fib (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP tribTerm (peanoVal n) = Peano.trib (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP tetraTerm (peanoVal n) = Peano.tetra (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : ∀ n, n < 10 →
-- [SKIPPED BY PROFILE_LAKE]     runP pentaTerm (peanoVal n) = Peano.penta (Peano.ofNat n) := by
-- [SKIPPED BY PROFILE_LAKE]   decide +kernel

end TermTests.RecUnionRecDepth
