module

public import TermTests.ToTermTest.ListLibraryBounded.Common
public meta import LeanScript.KernelRfl

@[expose] public section

/-! # `List.getD`, `l[i]?`, `l[i]!` and `panic!`, on every small input

The programs `getDOr7`, `getOpt`, `nthOr0`, `getBang` and `nthBang` of `TermTests/ToTermTest/ListLibrary.lean`, translated, agree with the Lean functions on every list of length at most `3` with entries below `4` and every index below `5` — so also at the indices out of range, where `l[i]!` is `default`.  See `TermTests/ToTermTest/ListLibraryBounded/Common.lean`. -/

namespace TermTests.ToTerm.ListLibrary

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

set_option maxRecDepth 20000

-- [SKIPPED BY PROFILE_LAKE] theorem getDOr7_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (i : Nat) (hi : i < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd getDOr7_term (natList l) i = getDOr7 l i :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ i < 5, runAdd getDOr7_term (natList l) i = getDOr7 l i) (by decide +kernel) l hlen hx i hi

-- [SKIPPED BY PROFILE_LAKE] theorem getOpt_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (i : Nat) (hi : i < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd getOpt_term (natList l) i = getOpt l i :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ i < 5, runAdd getOpt_term (natList l) i = getOpt l i) (by decide +kernel) l hlen hx i hi

-- [SKIPPED BY PROFILE_LAKE] theorem nthOr0_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (i : Nat) (hi : i < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd nthOr0_term (natList l) i = nthOr0 l i :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ i < 5, runAdd nthOr0_term (natList l) i = nthOr0 l i) (by decide +kernel) l hlen hx i hi

-- [SKIPPED BY PROFILE_LAKE] theorem getBang_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (i : Nat) (hi : i < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd getBang_term (natList l) i = getBang l i :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ i < 5, runAdd getBang_term (natList l) i = getBang l i) (by decide +kernel) l hlen hx i hi

-- [SKIPPED BY PROFILE_LAKE] theorem nthBang_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (i : Nat) (hi : i < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd nthBang_term (natList l) i = nthBang l i :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ i < 5, runAdd nthBang_term (natList l) i = nthBang l i) (by decide +kernel) l hlen hx i hi


end TermTests.ToTerm.ListLibrary
