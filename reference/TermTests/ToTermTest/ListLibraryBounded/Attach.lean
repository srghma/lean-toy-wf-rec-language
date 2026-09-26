module

public import TermTests.ToTermTest.ListLibraryBounded.Common
public meta import LeanScript.KernelRfl

@[expose] public section

/-! # `List.range` and `List.attach`, on every small input

The programs `rangeOnly`, `rangeDouble`, `attachVal`, `rangeIndex` and `attachWithSum` of `TermTests/ToTermTest/ListLibrary.lean`, translated, agree with the Lean functions on every natural number below `12` and every list of length at most `3` with entries below `4`.  See `TermTests/ToTermTest/ListLibraryBounded/Common.lean`. -/

namespace TermTests.ToTerm.ListLibrary

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

set_option maxRecDepth 20000

-- [SKIPPED BY PROFILE_LAKE] theorem rangeOnly_term_small (n : Nat) (hn : n < 12) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd rangeOnly_term n) = rangeOnly n :=
-- [SKIPPED BY PROFILE_LAKE]   (by decide +kernel : ∀ n < 12, readNatList (runAdd rangeOnly_term n) = rangeOnly n) n hn

-- [SKIPPED BY PROFILE_LAKE] theorem rangeDouble_term_small (n : Nat) (hn : n < 12) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd rangeDouble_term n) = rangeDouble n :=
-- [SKIPPED BY PROFILE_LAKE]   (by decide +kernel : ∀ n < 12, readNatList (runAdd rangeDouble_term n) = rangeDouble n) n hn

-- [SKIPPED BY PROFILE_LAKE] theorem attachVal_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd attachVal_term (natList l)) = attachVal l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => readNatList (runAdd attachVal_term (natList l)) = attachVal l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem rangeIndex_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd rangeIndex_term (natList l)) = rangeIndex l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => readNatList (runAdd rangeIndex_term (natList l)) = rangeIndex l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem attachWithSum_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd attachWithSum_term (natList l) = attachWithSum l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => runAdd attachWithSum_term (natList l) = attachWithSum l) (by decide +kernel) l hlen hx


end TermTests.ToTerm.ListLibrary
