module

public import TermTests.ToTermTest.ListLibraryBounded.Common
public meta import LeanScript.KernelRfl

@[expose] public section

/-! # `List.map`, `List.foldl` and `List.contains`, on every small input

The programs `mapInc`, `mapAddK`, `sumFoldl`, `binFoldl`, `hasThree` and `containsArg` of `TermTests/ToTermTest/ListLibrary.lean`, translated, agree with the Lean functions on every list of length at most `3` with entries below `4` (and every extra argument below the bound stated).  See `TermTests/ToTermTest/ListLibraryBounded/Common.lean`. -/

namespace TermTests.ToTerm.ListLibrary

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

set_option maxRecDepth 20000

-- [SKIPPED BY PROFILE_LAKE] theorem mapInc_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd mapInc_term (natList l)) = mapInc l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => readNatList (runAdd mapInc_term (natList l)) = mapInc l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem mapAddK_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (k : Nat) (hk : k < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd mapAddK_term k (natList l)) = mapAddK k l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ k < 4, readNatList (runAdd mapAddK_term k (natList l)) = mapAddK k l) (by decide +kernel) l hlen hx k hk

-- [SKIPPED BY PROFILE_LAKE] theorem sumFoldl_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd sumFoldl_term (natList l) = sumFoldl l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => runAdd sumFoldl_term (natList l) = sumFoldl l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem binFoldl_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd binFoldl_term (natList l) = binFoldl l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => runAdd binFoldl_term (natList l) = binFoldl l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem hasThree_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd hasThree_term (natList l) = hasThree l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => runAdd hasThree_term (natList l) = hasThree l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem containsArg_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4)
-- [SKIPPED BY PROFILE_LAKE]     (y : Nat) (hy : y < 5) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd containsArg_term (natList l) y = containsArg l y :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => ∀ y < 5, runAdd containsArg_term (natList l) y = containsArg l y) (by decide +kernel) l hlen hx y hy


end TermTests.ToTerm.ListLibrary
