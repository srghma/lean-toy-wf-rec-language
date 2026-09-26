module

public import LeanScript.Expr.Build

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The depth-zero fold of a mutual family **is** the plain fold

`LeanScript.Term.mutualRecursiveFamily_rec k` gives the fold of a mutual recursive family
a lookback depth, the way `LeanScript.Term.nat_rec k`, `LeanScript.Term.array_rec k` and
`LeanScript.Term.recTaggedUnion_rec k` have one: a branch may **look further down** —
dispatch on one of its constructor's occurrences of a member of the family, whichever
member it is, and so be given that subvalue's fields and the values of the fold at them,
or on an occurrence it has not looked into yet at a node above it on the path —
and at depth `k` it may do so `k` times.  Its branches are
`LeanScript.FamilyFoldKCases`.

At depth `0` no branch can look down at all: `LeanScript.FamilyFoldKBranch.deep` and
`LeanScript.FamilyFoldKBranch.deepOuter` are branches of a depth `k + 1` fold, so a
depth-zero branch is a term and nothing else.  This file says that precisely, by giving
the two translations and proving they are mutually inverse:

* `FamilyFoldCases.toFoldK` — the branches of the plain fold are branches of a fold of
  **any** depth: each of them answers where it stands;
* `FamilyFoldKCases.ofFoldK` — at depth `0`, back again;
* `FamilyFoldKCases.ofFoldK_toFoldK` and `FamilyFoldKCases.toFoldK_ofFoldK` — the two are
  inverse, so the depth-zero branches of a family are exactly the branches the fold had
  before the depth was added, and the node's default depth changes nothing.

Everything here is by structural recursion on the branch families, which are five mutual
inductive types (`FamilyFoldKCases`, `FamilyMemberFoldKCases`,
`FamilyTaggedUnionFoldKCases`, `FamilyCtorsWithPayloadFoldKCases` and
`FamilyTaggedUnionFoldKCasesRest`, whose leaves are `FamilyFoldKBranch`), so each
definition and each proof below is a mutual block with one clause per family.
-/

variable {Sg : Sig}

/-! ## The branches of the plain fold, at any depth -/

mutual

/-- Every branch of the plain fold of a family is a branch of a depth-`k` fold: it
    answers where it stands, looking no further down. -/
def FamilyFoldCases.toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} {k : Nat} :
    FamilyFoldCases Sg (TyWfIn (n + 2)) bind Γ τ ms →
    FamilyFoldKCases Sg n ms₀ bind Γ τ ms k
  | .nil => .nil
  | .cons m ms => .cons (FamilyMemberFoldCases.toFoldK m) (FamilyFoldCases.toFoldK ms)

/-- `FamilyFoldCases.toFoldK`, on the branches of one member. -/
def FamilyMemberFoldCases.toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} {k : Nat} :
    FamilyMemberFoldCases Sg (TyWfIn (n + 2)) bind Γ τ m →
    FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k outer
  | .ctors c => .ctors (TaggedUnionFoldCases.toFamFoldK c)
  | .record b => .record (.here b)
  | .alias b => .alias (.here b)

/-- `FamilyFoldCases.toFoldK`, on the constructors of a member that has constructors. -/
def TaggedUnionFoldCases.toFamFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} {τ : TyWf} {k : Nat} :
    TaggedUnionFoldCases Sg (TyWfIn (n + 2)) bind Γ l τ →
    FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer
  | .payloadFirst b₀ b₁ rest =>
      .payloadFirst (.here b₀) (.here b₁) (TaggedUnionFoldCasesRest.toFamFoldK rest)
  | .skip b₀ rest => .skip (.here b₀) (CtorsWithPayloadFoldCases.toFamFoldK rest)

/-- `TaggedUnionFoldCases.toFamFoldK`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldCases.toFamFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn (n + 2))} {τ : TyWf} {k : Nat} :
    CtorsWithPayloadFoldCases Sg (TyWfIn (n + 2)) bind Γ rest τ →
    FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ rest τ k outer
  | .here b rest => .here (.here b) (TaggedUnionFoldCasesRest.toFamFoldK rest)
  | .skip b rest => .skip (.here b) (CtorsWithPayloadFoldCases.toFamFoldK rest)

/-- `TaggedUnionFoldCases.toFamFoldK`, on the constructors still to be given a branch. -/
def TaggedUnionFoldCasesRest.toFamFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn (n + 2)))} {τ : TyWf} {k : Nat} :
    TaggedUnionFoldCasesRest Sg (TyWfIn (n + 2)) bind Γ rest τ →
    FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ k outer
  | .nil => .nil
  | .cons b rest => .cons (.here b) (TaggedUnionFoldCasesRest.toFamFoldK rest)

end

/-! ## At depth zero, back again -/

mutual

/-- At depth `0` a branch of a fold of a family cannot look down, so the branches are
    those of the plain fold. -/
def FamilyFoldKCases.ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} :
    FamilyFoldKCases Sg n ms₀ bind Γ τ ms 0 →
    FamilyFoldCases Sg (TyWfIn (n + 2)) bind Γ τ ms
  | .nil => .nil
  | .cons m ms => .cons (FamilyMemberFoldKCases.ofFoldK m) (FamilyFoldKCases.ofFoldK ms)

/-- `FamilyFoldKCases.ofFoldK`, on the branches of one member. -/
def FamilyMemberFoldKCases.ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} :
    FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m 0 outer →
    FamilyMemberFoldCases Sg (TyWfIn (n + 2)) bind Γ τ m
  | .ctors c => .ctors (FamilyTaggedUnionFoldKCases.ofFoldK c)
  | .record (.here b) => .record b
  | .alias (.here b) => .alias b

/-- `FamilyFoldKCases.ofFoldK`, on the constructors of a member that has
    constructors. -/
def FamilyTaggedUnionFoldKCases.ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} {τ : TyWf} :
    FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ 0 outer →
    TaggedUnionFoldCases Sg (TyWfIn (n + 2)) bind Γ l τ
  | .payloadFirst (.here b₀) (.here b₁) rest =>
      .payloadFirst b₀ b₁ (FamilyTaggedUnionFoldKCasesRest.ofFoldK rest)
  | .skip (.here b₀) rest => .skip b₀ (FamilyCtorsWithPayloadFoldKCases.ofFoldK rest)

/-- `FamilyTaggedUnionFoldKCases.ofFoldK`, on the constructors a `CtorsWithPayload`
    holds. -/
def FamilyCtorsWithPayloadFoldKCases.ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn (n + 2))} {τ : TyWf} :
    FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ rest τ 0 outer →
    CtorsWithPayloadFoldCases Sg (TyWfIn (n + 2)) bind Γ rest τ
  | .here (.here b) rest => .here b (FamilyTaggedUnionFoldKCasesRest.ofFoldK rest)
  | .skip (.here b) rest => .skip b (FamilyCtorsWithPayloadFoldKCases.ofFoldK rest)

/-- `FamilyTaggedUnionFoldKCases.ofFoldK`, on the constructors still to be given a
    branch. -/
def FamilyTaggedUnionFoldKCasesRest.ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn (n + 2)))} {τ : TyWf} :
    FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ 0 outer →
    TaggedUnionFoldCasesRest Sg (TyWfIn (n + 2)) bind Γ rest τ
  | .nil => .nil
  | .cons (.here b) rest => .cons b (FamilyTaggedUnionFoldKCasesRest.ofFoldK rest)

end

/-! ## The two are inverse -/

mutual

/-- Reading the branches of the plain fold as depth-zero branches and back gives them
    again. -/
theorem FamilyFoldKCases.ofFoldK_toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} :
    ∀ c : FamilyFoldCases Sg (TyWfIn (n + 2)) bind Γ τ ms,
      FamilyFoldKCases.ofFoldK (FamilyFoldCases.toFoldK (ms₀ := ms₀) (k := 0) c) = c
  | .nil => rfl
  | .cons m ms => by
      simp only [FamilyFoldCases.toFoldK, FamilyFoldKCases.ofFoldK,
        FamilyMemberFoldKCases.ofFoldK_toFoldK (ms₀ := ms₀) m,
        FamilyFoldKCases.ofFoldK_toFoldK (ms₀ := ms₀) ms]

/-- `FamilyFoldKCases.ofFoldK_toFoldK`, on the branches of one member. -/
theorem FamilyMemberFoldKCases.ofFoldK_toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} :
    ∀ c : FamilyMemberFoldCases Sg (TyWfIn (n + 2)) bind Γ τ m,
      FamilyMemberFoldKCases.ofFoldK
        (FamilyMemberFoldCases.toFoldK (ms₀ := ms₀) (k := 0) (outer := outer) c) = c
  | .ctors c => by
      simp only [FamilyMemberFoldCases.toFoldK, FamilyMemberFoldKCases.ofFoldK,
        FamilyTaggedUnionFoldKCases.ofFoldK_toFoldK (ms₀ := ms₀) c]
  | .record _ => rfl
  | .alias _ => rfl

/-- `FamilyFoldKCases.ofFoldK_toFoldK`, on the constructors of a member that has
    constructors. -/
theorem FamilyTaggedUnionFoldKCases.ofFoldK_toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} {τ : TyWf} :
    ∀ c : TaggedUnionFoldCases Sg (TyWfIn (n + 2)) bind Γ l τ,
      FamilyTaggedUnionFoldKCases.ofFoldK
        (TaggedUnionFoldCases.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer) c) = c
  | .payloadFirst _ _ rest => by
      simp only [TaggedUnionFoldCases.toFamFoldK, FamilyTaggedUnionFoldKCases.ofFoldK,
        FamilyTaggedUnionFoldKCasesRest.ofFoldK_toFoldK (ms₀ := ms₀) rest]
  | .skip _ rest => by
      simp only [TaggedUnionFoldCases.toFamFoldK, FamilyTaggedUnionFoldKCases.ofFoldK,
        FamilyCtorsWithPayloadFoldKCases.ofFoldK_toFoldK (ms₀ := ms₀) rest]

/-- `FamilyTaggedUnionFoldKCases.ofFoldK_toFoldK`, on the constructors a
    `CtorsWithPayload` holds. -/
theorem FamilyCtorsWithPayloadFoldKCases.ofFoldK_toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn (n + 2))} {τ : TyWf} :
    ∀ c : CtorsWithPayloadFoldCases Sg (TyWfIn (n + 2)) bind Γ rest τ,
      FamilyCtorsWithPayloadFoldKCases.ofFoldK
        (CtorsWithPayloadFoldCases.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer) c) = c
  | .here _ rest => by
      simp only [CtorsWithPayloadFoldCases.toFamFoldK,
        FamilyCtorsWithPayloadFoldKCases.ofFoldK,
        FamilyTaggedUnionFoldKCasesRest.ofFoldK_toFoldK (ms₀ := ms₀) rest]
  | .skip _ rest => by
      simp only [CtorsWithPayloadFoldCases.toFamFoldK,
        FamilyCtorsWithPayloadFoldKCases.ofFoldK,
        FamilyCtorsWithPayloadFoldKCases.ofFoldK_toFoldK (ms₀ := ms₀) rest]

/-- `FamilyTaggedUnionFoldKCases.ofFoldK_toFoldK`, on the constructors still to be given
    a branch. -/
theorem FamilyTaggedUnionFoldKCasesRest.ofFoldK_toFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn (n + 2)))} {τ : TyWf} :
    ∀ c : TaggedUnionFoldCasesRest Sg (TyWfIn (n + 2)) bind Γ rest τ,
      FamilyTaggedUnionFoldKCasesRest.ofFoldK
        (TaggedUnionFoldCasesRest.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer) c) = c
  | .nil => rfl
  | .cons _ rest => by
      simp only [TaggedUnionFoldCasesRest.toFamFoldK,
        FamilyTaggedUnionFoldKCasesRest.ofFoldK,
        FamilyTaggedUnionFoldKCasesRest.ofFoldK_toFoldK (ms₀ := ms₀) rest]

end

mutual

/-- Reading depth-zero branches as branches of the plain fold and back gives them
    again. -/
theorem FamilyFoldKCases.toFoldK_ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} :
    ∀ c : FamilyFoldKCases Sg n ms₀ bind Γ τ ms 0,
      FamilyFoldCases.toFoldK (ms₀ := ms₀) (k := 0) (FamilyFoldKCases.ofFoldK c) = c
  | .nil => rfl
  | .cons m ms => by
      simp only [FamilyFoldKCases.ofFoldK, FamilyFoldCases.toFoldK,
        FamilyMemberFoldKCases.toFoldK_ofFoldK m, FamilyFoldKCases.toFoldK_ofFoldK ms]

/-- `FamilyFoldKCases.toFoldK_ofFoldK`, on the branches of one member. -/
theorem FamilyMemberFoldKCases.toFoldK_ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx} {τ : TyWf}
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} :
    ∀ c : FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m 0 outer,
      FamilyMemberFoldCases.toFoldK (ms₀ := ms₀) (k := 0) (outer := outer)
        (FamilyMemberFoldKCases.ofFoldK c) = c
  | .ctors c => by
      simp only [FamilyMemberFoldKCases.ofFoldK, FamilyMemberFoldCases.toFoldK,
        FamilyTaggedUnionFoldKCases.toFoldK_ofFoldK c]
  | .record (.here _) => rfl
  | .alias (.here _) => rfl

/-- `FamilyFoldKCases.toFoldK_ofFoldK`, on the constructors of a member that has
    constructors. -/
theorem FamilyTaggedUnionFoldKCases.toFoldK_ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} {τ : TyWf} :
    ∀ c : FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ 0 outer,
      TaggedUnionFoldCases.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer)
        (FamilyTaggedUnionFoldKCases.ofFoldK c) = c
  | .payloadFirst (.here _) (.here _) rest => by
      simp only [FamilyTaggedUnionFoldKCases.ofFoldK, TaggedUnionFoldCases.toFamFoldK,
        FamilyTaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]
  | .skip (.here _) rest => by
      simp only [FamilyTaggedUnionFoldKCases.ofFoldK, TaggedUnionFoldCases.toFamFoldK,
        FamilyCtorsWithPayloadFoldKCases.toFoldK_ofFoldK rest]

/-- `FamilyTaggedUnionFoldKCases.toFoldK_ofFoldK`, on the constructors a
    `CtorsWithPayload` holds. -/
theorem FamilyCtorsWithPayloadFoldKCases.toFoldK_ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn (n + 2))} {τ : TyWf} :
    ∀ c : FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ rest τ 0 outer,
      CtorsWithPayloadFoldCases.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer)
        (FamilyCtorsWithPayloadFoldKCases.ofFoldK c) = c
  | .here (.here _) rest => by
      simp only [FamilyCtorsWithPayloadFoldKCases.ofFoldK,
        CtorsWithPayloadFoldCases.toFamFoldK,
        FamilyTaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]
  | .skip (.here _) rest => by
      simp only [FamilyCtorsWithPayloadFoldKCases.ofFoldK,
        CtorsWithPayloadFoldCases.toFamFoldK,
        FamilyCtorsWithPayloadFoldKCases.toFoldK_ofFoldK rest]

/-- `FamilyTaggedUnionFoldKCases.toFoldK_ofFoldK`, on the constructors still to be given
    a branch. -/
theorem FamilyTaggedUnionFoldKCasesRest.toFoldK_ofFoldK {n : Nat}
    {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))}
    {outer : List (List (TyWfIn (n + 2)))}
    {bind : List (TyWfIn (n + 2)) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn (n + 2)))} {τ : TyWf} :
    ∀ c : FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ rest τ 0 outer,
      TaggedUnionFoldCasesRest.toFamFoldK (ms₀ := ms₀) (k := 0) (outer := outer)
        (FamilyTaggedUnionFoldKCasesRest.ofFoldK c) = c
  | .nil => rfl
  | .cons (.here _) rest => by
      simp only [FamilyTaggedUnionFoldKCasesRest.ofFoldK,
        TaggedUnionFoldCasesRest.toFamFoldK,
        FamilyTaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]

end

end LeanScript
