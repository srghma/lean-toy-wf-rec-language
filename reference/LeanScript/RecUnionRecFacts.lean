module

public import LeanScript.Expr.Build

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The depth-zero fold of a recursive tagged union **is** the plain fold

`LeanScript.Term.recTaggedUnion_rec k` gives the fold of a recursive tagged union a
lookback depth, the way `LeanScript.Term.nat_rec k` and `LeanScript.Term.array_rec k`
have one: a branch may **look further down** — dispatch on one of its constructor's
occurrences of the union, or on one at a node above it on the path, and so be given that
subvalue's fields and the values of the fold at them — and at depth `k` it may do so `k`
times.  Its branches are `LeanScript.TaggedUnionFoldKCases`.

At depth `0` no branch can look down at all: `LeanScript.FoldKBranch.deep` and
`LeanScript.FoldKBranch.deepOuter` are branches of a depth `k + 1` fold, so a depth-zero
branch is a term and nothing else.  This file says
that precisely, by giving the two translations and proving they are mutually inverse:

* `TaggedUnionFoldCases.toFoldK` — the branches of the plain fold are branches of a fold
  of **any** depth: each of them answers where it stands;
* `TaggedUnionFoldKCases.ofFoldK` — at depth `0`, back again;
* `TaggedUnionFoldKCases.ofFoldK_toFoldK` and `TaggedUnionFoldKCases.toFoldK_ofFoldK` —
  the two are inverse, so the depth-zero branches of a union are exactly the branches the
  fold had before the depth was added, and the node's default depth changes nothing.

Everything here is by structural recursion on the branch families, which are four mutual
inductive types (`TaggedUnionFoldKCases`, `CtorsWithPayloadFoldKCases`,
`TaggedUnionFoldKCasesRest` and `FoldKBranch`), so each definition and each proof below
is a mutual block with one clause per family.
-/

variable {Sg : Sig} {outer : List (List (TyWfIn 1))}

/-! ## The branches of the plain fold, at any depth -/

mutual

/-- Every branch of the plain fold is a branch of a depth-`k` fold: it answers where it
    stands, looking no further down. -/
def TaggedUnionFoldCases.toFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} {k : Nat} :
    TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ →
    TaggedUnionFoldKCases Sg l₀ bind Γ l τ k outer
  | .payloadFirst b₀ b₁ rest =>
      .payloadFirst (.here b₀) (.here b₁) (TaggedUnionFoldCasesRest.toFoldK rest)
  | .skip b₀ rest => .skip (.here b₀) (CtorsWithPayloadFoldCases.toFoldK rest)

/-- `TaggedUnionFoldCases.toFoldK`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldCases.toFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {rest : CtorsWithPayload (TyWfIn 1)}
    {τ : TyWf} {k : Nat} :
    CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ rest τ →
    CtorsWithPayloadFoldKCases Sg l₀ bind Γ rest τ k outer
  | .here b rest => .here (.here b) (TaggedUnionFoldCasesRest.toFoldK rest)
  | .skip b rest => .skip (.here b) (CtorsWithPayloadFoldCases.toFoldK rest)

/-- `TaggedUnionFoldCases.toFoldK`, on the constructors still to be given a branch. -/
def TaggedUnionFoldCasesRest.toFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {rest : List (List (TyWfIn 1))}
    {τ : TyWf} {k : Nat} :
    TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ rest τ →
    TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ k outer
  | .nil => .nil
  | .cons b rest => .cons (.here b) (TaggedUnionFoldCasesRest.toFoldK rest)

end

/-! ## At depth zero, back again -/

mutual

/-- At depth `0` a branch of a fold cannot look down, so the branches are those of the
    plain fold. -/
def TaggedUnionFoldKCases.ofFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} :
    TaggedUnionFoldKCases Sg l₀ bind Γ l τ 0 outer →
    TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ
  | .payloadFirst (.here b₀) (.here b₁) rest =>
      .payloadFirst b₀ b₁ (TaggedUnionFoldKCasesRest.ofFoldK rest)
  | .skip (.here b₀) rest => .skip b₀ (CtorsWithPayloadFoldKCases.ofFoldK rest)

/-- `TaggedUnionFoldKCases.ofFoldK`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldKCases.ofFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {rest : CtorsWithPayload (TyWfIn 1)}
    {τ : TyWf} :
    CtorsWithPayloadFoldKCases Sg l₀ bind Γ rest τ 0 outer →
    CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ rest τ
  | .here (.here b) rest => .here b (TaggedUnionFoldKCasesRest.ofFoldK rest)
  | .skip (.here b) rest => .skip b (CtorsWithPayloadFoldKCases.ofFoldK rest)

/-- `TaggedUnionFoldKCases.ofFoldK`, on the constructors still to be given a branch. -/
def TaggedUnionFoldKCasesRest.ofFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {rest : List (List (TyWfIn 1))}
    {τ : TyWf} :
    TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ 0 outer →
    TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ rest τ
  | .nil => .nil
  | .cons (.here b) rest => .cons b (TaggedUnionFoldKCasesRest.ofFoldK rest)

end

/-! ## The two are inverse -/

mutual

/-- Reading the branches of the plain fold as depth-zero branches and back gives them
    again. -/
theorem TaggedUnionFoldKCases.ofFoldK_toFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} :
    ∀ c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ l τ,
      TaggedUnionFoldKCases.ofFoldK
        (TaggedUnionFoldCases.toFoldK (l₀ := l₀) (k := 0) (outer := outer) c) = c
  | .payloadFirst _ _ rest => by
      simp only [TaggedUnionFoldCases.toFoldK, TaggedUnionFoldKCases.ofFoldK,
        TaggedUnionFoldKCasesRest.ofFoldK_toFoldK (l₀ := l₀) rest]
  | .skip _ rest => by
      simp only [TaggedUnionFoldCases.toFoldK, TaggedUnionFoldKCases.ofFoldK,
        CtorsWithPayloadFoldKCases.ofFoldK_toFoldK (l₀ := l₀) rest]

/-- `TaggedUnionFoldKCases.ofFoldK_toFoldK`, on the constructors a `CtorsWithPayload`
    holds. -/
theorem CtorsWithPayloadFoldKCases.ofFoldK_toFoldK
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn 1)} {τ : TyWf} :
    ∀ c : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ rest τ,
      CtorsWithPayloadFoldKCases.ofFoldK
        (CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀) (k := 0) (outer := outer) c) = c
  | .here _ rest => by
      simp only [CtorsWithPayloadFoldCases.toFoldK, CtorsWithPayloadFoldKCases.ofFoldK,
        TaggedUnionFoldKCasesRest.ofFoldK_toFoldK (l₀ := l₀) rest]
  | .skip _ rest => by
      simp only [CtorsWithPayloadFoldCases.toFoldK, CtorsWithPayloadFoldKCases.ofFoldK,
        CtorsWithPayloadFoldKCases.ofFoldK_toFoldK (l₀ := l₀) rest]

/-- `TaggedUnionFoldKCases.ofFoldK_toFoldK`, on the constructors still to be given a
    branch. -/
theorem TaggedUnionFoldKCasesRest.ofFoldK_toFoldK
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn 1))} {τ : TyWf} :
    ∀ c : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ rest τ,
      TaggedUnionFoldKCasesRest.ofFoldK
        (TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀) (k := 0) (outer := outer) c) = c
  | .nil => rfl
  | .cons _ rest => by
      simp only [TaggedUnionFoldCasesRest.toFoldK, TaggedUnionFoldKCasesRest.ofFoldK,
        TaggedUnionFoldKCasesRest.ofFoldK_toFoldK (l₀ := l₀) rest]

end

mutual

/-- Reading depth-zero branches as branches of the plain fold and back gives them
    again. -/
theorem TaggedUnionFoldKCases.toFoldK_ofFoldK {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} :
    ∀ c : TaggedUnionFoldKCases Sg l₀ bind Γ l τ 0 outer,
      TaggedUnionFoldCases.toFoldK (l₀ := l₀) (k := 0)
        (TaggedUnionFoldKCases.ofFoldK c) = c
  | .payloadFirst (.here _) (.here _) rest => by
      simp only [TaggedUnionFoldKCases.ofFoldK, TaggedUnionFoldCases.toFoldK,
        TaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]
  | .skip (.here _) rest => by
      simp only [TaggedUnionFoldKCases.ofFoldK, TaggedUnionFoldCases.toFoldK,
        CtorsWithPayloadFoldKCases.toFoldK_ofFoldK rest]

/-- `TaggedUnionFoldKCases.toFoldK_ofFoldK`, on the constructors a `CtorsWithPayload`
    holds. -/
theorem CtorsWithPayloadFoldKCases.toFoldK_ofFoldK
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {rest : CtorsWithPayload (TyWfIn 1)} {τ : TyWf} :
    ∀ c : CtorsWithPayloadFoldKCases Sg l₀ bind Γ rest τ 0 outer,
      CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀) (k := 0)
        (CtorsWithPayloadFoldKCases.ofFoldK c) = c
  | .here (.here _) rest => by
      simp only [CtorsWithPayloadFoldKCases.ofFoldK, CtorsWithPayloadFoldCases.toFoldK,
        TaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]
  | .skip (.here _) rest => by
      simp only [CtorsWithPayloadFoldKCases.ofFoldK, CtorsWithPayloadFoldCases.toFoldK,
        CtorsWithPayloadFoldKCases.toFoldK_ofFoldK rest]

/-- `TaggedUnionFoldKCases.toFoldK_ofFoldK`, on the constructors still to be given a
    branch. -/
theorem TaggedUnionFoldKCasesRest.toFoldK_ofFoldK
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx}
    {rest : List (List (TyWfIn 1))} {τ : TyWf} :
    ∀ c : TaggedUnionFoldKCasesRest Sg l₀ bind Γ rest τ 0 outer,
      TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀) (k := 0)
        (TaggedUnionFoldKCasesRest.ofFoldK c) = c
  | .nil => rfl
  | .cons (.here _) rest => by
      simp only [TaggedUnionFoldKCasesRest.ofFoldK, TaggedUnionFoldCasesRest.toFoldK,
        TaggedUnionFoldKCasesRest.toFoldK_ofFoldK rest]

end

end LeanScript
