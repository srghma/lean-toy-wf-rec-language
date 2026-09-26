module

public import LeanScript.Den.Rec
public import LeanScript.Eval.Env

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The values of a recursive record and of a recursive newtype

`Ty.Den (.recObject F)` is the W-tree of the container of the record's fields
(`Ty.toPFunctorRecord F`), and `Ty.Den (.recAlias B)` the W-tree of the container of the
newtype's body (`Ty.toPFunctor B`): a node is the record's fields — or the body — **with
the occurrences of the binder blanked out**, and one subtree per occurrence.  This module
is the bridge between that and what a term of the language sees, exactly as
`LeanScript.Den.Rec` is for a recursive tagged union:

* `Ty.DenObj.mk` / `Ty.DenObj.unfold` and `Ty.DenAlias.mk` / `Ty.DenAlias.unfold`: the
  introduction form and the one-level elimination, from and to the *unfolded* fields or
  body, where an occurrence of the binder is a value of it again.  They are `Ty.roll` and
  `Ty.unroll` at the binder itself, and mutually inverse.
* Their `TyWf` versions, which are what `LeanScript.Term.eval` uses.  For a newtype they
  need no `cast` at all — the unfolded body of the bundle *is* the unfolded body of the
  tree — and for a record they move along the one equation between the unfolded fields of
  the bundle and of the tree.
* What a branch of the depth-`k` fold binds: the fields (or body) of the node, and the
  fold's **lookback window**, the node's shape with the answer tree of depth `k`
  (`TyWf.recObjectAnswerTree`, `TyWf.recAliasAnswerTree`) of each subvalue in its hole.
  They are read off a node whose subtrees are *memos* (`LeanScript.WType.memo`), so a
  deeper look reads answers that are already computed.
-/

namespace Ty

/-! ## Recursive records, on trees -/

/-- The fields of `recObject F`, unfolded, as trees. -/
abbrev recObjUnfoldTy (F : LeanRecordSchema Ty) : LeanRecordSchema Ty :=
  substOccRecord (.recObject F) .familyMember F

/-- A value of `recObject F` is a W-tree of the shapes of its fields. -/
example (F : LeanRecordSchema Ty) :
    Ty.Den (.recObject F) = WType (Ty.toPFunctorRecord F).B := rfl

/-- **The introduction form** of a recursive record: its fields, unfolded — rolled into
    one node, which Mathlib's `WType.ofSigma` makes a tree. -/
def DenObj.mk (F : LeanRecordSchema Ty) (v : Ty.DenRecord (recObjUnfoldTy F)) :
    Ty.Den (.recObject F) :=
  WType.ofSigma (rollShape (.recObject F) (.record F) v)

/-- **One level of a value** of a recursive record: its fields, unfolded — the root node
    (Mathlib's `WType.toSigma`), unrolled. -/
def DenObj.unfold (F : LeanRecordSchema Ty) (v : Ty.Den (.recObject F)) :
    Ty.DenRecord (recObjUnfoldTy F) :=
  unrollShape (.recObject F) (.record F) (WType.toSigma v)

theorem DenObj.unfold_mk (F : LeanRecordSchema Ty) (v : Ty.DenRecord (recObjUnfoldTy F)) :
    DenObj.unfold F (DenObj.mk F v) = v := by
  rw [DenObj.unfold, DenObj.mk, WType.toSigma_ofSigma]
  exact unroll_rollShape (.recObject F) (.record F) v

theorem DenObj.mk_unfold (F : LeanRecordSchema Ty) (v : Ty.Den (.recObject F)) :
    DenObj.mk F (DenObj.unfold F v) = v := by
  rw [DenObj.mk, DenObj.unfold, roll_unrollShape, WType.ofSigma_toSigma]

/-- The values of a recursive record **are** the values of its unfolded fields: the two
    directions `Ty.DenObj.mk` and `Ty.DenObj.unfold`, as a Mathlib `Equiv`. -/
def DenObj.equiv (F : LeanRecordSchema Ty) :
    Ty.DenRecord (recObjUnfoldTy F) ≃ Ty.Den (.recObject F) where
  toFun := DenObj.mk F
  invFun := DenObj.unfold F
  left_inv := DenObj.unfold_mk F
  right_inv := DenObj.mk_unfold F

/-! ## Recursive newtypes, on trees -/

/-- The body of `recAlias B`, unfolded, as a tree. -/
abbrev recAliasUnfoldTy (B : Ty) : Ty := substOcc (.recAlias B) .familyMember B

/-- A value of `recAlias B` is a W-tree of the shapes of its body. -/
example (B : Ty) : Ty.Den (.recAlias B) = WType (Ty.toPFunctor B).B := rfl

/-- **The introduction form** of a recursive newtype: its body, unfolded — rolled into one
    node, which Mathlib's `WType.ofSigma` makes a tree. -/
def DenAlias.mk (B : Ty) (v : Ty.Den (recAliasUnfoldTy B)) : Ty.Den (.recAlias B) :=
  WType.ofSigma (roll (.recAlias B) B v)

/-- **One level of a value** of a recursive newtype: its body, unfolded — the root node
    (Mathlib's `WType.toSigma`), unrolled. -/
def DenAlias.unfold (B : Ty) (v : Ty.Den (.recAlias B)) : Ty.Den (recAliasUnfoldTy B) :=
  unroll (.recAlias B) B (WType.toSigma v)

theorem DenAlias.unfold_mk (B : Ty) (v : Ty.Den (recAliasUnfoldTy B)) :
    DenAlias.unfold B (DenAlias.mk B v) = v := by
  rw [DenAlias.unfold, DenAlias.mk, WType.toSigma_ofSigma]
  exact unroll_roll (.recAlias B) B v

theorem DenAlias.mk_unfold (B : Ty) (v : Ty.Den (.recAlias B)) :
    DenAlias.mk B (DenAlias.unfold B v) = v := by
  rw [DenAlias.mk, DenAlias.unfold, roll_unroll, WType.ofSigma_toSigma]

/-- The values of a recursive newtype **are** the values of its unfolded body, as a
    Mathlib `Equiv`. -/
def DenAlias.equiv (B : Ty) : Ty.Den (recAliasUnfoldTy B) ≃ Ty.Den (.recAlias B) where
  toFun := DenAlias.mk B
  invFun := DenAlias.unfold B
  left_inv := DenAlias.unfold_mk B
  right_inv := DenAlias.mk_unfold B

end Ty

/-! ## At the level of bundles -/

namespace TyWf

/-- The trees of a record schema of bundles unfolded at `X` are the record's trees with
    `X` substituted for the binder. -/
theorem recordUnfold_map_toTy (fs : LeanRecordSchema (TyWfIn 1)) (X : TyWf) :
    (fs.map (TyWfIn.unfold X)).map TyWf.toTy =
      Ty.substOccRecord X.toTy .familyMember (fs.map TyWfIn.toTy) := by
  rw [Ty.substOccRecord_eq_map]
  obtain ⟨a, b, rest⟩ := fs
  simp only [LeanRecordSchema.map, Functor.map, List.map_map]
  rfl

/-- The unfolded fields of a recursive record of bundles are, as trees, the unfolded
    fields of its tree. -/
theorem recObjectUnfold_map_toTy (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) :
    (recObjectUnfold fs hwf).map TyWf.toTy = Ty.recObjUnfoldTy (fs.map TyWfIn.toTy) :=
  recordUnfold_map_toTy fs (recObject fs hwf)

/-- The values of the unfolded fields, as the list a spine of terms gives and as the
    record of trees, are the same. -/
theorem denList_recObjectUnfold (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) :
    TyWf.DenList (recObjectUnfold fs hwf).toList =
      Ty.DenRecord (Ty.recObjUnfoldTy (fs.map TyWfIn.toTy)) := by
  rw [← recObjectUnfold_map_toTy fs hwf, Ty.denRecord_eq]
  rfl

/-- **The introduction form** of a recursive record of bundles, from the values of its
    unfolded fields, in declaration order. -/
def DenObj.mk (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (recObjectTy fs))
    (v : TyWf.DenList (recObjectUnfold fs hwf).toList) : TyWf.Den (recObject fs hwf) :=
  Ty.DenObj.mk (fs.map TyWfIn.toTy) (cast (denList_recObjectUnfold fs hwf) v)

/-- **One level of a value** of a recursive record of bundles: the values of its unfolded
    fields, in declaration order, which is what `Term.recObject_casesOn` binds. -/
def DenObj.unfold (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (recObjectTy fs))
    (v : TyWf.Den (recObject fs hwf)) : TyWf.DenList (recObjectUnfold fs hwf).toList :=
  cast (denList_recObjectUnfold fs hwf).symm (Ty.DenObj.unfold (fs.map TyWfIn.toTy) v)

theorem DenObj.unfold_mk (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (recObjectTy fs))
    (v : TyWf.DenList (recObjectUnfold fs hwf).toList) :
    DenObj.unfold fs hwf (DenObj.mk fs hwf v) = v := by
  simp only [DenObj.unfold, DenObj.mk, Ty.DenObj.unfold_mk, cast_cast, cast_eq]

theorem DenObj.mk_unfold (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (recObjectTy fs))
    (v : TyWf.Den (recObject fs hwf)) :
    DenObj.mk fs hwf (DenObj.unfold fs hwf v) = v := by
  simp only [DenObj.unfold, DenObj.mk, cast_cast, cast_eq]
  exact Ty.DenObj.mk_unfold _ v

/-- `TyWf.DenObj.mk` and `TyWf.DenObj.unfold`, as a Mathlib `Equiv`. -/
def DenObj.equiv (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (recObjectTy fs)) :
    TyWf.DenList (recObjectUnfold fs hwf).toList ≃ TyWf.Den (recObject fs hwf) where
  toFun := DenObj.mk fs hwf
  invFun := DenObj.unfold fs hwf
  left_inv := DenObj.unfold_mk fs hwf
  right_inv := DenObj.mk_unfold fs hwf

/-- **The introduction form** of a recursive newtype of bundles, from the value of its
    unfolded body.  The two types are the same, so there is no `cast`. -/
def DenAlias.mk (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (v : TyWf.Den (recAliasUnfold b hwf)) : TyWf.Den (recAlias b hwf) :=
  Ty.DenAlias.mk b.toTy v

/-- **One level of a value** of a recursive newtype of bundles: its unfolded body, which
    is what `Term.recAlias_casesOn` binds. -/
def DenAlias.unfold (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (v : TyWf.Den (recAlias b hwf)) : TyWf.Den (recAliasUnfold b hwf) :=
  Ty.DenAlias.unfold b.toTy v

theorem DenAlias.unfold_mk (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (v : TyWf.Den (recAliasUnfold b hwf)) : DenAlias.unfold b hwf (DenAlias.mk b hwf v) = v :=
  Ty.DenAlias.unfold_mk b.toTy v

theorem DenAlias.mk_unfold (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b))
    (v : TyWf.Den (recAlias b hwf)) : DenAlias.mk b hwf (DenAlias.unfold b hwf v) = v :=
  Ty.DenAlias.mk_unfold b.toTy v

/-- `TyWf.DenAlias.mk` and `TyWf.DenAlias.unfold`, as a Mathlib `Equiv`. -/
def DenAlias.equiv (b : TyWfIn 1) (hwf : Ty.Wf (recAliasTy b)) :
    TyWf.Den (recAliasUnfold b hwf) ≃ TyWf.Den (recAlias b hwf) where
  toFun := DenAlias.mk b hwf
  invFun := DenAlias.unfold b hwf
  left_inv := DenAlias.unfold_mk b hwf
  right_inv := DenAlias.mk_unfold b hwf

end TyWf

/-! ## What a branch of the fold of a recursive record binds

`LeanScript.Term.recObject_rec` folds a value by `LeanScript.WType.memo`, as
`Term.recTaggedUnion_rec` does: the answer at every node is computed once, bottom-up, and
stored beside the node.  Its branch binds the node's fields, unfolded, and the lookback
window `TyWf.recObjectMap fs (TyWf.recObjectAnswerTree fs τ k)`: the node's shape with, in
the hole of each subvalue, the answer tree of depth `k` at it — the answer stored there,
and (for `k > 0`) the subvalue's own shape with the answer trees of depth `k - 1` below. -/

/-- The trees of a record schema of bundles. -/
abbrev objF (fs : LeanRecordSchema (TyWfIn 1)) : LeanRecordSchema Ty := fs.map TyWfIn.toTy

/-- A value of `recObject fs` with the answer of a fold of motive `τ` at every node. -/
abbrev ObjMemo (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) : Type :=
  WType.Memo (Ty.toPFunctorRecord (objF fs)).A (Ty.toPFunctorRecord (objF fs)).B (TyWf.Den τ)

/-- The shape of a node of `recObject fs` with a value of `X` in each hole is a value of
    `TyWf.recObjectMap fs X`, the record's fields with `X` for the record. -/
def objMap (fs : LeanRecordSchema (TyWfIn 1)) (X : TyWf)
    (x : (Ty.toPFunctorRecord (objF fs)).Obj (TyWf.Den X)) : TyWf.Den (TyWf.recObjectMap fs X) :=
  cast (congrArg (fun F => Ty.DenRecord F) (TyWf.recordUnfold_map_toTy fs X).symm)
    (Ty.unrollShape X.toTy (.record (objF fs)) x)

/-- **The answer tree of depth `j`** at a node of the memo: at `0` the answer stored
    there, and at `j + 1` that answer with the node's shape carrying the answer trees of
    depth `j` of its subvalues. -/
def objAnswerTree (fs : LeanRecordSchema (TyWfIn 1)) (τ : TyWf) :
    (j : Nat) → ObjMemo fs τ → TyWf.Den (TyWf.recObjectAnswerTree fs τ j)
  | 0, m => m.answer
  | j + 1, .mk (s, a) kids =>
      (a, objMap fs (TyWf.recObjectAnswerTree fs τ j)
        ⟨s, fun p => objAnswerTree fs τ j (kids p)⟩, PUnit.unit)

/-- The environment the branch of a depth-`k` fold of a recursive record binds, at a node
    of shape `s` whose subtrees are memos: the node's fields, unfolded, and the window. -/
def objRecEnv (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (τ : TyWf) (k : Nat) (s : (Ty.toPFunctorRecord (objF fs)).A)
    (kids : (Ty.toPFunctorRecord (objF fs)).B s → ObjMemo fs τ) :
    TyWf.DenList (TyWf.recObjectRecBinders fs hwf τ k) :=
  Env.append (TyWf.DenObj.unfold fs hwf (WType.mk s fun p => (kids p).tree))
    (Env.cons (objMap fs _ ⟨s, fun p => objAnswerTree fs τ k (kids p)⟩) Env.nil)

/-! ## What a branch of the fold of a recursive newtype binds -/

/-- A value of `recAlias b` with the answer of a fold of motive `τ` at every node. -/
abbrev AliasMemo (b : TyWfIn 1) (τ : TyWf) : Type :=
  WType.Memo (Ty.toPFunctor b.toTy).A (Ty.toPFunctor b.toTy).B (TyWf.Den τ)

/-- The shape of a node of `recAlias b` with a value of `X` in each hole is a value of
    `TyWf.recAliasMap b X`, the body with `X` for the newtype.  No `cast`: that type is the
    body unrolled at `X`. -/
def aliasMap (b : TyWfIn 1) (X : TyWf) (x : (Ty.toPFunctor b.toTy).Obj (TyWf.Den X)) :
    TyWf.Den (TyWf.recAliasMap b X) :=
  Ty.unroll X.toTy b.toTy x

/-- **The answer tree of depth `j`** at a node of the memo of a newtype. -/
def aliasAnswerTree (b : TyWfIn 1) (τ : TyWf) :
    (j : Nat) → AliasMemo b τ → TyWf.Den (TyWf.recAliasAnswerTree b τ j)
  | 0, m => m.answer
  | j + 1, .mk (s, a) kids =>
      (a, aliasMap b (TyWf.recAliasAnswerTree b τ j)
        ⟨s, fun p => aliasAnswerTree b τ j (kids p)⟩, PUnit.unit)

/-- The environment the branch of a depth-`k` fold of a recursive newtype binds, at a node
    of shape `s` whose subtrees are memos: the body, unfolded, and the window. -/
def aliasRecEnv (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b)) (τ : TyWf) (k : Nat)
    (s : (Ty.toPFunctor b.toTy).A) (kids : (Ty.toPFunctor b.toTy).B s → AliasMemo b τ) :
    TyWf.DenList (TyWf.recAliasRecBinders b hwf τ k) :=
  (TyWf.DenAlias.unfold b hwf (WType.mk s fun p => (kids p).tree),
    aliasMap b _ ⟨s, fun p => aliasAnswerTree b τ k (kids p)⟩, PUnit.unit)

end LeanScript

end
