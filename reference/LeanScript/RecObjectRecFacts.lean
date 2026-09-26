module

public import LeanScript.Expr.Build

@[expose] public section

set_option autoImplicit false

/-!
# What the fold of a recursive record binds, and why it needs an answer window

`LeanScript.Term.recObject_rec` is the one fold whose branch cannot be written with
`LeanScript.TyWf.recBinders`, the binders every other fold uses.  `recBinders` puts the
value of the fold after a field that is **literally** an occurrence of the type being
folded over, and a recursive record never has such a field: a record has values only when
all of its fields do, so a field written `Ty.self` would leave the record with no value at
all and the tree would not be a type (`Ty.not_wf_recObject_self`).

`recBinders_recObject` below is that statement: at a recursive record the binders of the
old fold are *exactly* the binders of `Term.recObject_casesOn`, so the plain fold handed
its branch no answer whatsoever.  What the depth-`k` fold hands it instead is one
**lookback window** binder — the record's own fields with each subvalue replaced by its
answer tree of depth `k` (`TyWf.recObjectAnswerTree`) — and `recObjectRecBinders_zero`
says that the default depth is the old branch context with the one answer the old one was
missing appended to it.
-/

namespace LeanScript

namespace Ty

/-- Every type of a list of types that all have values has values. -/
theorem habIn_of_habAllIn {S : List Nat} : ∀ {ts : List Ty} {t : Ty},
    HabAllIn S ts → t ∈ ts → HabIn S t
  | _, _, .cons h _, .head .. => h
  | _, _, .cons _ hs, .tail _ hm => habIn_of_habAllIn hs hm

/-- **A field of a recursive record is never the record itself.**  All of the fields of a
    record have to have values, and the record being defined is not assumed to have one,
    so a field written `Ty.self` would make the tree describe no value. -/
theorem ne_self_of_wf_recObject {fs : LeanRecordSchema Ty} (h : Wf (.recObject fs))
    {t : Ty} (hm : t ∈ fs.toList) : t ≠ .self := by
  intro ht
  have hhab : HabAllIn [] fs.toList :=
    (wfHere_of_wfIn h).elim (fun h => h.2.2) (fun h => h.2.2)
  exact not_habIn_nil_self (ht ▸ habIn_of_habAllIn hhab hm)

end Ty

namespace TyWf

/-- Where no field is an occurrence of the type being folded over, a branch of a fold
    binds nothing but the fields. -/
theorem recBinders_eq_map (r motive : TyWf) : ∀ {l : List (TyWfIn 1)},
    (∀ a ∈ l, a.toTy ≠ Ty.self) → recBinders r motive l = l.map (TyWfIn.unfold r)
  | [], _ => rfl
  | ⟨a, ha⟩ :: l, h => by
    have ih : recBinders r motive l = l.map (TyWfIn.unfold r) :=
      recBinders_eq_map r motive fun b hb => h b (List.mem_cons_of_mem _ hb)
    cases a with
    | self => exact absurd rfl (h _ List.mem_cons_self)
    | familyMember i => exact congrArg _ ih
    | shape s => exact congrArg _ ih
    | recTaggedUnion l' => exact congrArg _ ih
    | recObject fs' => exact congrArg _ ih
    | recAlias b => exact congrArg _ ih
    | mutualRecursiveFamily f => exact congrArg _ ih

/-- **The plain fold of a recursive record gave its branch no answer**: its binders are
    the fields of the record, unfolded, which is what `Term.recObject_casesOn` binds. -/
theorem recBinders_recObject (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) (motive : TyWf) :
    recBinders (recObject fs hwf) motive fs.toList = (recObjectUnfold fs hwf).toList := by
  refine recBinders_eq_map _ _ fun a hm => ?_
  exact Ty.ne_self_of_wf_recObject hwf (List.mem_map_of_mem hm)

/-- The branch of a depth-zero fold of a recursive record is the branch of the plain fold
    with the answers at the immediate subvalues — the one thing it was missing — bound
    after the fields. -/
theorem recObjectRecBinders_zero (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) (motive : TyWf) :
    recObjectRecBinders fs hwf motive 0 =
      recBinders (recObject fs hwf) motive fs.toList ++
        [recObjectMap fs motive] := by
  rw [recObjectRecBinders, recBinders_recObject]
  rfl

/-- One more depth is one more level inside the window: the answer tree of depth `k + 1`
    at a subvalue is the answer at it beside the depth-`k` trees of *its* subvalues. -/
theorem recObjectAnswerTree_succ (fs : LeanRecordSchema (TyWfIn 1)) (motive : TyWf)
    (k : Nat) :
    recObjectAnswerTree fs motive (k + 1) =
      .record ⟨motive, recObjectMap fs (recObjectAnswerTree fs motive k), []⟩ := rfl

/-- The branch of a depth-`k` fold binds the record's fields and one answer window. -/
theorem length_recObjectRecBinders (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (recObjectTy fs)) (motive : TyWf) (k : Nat) :
    (recObjectRecBinders fs hwf motive k).length = fs.length + 1 := by
  simp [recObjectRecBinders, recObjectUnfold, LeanRecordSchema.map,
    LeanRecordSchema.length]

end TyWf

end LeanScript

end
