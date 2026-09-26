module

public meta import LeanScript.Ty.WfTactic.Leaves

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace LeanScript.Ty

/-!
# `ty_wf`: inhabitation

The walk of `ty_wf`, for `LeanScript.Ty.HabIn`: it answers "does this tree have a value,
given that the members listed in `S` do?".  A leaf that some instance or some hypothesis
already answers for is closed by `Ty.HabIn.of_wf` applied to that proof — a checked type has
values — so again no checked tree is looked at.
-/

mutual

/-- A proof of `Ty.HabIn S t`. -/
partial def mkHabIn (S : List Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  if let some p ← instanceWf? t then
    return ← mkAppOptM ``LeanScript.Ty.HabIn.of_wf #[some (← natListE S), none, some p]
  if let some p ← hypWf? t then
    return ← mkAppOptM ``LeanScript.Ty.HabIn.of_wf #[some (← natListE S), none, some p]
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless S.contains 0 do
        throwError "ty_wf: the declaration being defined is assumed to have a value by \
          its own definition, so the definition describes no value"
      mkAppOptM ``LeanScript.Ty.HabIn.self
        #[some (← natListE S), some (← memProof 0 S)]
  | (``LeanScript.Ty.familyMember, #[i]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member number {i} is unknown"
      unless S.contains i do
        throwError "ty_wf: member {i} of the family is not known to have a value here"
      mkAppOptM ``LeanScript.Ty.HabIn.familyMember
        #[some (← natListE S), some (natE i), some (← memProof i S)]
  | (``LeanScript.Ty.shape, #[s]) =>
      mkAppOptM ``LeanScript.Ty.HabIn.shape
        #[some (← natListE S), some s, some (← mkHabShapeIn S s)]
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.HabIn.recTaggedUnion
        #[some (← natListE S), some l, some (← mkHabSomeIn [] ctors)]
  | (``LeanScript.Ty.recObject, #[fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.HabIn.recObject
        #[some (← natListE S), some fs, some (← mkHabAllIn [] tys)]
  | (``LeanScript.Ty.recAlias, #[b]) =>
      mkAppOptM ``LeanScript.Ty.HabIn.recAlias
        #[some (← natListE S), some b, some (← mkHabIn [] b)]
  | (``LeanScript.Ty.mutualRecursiveFamily, #[f]) =>
      let ms ← mkAppM ``LeanScript.LeanMutualRecFamily.members #[f]
      mkAppOptM ``LeanScript.Ty.HabIn.mutualRecursiveFamily
        #[some (← natListE S), some f, some (← mkFamHab ms)]
  | _ => throwError "ty_wf: not a type of the language: {t}"

/-- A proof of `Ty.HabShapeIn S s`. -/
partial def mkHabShapeIn (S : List Nat) (s : Expr) : MetaM Expr := do
  let SE ← natListE S
  let s ← whnf s
  match s.getAppFnArgs with
  | (``LeanScript.TyShape.prim, #[_, p]) =>
      mkAppOptM ``LeanScript.Ty.HabShapeIn.prim #[some SE, some p]
  | (``LeanScript.TyShape.enum, #[_, e]) =>
      mkAppOptM ``LeanScript.Ty.HabShapeIn.enum #[some SE, some e]
  | (``LeanScript.TyShape.fn, #[_, a, b]) =>
      -- the constant function: only the result has to have a value
      mkAppOptM ``LeanScript.Ty.HabShapeIn.fn
        #[some SE, some a, some b, some (← mkHabIn S b)]
  | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      let c ← whnf c
      match c.getAppFnArgs with
      | (``LeanScript.LeanPrimTyCovariant.array, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.array #[some SE, some v]
      | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.thunk
            #[some SE, some v, some (← mkHabIn S v)]
      | (``LeanScript.LeanPrimTyCovariant.lazy, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.lazy
            #[some SE, some v, some (← mkHabIn S v)]
      | _ => throwError "ty_wf: not an array, a thunk or a lazy value: {c}"
  | (``LeanScript.TyShape.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.HabShapeIn.record
        #[some SE, some fs, some (← mkHabAllIn S tys)]
  | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.HabShapeIn.taggedUnion
        #[some SE, some l, some (← mkHabSomeIn S ctors)]
  | _ => throwError "ty_wf: not a shape of the language: {s}"

/-- A proof of `Ty.HabAllIn S ts`: every field of one constructor has a value. -/
partial def mkHabAllIn (S : List Nat) (ts : Expr) : MetaM Expr := do
  let SE ← natListE S
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => mkAppOptM ``LeanScript.Ty.HabAllIn.nil #[some SE]
  | (``List.cons, #[_, h, t]) =>
      mkAppOptM ``LeanScript.Ty.HabAllIn.cons
        #[some SE, some h, some t, some (← mkHabIn S h), some (← mkHabAllIn S t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.HabSomeIn S cs`: the first constructor all of whose fields have a
    value. -/
partial def mkHabSomeIn (S : List Nat) (cs : Expr) : MetaM Expr := do
  let SE ← natListE S
  let cs ← whnf cs
  match cs.getAppFnArgs with
  | (``List.nil, _) =>
      throwError "ty_wf: no constructor here can be built, so the type has no values"
  | (``List.cons, #[_, h, t]) =>
      try
        mkAppOptM ``LeanScript.Ty.HabSomeIn.head
          #[some SE, some h, some t, some (← mkHabAllIn S h)]
      catch _ =>
        mkAppOptM ``LeanScript.Ty.HabSomeIn.tail
          #[some SE, some h, some t, some (← mkHabSomeIn S t)]
  | _ => throwError "ty_wf: not a list of constructors: {cs}"

/-- A proof of `Ty.MemberHab S m`, for one member of a family. -/
partial def mkMemberHab (S : List Nat) (m : Expr) : MetaM Expr := do
  let SE ← natListE S
  let m ← whnf m
  match m.getAppFnArgs with
  | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.MemberHab.ctors
        #[some SE, some l, some (← mkHabSomeIn S ctors)]
  | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.MemberHab.record
        #[some SE, some fs, some (← mkHabAllIn S tys)]
  | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
      mkAppOptM ``LeanScript.Ty.MemberHab.alias
        #[some SE, some b, some (← mkHabIn S b)]
  | _ => throwError "ty_wf: not a member of a family: {m}"

/-- A proof of `Ty.FamHab ms`: the least fixpoint, computed.  Members are added to the
    known set one at a time, each on the strength of the ones before it, until no more can
    be added; if one is left over, the family describes a member with no values. -/
partial def mkFamHab (msE : Expr) : MetaM Expr := do
  let ms ← listElems msE
  let n := ms.length
  let mut known : List Nat := []
  let mut proof ← mkAppOptM ``LeanScript.Ty.FamKnown.nil #[some msE]
  let mut progress := true
  while progress && known.length < n do
    progress := false
    for i in [0:n] do
      if known.contains i then continue
      let m := ms[i]!
      let some hm ← (try pure (some (← mkMemberHab known m)) catch _ => pure none)
        | continue
      let hEq ← mkEqRefl (← mkAppOptM ``Option.some
        #[some (mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (mkConst ``LeanScript.Ty)),
          some m])
      proof ← mkAppOptM ``LeanScript.Ty.FamKnown.cons
        #[some msE, some (← natListE known), some (natE i), some m, some proof, some hEq,
          some hm]
      known := i :: known
      progress := true
  unless known.length == n do
    let missing := (List.range n).filter fun i => !known.contains i
    throwError "ty_wf: member {missing.head!} of this family has no values, so the \
      family describes no type"
  let SE ← natListE known
  let lenE ← mkAppM ``List.length #[msE]
  let allTy ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let body ← mkArrow (← mkAppM ``LT.lt #[i, lenE])
      (← mkAppM ``Membership.mem #[SE, i])
    mkForallFVars #[i] body
  mkAppOptM ``LeanScript.Ty.FamHab.mk
    #[some msE, some SE, some proof, some (← mkDecideProof allTy)]

end

end LeanScript.Ty

end

end
