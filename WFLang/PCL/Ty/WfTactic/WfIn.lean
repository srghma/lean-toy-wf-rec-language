module

public meta import LeanScript.Ty.WfTactic.Hab

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace LeanScript.Ty

/-!
# `ty_wf`: well-formedness and occurrences

The walk of `ty_wf` for `Ty.WfIn`, `Ty.WfShapeIn`, `Ty.WfAllIn` and the occurrence
propositions: one node at a time, applying the rule of that node.  The inhabitation side
conditions of a family are written by `LeanScript.Ty.WfTactic.Hab`.
-/

mutual

/-- A proof of `Ty.WfIn n t`. -/
partial def mkWfIn (n : Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  -- a checked type, dropped in as a leaf: reuse its proof rather than its tree
  if let some p ← instanceWf? t then
    return ← ifClosed n p
  if let some p ← hypWf? t then
    return ← ifClosed n p
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless n == 1 do
        throwError "ty_wf: `Ty.self` is not a type in a scope of {n} members"
      return mkConst ``LeanScript.Ty.WfIn.self
  | (``LeanScript.Ty.familyMember, #[i]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member number {i} is unknown"
      unless 2 ≤ n && i < n do
        throwError "ty_wf: member {i} is not a member of a scope of {n} members"
      mkAppOptM ``LeanScript.Ty.WfIn.familyMember
        #[some (natE n), some (natE i), some (← leProof 2 n), some (← ltProof i n)]
  | (``LeanScript.Ty.shape, #[s]) =>
      mkAppOptM ``LeanScript.Ty.WfIn.shape
        #[some (natE n), some s, some (← mkWfShapeIn n s)]
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      let tys ← mkAppM ``List.flatten #[ctors]
      mkAppOptM ``LeanScript.Ty.WfIn.recTaggedUnion
        #[some (natE n), some l, some (← mkWfAllIn 1 tys), some (← mkOccursSomeIn 0 tys),
          some (← mkHabSomeIn [] ctors)]
  | (``LeanScript.Ty.recObject, #[fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.WfIn.recObject
        #[some (natE n), some fs, some (← mkWfAllIn 1 tys), some (← mkOccursSomeIn 0 tys),
          some (← mkHabAllIn [] tys)]
  | (``LeanScript.Ty.recAlias, #[b]) =>
      mkAppOptM ``LeanScript.Ty.WfIn.recAlias
        #[some (natE n), some b, some (← mkWfIn 1 b), some (← mkOccursIn 0 b),
          some (← mkHabIn [] b)]
  | (``LeanScript.Ty.mutualRecursiveFamily, #[f]) =>
      let ms ← mkAppM ``LeanScript.LeanMutualRecFamily.members #[f]
      let k := (← listElems ms).length
      let tys ← mkAppM ``LeanScript.Ty.familyTys #[f]
      mkAppOptM ``LeanScript.Ty.WfIn.mutualRecursiveFamily
        #[some (natE n), some f, some (← mkWfAllIn k tys), some (← mkMembersOccur k tys),
          some (← mkFamHab ms)]
  | _ => throwError "ty_wf: not a type of the language: {t}"

/-- A closed type is a type in any scope; in the closed scope the proof is already the
    one that is wanted. -/
partial def ifClosed (n : Nat) (p : Expr) : MetaM Expr := do
  if n == 0 then return p
  let some t := (← whnfR (← inferType p)).getAppArgs[1]?
    | throwError "ty_wf: {← inferType p} is not a well-formedness proof"
  mkAppOptM ``LeanScript.Ty.WfIn.closed #[some (natE n), some t, some p]

/-- A proof of `Ty.WfShapeIn n s`. -/
partial def mkWfShapeIn (n : Nat) (s : Expr) : MetaM Expr := do
  let s ← whnf s
  match s.getAppFnArgs with
  | (``LeanScript.TyShape.prim, #[_, p]) =>
      mkAppOptM ``LeanScript.Ty.WfShapeIn.prim #[some (natE n), some p]
  | (``LeanScript.TyShape.enum, #[_, e]) =>
      mkAppOptM ``LeanScript.Ty.WfShapeIn.enum #[some (natE n), some e]
  | (``LeanScript.TyShape.fn, #[_, a, b]) =>
      -- the domain is checked closed: an occurrence may not stand to the left of an arrow
      mkAppOptM ``LeanScript.Ty.WfShapeIn.fn
        #[some (natE n), some a, some b, some (← mkWfInDomain a), some (← mkWfIn n b)]
  | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      let v ← mkAppM ``LeanScript.LeanPrimTyCovariant.val #[c]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.primCovariant
        #[some (natE n), some c, some (← mkWfIn n v)]
  | (``LeanScript.TyShape.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.record
        #[some (natE n), some fs, some (← mkWfAllIn n tys)]
  | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
      let tys ← mkAppM ``List.flatten #[← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.taggedUnion
        #[some (natE n), some l, some (← mkWfAllIn n tys)]
  | _ => throwError "ty_wf: not a shape of the language: {s}"

/-- A proof of `Ty.WfAllIn n ts`. -/
partial def mkWfAllIn (n : Nat) (ts : Expr) : MetaM Expr := do
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => mkAppOptM ``LeanScript.Ty.WfAllIn.nil #[some (natE n)]
  | (``List.cons, #[_, h, t]) =>
      mkAppOptM ``LeanScript.Ty.WfAllIn.cons
        #[some (natE n), some h, some t, some (← mkWfIn n h), some (← mkWfAllIn n t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.OccursIn i t`. -/
partial def mkOccursIn (i : Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  if (← instanceWf? t).isSome || (← hypWf? t).isSome then
    throwError "ty_wf: a closed type mentions no member of the scope around it"
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless i == 0 do throwError "ty_wf: `Ty.self` is member 0, not member {i}"
      return mkConst ``LeanScript.Ty.OccursIn.self
  | (``LeanScript.Ty.familyMember, #[j]) =>
      let some j := (← natOf? j) | throwError "ty_wf: the member number {j} is unknown"
      unless i == j do throwError "ty_wf: member {j} is not member {i}"
      mkAppOptM ``LeanScript.Ty.OccursIn.familyMember #[some (natE i)]
  | (``LeanScript.Ty.shape, #[s]) =>
      let cs ← mkAppM ``LeanScript.TyShape.children #[s]
      mkAppOptM ``LeanScript.Ty.OccursIn.shape
        #[some (natE i), some s, some (← mkOccursSomeIn i cs)]
  | _ => throwError "ty_wf: {t} does not mention member {i} of the scope around it"

/-- A proof of `Ty.OccursSomeIn i ts`: the first of the types that mentions member `i`. -/
partial def mkOccursSomeIn (i : Nat) (ts : Expr) : MetaM Expr := do
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => throwError "ty_wf: nothing here mentions member {i}"
  | (``List.cons, #[_, h, t]) =>
      try
        mkAppOptM ``LeanScript.Ty.OccursSomeIn.head
          #[some (natE i), some h, some t, some (← mkOccursIn i h)]
      catch _ =>
        mkAppOptM ``LeanScript.Ty.OccursSomeIn.tail
          #[some (natE i), some h, some t, some (← mkOccursSomeIn i t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.MembersOccur k ts`: each of the members below `k` is mentioned. -/
partial def mkMembersOccur (k : Nat) (ts : Expr) : MetaM Expr := do
  match k with
  | 0 => mkAppOptM ``LeanScript.Ty.MembersOccur.zero #[some ts]
  | j + 1 =>
      mkAppOptM ``LeanScript.Ty.MembersOccur.succ
        #[some (natE j), some ts, some (← mkMembersOccur j ts),
          some (← mkOccursSomeIn j ts)]

/-- A proof of `Ty.WfIn 0 a` for the **domain** of a function type, with a message that
    says what the closed scope means there. -/
partial def mkWfInDomain (a : Expr) : MetaM Expr := do
  try
    mkWfIn 0 a
  catch e =>
    let mentionsScope := (a.find? fun x =>
      x.isConstOf ``LeanScript.Ty.self || x.isAppOf ``LeanScript.Ty.familyMember).isSome
    if mentionsScope then
      throwError "ty_wf: the declaration being defined occurs to the left of an arrow, \
        which no type of the language does"
    else
      throw e


end

end LeanScript.Ty

end

end
