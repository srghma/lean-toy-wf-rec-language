module

public meta import LeanScript.ToTerm.ObjectExpr

@[expose] public section

meta section

/-!
# A tree as a view, and the tree of a Lean type

`TyView` is one node of a reduced tree of the language with its children bundled, and
`treeOfType` is the tree of the language that models a given Lean type.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The shapes of a tree, as a view -/

/-- One node of a reduced tree of the language, with its children. -/
inductive TyView where
  /-- A terminal type, with its `LeanScript.LeanPrimTy`. -/
  | prim (p : Expr)
  /-- A function type. -/
  | fn (a b : Expr)
  /-- An array. -/
  | array (a : Expr)
  /-- A memoised delay. -/
  | thunk (a : Expr)
  /-- An unmemoised delay. -/
  | lazy (a : Expr)
  /-- An enum, with its schema. -/
  | enum (s : Expr)
  /-- A record, with its schema. -/
  | record (fs : Expr)
  /-- A tagged union, with its schema. -/
  | taggedUnion (l : Expr)
  /-- A **recursive** tagged union, with its payload — a schema of `TyWfIn 1`, the
      shape of `List α` — and the proof that the binder is a type. -/
  | recTaggedUnion (l hwf : Expr)
  /-- A **recursive record**, with its fields — a schema of `TyWfIn 1` — and the proof
      that the binder is a type. -/
  | recObject (fs hwf : Expr)
  /-- A **recursive newtype**, with its body — a tree of `TyWfIn 1` — and the proof that
      the binder is a type. -/
  | recAlias (b hwf : Expr)
  /-- A member of a **mutual recursive family**: the number `n` for which the family has
      `n + 2` members, the family — schemas of `TyWfIn (n + 2)`, with the member it
      selects — and the proof that the family describes types. -/
  | mutualRecursiveFamily (n f hwf : Expr)
  /-- Anything else — another recursive binder or an occurrence. -/
  | other
  deriving BEq, Repr

/-- One member of a family, bundled at the scope `sc` of the whole family. -/
def bundleFamMemberE (sc : Nat) (m : Expr) : MetaM Expr := do
  let ι := scopeTyE sc
  match (← whnf m).getAppFnArgs with
  | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
      return mkApp2 (mkConst ``LeanScript.LeanFamMemberSchema.ctors) ι (← bundleTUE sc l)
  | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
      return mkApp2 (mkConst ``LeanScript.LeanFamMemberSchema.record) ι
        (← bundleRecordE sc fs)
  | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
      return mkApp2 (mkConst ``LeanScript.LeanFamMemberSchema.alias) ι (← bundleTyE sc b)
  | _ => throwError "`#leanscript_to_term`: not a member of a family: {m}"

/-- A list of members of a family, bundled at the scope `sc` of the whole family. -/
def bundleFamMembersE (sc : Nat) (ms : Expr) : MetaM Expr := do
  let xs ← (← listOfExpr ms).mapM (bundleFamMemberE sc)
  let elem := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (scopeTyE sc)
  return xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) elem)

/-- A mutual family of trees, with the number of its members, bundled at the scope of the
    whole family: the family, and that number. -/
def bundleFamE (f : Expr) : MetaM (Expr × Nat) := do
  match (← whnf f).getAppFnArgs with
  | (``LeanScript.LeanMutualRecFamily.selectedThenMore, #[_, before, cur, next, after]) =>
      let sc := (← listOfExpr before).length + 2 + (← listOfExpr after).length
      return (mkAppN (mkConst ``LeanScript.LeanMutualRecFamily.selectedThenMore)
        #[scopeTyE sc, ← bundleFamMembersE sc before, ← bundleFamMemberE sc cur,
          ← bundleFamMemberE sc next, ← bundleFamMembersE sc after], sc)
  | (``LeanScript.LeanMutualRecFamily.selectedLast, #[_, first, before, cur]) =>
      let sc := (← listOfExpr before).length + 2
      return (mkAppN (mkConst ``LeanScript.LeanMutualRecFamily.selectedLast)
        #[scopeTyE sc, ← bundleFamMemberE sc first, ← bundleFamMembersE sc before,
          ← bundleFamMemberE sc cur], sc)
  | _ => throwError "`#leanscript_to_term`: not a mutual family: {f}"

/-- The node a type of the language is, with the children **bundled**: what the view
    hands back is what the grammar's constructors ask for. -/
def tyView (τ : Expr) : MetaM TyView := do
  let t ← treeOfTyE τ
  match t.getAppFnArgs with
  | (``LeanScript.Ty.shape, #[s]) =>
    match s.getAppFnArgs with
    | (``LeanScript.TyShape.prim, #[_, p]) => return .prim p
    | (``LeanScript.TyShape.fn, #[_, a, b]) =>
        return .fn (← bundleTyE 0 a) (← bundleTyE 0 b)
    | (``LeanScript.TyShape.enum, #[_, e]) => return .enum e
    | (``LeanScript.TyShape.record, #[_, fs]) => return .record (← bundleRecordE 0 fs)
    | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
        return .taggedUnion (← bundleTUE 0 l)
    | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      match c.getAppFnArgs with
      | (``LeanScript.LeanPrimTyCovariant.array, #[_, a]) =>
          return .array (← bundleTyE 0 a)
      | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, a]) =>
          return .thunk (← bundleTyE 0 a)
      | (``LeanScript.LeanPrimTyCovariant.lazy, #[_, a]) =>
          return .lazy (← bundleTyE 0 a)
      | _ => return .other
    | _ => return .other
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      -- the payload is written in the scope the binder opens, so it is bundled at `1`,
      -- and the binder itself carries the proof that it describes a type
      let hwf ← LeanScript.Ty.mkWfIn 0 t
      return .recTaggedUnion (← bundleTUE 1 l) hwf
  | (``LeanScript.Ty.recObject, #[fs]) =>
      let hwf ← LeanScript.Ty.mkWfIn 0 t
      return .recObject (← bundleRecordE 1 fs) hwf
  | (``LeanScript.Ty.recAlias, #[b]) =>
      let hwf ← LeanScript.Ty.mkWfIn 0 t
      return .recAlias (← bundleTyE 1 b) hwf
  | (``LeanScript.Ty.mutualRecursiveFamily, #[f]) =>
      let hwf ← LeanScript.Ty.mkWfIn 0 t
      let (fB, sc) ← bundleFamE f
      return .mutualRecursiveFamily (mkNatLit (sc - 2)) fB hwf
  | _ => return .other

/-- Is this the terminal type `bool`? -/
def isBoolTy (τ : Expr) : MetaM Bool := do
  match ← tyView τ with
  | .prim p => return p.isConstOf ``LeanScript.LeanPrimTy.bool
  | _ => return false

/-! ## The tree that models a Lean type -/

/-- The tree of an auxiliary type of a nested inductive (`List Rose`), from the instance
    `deriving LeanScriptTyWf` added for it, which selects its member of the family. -/
def nestedAuxTree? (α : Expr) : MetaM (Option Expr) := do
  let cls ← mkAppM ``LeanScript.LeanScriptTyWf #[α]
  let .some inst ← trySynthInstance cls | return none
  let .const n _ := inst.getAppFn | return none
  unless n.isStr && n.getString!.startsWith "instLeanScriptTyWfNested" do return none
  return some (← reduceTy (← mkAppOptM ``LeanScript.tyOf #[α, inst]))

/-- Reduce, inside a type, every projection out of a value that is written out
    (`countdown.State`, where `countdown : Unfold Nat` is a value of a datatype with
    existentials, or `(countFrom k).State`): the type that value chose for its type field.
    A projection out of a variable (`u.State`, for `u : Unfold Nat` bound by a `fun`) does
    not reduce, and is left as it is. -/
def reduceClosedTypeProjs (α : Expr) : MetaM Expr :=
  Meta.transform α (pre := fun e => return .continue e.headBeta) (post := fun e => do
    if e.hasLooseBVars || e.hasMVar then return .continue
    let isProj : Bool ← match e, e.getAppFn with
      | .proj .., _ => pure true
      | _, .const n _ => pure (← getProjectionFnInfo? n).isSome
      | _, _ => pure false
    unless isProj do return .continue
    let e' ← whnf e
    if e' == e then return .continue
    return .done e')

/-- The tree of the language that models the Lean type `α`, reduced.

    `List α` is the recursive tagged union it is, `Array α` is `Ty.array`; a
    non-dependent function type is `Ty.fn`; everything else is the type's
    `LeanScript.LeanScriptTyWf` instance. -/
partial def treeOfType (α : Expr) : MetaM Expr := do
  let α' ← whnf α
  match α'.getAppFnArgs with
  | (``List, #[β]) =>
      -- the list of the declarations of a nested inductive (`List Rose`) is a member of
      -- their family, the instance `deriving LeanScriptTyWf` added for it
      if let some t ← nestedAuxTree? α' then return t
      reduceTy (listTyE (← treeOfType β))
  | (``Array, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.array) (← treeOfType β))
  | (``Thunk, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.thunk) (← treeOfType β))
  | _ =>
    match α' with
    | .forallE _ d b _ =>
        -- a domain the language erases (`Unit`, a proof, an instance) is dropped
        if !b.hasLooseBVar 0 && (← LeanScript.Deriving.erasedBinder d) then
          return ← treeOfType b
        if b.hasLooseBVar 0 then
          -- a dependence only through the index of an indexed family
          -- (`(m : Nat) → Vec α m → Vec α (m + n)`) leaves the trees independent of the
          -- argument: that is the function type of the language all the same
          let r? ← withLocalDeclD `x d fun x => do
            let t ← try some <$> treeOfType (b.instantiate1 x) catch _ => pure none
            return t.filter (!·.containsFVar x.fvarId!)
          let some bt := r?
            | throwError "`#leanscript_to_term`: the language has no dependent function \
                type, so {α} cannot be translated"
          reduceTy (mkApp2 (mkConst ``LeanScript.Ty.fn) (← treeOfType d) bt)
        else
          reduceTy (mkApp2 (mkConst ``LeanScript.Ty.fn) (← treeOfType d)
            (← treeOfType b))
    | _ => do
      let cls ← mkAppM ``LeanScript.LeanScriptTyWf #[α']
      match ← trySynthInstance cls with
      | .some inst => reduceTy (← mkAppOptM ``LeanScript.tyOf #[α', inst])
      | _ =>
        -- a type field of a value of a datatype with existentials that is written out
        -- (`countdown.State`) is the type that value chose
        let α'' ← reduceClosedTypeProjs α'
        if α'' != α' then return ← treeOfType α''
        if let .const ind _ := α'.getAppFn then
          if (← getEnv).find? ind matches some (.inductInfo _) then
            if let some f ← LeanScript.Deriving.existentialField? ind α'.getAppArgs then
              throwError "`#leanscript_to_term`: the type {α} has no tree of the \
                language: existential typing is not supported, `{f}` is an existential"
        throwError "`#leanscript_to_term`: the type {α} has no tree of the language \
          (no `LeanScriptTyWf` instance); derive one with `deriving LeanScriptTyWf`"

/-- The type of the language that models the Lean type `α`: its tree, with the proof
    that the tree is a type. -/
def tyOfType (α : Expr) : MetaM Expr := do
  bundleTyE 0 (← treeOfType α)

/-- The tree of the type of `e`. -/
def tyOfTerm (e : Expr) : MetaM Expr := do tyOfType (← inferType e)

end LeanScript.ToTerm

end

end
