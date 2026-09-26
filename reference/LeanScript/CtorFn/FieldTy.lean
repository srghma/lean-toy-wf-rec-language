module

public meta import LeanScript.CtorFn.Cache

@[expose] public section

/-!
# `#leanscript_ctor`: translating the type of a field

The type of a constructor field, as a tree of `TyWf`: the type arguments, and the members of
the datatype's `mutual` block, become holes of the tree.
-/

meta section

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType?)

/-- What a field type is translated in. -/
structure TrCtx where
  /-- The members of the datatype's `mutual` block: an occurrence of one is a hole. -/
  members : Array Name
  /-- Each type variable — parameter, type index or existential — with its `TyWf`. -/
  tyVars : Array (Expr × Expr)
  /-- The holes for the field types the language has no tree for: the Lean type, the name
      of the argument and the local it is. -/
  holes : IO.Ref (Array (Expr × Name × FVarId))
  /-- The names already taken by arguments. -/
  used : IO.Ref (Array Name)
  /-- The type variables the language erases at this use (`Unit`), each with the erased type
      that stands for it in the field types. -/
  subst : Array (Expr × Expr) := #[]

/-- Run `k` with the holes created so far in the local context. -/
def withHoles (c : TrCtx) (k : MetaM α) : MetaM α := do
  let hs ← c.holes.get
  let mut lctx ← getLCtx
  for (_, n, id) in hs do
    unless lctx.contains id do lctx := lctx.mkLocalDecl id n tyWfE
  withLCtx lctx (← getLocalInstances) k

/-- A fresh argument name built from `base`. -/
def freshName (c : TrCtx) (base : String) : MetaM Name := do
  let used ← c.used.get
  let mut n := Name.mkSimple base
  let mut i := 2
  while used.contains n do
    n := Name.mkSimple s!"{base}{i}"
    i := i + 1
  c.used.modify (·.push n)
  return n

/-- The last component of a binder's name, without macro scopes. -/
def baseName (n : Name) : String :=
  match n.eraseMacroScopes with
  | .str _ s => s
  | _ => "x"

/-- The hole for the field type `t` of the field `field`: shared with every field of the same
    type. -/
def holeFor (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  if let some (_, _, id) := (← c.holes.get).find? (·.1 == t) then return .fvar id
  let n ← freshName c (baseName field ++ "Ty")
  let id ← mkFreshFVarId
  c.holes.modify (·.push (t, n, id))
  return .fvar id

/-- The node a reduced tree is, when it is not a recursive binder: the name of the
    `TyShape` (or, under `primCovariant`, the `LeanPrimTyCovariant`) constructor, and its
    arguments after the type parameter. -/
def shapeView? (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let e ← whnf e
  let (``LeanScript.Ty.shape, #[s]) := e.getAppFnArgs | return none
  let s ← whnf s
  let .const n _ := s.getAppFn | return none
  let args := s.getAppArgs.extract 1 s.getAppArgs.size
  if n == ``LeanScript.TyShape.primCovariant then
    let some c := args[0]? | return none
    let c ← whnf c
    let .const m _ := c.getAppFn | return none
    return some (m, c.getAppArgs.extract 1 c.getAppArgs.size)
  return some (n, args)

/-- The bundle of a closed type that has an instance: `TyWf.prim p` for a terminal type,
    `tyWfOf t` otherwise. -/
def closedLayout (t inst : Expr) : MetaM Expr := do
  let b ← mkAppOptM ``LeanScript.tyWfOf #[some t, some inst]
  if let some (``LeanScript.TyShape.prim, #[p]) ← shapeView? (mkApp (mkConst ``LeanScript.TyWf.toTy) b) then
    return mkApp (mkConst ``LeanScript.TyWf.prim) p
  return b

mutual

/-- The tree `e : Ty` of an instance, rewritten with the bundled smart constructors of
    `LeanScript.TyWf`, each stand-in `x` becoming its `y`.  `none` when the tree holds a node
    that has no bundled smart constructor (a recursive binder). -/
partial def convTy (sub : Array (Expr × Expr)) (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if let some (_, y) := sub.find? (·.1 == α) then return some y
    if sub.any (fun (x, _) => α.containsFVar x.fvarId!) then return none
    if let some (``LeanScript.TyShape.prim, #[p]) ← shapeView? e then
      return some (mkApp (mkConst ``LeanScript.TyWf.prim) p)
    match e with
    | .proj _ 0 b => return some b
    | _ =>
      match e.getAppFnArgs with
      | (``LeanScript.TyWf.toTy, #[b]) => return some b
      | (``LeanScript.tyOf, #[α, inst]) =>
          return some (← mkAppOptM ``LeanScript.tyWfOf #[some α, some inst])
      | _ => return none
  let un (ctor : Name) (a : Expr) : MetaM (Option Expr) := do
    let some a' ← convTy sub a | return none
    return some (mkApp (mkConst ctor) a')
  match ← shapeView? e with
  | some (``LeanScript.TyShape.prim, #[p]) =>
      return some (mkApp (mkConst ``LeanScript.TyWf.prim) p)
  | some (``LeanScript.TyShape.fn, #[a, b]) =>
      let some a' ← convTy sub a | return none
      let some b' ← convTy sub b | return none
      return some (mkApp2 (mkConst ``LeanScript.TyWf.fn) a' b')
  | some (``LeanScript.LeanPrimTyCovariant.array, #[a]) => un ``LeanScript.TyWf.array a
  | some (``LeanScript.LeanPrimTyCovariant.thunk, #[a]) => un ``LeanScript.TyWf.thunk a
  | some (``LeanScript.LeanPrimTyCovariant.lazy, #[a]) => un ``LeanScript.TyWf.lazy a
  | some (``LeanScript.TyShape.enum, #[s]) =>
      return some (mkApp (mkConst ``LeanScript.TyWf.enum) s)
  | some (``LeanScript.TyShape.record, #[fs]) =>
      let some fs' ← convSch sub fs | return none
      return some (mkApp (mkConst ``LeanScript.TyWf.record) fs')
  | some (``LeanScript.TyShape.taggedUnion, #[l]) =>
      let some l' ← convSch sub l | return none
      return some (mkApp (mkConst ``LeanScript.TyWf.taggedUnion) l')
  | _ => return none

/-- A schema, a list or a non-empty list of trees, rewritten element by element. -/
partial def convSch (sub : Array (Expr × Expr)) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnf e
  let fn := e.getAppFn
  unless fn.isConst do return none
  let mut out := fn
  for a in e.getAppArgs do
    if a.isConstOf ``LeanScript.Ty then
      out := mkApp out tyWfE
      continue
    let aty ← whnf (← inferType a)
    if aty.isSort then
      -- a type argument (`List Ty`): the same type, of bundles
      out := mkApp out (a.replace fun x =>
        if x.isConstOf ``LeanScript.Ty then some tyWfE else none)
    else if aty.isConstOf ``LeanScript.Ty then
      let some a' ← convTy sub a | return none
      out := mkApp out a'
    else if (aty.find? (·.isConstOf ``LeanScript.Ty)).isSome then
      let some a' ← convSch sub a | return none
      out := mkApp out a'
    else
      out := mkApp out a
  return some out

end

/-- The universe a type lives in: `u` for `Sort u`. -/
def sortLevel (t : Expr) : MetaM Level := do
  match ← whnf (← inferType t) with
  | .sort l => return l
  | _ => throwError "`#leanscript_ctor`: {t} is not a type"

mutual

/-- The `TyWf` of the field type `t`, or `none` when the language erases it. -/
partial def trTy (c : TrCtx) (field : Name) (t : Expr) : MetaM (Option Expr) := do
  if ← erasedBinder t then return none
  let t ← instantiateMVars t
  if let some (_, h) := c.tyVars.find? (·.1 == t) then return some h
  let mentions (e : Expr) := e.getUsedConstants.any c.members.contains
  if !t.hasFVar && !mentions t then
    if let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[t]) then
      return some (← closedLayout t inst)
  let tw ← whnf t
  if let some (_, h) := c.tyVars.find? (·.1 == tw) then return some h
  if tw.isForall then return some (← trFn c field tw)
  if !tw.hasFVar && !mentions tw then
    if let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[tw]) then
      return some (← closedLayout tw inst)
    return some (← holeFor c field t)
  some <$> trFormer c field tw

/-- A function type: `TyWf.fn` over the domains the language keeps.  A dependent or
    polymorphic function type is a hole. -/
partial def trFn (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let r? ← forallTelescopeReducing t fun xs body => do
    let isX (id : FVarId) := xs.any (·.fvarId! == id)
    let mut doms : Array Expr := #[]
    for x in xs do
      let d ← inferType x
      if d.hasAnyFVar isX then return none
      if (← whnf d).isSort then return none
      if ← erasedBinder d then continue
      match ← trTy c field d with
      | some a => doms := doms.push a
      | none => pure ()
    if body.hasAnyFVar isX then return none
    match ← trTy c field body with
    | none => return none
    | some r => return some (doms.foldr (fun a b => mkApp2 (mkConst ``LeanScript.TyWf.fn) a b) r)
  match r? with
  | some r => return r
  | none => holeFor c field t

/-- An application of a type former to types that mention type variables or the datatype:
    the former's own tree, at the trees of those arguments. -/
partial def trFormer (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let fn := t.getAppFn
  let .const fnName _ := fn | holeFor c field t
  if c.members.contains fnName then return ← holeFor c field t
  let args := t.getAppArgs
  let mut idxs : Array Nat := #[]
  let mut subs : Array Expr := #[]
  for i in [0:args.size] do
    let a := args[i]!
    unless a.hasFVar || a.getUsedConstants.any c.members.contains do continue
    unless ← isTypeField (← inferType a) do return ← holeFor c field t
    match ← trTy c field a with
    | some a' => idxs := idxs.push i; subs := subs.push a'
    | none => return ← holeFor c field t
  let standDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    idxs.mapIdx fun k i => (Name.mkSimple s!"X{k}", .default, fun _ => inferType args[i]!)
  let r? ← withLocalDecls standDecls fun xs => do
    let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      xs.mapIdx fun k x => (Name.mkSimple s!"instX{k}", .instImplicit,
        fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[x])
    withLocalDecls instDecls fun insts => do
      let mut args' := args
      for k in [0:idxs.size] do args' := args'.set! idxs[k]! xs[k]!
      let t' := mkAppN fn args'
      let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[t'])
        | return none
      -- stand-ins for the arguments' trees, replaced by those trees at the end
      let yDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
        xs.mapIdx fun k _ => (Name.mkSimple s!"Y{k}", .default, fun _ => pure tyWfE)
      withLocalDecls yDecls fun ys => do
        let tree ← whnf (← mkAppOptM ``LeanScript.tyOf #[some t', some inst])
        let clean? ← convTy (xs.zip ys) tree
        let clean? ← match clean? with
          | some r =>
              if (xs ++ insts).any (fun x => r.containsFVar x.fvarId!) then pure none
              else if ← isTypeCorrect r then pure (some r) else pure none
          | none => pure none
        let r ← match clean? with
          | some r => pure r
          | none => do
            -- the former's own instance, at stand-in types whose models are the trees
            let mut vals : Array Expr := #[]
            for k in [0:xs.size] do
              let .succ u ← sortLevel xs[k]!
                | throwError "`#leanscript_ctor`: {xs[k]!} is not a type"
              vals := vals.push (mkApp (mkConst ``LeanScript.TyWf.AsType [u]) ys[k]!)
            let t'' := t'.replaceFVars xs vals
            let .some inst' ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[t''])
              | throwError "`#leanscript_ctor`: no instance for {t''}"
            mkAppOptM ``LeanScript.tyWfOf #[some t'', some inst']
        return some (r.replaceFVars ys subs)
  match r? with
  | some r => return r
  | none => holeFor c field t

end

end LeanScript.CtorFn

end

end
