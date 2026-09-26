module

public meta import LeanScript.ToTerm.TransRecUnion

@[expose] public section

meta section

/-!
# The translation of a recursion on a mutual family: its pieces

What `LeanScript.ToTerm.TransRecFamily` reads a family and its recursion into (`RecFamInfo`,
one `FamMemberInfo` per member, one `FamCtor` per constructor), and the pieces it builds
the fold's case tree from: the tuple of answers of members that answer different types,
the history handed to a Lean branch, a leaf of the case tree, the pointers into the
fields of a node (`LeanScript.FamilyMemberField`, `LeanScript.FamilyOuterMemberField`) and
the dispatch on some of the constructors of a member.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- One field of a constructor of a member of a family, as the fold reads it. -/
inductive FamField where
  /-- A field that does not mention the family, of this Lean type. -/
  | plain (ty : Expr)
  /-- A field that is a value of member `i` of the family. -/
  | member (i : Nat)
  /-- A field of Lean type `ty` that holds values of member `i` of the family only
      **inside** it — an array of them (`Array Q`, `Array (Array Q)`), a function into one
      (`Nat → Q`) or a delay of one (`Thunk Q`) — read as `p` says, where
      `RecObjPayloadField.self` stands for member `i`.  The fold binds, after it, the
      answers at them in its shape (`LeanScript.TyWf.famAnswerBinders`). -/
  | nested (ty : Expr) (i : Nat) (p : RecObjPayloadField)
  deriving Inhabited

/-- How a field of Lean type `t` that mentions a family but is not one of its members is
    read: an array of values of a member or of such arrays, a function into a member, or a
    delay of one — the member, and the reading — or `none`.  `memberOf` gives the member a
    Lean type is, `mentions` whether it mentions the family at all. -/
partial def classifyFamNested (memberOf : Expr → MetaM (Option Nat)) (mentions : Expr → Bool)
    (t : Expr) : MetaM (Option (Nat × RecObjPayloadField)) := do
  if let some k ← memberOf t then return some (k, .self)
  if t.isAppOfArity ``Array 1 then
    let some (k, p) ← classifyFamNested memberOf mentions t.appArg! | return none
    return some (k, .array t t.appArg! p)
  if t.isAppOfArity ``Thunk 1 then
    if let some k ← memberOf t.appArg! then return some (k, .thunk t)
    return none
  if let .forallE _ dom cod _ := t then
    if !cod.hasLooseBVars && !mentions dom then
      if let some k ← memberOf cod then return some (k, .fn t dom)
  return none

/-- The members of a family a field of Lean type `t` holds, read against the field's tree
    `tree`: an occurrence `Ty.familyMember i` is a value of `t`, and an array, a delay or a
    function into something is read into.  Each member found, with its Lean type. -/
partial def famAlignTree (tree t : Expr) : MetaM (Array (Nat × Expr)) := do
  match tree.getAppFnArgs with
  | (``LeanScript.Ty.familyMember, #[i]) => return #[(← natOfExpr i, t)]
  | (``LeanScript.Ty.shape, #[sh]) =>
      match sh.getAppFnArgs with
      | (``LeanScript.TyShape.primCovariant, #[_, cv]) =>
          let t' ← whnf t
          match cv.getAppFnArgs, t'.getAppFnArgs with
          | (``LeanScript.LeanPrimTyCovariant.array, #[_, a]), (``Array, #[e]) =>
              famAlignTree a e
          | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, a]), (``Thunk, #[e]) =>
              famAlignTree a e
          | _, _ => return #[]
      | (``LeanScript.TyShape.fn, #[_, _, b]) =>
          match ← whnf t with
          | .forallE _ _ cod _ =>
              if cod.hasLooseBVars then return #[] else famAlignTree b cod
          | _ => return #[]
      | _ => return #[]
  | _ => return #[]

/-- A field of a node of the case tree that holds values of a member only inside it
    (`FamField.nested`), as the leaves of the case tree read it: the answers of the Lean
    recursion at it are computed from the window the fold binds after it. -/
structure FamNested where
  /-- The member whose values it holds. -/
  member : Nat
  /-- How it is read, `RecObjPayloadField.self` standing for the member. -/
  read : RecObjPayloadField
  /-- Its Lean value, a variable of the branch. -/
  val : Expr
  /-- The variable of the window after it: the answers at the values it holds. -/
  win : FVarId
  /-- The language type of the window. -/
  winTy : Expr

/-- One constructor of a member of a family, as the fold reads it. -/
structure FamCtor where
  /-- The Lean constructor. -/
  name : Name
  /-- Its fields. -/
  fields : Array FamField
  /-- The list of its field trees, as an expression of type `List (TyWfIn (n + 2))` —
      the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- The universe levels and the parameters the constructor is applied at: those of the
      block, or those of the wrapper an auxiliary type of a nested inductive is
      (`List.cons` at `Rose`). -/
  lvls : List Level := []
  /-- See `lvls`. -/
  params : Array Expr := #[]
  deriving Inhabited

/-- One member of a family, as the fold reads it. -/
structure FamMemberInfo where
  /-- The Lean inductive. -/
  ind : Name
  /-- The Lean type of the member, at the parameters. -/
  selfTy : Expr
  /-- The member's schema, an expression of type `LeanFamMemberSchema (TyWfIn (n + 2))`. -/
  schema : Expr
  /-- The constructors, in order. -/
  ctors : Array FamCtor
  /-- The Lean branch of the `brecOn` for this member. -/
  brecF : Expr
  /-- Is the motive of this member the answer type (and not `PUnit`)? -/
  answering : Bool
  /-- The number of the motive of the `brecOn` for this member (the motives are the
      member's and those of the auxiliary types that are not members: `Array Q`, and the
      `List Q` inside it). -/
  motive : Nat := 0
  deriving Inhabited

/-- What the fold of a mutual family needs to know about it and the recursion. -/
structure RecFamInfo where
  /-- The universe levels of the inductives. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- `n`, as an expression: the family has `n + 2` members. -/
  nE : Expr
  /-- The scope of the family, `n + 2`. -/
  sc : Nat
  /-- The members, in order, as an expression of type
      `List (LeanFamMemberSchema (TyWfIn (n + 2)))`. -/
  msE : Expr
  /-- The members. -/
  members : Array FamMemberInfo
  /-- The binders of a branch, `TyWf.famRecBinders f hwf τ`. -/
  bindE : Expr
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- The motives of the `brecOn`. -/
  motives : Array Expr
  /-- The branches of the `brecOn`, one per motive. -/
  brecFs : Array Expr := #[]
  /-- The type each motive is a function of. -/
  motiveDoms : Array Expr := #[]
  /-- For each motive, is it the motive of a member that answers (and not `PUnit`, nor
      the motive of an auxiliary type that is not a member)? -/
  motiveAnswering : Array Bool := #[]
  /-- The answer given by the branches of a member whose motive is `PUnit`. -/
  dflt : Option Expr
  /-- Do the answering members answer different types?  Then the fold answers the tuple
      `τLean` of all of them (`PProd`, nested to the right), each member's branch fills in
      its own component and the defaults elsewhere, and an answer at an occurrence of a
      member is read as its component. -/
  tuple : Bool := false
  /-- In a tuple fold, the component of each motive (`none` for a `PUnit` one, and for
      one of an auxiliary type that is not a member). -/
  slots : Array (Option Nat) := #[]
  /-- In a tuple fold, the component types. -/
  comps : Array Expr := #[]
  /-- In a tuple fold, the default of each component, unfolded. -/
  compDflts : Array Expr := #[]

/-- The `i`-th component of a value `x` of the right-nested tuple of `n` components. -/
def tupleProj (n i : Nat) (x : Expr) : MetaM Expr := do
  let mut cur := x
  for _ in [0:i] do cur ← mkAppM ``PProd.snd #[cur]
  if i + 1 < n then cur ← mkAppM ``PProd.fst #[cur]
  return cur

/-- The right-nested tuple of these components. -/
def tupleMk (xs : Array Expr) : MetaM Expr := do
  let mut acc := xs.back!
  for r in [1:xs.size] do
    acc ← mkAppM ``PProd.mk #[xs[xs.size - 1 - r]!, acc]
  return acc

/-- The right-nested tuple type of these types. -/
def tupleTy (ts : Array Expr) : MetaM Expr := do
  let mut acc := ts.back!
  for r in [1:ts.size] do
    acc ← mkAppM ``PProd #[ts[ts.size - 1 - r]!, acc]
  return acc

/-- The answer of member `m` read out of the fold's answer `a`. -/
def RecFamInfo.readAnswer (info : RecFamInfo) (m : Nat) (a : Expr) : MetaM Expr := do
  unless info.tuple do return a
  let some i := info.slots[m]! | return a
  tupleProj info.comps.size i a

/-- The history of a structural recursion on a family, at a value whose shape is known:
    as `LeanScript.ToTerm.buildRecObjHistory`, except that the entry of **any** motive
    marked in `answering` at a bound subvalue is the variable `answers` maps it to. -/
partial def buildFamHistory (motiveVars : Array Expr) (motives : Array Expr)
    (answering : Array Bool) (answers : Array (Expr × Expr)) (placeholder : Expr)
    (proj : Nat → Expr → MetaM Expr := fun _ a => pure a) :
    MetaM Expr := do
  let real (t : Expr) : Expr := t.replaceFVars motiveVars motives
  let t ← whnf placeholder
  -- below a function field `f` (or a delay): at every argument `a`, the answer at `f a`
  -- (the window of `f` applied to `a`) and what is below it
  if let .forallE n d b bi := t then
    return ← withLocalDecl n bi (real d) fun a => do
      let extra := answers.filterMap fun (s, ans) => match s with
        | .mdata md f => if md.getBool `leanscriptFn then some (mkApp f a, (mkApp ans a).headBeta)
            else none
        | _ => none
      let v ← buildFamHistory motiveVars motives answering (answers ++ extra)
        (b.instantiate1 a) proj
      mkLambdaFVars #[a] v
  match t.getAppFn, t.getAppArgs with
  | .const ``PProd ls, #[a, b] =>
      let va ← buildFamHistory motiveVars motives answering answers a proj
      let vb ← buildFamHistory motiveVars motives answering answers b proj
      return mkAppN (mkConst ``PProd.mk ls) #[real a, real b, va, vb]
  | .const ``PUnit ls, #[] => return mkConst ``PUnit.unit ls
  | .fvar f, #[x] =>
      match motiveVars.findIdx? (·.fvarId! == f) with
      | some i =>
          if answering[i]! then
            for (s, ans) in answers do
              if s == x then return ← proj i ans
            for (s, ans) in answers do
              if ← isDefEq s x then return ← proj i ans
            mkFreshExprMVar (real t)
          else
            -- the answer of the motive of an auxiliary type that is not a member (`Array
            -- Q`, `List Q`), if it is known
            let key := motiveKey i x
            for (s, ans) in answers do
              if s == key then return ans
            for (s, ans) in answers do
              if let .mdata d s' := s then
                if d.getNat `leanscriptMotive == i then
                  if ← isDefEq s' x then return ans
            let rt ← whnf (real t)
            match rt with
            | .const ``PUnit ls => return mkConst ``PUnit.unit ls
            | _ => mkFreshExprMVar (real t)
      | none => mkFreshExprMVar (real t)
  | _, _ => mkFreshExprMVar (real t)

/-- The fold of a record over the values of member `k` of a family, as the reading of a
    field that holds them inside it (`FamField.nested`) needs it: the Lean recursion's
    branches for the auxiliary types (`Array Q`, `List Q`), and the answer at a value of the
    member read out of the fold's answer. -/
def RecFamInfo.nestedObjInfo (info : RecFamInfo) (trans : TransFn) (k : Nat) :
    RecObjInfo :=
  let mk := info.members[k]!
  { ind := mk.ind, ctor := .anonymous, lvls := info.lvls, params := info.params,
    selfTy := mk.selfTy, fields := #[], τLean := info.τLean, τ := info.τ, trans,
    motives := info.motives, brecFs := info.brecFs, motiveDoms := info.motiveDoms,
    selfMotive := mk.motive, selfProj := info.readAnswer mk.motive }

/-- The answers of the Lean recursion at the fields `ns` that hold values of members only
    inside them, let-bound in front of what `cont` builds, with `answers` extended by
    them: for an array, the answers of the motives of `List` and `Array` of its elements,
    folded out of the window (`recObjBindArray`); for a function or a delay, the window
    itself, which is the function of (the delayed) answers. -/
def bindFamNested (trans : TransFn) (info : RecFamInfo) (c : TCtx)
    (answers : Array (Expr × Expr)) :
    List FamNested → (TCtx → Array (Expr × Expr) → MetaM Expr) → MetaM Expr
  | [], cont => cont c answers
  | n :: ns, cont => do
      match n.read with
      | .array arrTy elemTy elem =>
          let ri := info.nestedObjInfo trans n.member
          recObjBindArray ri c answers n.val (← c.var n.win) n.winTy arrTy elemTy elem 0
            fun c' answers' => bindFamNested trans info c' answers' ns cont
      | .fn .. =>
          bindFamNested trans info c (answers.push (fnKey n.val, mkFVar n.win)) ns cont
      | .thunk _ =>
          -- the value is `Thunk.mk g` (see `famThunkShape`), and the answer at `g ()` is
          -- the delayed answer forced
          let .app _ g := n.val
            | throwError "`#leanscript_to_term`: internal: a delayed field is not `Thunk.mk g`"
          let uτ ← getDecLevel info.τLean
          let force := mkLambda `u .default (mkConst ``Unit)
            (mkApp2 (mkConst ``Thunk.get [uτ]) info.τLean (mkFVar n.win))
          bindFamNested trans info c (answers.push (fnKey g, force)) ns cont
      | _ => throwError "`#leanscript_to_term`: internal: not a field that holds a member \
          inside it"

/-- The value a delayed field `x : Thunk Q` of a member is given in the shape a Lean branch
    is instantiated at: `Thunk.mk (fun _ => x.get)`, whose history `Thunk.below` reduces
    to the answer at `x.get` — and which the reduced branch is rewritten back to `x`
    (`unfamThunkShape`). -/
def famThunkShape (x : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType x)
  let elemTy := ty.appArg!
  let u ← getDecLevel elemTy
  let g := mkLambda `u .default (mkConst ``Unit) (mkApp2 (mkConst ``Thunk.get [u]) elemTy x)
  return mkApp2 (mkConst ``Thunk.mk [u]) elemTy g

/-- `famThunkShape`, undone: `Thunk.mk (fun _ => x.get)` is `x`. -/
def unfamThunkShape (e : Expr) : Expr :=
  e.replace fun s =>
    if s.isAppOfArity ``Thunk.mk 2 then
      match s.appArg! with
      | .lam _ _ b _ =>
          if b.isAppOfArity ``Thunk.get 2 && !b.hasLooseBVars then some b.appArg! else none
      | _ => none
    else none

/-- The branch of the fold at a node of the case tree of member `top`'s branches: the
    Lean branch of that member instantiated at the shape found so far and at the history
    in which the answer at a bound subvalue is its variable, reduced, and translated in
    `c`.  The answers at the fields `nested` that hold values of members inside them are
    let-bound in front of it (`bindFamNested`).

    When the reduced branch still reads something the fold has not given — the history
    below a subvalue that has not been looked into — the result is `.inr` of those of the
    `pending` subvalues (the occurrences not yet looked into, at this node and at the
    nodes above it) whose history it reads: a deeper look into one of them is what the
    branch needs.  It fails when it reads nothing that a deeper look could give. -/
def recFamLeaf (trans : TransFn) (info : RecFamInfo) (c : TCtx) (topM : Nat) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr))
    (pending : Array FVarId) (nested : Array FamNested := #[]) :
    MetaM (Expr ⊕ Array FVarId) := do
  let mi := info.members[topM]!
  unless mi.answering do
    let some d := info.dflt
      | throwError "`#leanscript_to_term`: internal: no default answer"
    -- the default is unfolded all the way — for an answer that is a function (a recursion
    -- with arguments after the value) it is `fun _ => default`, and the instance is not a
    -- value of the language — and the default of `Nat`, `Nat.zero`, is written as the
    -- literal
    let d' ← Meta.reduce d
    let d' := d'.replace fun s => if s.isConstOf ``Nat.zero then some (mkNatLit 0) else none
    return .inl (← trans c d')
  let shape := resolveShape descend top
  let fty ← instantiateForall (← inferType mi.brecF) #[shape]
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nP := info.params.size
  let nM := info.motives.size
  let motiveTys ← info.motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let needed ← IO.mkRef (none : Option (Array FVarId))
  let t ← bindFamNested trans info c answers nested.toList fun c answers => do
    let answers := answers.map fun (s, a) => (resolveShape descend s, a)
    let hist ← withLocalDeclsD decls fun ms => do
      let lvls := histTy.getAppFn.constLevels!
      let placeholder := mkAppN (mkConst fn lvls)
        (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
      let h ← buildFamHistory ms info.motives info.motiveAnswering answers placeholder
        info.readAnswer
      if ms.any (fun m => h.containsFVar m.fvarId!) then
        throwError "`#leanscript_to_term`: internal: the history mentions its motive"
      pure h
    let body ← reduceBrecBodyDeep (mkAppN mi.brecF #[shape, hist])
    let body ← instantiateMVars (← reduceHistoryProjs body)
    let body := unfamThunkShape body
    -- in a tuple fold, the member's answer is its component, the defaults elsewhere
    let body ← if info.tuple then
        match info.slots[mi.motive]! with
        | some i => tupleMk (info.compDflts.set! i body)
        | none => pure body
      else pure body
    if body.hasExprMVar then
      -- the unknown parts of the history are the histories below the subvalues not looked
      -- into, each a metavariable whose type names its subvalue
      let mut tys : Array Expr := #[]
      for m in ← getMVars body do
        tys := tys.push (← instantiateMVars (← m.getType))
      let need := pending.filter fun f => tys.any (·.containsFVar f)
      unless need.isEmpty do
        needed.set (some need)
        return mkConst ``Unit
      throwError "`#leanscript_to_term`: this recursion on a mutual family reads the value \
        of the function, or takes a value apart, further down than the fold looks at this \
        depth"
    trans { c with foldInds := c.foldInds ++ info.members.map (·.ind) } body
  match ← needed.get with
  | some need => return .inr need
  | none => return .inl t

/-- The pointer at the `p`-th field of this list of field trees, which is an occurrence
    of member `i` of the family. -/
def mkFamMemberFieldE (info : RecFamInfo) (fsL : Array Expr) (p i : Nat) : MetaM Expr := do
  let ι := tyWfInE info.sc
  let iE := mkNatLit i
  let pred := mkAppN (mkConst ``LeanScript.IsFamilyMemberField) #[info.nE, iE]
  let mut acc : Option Expr := none
  for r in [0:p + 1] do
    let j := p - r
    let a := fsL[j]!
    let rest ← mkListLit ι (fsL.extract (j + 1) fsL.size).toList
    match acc with
    | none =>
        let h ← mkEqRefl (mkApp (mkConst ``LeanScript.Ty.familyMember) iE)
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.here) #[ι, pred, a, rest, h])
    | some inner =>
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.there) #[ι, pred, a, rest, inner])
  return acc.get!

/-- The proof that member `i` of the family is its `i`-th schema. -/
def mkFamMemberAtE (info : RecFamInfo) (i : Nat) : MetaM Expr := do
  let ms := info.members.map (·.schema)
  let elem := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (tyWfInE info.sc)
  let tail (j : Nat) : MetaM Expr := mkListLit elem (ms.extract j ms.size).toList
  let mut acc := mkAppN (mkConst ``LeanScript.FamilyMemberAt.here)
    #[info.nE, ms[i]!, ← tail (i + 1)]
  for r in [0:i] do
    let j := i - 1 - r
    acc := mkAppN (mkConst ``LeanScript.FamilyMemberAt.there)
      #[info.nE, mkNatLit (i - 1 - j), ms[j]!, ms[i]!, ← tail (j + 1), acc]
  return acc

/-- The branches of a fold over the member schema `l` (of a `ctors` member), in its
    shape: `pre` are the implicit arguments every family of the case tree shares
    (signature, `n`, members, binders, context, answer type, depth). -/
partial def mkFamTUFoldKCases (sc : Nat) (pre : Array Expr) (l : Expr)
    (branches : Array Expr) : MetaM Expr := do
  let ι := tyWfInE sc
  let rest (from_ : Nat) (fsLists : List Expr) : MetaM Expr := do
    let mut acc := mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCasesRest.nil) pre
    let n := fsLists.length
    for i in [0:n] do
      let idx := n - 1 - i
      let fs := fsLists[idx]!
      let more ← mkListLit (mkApp (mkConst ``List [Level.zero]) ι) (fsLists.drop (idx + 1))
      acc := mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCasesRest.cons)
        (pre ++ #[fs, more, branches[from_ + idx]!, acc])
    return acc
  let rec cpCases (cp : Expr) (i : Nat) : MetaM Expr := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, restL]) =>
        let rs ← listOfExpr restL
        return mkAppN (mkConst `LeanScript.FamilyCtorsWithPayloadFoldKCases.here)
          (pre ++ #[fields, restL, branches[i]!, ← rest (i + 1) rs])
    | (``LeanScript.CtorsWithPayload.skip, #[_, more]) =>
        return mkAppN (mkConst `LeanScript.FamilyCtorsWithPayloadFoldKCases.skip)
          (pre ++ #[more, branches[i]!, ← cpCases more (i + 1)])
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, restL]) =>
      let rs ← listOfExpr restL
      return mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCases.payloadFirst)
        (pre ++ #[fields, next, restL, branches[0]!, branches[1]!, ← rest 2 rs])
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) =>
      return mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCases.skip)
        (pre ++ #[cp, branches[0]!, ← cpCases cp 1])
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- A node of the case tree of a fold of a family that the fold has dispatched on: its
    constructor's field trees (`fsE`, with elements `fsL`) and, for each of its
    occurrences of a member, the position of the field, the member, and the variable bound
    for the subvalue there. -/
structure FamFrame where
  /-- The list of the constructor's field trees, the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- The occurrences of members among the fields: position, member and variable. -/
  subs : Array (Nat × Nat × FVarId)
  deriving Inhabited

/-- The nodes above a branch, innermost first, as the expression of type
    `List (List (TyWfIn (n + 2)))` the families of the case tree are indexed by. -/
def famOuterE (info : RecFamInfo) (outer : List FamFrame) : MetaM Expr :=
  mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE info.sc)) (outer.map (·.fsE))

/-- The pointer `LeanScript.FamilyOuterMemberField` at the occurrence `field` (of member
    `k`) of the `i`-th node above (`0` the innermost). -/
def mkFamOuterFieldE (info : RecFamInfo) (k : Nat) :
    List FamFrame → Nat → Expr → MetaM Expr
  | f :: rest, 0, field => do
      return mkAppN (mkConst ``LeanScript.FamilyOuterMemberField.here)
        #[info.nE, mkNatLit k, f.fsE, ← famOuterE info rest, field]
  | f :: rest, i + 1, field => do
      return mkAppN (mkConst ``LeanScript.FamilyOuterMemberField.there)
        #[info.nE, mkNatLit k, f.fsE, ← famOuterE info rest,
          ← mkFamOuterFieldE info k rest i field]
  | [], _, _ => throwError "`#leanscript_to_term`: internal: no node above to look into"

end LeanScript.ToTerm

end

end
