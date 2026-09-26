module

public meta import LeanScript.ToTerm.ObjectExpr
public meta import LeanScript.ToTerm.Options

@[expose] public section

meta section

/-!
# The compiled form of a structural recursion

Reducing a `brecOn` body far enough to see the branch it takes, and reading the values of
the recursion at the previous arguments out of the history it is given.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The compiled form of a structural recursion

Lean compiles a structurally recursive definition into `X.brecOn`, which hands the branch
the whole **history** of the recursion — the value of the function at every smaller
argument — while the grammar's folds hand the branch a fixed number of the nearest
answers (`LeanScript.Term.nat_rec' k`, `LeanScript.Term.recTaggedUnion_rec'`).  So a
`brecOn` is translated by *reducing the history away*: the branch is instantiated at a
history whose nearest entries are variables standing for those answers, and the
translation succeeds exactly when nothing else of the history is read. -/

/-- Reduce an application far enough to see the branch it takes: beta, `match`, `casesOn`
    and the auxiliary the compiler names `_f`, and **nothing else** — a call the
    translation has to see is left standing. -/
def isBrecAux (n : Name) : Bool :=
  let s := n.getString!
  s == "_f" || s.startsWith "match_" || s == "casesOn" || s == "brecOn" || s == "_unary"

/-- Is this `match` stuck on a value of a structure that is not built in place (the
    answer of the recursion, say, when it is a pair)?  Reducing it would only take the
    value apart into its projections, one per use, so it is left standing: the
    translation takes it apart once, as the record's case analysis. -/
def matchStuckOnStructure (e : Expr) : MetaM Bool := do
  let some m ← matchMatcherApp? e | return false
  for d in m.discrs do
    let d' ← whnfCore d
    if let .const cn _ := d'.getAppFn then
      if (← getEnv).find? cn matches some (.ctorInfo _) then continue
    let ty ← whnf (← inferType d)
    let .const indName _ := ty.getAppFn | continue
    let some (.inductInfo ii) := (← getEnv).find? indName | continue
    if ii.ctors.length == 1 && ii.numIndices == 0 && !ii.isRec then return true
  return false

/-- Is this argument (a part of) the history of a structural recursion: a value built for
    it, with unknown parts, or one whose type is built out of `PProd`, `PUnit` and
    `below`? -/
def isHistoryArg (a : Expr) : MetaM Bool := do
  if a.hasExprMVar then return true
  let t ← instantiateMVars (← inferType a)
  return (t.find? fun s => match s with
    | .const n _ => n == ``PProd || n == ``PUnit || (n.isStr && n.getString! == "below")
    | _ => false).isSome

/-- `X.rec` applied to more arguments than it takes (the history), whose minor premises
    do not use the answers at the recursive fields — what `whnfCore` makes of a
    `X.casesOn` — written back as that `X.casesOn`. -/
def recAsCasesOn? (s : Expr) : MetaM (Option Expr) := do
  let .const rn us := s.getAppFn | return none
  unless rn.isStr && rn.getString! == "rec" do return none
  let some (.recInfo ri) := (← getEnv).find? rn | return none
  unless ri.numMotives == 1 do return none
  let args := s.getAppArgs
  let nP := ri.numParams
  let nM := ri.numMinors
  let nI := ri.numIndices
  let arity := nP + 1 + nM + nI + 1
  unless args.size > arity do return none
  let motive := args[nP]!
  -- the number of binders of each minor premise: its fields and the answers at them
  let counts? ← withLocalDeclD `motive (← inferType motive) fun m => do
    let ty ← instantiateForall ri.type (args.extract 0 nP |>.push m)
    forallBoundedTelescope ty nM fun minors _ => minors.mapM fun mi => do
      forallTelescopeReducing (← inferType mi) fun xs _ => pure xs.size
  let mut alts : Array Expr := #[]
  for i in [0:nM] do
    let minor := args[nP + 1 + i]!
    let nf := ri.rules[i]!.nfields
    let alt? ← forallBoundedTelescope (← inferType minor) counts?[i]! fun xs _ => do
      let body := (mkAppN minor xs).headBeta
      let ihs := xs.extract nf xs.size
      if ihs.any (fun ih => body.containsFVar ih.fvarId!) then return none
      return some (← mkLambdaFVars (xs.extract 0 nf) body)
    let some alt := alt? | return none
    alts := alts.push alt
  let cn := rn.getPrefix ++ `casesOn
  unless (← getEnv).contains cn do return none
  return some (mkAppN (mkConst cn us)
    (args.extract 0 nP ++ #[motive] ++ args.extract (nP + 1 + nM) arity ++ alts
      ++ args.extract arity args.size))

/-- The casts a `match` on an indexed family leaves in a branch once the indices are
    known — `Nat.Internal.elimOffset`, `h ▸ x`, `Eq.ndrec`, `cast` — reduced, anywhere:
    each is an `Eq.rec` whose two sides are then the same, which reduces whatever the
    proof. -/
def reduceIndexCasts (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if t.isHeadBetaTarget then return .visit t.headBeta
    let .const n _ := t.getAppFn | return .done t
    -- `Eq.rec` reduces (by the rule for equality) once both sides are the same, whatever
    -- the proof: to its branch, applied to what the cast is applied to
    let args := t.getAppArgs
    if n == ``Eq.rec && args.size ≥ 6 then
      if ← isDefEq args[1]! args[4]! then
        return .visit (mkAppN args[3]! (args.extract 6 args.size)).headBeta
      return .done t
    if n == ``HEq.rec && args.size ≥ 7 then
      if (← isDefEq args[0]! args[4]!) && (← isDefEq args[1]! args[5]!) then
        return .visit (mkAppN args[3]! (args.extract 7 args.size)).headBeta
      return .done t
    unless n == ``Nat.Internal.elimOffset || n == ``Eq.ndrec || n == ``Eq.mpr ||
        n == ``Eq.mp || n == ``cast || n == ``HEq.ndrec || n == ``Eq.casesOn ||
        n == ``HEq.casesOn do
      return .done t
    match ← unfoldDefinition? t with
    | some t' => return .visit t'.headBeta
    | none => return .done t)

/-- The branches of `X.casesOn` on a variable of an **indexed family** (`Vec α n`), read
    off the whole application `e` — the `match` Lean compiled carries equations between
    the indices in its motive, `n = m + 1 → x ≍ cons a v → …`, which hold at the
    constructor.  So at each constructor the application is instantiated at the value
    `C fields` and at the indices it has (a variable of the context that an index
    mentions is unified with the constructor's: `n + 1 = m + 1` sets `n := m`), and its
    casts reduced (`reduceIndexCasts`): the branch, as `fun fields => …`.

    A constructor the index rules out (`nil` for a value of `Vec α (n + 1)`) has no Lean
    branch; its branch is the `default` of the answer's type (it is never taken on a value
    of the Lean type).  Returns the answer's Lean type and the branches; `none` when `e` is
    not such a dispatch on a variable. -/
def indexedCasesMinors? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let .const cn _ := e.getAppFn | return none
  unless cn.isStr && cn.getString! == "casesOn" do return none
  let ind := cn.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let nP := ii.numParams
  let nI := ii.numIndices
  let nC := ii.ctors.length
  let arity := nP + 2 + nI + nC
  let args := e.getAppArgs
  unless nI != 0 && args.size ≥ arity do return none
  let major := args[nP + 1 + nI]!
  unless major.isFVar do return none
  let params := args.extract 0 nP
  let minorsL := args.extract (nP + 2 + nI) arity
  let extra := args.extract arity args.size
  let τLean ← instantiateMVars (← inferType e)
  let majTy ← whnf (← inferType major)
  -- the constructors' levels are the family's (the `casesOn`'s start with the motive's)
  let ilvls := majTy.getAppFn.constLevels!
  -- the indices the dispatch is at: its own index arguments (which a dispatch above may
  -- have fixed already), rather than the type of the variable
  let idxM := args.extract (nP + 1) (nP + 1 + nI)
  -- the variables of the context the indices mention
  let mut fvs : Array Expr := #[]
  for a in idxM do
    for f in (collectFVars {} a).fvarIds do
      unless (← f.getDecl).isLet || fvs.contains (.fvar f) || f == major.fvarId! do
        fvs := fvs.push (.fvar f)
  let ctors := ii.ctors.toArray
  let mut minors : Array Expr := #[]
  for h : i in [0:nC] do
    let cn := ctors[i]
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls) params
    let m ← forallTelescopeReducing cty fun xs resTy => do
      let shape := mkAppN (mkConst cn ilvls) (params ++ xs)
      let idxS := resTy.getAppArgs.extract nP (nP + nI)
      let mvs ← fvs.mapM fun f => do mkFreshExprMVar (← inferType f)
      let mut ok := true
      for (a, b) in idxM.zip idxS do
        if ok then
          ok ← isDefEq (a.replaceFVars fvs mvs) b
      let body ← if ok then do
          let vals ← (mvs.zip fvs).mapM fun (mv, f) => do
            let v ← instantiateMVars mv
            pure (if v.hasExprMVar then f else v)
          let sub (t : Expr) : Expr := t.replaceFVars (fvs.push major) (vals.push shape)
          -- the step `casesOn (C xs) … ⇒ minor xs`, then the casts the equations make
          let b := (mkAppN (sub minorsL[i]!) (xs ++ extra.map sub)).headBeta
          reduceIndexCasts b
        else do
          let inst ← try synthInstance (mkApp (mkConst ``Inhabited [← getLevel τLean]) τLean)
            catch _ => throwError "`#leanscript_to_term`: the constructor {cn} of the \
              indexed family {ind} cannot have the index of {major}, but the dispatch of \
              the language has a branch for it, and the answer's type {τLean} has no \
              `default` to put there"
          -- (unfolded, and a `Nat.zero` written as the literal the language has)
          let d ← whnf (mkApp2 (mkConst ``Inhabited.default [← getLevel τLean]) τLean inst)
          pure <| d.replace fun t =>
            if t.isConstOf ``Nat.zero then some (mkRawNatLit 0) else none
      mkLambdaFVars xs body
    minors := minors.push m
  return some (τLean, minors)

/-- `indexedCasesMinors?`, written back as a `casesOn` of a motive that mentions nothing,
    applied to nothing more: what the branches read (the history of a recursion, handed
    through the dispatch) is then in plain sight.  `none` when `e` is not such a
    dispatch, or a branch has no term. -/
def normalizeIndexedCasesOn? (e : Expr) : MetaM (Option Expr) := do
  let some (τLean, minors) ← (try indexedCasesMinors? e catch _ => pure none) | return none
  let .const cn us := e.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? cn.getPrefix | return none
  let args := e.getAppArgs
  let nP := ii.numParams
  let nI := ii.numIndices
  let motive ← lambdaBoundedTelescope args[nP]! (nI + 1) fun xs _ => mkLambdaFVars xs τLean
  let ci ← getConstInfo cn
  let lvl ← getLevel τLean
  let us' := if ci.levelParams.length == ii.levelParams.length + 1 then lvl :: us.tail else us
  return some (mkAppN (mkConst cn us')
    (args.extract 0 nP ++ #[motive] ++ args.extract (nP + 1) (nP + 2 + nI) ++ minors))

/-- A `casesOn` stuck on a value the fold has not dispatched on (a later argument of the
    recursion, say), applied to the history: Lean's `match` passes the history through
    the dispatch when the motive of the recursion is a function.  When the type of the
    history does not depend on the value dispatched on, the history is pushed into the
    alternatives, `casesOn (motive := fun y => H → B) y f g h` becoming
    `casesOn (motive := fun y => B) y (f h) (fun … => g … h)`, where it is read like
    anywhere else. -/
def pushHistoryIntoCasesOn? (s : Expr) : MetaM (Option Expr) := do
  let s := (← recAsCasesOn? s).getD s
  let .const cn us := s.getAppFn | return none
  unless cn.isStr && cn.getString! == "casesOn" do return none
  let some (.inductInfo ii) := (← getEnv).find? cn.getPrefix | return none
  let args := s.getAppArgs
  let nP := ii.numParams
  let nI := ii.numIndices
  let nC := ii.ctors.length
  let arity := nP + 1 + nI + 1 + nC
  unless args.size > arity do return none
  -- the history is the first extra argument — or, for an indexed family, the first one
  -- after the equations between the indices a `match` hands its dispatch (`k` of them)
  let mut k := 0
  let mut found := false
  for j in [arity:args.size] do
    unless found do
      if ← isHistoryArg args[j]! then found := true else k := k + 1
  unless found && (k == 0 || nI != 0) do return none
  let a := args[arity + k]!
  let newMotive? ← lambdaBoundedTelescope args[nP]! (nI + 1) fun xs body => do
    unless xs.size == nI + 1 do return none
    forallBoundedTelescope (← whnf body) k fun eqs body' => do
      unless eqs.size == k do return none
      let .forallE _ dom b _ ← whnf body' | return none
      if dom.hasAnyFVar (fun f => xs.any (·.fvarId! == f) || eqs.any (·.fvarId! == f)) then
        return none
      let b' := b.instantiate1 a
      return some (← mkLambdaFVars xs (← mkForallFVars eqs b'), ← getLevel b')
  let some (newMotive, lvl) := newMotive? | return none
  let ci ← getConstInfo cn
  let us' := if ci.levelParams.length == ii.levelParams.length + 1 then
    lvl :: us.tail else us
  let mut alts : Array Expr := #[]
  for i in [0:nC] do
    let alt := args[nP + 1 + nI + 1 + i]!
    let nf := (← getConstInfoCtor ii.ctors[i]!).numFields
    let alt' ← forallBoundedTelescope (← inferType alt) (nf + k) fun fs _ => do
      mkLambdaFVars fs (mkAppN alt (fs.push a)).headBeta
    alts := alts.push alt'
  return some (mkAppN (mkConst cn us')
    (args.extract 0 nP ++ #[newMotive] ++ args.extract (nP + 1) (nP + 1 + nI + 1) ++ alts
      ++ args.extract arity (arity + k) ++ args.extract (arity + k + 1) args.size))

/-- A `match` handed the history of the recursion as an extra argument (Lean passes it
    through the dispatch when the motive of the recursion is a function), unfolded into
    the `casesOn`s it is compiled to, so that the history can be pushed into them
    (`pushHistoryIntoCasesOn?`).  `unfoldDefinition?` does not unfold a matcher. -/
def unfoldMatcherWithHistory? (e : Expr) : MetaM (Option Expr) := do
  let some m ← matchMatcherApp? e | return none
  if m.remaining.isEmpty || !(← m.remaining.anyM isHistoryArg) then return none
  let .const n us := e.getAppFn | return none
  let ci ← getConstInfo n
  let v ← instantiateValueLevelParams ci us
  return some (v.betaRev e.getAppRevArgs)

/-- A `match` with a default (the auxiliary `f._sparseCasesOn_i` Lean compiles it to) on
    a value whose constructor the shape fixes: the branch that constructor takes.  Lean's
    `match` with a catch-all pattern (`List.get?Internal`, `| _, _ => none`) is compiled
    this way, and its motive mentions the history of the recursion, so the dispatch is
    reduced away here rather than translated.  `none` when the value is not a
    constructor application. -/
def reduceSparseCasesOnCtor? (e : Expr) : MetaM (Option Expr) := do
  let .const n _ := e.getAppFn | return none
  unless n.isStr && n.getString!.startsWith "_sparseCasesOn" do return none
  let some u ← withTransparency .all (unfoldDefinition? e) | return none
  let some r ← reduceRecMatcher? u.headBeta | return none
  return some r.headBeta

/-- `whnfCore`, unfolding the auxiliaries of a compiled recursion on the way. -/
partial def reduceBrecBody (e : Expr) : MetaM Expr := do
  -- `whnfCore`, one `match` or recursor at a time, so that a `match` stuck on a
  -- structure is seen before it is taken apart into projections
  let e ← withConfig (fun cfg => { cfg with iota := false }) (whnfCore e)
  if ← matchStuckOnStructure e then return e
  if let some e' ← reduceRecMatcher? e then return ← reduceBrecBody e'
  if let some e' ← reduceSparseCasesOnCtor? e then return ← reduceBrecBody e'
  match e.getAppFn with
  | .const n _ =>
      if isBrecAux n then
        match ← withTransparency .all (unfoldDefinition? e) with
        | some e' =>
            if n.isStr && n.getString! == "casesOn" then
              -- a `casesOn` stuck on a value the shape does not fix, handed the history,
              -- is kept (with the history pushed into its alternatives) rather than
              -- unfolded into the recursor
              let e'' ← withConfig (fun cfg => { cfg with iota := false }) (whnfCore e')
              if let some r ← reduceRecMatcher? e'' then return ← reduceBrecBody r
              if let some pushed ← pushHistoryIntoCasesOn? e then return pushed
              -- a stuck dispatch on an indexed family is kept whole: its translation
              -- reads the equations between the indices it carries
              if let some (.inductInfo ii) := (← getEnv).find? n.getPrefix then
                if ii.numIndices != 0 then return e
            reduceBrecBody e'
        | none =>
            match ← unfoldMatcherWithHistory? e with
            | some e' => reduceBrecBody e'
            | none => return e
      else return e
  | _ => return e

/-- One step of `reduceBranchMatches` at a subterm, if it applies. -/
def reduceBranchStep? (s : Expr) : MetaM (Option Expr) := do
  if s.isHeadBetaTarget then return some s.headBeta
  -- a `match` (or `casesOn`) that is not at the head of the branch — an argument of `+`,
  -- say — is not reduced by `reduceBrecBody`; once the shape the branch is instantiated
  -- at makes its discriminant a constructor, it is reduced here, so that the history it
  -- is handed is read like any other
  if s.isApp then
    if let .const n _ := s.getAppFn then
      let env ← getEnv
      if (isBrecAux n || isRecCore env n) && !(← matchStuckOnStructure s) then
        if let some s' ← reduceRecMatcher? s then
          -- (a `casesOn` that is only unfolded into its stuck recursor is not reduced)
          let stuckRec := match s'.getAppFn with
            | .const r _ => isRecCore env r
            | _ => false
          unless stuckRec do return some s'.headBeta
      if let some s' ← reduceSparseCasesOnCtor? s then return some s'
  -- a dispatch stuck on something else, handed the history: push the history inside
  if let some s' ← unfoldMatcherWithHistory? s then return some (← reduceBrecBody s')
  if let some s' ← pushHistoryIntoCasesOn? s then return some s'
  return none

/-- Reduce, **anywhere** in a branch of a compiled recursion, the dispatches its shape
    decides and the dispatches the history is pushed through (`reduceBranchStep?`). -/
def reduceBranchMatches (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun s => do
    match ← reduceBranchStep? s with
    | some s' => return .visit s'
    | none => return .done s)

/-- `reduceBrecBody`, continued **under the binders** the branch opens.  A recursion that
    takes more than one argument is compiled with the later arguments in the motive, so
    its branch is a function and the `match` that reads the history sits under a lambda;
    reducing there is what lets an accumulator-passing loop be seen as a fold. -/
partial def reduceBrecBodyDeep (e : Expr) : MetaM Expr := do
  let e ← reduceBrecBody e
  match e with
  | .lam .. =>
      lambdaBoundedTelescope e 1 fun xs b => do
        mkLambdaFVars xs (← reduceBrecBodyDeep b)
  | _ =>
      -- the functions of a `mutual` block that recurse on the same type are compiled
      -- into one `brecOn` whose branch pairs up their branches, `⟨f._f t h, g._f t h⟩`:
      -- each component is reduced like a branch of its own
      if e.isAppOfArity ``PProd.mk 4 then
        let args := e.getAppArgs
        return mkAppN e.getAppFn
          #[args[0]!, args[1]!, ← reduceBrecBodyDeep args[2]!, ← reduceBrecBodyDeep args[3]!]
      return e

/-- How deep a recursion on a natural number the translation looks for: `fib` descends
    two steps, the hexanacci numbers six, and a definition that descends more steps than
    this is refused rather than searched for indefinitely.  It is the option
    `leanscript.toTerm.maxNatRecDepth` (`64` by default). -/
def maxNatRecDepth : MetaM Nat :=
  return leanscript.toTerm.maxNatRecDepth.get (← getOptions)

/-- One component of a `PProd`, however it is written: `(0, x)` for the first component
    of `x` and `(1, x)` for the second, whether it is a projection or an application of
    `PProd.fst` / `PProd.snd`. -/
def pprodProj? (e : Expr) : Option (Nat × Expr) :=
  match e.consumeMData with
  | .proj ``PProd i x => some (i, x)
  | e' =>
      match e'.getAppFnArgs with
      | (``PProd.fst, #[_, _, x]) => some (0, x)
      | (``PProd.snd, #[_, _, x]) => some (1, x)
      | _ => none

/-- The history `i` steps back: `hist` itself is `0`, and `t.2` is one step further than
    `t`, since `below (n + 1)` is `motive n ×' below n`. -/
partial def histTail? (hist : FVarId) (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .fvar f => if f == hist then some 0 else none
  | e' =>
      match pprodProj? e' with
      | some (1, x) => (histTail? hist x).map (· + 1)
      | _ => none

/-- Which entry of the history does this expression read?  `hist.1` is the value at the
    immediate predecessor, `hist.2.1` the value one step further back, and so on. -/
def histEntry? (hist : FVarId) (e : Expr) : Option Nat :=
  match pprodProj? e with
  | some (0, x) => histTail? hist x
  | _ => none

/-- Read the values of the recursion at the nearest predecessors out of the history:
    entry `i` becomes `ihs[i]`.  Whatever still mentions the history afterwards is a read
    the fold that is being built cannot serve. -/
def substHistory (e : Expr) (hist : FVarId) (ihs : Array Expr) : Expr :=
  e.replace fun s =>
    match histEntry? hist s with
    | some i => ihs[i]?
    | none => none

/-- Read the value of the recursion at the immediate predecessor out of the history:
    `history.1` becomes the variable that stands for it.  Whatever is left of the history
    afterwards is a deeper call, which a one-step fold cannot express. -/
def substHistoryHead (e : Expr) (hist : FVarId) (ih : Expr) : Expr :=
  substHistory e hist #[ih]

end LeanScript.ToTerm

end

end
