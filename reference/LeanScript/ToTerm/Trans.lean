module

public meta import LeanScript.ToTerm.TransBrec
public meta import LeanScript.ToTerm.TransRecObject
public meta import LeanScript.ToTerm.TransRecUnion
public meta import LeanScript.ToTerm.TransRecFamily
public meta import LeanScript.ToTerm.TransRecCases
public meta import LeanScript.ToTerm.Extern
public meta import LeanScript.ToTerm.Cache
public meta import LeanScript.ToTerm.Existential
public meta import LeanScript.ToTerm.ForIn

@[expose] public section

meta section

/-!
# The translation

The translation proper: one `mutual` block, since every clause of it may meet any
expression.  The clauses for recursors, sparse `casesOn`s, inlined definitions and
structural recursion are in `LeanScript.ToTerm.TransRec` and `LeanScript.ToTerm.TransBrec`,
and are passed `trans` as an argument.  The elaborator that calls it is
`LeanScript.ToTerm.Elab`.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The translation -/

/-- `@default α inst`, unfolded to the value of the instance (a `Nat.zero` written as the
    literal the language has).  It stays `@default α inst` when the instance is not known
    (a variable). -/
def transDefaultValue (α inst : Expr) : MetaM Expr := do
  let d := mkApp2 (mkConst ``Inhabited.default [← getLevel α]) α inst
  let d' ← whnf d
  return d'.replace fun t => if t.isConstOf ``Nat.zero then some (mkRawNatLit 0) else none

/-- The functions `panic!` and the `!` accessors reach, each of which is, in Lean's logic,
    the `default` of the `Inhabited` instance it takes second (after the type), with the
    number of arguments each takes. -/
def panicNames : List (Name × Nat) :=
  [(``panicCore, 3), (``panic, 3), (``panicWithPos, 6), (``panicWithPosWithDecl, 7),
    (``outOfBounds, 2)]

/-- `l[i]` on a list, with its proof `i < l.length`, as `l.getD i d` for a default `d` of
    the elements (`synthDefault?`).  The two are equal whenever the proof holds, and the
    proof is what the language erases: Lean's own `List.get` is a recursion whose motive
    mentions it, which the language has no eliminator for.  `none` when the collection is
    not a list indexed by a `Nat`, or the elements have no default. -/
def listGetElemAsGetD? (args : Array Expr) : MetaM (Option Expr) := do
  unless args.size ≥ 8 do return none
  let coll ← whnfR args[0]!
  let .const ``List [u] := coll.getAppFn | return none
  unless (← whnfR args[1]!).isConstOf ``Nat do return none
  let some d ← synthDefault? args[2]! | return none
  return some (mkAppN (mkConst ``List.getD [u])
    (#[args[2]!, args[5]!, args[6]!, d] ++ args.extract 8 args.size))

mutual

/-- The term a Lean expression translates to, in the context `c`. -/
partial def trans (c : TCtx) (e0 : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e0).headBeta
  match e with
  | .mdata _ b => trans c b
  | .fvar f => c.var f
  | .lam .. => transLam c e
  | .letE .. => transLet c e
  | .proj .. => transProj c e
  | .sort .. | .forallE .. =>
      throwError "`#leanscript_to_term`: a type is not a value of the language: {e}"
  | _ =>
      if let some t ← transLit? c e then return t
      transApp c e

/-- `fun x => b`. -/
partial def transLam (c : TCtx) (e : Expr) : MetaM Expr := do
  let fty ← whnf (← inferType e)
  let .forallE _ d _ _ := fty
    | throwError "`#leanscript_to_term`: not a function: {e}"
  -- a binder the language erases (`Unit`) is dropped, as a `Unit` domain is
  if ← LeanScript.Deriving.erasedBinder d then
    return ← withErasedBinder e (trans c)
  let σ ← tyOfType d
  lambdaBoundedTelescope e 1 fun xs body => do
    let c' := c.push xs[0]!.fvarId! σ
    let b ← trans c' body
    let τ ← tyOfTermOr body b
    return mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

/-- `let x := v; b`, and `have h : p := proof; b` (the proof in place of `h`). -/
partial def transLet (c : TCtx) (e : Expr) : MetaM Expr := do
  let .letE n t v b _ := e
    | throwError "`#leanscript_to_term`: internal: not a `let`"
  -- `have h : p := proof`: the language erases proofs, so the proof is put in place of
  -- `h`, where it is erased as any proof is
  if ← isProp t then return ← trans c (b.instantiate1 v)
  let v' ← trans c v
  let σ ← tyOfTermOr v v'
  withLetDecl n t v fun x => do
    let c' := c.push x.fvarId! σ
    let body := b.instantiate1 x
    let b' ← trans c' body
    let τ ← tyOfTermOr body b'
    return mkAppN (mkConst `LeanScript.Term.letE') #[c.sg, c.gamma, σ, τ, v', b']

/-- A literal of a terminal type, carried into the term as it stands. -/
partial def transLit? (c : TCtx) (e : Expr) : MetaM (Option Expr) := do
  unless isLitLike e do return none
  let t ← whnf (← inferType e)
  let .const n _ := t.getAppFn | return none
  let some ctor := litCtorFor n | return none
  return some (mkAppN (mkConst ctor) #[c.sg, c.gamma, e])

/-- An application, or a bare head. -/
partial def transApp (c : TCtx) (e : Expr) : MetaM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  -- a redex the elaborator left behind (a `match` branch, say) is reduced, not applied
  if f.consumeMData.isLambda && !args.isEmpty then
    return ← trans c ((mkAppN f.consumeMData args).headBeta)
  match f with
  | .const n lvls => transConstApp c e n lvls args
  | .fvar id => applyArgs trans c (← c.var id) f args
  | .proj .. => applyArgs trans c (← transProj c f) f args
  | .lam .. | .letE .. => applyArgs trans c (← trans c f) f args
  | _ => throwError "`#leanscript_to_term`: cannot translate {e}"

/-- A structure projection: the case analysis that binds every field, followed by the
    field that was asked for. -/
partial def transProj (c : TCtx) (e : Expr) : MetaM Expr := do
  let .proj structName idx s := e
    | throwError "`#leanscript_to_term`: internal: not a projection"
  -- a projection out of a closed value — an instance, for one — is that value's field
  unless s.hasFVar do
    let e' ← whnf e
    unless e' == e do return ← trans c e'
  let sty? ← try some <$> tyOfTerm s catch _ => pure none
  let some sty := sty? | do
    -- a field of a value of a datatype with existentials that is written out
    -- (`(countFrom k).seed`) is that value's field
    let e' ← whnf e
    if e' == e then
      let _ ← tyOfTerm s
      throwError "`#leanscript_to_term`: cannot project out of {s}"
    return ← trans c e'
  let scrut ← trans c s
  let ind ← getConstInfoInduct structName
  let [ctorName] := ind.ctors
    | throwError "`#leanscript_to_term`: {structName} is not a structure"
  let ci ← getConstInfoCtor ctorName
  -- which of the fields that are kept is this one?
  let params := (← whnf (← inferType s)).getAppArgs
  let keptIdx? ← forallBoundedTelescope (← instantiateForall ci.type params)
      (some ci.numFields) fun xs _ => do
    let mut kept := 0
    let mut hit := none
    for h : i in [0:xs.size] do
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then continue
      if i == idx then hit := some kept
      kept := kept + 1
    return hit
  let some k := keptIdx?
    | throwError "`#leanscript_to_term`: the field {idx} of {structName} carries no \
        value of the language"
  match ← tyView sty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let τ ← tyOfTerm e
      let ids ← fieldTys.mapM fun t => do return ((← mkFreshFVarId), t)
      let c' := c.pushFields ids.toArray
      let some (fid, _) := ids[k]?
        | throwError "`#leanscript_to_term`: the field {idx} of {structName} is not a \
            field of its tree"
      let body ← c'.var fid
      return mkAppN (mkConst `LeanScript.Term.record_casesOn')
        #[c.sg, c.gamma, τ, fs, scrut, body]
  | _ =>
      -- a one-field structure is its field: the wrapper is erased
      if k == 0 then return scrut
      throwError "`#leanscript_to_term`: cannot project the field {idx} of \
        {structName}"

/-- `do` in the identity monad is not an effect: `Id.run`, `pure`, `>>=` and `<$>` are
    the plumbing a `do` block leaves behind, and each of them is a `let` or an
    application once the monad is `Id`.  A `for` is the one that is not: it is a fold,
    built by `transForInList?` over a list and by `transForInRange?` over a range.  In any other monad this answers
    `none`, and the call is refused as any other undeclared call is. -/
partial def transIdOp? (c : TCtx) (n : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let isId (m : Expr) : MetaM Bool := do return m.consumeMData.isConstOf ``Id
  match n with
  | ``Id.run =>
      let some x := args[1]? | return none
      return some (← trans c x)
  | ``Pure.pure =>
      unless args.size == 4 do return none
      unless ← isId args[0]! do return none
      return some (← trans c args[3]!)
  | ``Bind.bind =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[5]! args[4]!).headBeta)
  | ``Functor.map =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[4]! args[5]!).headBeta)
  | ``ForIn.forIn =>
      unless args.size ≥ 8 do return none
      unless ← isId args[0]! do return none
      if let some t ← transForInList? c args[1]! args[3]! args[args.size - 3]!
          args[args.size - 2]! args[args.size - 1]! false then
        return some t
      transForInRange? c args[1]! args[args.size - 3]! args[args.size - 2]! args[args.size - 1]!
  | ``ForIn'.forIn' =>
      unless args.size ≥ 9 do return none
      unless ← isId args[0]! do return none
      if let some t ← transForInList? c args[1]! args[4]! args[args.size - 3]!
          args[args.size - 2]! args[args.size - 1]! true then
        return some t
      transForIn'Range? c args[1]! args[args.size - 3]! args[args.size - 2]!
        args[args.size - 1]!
  | _ => return none

/-- `for x in l do …` (and `for h : x in l do …`), in the identity monad, over a list with
    the library's `ForIn'` instance: the loop is `List.foldl` of the body read as the next
    state (`LeanScript.ToTerm.listForInAsFoldl`), and that fold is translated as any
    other.  A body that can leave the loop (`break`, or `return` out of it) folds the
    step `ForInStep β` instead of the state.  Answers `none` for any other
    collection. -/
partial def transForInList? (c : TCtx) (ρ inst coll init body : Expr) (withProof : Bool) :
    MetaM (Option Expr) := do
  let ρ ← whnfR ρ
  unless ρ.isAppOfArity ``List 1 do return none
  unless (inst.find? (·.isConstOf ``List.instForIn'InferInstanceMembershipOfMonad)).isSome do
    return none
  let β ← inferType init
  let e ← listForInAsFoldl ρ.appArg! β coll init body withProof
  return some (← trans c e)

/-- `for i in [:n] do …`, in the identity monad: the loop is the fold of `n` whose value
    is the state, so it is `Term.nat_rec` — the branch binds the index (de Bruijn index
    `0`) and the state before the iteration (index `1`), and answers with the state
    after it.

    Any other range `[start:stop:step]` is first rewritten as the loop over `[:size]`,
    `size = (stop - start + step - 1) / step`, whose body reads the index
    `start + j * step` (`LeanScript.ToTerm.rangeForInReindex`).  A body that can leave the loop
    (`break`, or `return` out of it) makes the state of the fold a `ForInStep β`, the
    step after each iteration: once it is `done` the remaining iterations keep it
    (`LeanScript.ToTerm.rangeForInBreakAsNatRec`). -/
partial def transForInRange? (c : TCtx) (ρ coll init body : Expr) : MetaM (Option Expr) := do
  unless ρ.consumeMData.isConstOf ``Std.Legacy.Range do return none
  let (``Std.Legacy.Range.mk, #[startE, stopE, stepE, _]) := (← whnf coll).getAppFnArgs
    | throwError "`#leanscript_to_term`: the range of this `for` is not written out"
  -- a start or step that is a known number is written as that literal
  let start ← evalNat (← whnf startE)
  let step ← evalNat (← whnf stepE)
  let startE := match start with | some k => mkNatLit k | none => startE
  let stepE := match step with | some k => mkNatLit k | none => stepE
  -- any other range than `[:n]` is the loop over `[:size]` whose body reads the index
  -- `start + j * step`
  let (stopE, body) ← if start == some 0 && step == some 1 then pure (stopE, body)
    else rangeForInReindex startE stopE stepE start step body
  let β ← inferType init
  -- a body that can leave the loop: the recursion whose value is the step, as a Lean
  -- expression, translated as any other `Nat.rec`
  let breaking ← withLocalDeclD `i (mkConst ``Nat) fun i =>
    withLocalDeclD `state β fun s => do
      let (next, breaks) ← forInBody β (mkApp2 body i s)
      unless breaks do return none
      return some (← rangeForInBreakAsNatRec β stopE init i s next)
  if let some e := breaking then return some (← trans c e)
  let τ ← tyOfType β
  let natTy ← tyOfType (mkConst ``Nat)
  let scrut ← trans c stopE
  let z ← trans c init
  let branch ← withLocalDeclD `i (mkConst ``Nat) fun i =>
    withLocalDeclD `state β fun s => do
      let next ← forInYieldValue β (mkApp2 body i s)
      let c' := c.pushFields #[(i.fvarId!, natTy), (s.fvarId!, τ)]
      trans c' next
  return some <| mkAppN (mkConst `LeanScript.Term.nat_rec')
    #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], branch]

/-- `for h : i in r do …`, in the identity monad, over a range `r = [start:stop:step]`:
    the loop that names the membership proof `h : i ∈ r`.  When the body does not read
    `h`, it is the loop `for i in r` without it.  Otherwise it is the loop over
    `[:size]` whose body, at `j`, is guarded by `if hj : j < size`, and reads the index
    `start + j * step` with the proof `Std.Legacy.Range.mem_start_add_mul_step r hj`
    (`LeanScript.ToTerm.rangeForIn'AsForIn`); that loop is translated by
    `transForInRange?`.  The proof is erased, as any proof is. -/
partial def transForIn'Range? (c : TCtx) (ρ coll init body : Expr) : MetaM (Option Expr) := do
  unless ρ.consumeMData.isConstOf ``Std.Legacy.Range do return none
  let (``Std.Legacy.Range.mk, #[startE, stopE, stepE, _]) := (← whnf coll).getAppFnArgs
    | throwError "`#leanscript_to_term`: the range of this `for` is not written out"
  let start ← evalNat (← whnf startE)
  let step ← evalNat (← whnf stepE)
  let startE := match start with | some k => mkNatLit k | none => startE
  let stepE := match step with | some k => mkNatLit k | none => stepE
  let β ← inferType init
  match ← rangeForIn'AsForIn β coll startE stopE stepE start step body with
  | (none, body') => transForInRange? c ρ coll init body'
  | (some size, body') =>
      let coll' := mkApp4 (mkConst ``Std.Legacy.Range.mk) (mkNatLit 0) size (mkNatLit 1)
        (mkConst ``Nat.zero_lt_one)
      transForInRange? c ρ coll' init body'

/-- An application whose head is a constant. -/
partial def transConstApp (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  -- a function implemented by an extern of `Init` is that extern: it is never looked up
  -- in the signature, and one the catalogue does not model is refused
  unless (← isSpecialConst n args) do
    if let some t ← transExternApp? trans c e n lvls args then return t
  -- a function marked `@[extern]` that is translated as an ordinary function (`Nat.gcd`)
  -- is a declaration of the signature, whatever its definition is
  if externAsOrdinary.contains n then
    if let some g := c.global? n then
      let gt := mkAppN (mkConst `LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
      return ← applyArgs trans c gt (mkConst n lvls) args
    throwError "`#leanscript_to_term`: `{n}` is translated as an ordinary function, and is \
      not declared in the signature, so a term cannot call it.  Add a `GlobalDecl` named \
      \"{n.getString!}\" (or \"{n}\") to the signature."
  -- a structural recursion on a recursive record is the fold of the record
  if n.getString! == "brecOn" || (n.isStr && n.getString!.startsWith "brecOn_") then
    -- a structural recursion on a member of a mutual inductive block is the fold of
    -- the family, at the depth it needs
    if let some t ← transRecFamilyBrecOn? trans c e n lvls args then return t
    if let some t ← transRecObjectBrecOn? trans c e n lvls args then return t
    -- a structural recursion on a recursive tagged union other than a list is the fold
    -- of the union, at the depth it needs
    if n != ``List.brecOn then
      if let some t ← transRecUnionBrecOn? trans c e n lvls args then return t
  checkConst n
  if let some t ← transIdOp? c n args then return t
  -- `panic msg` (what `l[i]!`, `a.get!`, … reach on an index out of range) is, in Lean's
  -- logic, the `default` of the `Inhabited` instance it is handed: the message is an
  -- effect of the compiled code only
  if let some (_, arity) := panicNames.find? (·.1 == n) then
    if args.size ≥ arity then
      let d ← transDefaultValue args[0]! args[1]!
      return ← trans c (mkAppN d (args.extract arity args.size)).headBeta
  -- `xs[i]!` is the `getElem!` of the collection's instance, a function of the
  -- `Inhabited` instance of the elements: unfolded and applied to it here, so that the
  -- instance stays a Lean value rather than a binder of the language
  -- (`List.get!Internal`, `Array.get!Internal`, …)
  if n == ``GetElem?.getElem! then
    if let some e' ← unfoldProjInst? e then return ← trans c e'.headBeta
  -- `l.attach` and `l.attachWith P h` pair each element with a proof, which the language
  -- erases (a subtype has the tree of its values): they are `l` itself
  if (n == ``List.attach && args.size ≥ 2) || (n == ``List.attachWith && args.size ≥ 4) then
    let arity := if n == ``List.attach then 2 else 4
    return ← trans c (mkAppN args[1]! (args.extract arity args.size))
  if n == ``Inhabited.default && args.size == 2 then
    let d ← transDefaultValue args[0]! args[1]!
    unless d == e do return ← trans c d
  if n == ``ite then return ← transIte c args
  if n == ``dite then return ← transDite c args
  -- `decide p`: the `Bool` the decision procedure gives, as the test of an `if` is read
  if n == ``Decidable.decide && args.size == 2 then
    return ← boolOfDecidable c args[0]! args[1]!
  -- `xs[i]` (with its proof) is the extern its instance unfolds to, `Array.getInternal`
  if n == ``GetElem.getElem then
    if let some x ← decidableExtern? e then return ← trans c x
    if let some x ← listGetElemAsGetD? args then return ← trans c x
  if n == ``cond then
    let some scrut := args[1]? | throwError "`#leanscript_to_term`: `cond` needs its test"
    return ← mkBoolCases c (← trans c scrut) args[2]! args[3]!
  if n == ``Thunk.get then
    let some t := args[1]? | throwError "`#leanscript_to_term`: `Thunk.get` needs a thunk"
    let τ ← tyOfTerm e
    return mkAppN (mkConst `LeanScript.Term.thunk_force) #[c.sg, c.gamma, τ, ← trans c t]
  if n == ``List.toArray || n == ``Array.mk then
    -- an array literal, written as the list of its elements
    return ← transListLit c e
  if n == ``List.brecOn then
    -- the one-step translation first (which also serves a recursion on the elements of
    -- an array); a recursion that reads further down the list is the fold of the list
    -- as a recursive tagged union, at the depth it needs
    let onArray := match args[2]? with
      | some major => (arrayOfToList? major).isSome
      | none => false
    try
      return ← transBrecOn trans c e n lvls args
    catch ex =>
      let fallback? : Option Expr ←
        if onArray = true then pure none else transRecUnionBrecOn? trans c e n lvls args
      match fallback? with
      | some t => return t
      | none => throw ex
  if n == ``Nat.brecOn then
    return ← transBrecOn trans c e n lvls args
  if isSparseCasesOn n then
    if let some t ← transSparseCasesOn? trans c e n lvls args then return t
    -- a type whose tree has no partial dispatch: the exhaustive one
    if let some e' ← sparseAsCasesOn? n args then return ← trans c e'
    if let some e' ← unfoldHere? e then return ← trans c e'
  -- a dispatch on a value written out whose type has no tree (a datatype with
  -- existentials): the branch of its constructor
  if let some e' ← reduceDispatchOnNoTreeCtor? e n then return ← trans c e'
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ← transCtorApp c e ci args
  | some (.recInfo ri) => return ← transRecApp trans c e ri lvls args
  | _ => pure ()
  -- a one-level `match` on a value of a user-defined recursive type (a recursive union,
  -- record or newtype, or a member of a mutual block): its `…_casesOn`, not its recursor
  if let some t ← transRecKindCasesOn? trans c e n lvls args then return t
  if (← Meta.isMatcherApp e) || n.getString! == "casesOn" || n.getString! == "recOn" then
    if let some e' ← unfoldHere? e then
      return ← trans c e'
    throwError "`#leanscript_to_term`: cannot take apart the dispatch {n}"
  -- a structural recursion on lists applied to the elements of an array: unfolded, it
  -- is a `List.brecOn` on `a.toList`, which is the fold of the array `a`
  if args.any (fun a => (arrayOfToList? a).isSome) then
    if let some e' ← unfoldHere? e then
      let e' := e'.headBeta
      if e'.isAppOf ``List.brecOn then
        if let some major := e'.getAppArgs[2]? then
          if (arrayOfToList? major).isSome then
            return ← trans c e'
  if let some g := c.global? n then
    let gt := mkAppN (mkConst `LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
    return ← applyArgs trans c gt (mkConst n lvls) args
  -- the projection function of a structure, applied to a value: that projection, which
  -- is the record's case analysis rather than a function applied to the value
  if let some pinfo ← getProjectionFnInfo? n then
    if !pinfo.fromClass && args.size > pinfo.numParams then
      let ci ← getConstInfoCtor pinfo.ctorName
      let p := Expr.proj ci.induct pinfo.i args[pinfo.numParams]!
      return ← trans c (mkAppN p (args.extract (pinfo.numParams + 1) args.size))
  if ← isInlinable n then
    return ← transInline trans c e n lvls args
  -- a structural recursion defined on its own and called from here (or a wrapper of
  -- one): the fold it compiles to, inlined at the call site
  if ← callsStructuralRecursion n then
    return ← transInline trans c e n lvls args
  -- a call on a value of a datatype with existentials, or one that builds such a value:
  -- that value has no tree, so the function cannot be declared in the signature; it is
  -- inlined, and specialized to the value
  if (← getEnv).find? n matches some (.defnInfo _) then
    if (← args.anyM argHasNoTree) || (← argHasNoTree e) then
      return ← transInline trans c e n lvls args
  throwError "`#leanscript_to_term`: `{n}` is not declared in the signature and is not \
    inlinable, so a term cannot call it.  Either add a `GlobalDecl` named \
    \"{n.getString!}\" (or \"{n}\") to the signature, or mark `{n}` `@[inline]`.  (A \
    structural recursion is inlined without either.)"

/-- Is this call one the translation builds itself, although its head is implemented by
    an extern?  A constructor (`Thunk.mk`, `Array.mk`) is built in place, an array literal
    is built from all of its elements at once, and `Thunk.get` is `thunk_force`. -/
partial def isSpecialConst (n : Name) (args : Array Expr) : MetaM Bool := do
  if n == ``Array.mk then
    if let some l := args[1]? then return isListLit l
  if (← getEnv).find? n matches some (.ctorInfo _) then return true
  if n == ``Thunk.get then return true
  if n == ``List.toArray then
    if let some l := args[1]? then return isListLit l
  return false

/-- Is this list written out, element by element? -/
partial def isListLit (l : Expr) : Bool :=
  match l.consumeMData.getAppFnArgs with
  | (``List.nil, _) => true
  | (``List.cons, #[_, _, as]) => isListLit as
  | _ => false

/-- `if c then t else e`: the test must be a `Bool`. -/
partial def transIte (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `ite` needs its test"
  if let some n ← natZeroTest? cnd then
    return ← mkNatZeroCases c n args[3]! args[4]! none
  let inst := args[2]!
  let test ← boolOfDecidable c cnd inst
  mkBoolCases c test args[3]! args[4]!

/-- `if h : c then t else e`: the test is decided as for `if c then t else e`, and the
    proof `h` each branch binds is erased — a branch can still hand it to an extern that
    takes a proof, which decides the proposition again when the term runs
    (`Term.externCallChecked`). -/
partial def transDite (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `dite` needs its test"
  unless args.size == 5 do
    throwError "`#leanscript_to_term`: this `if h : c then … else …` is applied to \
      arguments, which the translation does not take apart"
  let test ← boolOfDecidable c cnd args[2]!
  let τ ← tyOfType args[0]!
  let branch (p : Expr) (b : Expr) : MetaM Expr :=
    withLocalDeclD `h p fun h => do
      let t ← trans c (mkApp b h).headBeta
      if t.containsFVar h.fvarId! then
        throwError "`#leanscript_to_term`: a branch of `if h : {cnd} then … else …` uses \
          the proof `h` as a value, and the language erases proofs"
      return t
  mkBoolCases' c test (← branch cnd args[3]!) (← branch (mkNot cnd) args[4]!) τ

/-- The natural number `n` of the test `n = 0` (or `0 = n`). -/
partial def natZeroTest? (cnd : Expr) : MetaM (Option Expr) := do
  let (``Eq, #[α, lhs, rhs]) := cnd.getAppFnArgs | return none
  unless (← whnf α).isConstOf ``Nat do return none
  if (← evalNat rhs) == some 0 then return some lhs
  if (← evalNat lhs) == some 0 then return some rhs
  return none

/-- `if n = 0 then t else e`: the case analysis on `n`, whose successor branch does not
    read the predecessor.  With `τ?`, both branches are translated against that type. -/
partial def mkNatZeroCases (c : TCtx) (n thenB elseB : Expr) (τ? : Option Expr) :
    MetaM Expr := do
  let natTy ← tyOfType (mkConst ``Nat)
  let scrut ← trans c n
  let c' := c.pushFields #[(← mkFreshFVarId, natTy)]
  let (τ, z, s) ← match τ? with
    | some τ => pure (τ, ← transCheck c thenB τ, ← transCheck c' elseB τ)
    | none => transBranchPair c thenB c' elseB
  return mkAppN (mkConst `LeanScript.Term.nat_casesOn') #[c.sg, c.gamma, τ, scrut, z, s]

/-- Two branches of one dispatch, each in its own context: their common type and their
    translations.  When the Lean type of the branches has no tree (a datatype with
    existentials), each branch is translated first; if the two types differ, they are joined
    (`joinTy`) and both branches are translated again against the join. -/
partial def transBranchPair (c1 : TCtx) (e1 : Expr) (c2 : TCtx) (e2 : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match ← (try some <$> tyOfTerm e1 catch _ => pure none) with
  | some τ => return (τ, ← trans c1 e1, ← trans c2 e2)
  | none =>
    let t1 ← trans c1 e1
    let t2 ← trans c2 e2
    let τ1 ← termTyOf t1
    let τ2 ← termTyOf t2
    if ← isDefEq τ1 τ2 then return (τ1, t1, t2)
    let j ← joinTy τ1 τ2
    return (j, ← transCheck c1 e1 j, ← transCheck c2 e2 j)

/-- The term an expression translates to, **against** the type `τ`.  A constructor of a
    datatype with existentials takes the trees of its holes from `τ`, a function and the
    branches of an `if` pass `τ` on, and a value whose type is one alternative of a
    `TyWf.oneOf` is injected into it; any other expression is translated as it stands, and
    must have the type `τ`. -/
partial def transCheck (c : TCtx) (e0 τ0 : Expr) : MetaM Expr := do
  let τ ← instantiateMVars τ0
  let e := (← instantiateMVars e0).headBeta.consumeMData
  if τ.hasExprMVar then
    let t ← trans c e
    let τt ← termTyOf t
    unless ← isDefEq τt τ do
      throwError "`#leanscript_to_term`: this value has the type{indentExpr τt}\nwhich is \
        not of the form{indentExpr τ}"
    return t
  match e with
  | .lam _ d _ _ =>
      if ← LeanScript.Deriving.erasedBinder d then
        return ← withErasedBinder e fun b => transCheck c b τ
      match τ.getAppFnArgs with
      | (``LeanScript.TyWf.fn, #[σ, ρ]) =>
          lambdaBoundedTelescope e 1 fun xs body => do
            let b ← transCheck (c.push xs[0]!.fvarId! σ) body ρ
            return mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, ρ, b]
      | _ => coerceTo c (← trans c e) τ
  | _ =>
    if let .const n _ := e.getAppFn then
      let args := e.getAppArgs
      if n == ``ite && args.size == 5 then
        if let some m ← natZeroTest? args[1]! then
          return ← mkNatZeroCases c m args[3]! args[4]! (some τ)
        let test ← boolOfDecidable c args[1]! args[2]!
        return ← mkBoolCases' c test (← transCheck c args[3]! τ) (← transCheck c args[4]! τ) τ
      if let some (.ctorInfo ci) := (← getEnv).find? n then
        if args.size ≥ ci.numParams + ci.numFields then
          if (← usesCtorFn e ci) && (← oneOfAlts? τ).isNone then
            return ← coerceTo c (← ctorFnApp trans transCheck c ci args (some τ)) τ
    coerceTo c (← trans c e) τ

/-- The `Bool` a decidable proposition tests. -/
partial def boolOfDecidable (c : TCtx) (cnd : Expr) (inst : Expr) : MetaM Expr := do
  match cnd.getAppFnArgs with
  | (``Eq, #[α, lhs, rhs]) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true then
        return ← trans c lhs
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.false then
        let t ← trans c lhs
        return ← mkBoolCases' c t (mkAppN (mkConst `LeanScript.Term.bool_mk)
            #[c.sg, c.gamma, mkConst ``Bool.false])
          (mkAppN (mkConst `LeanScript.Term.bool_mk) #[c.sg, c.gamma, mkConst ``Bool.true])
          (← tyOfType (mkConst ``Bool))
      -- a decision procedure that is an extern (`Nat.decEq`, say) is that extern
      if let some x ← decidableExtern? inst then return ← trans c x
      -- `a = b` at a type with a `BEq`: the test is `a == b`
      match ← trySynthInstance (← mkAppM ``BEq #[α]) with
      | .some _ => return ← trans c (← mkAppM ``BEq.beq #[lhs, rhs])
      | _ => pure ()
      throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`"
  | _ =>
      -- a decision procedure that is an extern (`Nat.decLt`, say) is that extern, whose
      -- value is the `Bool` it decides
      if let some x ← decidableExtern? inst then return ← trans c x
      let d ← whnf (mkApp2 (mkConst ``Decidable.decide) cnd inst)
      if d.isAppOfArity ``Decidable.decide 2 ||
          (d.find? (fun s => s.isConstOf ``Decidable.rec) |>.isSome) then
        throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`: write the \
          condition as a `Bool`, or declare the decision procedure in the signature"
      trans c d

/-- `bool_casesOn`, from the two Lean branches. -/
partial def mkBoolCases (c : TCtx) (test : Expr) (thenB elseB : Expr) : MetaM Expr := do
  let (τ, t, e) ← transBranchPair c thenB c elseB
  mkBoolCases' c test t e τ

/-- `bool_casesOn`, from the two translated branches. -/
partial def mkBoolCases' (c : TCtx) (test t e τ : Expr) : MetaM Expr := do
  return mkAppN (mkConst `LeanScript.Term.bool_casesOn') #[c.sg, c.gamma, τ, test, t, e]

/-- A list, or an array, written out: every element of it at once. -/
partial def transListLit (c : TCtx) (e : Expr) : MetaM Expr := do
  let ty ← tyOfTerm e
  let .array σ ← tyView ty
    | throwError "`#leanscript_to_term`: {e} is not an array"
  let mut elems : Array Expr := #[]
  let mut cur := e
  repeat
    match cur.getAppFnArgs with
    | (``List.nil, _) => break
    | (``List.cons, #[_, a, as]) => elems := elems.push a; cur := as
    | (``List.toArray, #[_, l]) => cur := l
    | (``Array.mk, #[_, l]) => cur := l
    | _ =>
        throwError "`#leanscript_to_term`: the grammar builds an array from all of its \
          elements at once, so only a list written out can be translated; {cur} is not \
          one"
  let mut ts := mkAppN (mkConst `LeanScript.Terms.nil) #[c.sg, c.gamma, σ]
  for i in [0:elems.size] do
    let a := elems[elems.size - 1 - i]!
    ts := mkAppN (mkConst `LeanScript.Terms.cons) #[c.sg, c.gamma, σ, ← trans c a, ts]
  return mkAppN (mkConst `LeanScript.Term.array_mk) #[c.sg, c.gamma, σ, ts]

/-- A spine of arguments at the given trees. -/
partial def mkSpine (c : TCtx) (tys : List Expr) (vals : Array Expr) : MetaM Expr := do
  unless tys.length == vals.size do
    throwError "`#leanscript_to_term`: this constructor carries {vals.size} values but \
      its tree has {tys.length} fields"
  let mut sp := mkAppN (mkConst `LeanScript.Spine.nil) #[c.sg, c.gamma]
  let tysA := tys.toArray
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    let t ← trans c vals[j]!
    sp := mkAppN (mkConst `LeanScript.Spine.cons)
      #[c.sg, c.gamma, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- An application of a constructor: it is built in place. -/
partial def transCtorApp (c : TCtx) (e : Expr) (ci : ConstructorVal)
    (args : Array Expr) : MetaM Expr := do
  if args.size < ci.numParams + ci.numFields then
    return ← trans c (← etaExpand e)
  if ci.induct == ``Array then
    return ← transListLit c e
  -- a value of a datatype with existentials: its constructor function
  if ← usesCtorFn e ci then
    return ← ctorFnApp trans transCheck c ci args none
  let ty ← tyOfTerm e
  let fields ← ctorValueArgs ci args
  -- a delay
  if let .thunk σ ← tyView ty then
    let some body := fields[0]?
      | throwError "`#leanscript_to_term`: a thunk needs its body"
    let inner := (mkApp body (mkConst ``Unit.unit)).headBeta
    return mkAppN (mkConst `LeanScript.Term.thunk_mk)
      #[c.sg, c.gamma, σ, ← trans c inner]
  -- a one-field wrapper is its field (a type with one constructor: a constructor of a
  -- union whose one field is the union itself, `succ n`, is not a wrapper)
  if h : fields.size = 1 then
    let indInfo ← getConstInfoInduct ci.induct
    let fty ← tyOfTerm fields[0]
    if indInfo.ctors.length == 1 && fty == ty then return ← trans c fields[0]
  match ← tyView ty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.record_mk) #[c.sg, c.gamma, fs, spine]
  | .taggedUnion l =>
      let ctys ← taggedUnionCtorTys l
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.taggedUnion_mk)
        #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
  | .recTaggedUnion l hwf =>
      -- the fields of a value are the payload **unfolded**: a field that is an
      -- occurrence of the union is a value of the union again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf
      let ctys ← taggedUnionCtorTys (← reduceTy unfE)
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_mk)
        #[c.sg, c.gamma, l, hwf, mkNatLit ci.cidx, prf, spine]
  | .recObject fs hwf =>
      -- the fields of a value are the record's fields **unfolded**: an occurrence of the
      -- record inside a field is a value of the record again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recObjectUnfold) fs hwf
      let fieldTys ← recordFieldTys (← reduceTy unfE)
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.recObject_mk) #[c.sg, c.gamma, fs, hwf, spine]
  | .recAlias b hwf =>
      let indInfo ← getConstInfoInduct ci.induct
      if indInfo.ctors.length > 1 then
        -- a declaration of several constructors with an occurrence of itself inside
        -- another type: its body is the union of its constructors, **unfolded**
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recAliasUnfold) b hwf)
        let .taggedUnion l ← tyView unfE
          | throwError "`#leanscript_to_term`: internal: the body of {ci.induct} is not a \
              tagged union"
        let ctys ← taggedUnionCtorTys l
        let some fieldTys := ctys[ci.cidx]?
          | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
              {ci.cidx}"
        let spine ← mkSpine c fieldTys fields
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
        let body := mkAppN (mkConst `LeanScript.Term.taggedUnion_mk)
          #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
        return mkAppN (mkConst `LeanScript.Term.recAlias_mk) #[c.sg, c.gamma, b, hwf, body]
      -- the one field of a value is the body **unfolded**: an occurrence of the newtype
      -- inside it is a value of the newtype again
      let some v := fields[0]?
        | throwError "`#leanscript_to_term`: a value of the recursive newtype \
            {ci.induct} needs its body"
      unless fields.size == 1 do
        throwError "`#leanscript_to_term`: the constructor of the recursive newtype \
          {ci.induct} has {fields.size} fields"
      return mkAppN (mkConst `LeanScript.Term.recAlias_mk)
        #[c.sg, c.gamma, b, hwf, ← trans c v]
  | .mutualRecursiveFamily nE f hwf =>
      -- a value of the member the family selects, with its fields **unfolded** in the
      -- scope of the whole family: an occurrence of a member is a value of that member
      let curE := mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.current)
        (tyWfInE ((← natOfExpr nE) + 2)) f
      let unfE ← reduceTy (mkAppN (mkConst ``LeanScript.LeanFamMemberSchema.map)
        #[tyWfInE ((← natOfExpr nE) + 2), tyE,
          mkApp3 (mkConst ``LeanScript.TyWfIn.unfoldFam) nE f hwf, curE])
      let value ← match unfE.getAppFnArgs with
        | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
            let ctys ← taggedUnionCtorTys l
            let some fieldTys := ctys[ci.cidx]?
              | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no \
                  constructor {ci.cidx}"
            let spine ← mkSpine c fieldTys fields
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.ctors)
              #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
        | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
            let spine ← mkSpine c (← recordFieldTys fs) fields
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.record)
              #[c.sg, c.gamma, fs, spine]
        | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
            let some v := fields[0]?
              | throwError "`#leanscript_to_term`: a value of {ci.induct} needs its body"
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.alias)
              #[c.sg, c.gamma, b, ← trans c v]
        | _ => throwError "`#leanscript_to_term`: internal: the member of the family \
            {ci.induct} has no shape: {unfE}"
      return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_mk)
        #[c.sg, c.gamma, nE, f, hwf, value]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      return mkAppN (mkConst `LeanScript.Term.enum_mk)
        #[c.sg, c.gamma, s, ← mkFinLit nE ci.cidx]
  | .prim _ =>
      if ← isBoolTy ty then
        return mkAppN (mkConst `LeanScript.Term.bool_mk)
          #[c.sg, c.gamma, toExpr (ci.cidx == 1)]
      throwError "`#leanscript_to_term`: {ci.name} builds a value of a terminal type, \
        which has no constructor in the language; write it as a literal"
  | _ =>
      throwError "`#leanscript_to_term`: the tree of {ci.induct} has no introduction \
        form in the grammar"

end

end LeanScript.ToTerm

end

end
