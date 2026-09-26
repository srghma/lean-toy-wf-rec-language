import RequestProject.WFLang.Capture.Translate.Context

/-!
# Translating Lean terms into `PCL` surface syntax

The capture elaborator produces *surface syntax* of `PCL`, which Lean then elaborates against
the expected type.  This file translates the call-free part of a Lean term into `PExpr` syntax
(`pexpr`, `pprop`), and recognises the control-flow forms of a Lean term (`branch?`: `if`,
`if h : …`, `match` on `Nat`/`Bool`/lists (also with literal patterns and `match h : e`),
`cond`, short-circuit `&&`/`||`), which `Capture/Elab.lean` turns into `PCL.Expr.ite` nodes.
`match` on pairs becomes projections, and the property of a subtype is dropped (it becomes
a postcondition).
-/

namespace WFLang.Translate

open Lean Meta Elab Term
open WFLang.Meta (tyOf natBin? intBin? isLibraryConst FnSig FnRef mkSpecRef specPosAt constArity)

/-- **Case of known constructor, case of `if`.**  A case split `T.casesOn x …` (with a
non-dependent motive) whose scrutinee `x` is a constructor application is reduced (`whnfCore`),
and one whose scrutinee is an `if c then a else b` (or `if h : c then …`) is pushed into the
branches: `if c then T.casesOn a … else T.casesOn b …`.  Used for the bodies of loops that may
stop early (`ForInStep.casesOn (if c then .done x else .yield y) …`, see `Core/ListLoops.lean`)
and for `match` on an `if` in general. -/
def pushCases? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const n _ := e.getAppFn | return none
  unless isCasesOnRecursor (← getEnv) n do return none
  let .inductInfo ind ← getConstInfo n.getPrefix | return none
  let args := e.getAppArgs
  let motivePos := ind.numParams
  let majorPos := ind.numParams + 1 + ind.numIndices
  unless args.size > majorPos + ind.ctors.length do return none
  -- the motive must not depend on the scrutinee (nor on the indices)
  let motive := args[motivePos]!
  let some body := (do
    let mut m := motive
    for _ in [0:ind.numIndices + 1] do
      let .lam _ _ b _ := m | none
      m := b
    let mb := m.headBeta
    if mb.hasLooseBVars then none else some mb) | return none
  let major := args[majorPos]!.consumeMData
  let withMajor (x : Lean.Expr) : Lean.Expr := mkAppN e.getAppFn (args.set! majorPos x)
  -- a β-redex scrutinee (the body of a loop applied to its arguments): reduce it
  if major.isHeadBetaTarget then return some (withMajor major.headBeta)
  -- a `let` (or `have`) scrutinee: substitute it
  if major.isLet then
    return some (withMajor (major.letBody!.instantiate1 major.letValue!))
  if let .const c _ := major.getAppFn then
    if ind.ctors.contains c then
      let r ← whnfCore e
      return if r == e then none else some r.headBeta
  if major.isAppOfArity ``ite 5 then
    let margs := major.getAppArgs
    let resTy ← if args.size == majorPos + 1 + ind.ctors.length then pure body else inferType e
    return some (mkAppN (mkConst ``ite [← getLevel resTy])
      #[resTy, margs[1]!, margs[2]!, withMajor margs[3]!, withMajor margs[4]!])
  if major.isAppOfArity ``dite 5 then
    let margs := major.getAppArgs
    let resTy ← inferType e
    let branch (f : Lean.Expr) : MetaM Lean.Expr := do
      let .lam nm ty b bi := f | throwError "unexpected branch of dite"
      withLocalDecl nm bi ty fun h => do
        mkLambdaFVars #[h] (withMajor (b.instantiate1 h))
    return some (mkAppN (mkConst ``dite [← getLevel resTy])
      #[resTy, margs[1]!, margs[2]!, ← branch margs[3]!, ← branch margs[4]!])
  return none

/-- Unfold one layer of `match`/`let`, if possible.  A `match` on a pair
(`Prod.casesOn p (fun a b => …)`) becomes the body applied to the projections of `p`. -/
def unfoldStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isLet then return some (e.letBody!.instantiate1 e.letValue!)
  if e.isAppOf ``Prod.casesOn && e.getAppNumArgs ≥ 5 then
    -- `@Prod.casesOn α β motive p f`
    let args := e.getAppArgs
    let p := args[3]!
    let extra := args.extract 5 args.size
    return some (mkAppN args[4]! (#[← mkAppM ``Prod.fst #[p], ← mkAppM ``Prod.snd #[p]] ++
      extra)).headBeta
  if let .const n lvls := e.getAppFn then
    if (← isMatcher n) then
      let v ← instantiateValueLevelParams (← getConstInfo n) lvls
      return some (v.beta e.getAppArgs).headBeta
  if let some e' ← pushCases? e then return some e'
  return none

/-- The test of a two-way branch. -/
inductive Test where
  /-- A decidable proposition (`if p then … else …`). -/
  | prop (p : Lean.Expr)
  /-- A boolean (`cond b …`, `b && …`, `b || …`). -/
  | bool (b : Lean.Expr)
  /-- `t = 0` (`Nat.casesOn t …`, i.e. `match t with | 0 => … | n + 1 => …`). -/
  | isZero (t : Lean.Expr)
  /-- `l = []` (`List.casesOn l …`, i.e. `match l with | [] => … | x :: xs => …`). -/
  | isNil (l : Lean.Expr)
  /-- `o.isSome` (`match o with | some x => … | none => …`) -/
  | isSome (o : Lean.Expr)
  /-- `x.isLeft` (`match x with | .inl a => … | .inr b => …`) -/
  | isLeft (x : Lean.Expr)
  /-- `x.isOk` (`match x with | .ok a => … | .error e => …`) -/
  | isOk (x : Lean.Expr)
  /-- `0 ≤ i` on `Int` (`match i with | .ofNat n => … | .negSucc n => …`) -/
  | nonneg (i : Lean.Expr)

/-- The Lean term inspected by a test. -/
def Test.expr : Test → Lean.Expr
  | .prop e | .bool e | .isZero e | .isNil e | .isSome e | .isLeft e | .isOk e | .nonneg e => e

/-- The same test on another term. -/
def Test.withExpr : Test → Lean.Expr → Test
  | .prop _, e => .prop e
  | .bool _, e => .bool e
  | .isZero _, e => .isZero e
  | .isNil _, e => .isNil e
  | .isSome _, e => .isSome e
  | .isLeft _, e => .isLeft e
  | .isOk _, e => .isOk e
  | .nonneg _, e => .nonneg e

/-- Erase the casts `h ▸ m` (`Eq.ndrec`, `Eq.rec`, `Eq.ndrec_symm`, `Eq.mpr`, `cast`) that the compilation of
`match` inserts: with literal patterns (`| 5 => …` becomes `if h : n = 3 then h ▸ … else …`)
and with `match h : e with` (the named equation is transported by `Eq.ndrec`).  The motive is
constant up to such hypotheses, so the cast only changes the type of an argument that the
branch ignores.  The result is only translated, never type-checked as a Lean term: a wrong
erasure makes the elaboration of the `PCL` program or the agreement proof fail, it cannot
produce a wrong program. -/
partial def eraseCasts (e : Lean.Expr) : Lean.Expr :=
  e.replace fun x =>
    let f := x.getAppFn
    let args := x.getAppArgs
    let strip (minor start : Nat) : Option Lean.Expr :=
      some (eraseCasts (mkAppN args[minor]! (args.extract start args.size)).headBeta)
    if (f.isConstOf ``Eq.ndrec || f.isConstOf ``Eq.rec || f.isConstOf ``Eq.ndrec_symm ||
        f.isConstOf ``HEq.homo_ndrec_symm) && args.size ≥ 6 then strip 3 6
    else if (f.isConstOf ``Eq.mpr || f.isConstOf ``cast) && args.size ≥ 4 then strip 3 4
    else none

/-- The body of the branch `fun h => b` of a `dite` on the proposition `p`, applied to
`extra` arguments, with casts erased.  The hypothesis `h` is
replaced by an erased proof: it may only be used in proofs (termination proofs, subtype
properties, preconditions of calls, casts), which the translation ignores. -/
def diteBranch (p a : Lean.Expr) (extra : Array Lean.Expr) : Lean.Expr :=
  eraseCasts (mkAppN (mkApp a (erasedProof p)) extra).headBeta

/-- `Ty.default` of the object type of the Lean type `α`. -/
def tyDefault (α : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp (mkConst ``WFLang.Ty.default) (← tyOf α)

/-- The value of an option known to be `some` (`o.getD default`). -/
def optVal (α o : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp3 (mkConst ``Option.getD [← getLevel α]) α o (← tyDefault α)

/-- The values of the two sides of a sum. -/
def sumLeft (α β x : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp4 (mkConst ``WFLang.sumGetLeftD) α β (← tyDefault α) x
def sumRight (α β x : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp4 (mkConst ``WFLang.sumGetRightD) α β (← tyDefault β) x

/-- The values of the two sides of an `Except`. -/
def excOk (ε α x : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp4 (mkConst ``WFLang.exceptGetOkD) ε α (← tyDefault α) x
def excError (ε α x : Lean.Expr) : MetaM Lean.Expr := do
  return mkApp4 (mkConst ``WFLang.exceptGetErrorD) ε α (← tyDefault ε) x

/-- The arguments of the two constructors of `Int` for a known `i`: `i.toNat` (for `ofNat`) and
`(-i - 1).toNat` (for `negSucc`). -/
def intOfNatArg (i : Lean.Expr) : MetaM Lean.Expr := mkAppM ``Int.toNat #[i]
def intNegSuccArg (i : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Int.toNat #[← mkAppM ``HSub.hSub #[← mkAppM ``Neg.neg #[i], toExpr (1 : Int)]]

/-- Is `n` an auxiliary "sparse" case split (`f._sparseCasesOn_1`), which the compilation of
overlapping patterns produces: it covers some constructors and has an `else` alternative
(taking a proof that the constructor is another one) for the others? -/
def isSparseCasesOn (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_sparseCasesOn"
  | _ => false

/-- A sparse case split on a `Nat`, a `Bool` or a list, covering one constructor, as a two-way
branch. -/
def sparseBranch? (e : Lean.Expr) : MetaM (Option (Test × Lean.Expr × Lean.Expr)) := do
  let .const n lvls := e.getAppFn | return none
  unless isSparseCasesOn n do return none
  let args := e.getAppArgs
  let ty ← instantiateTypeLevelParams (← getConstInfo n).toConstantVal lvls
  forallTelescope ty fun xs _ => do
    -- the scrutinee is the first explicit parameter; then one alternative and `else`
    let mut idx : Option Nat := none
    for j in [0:xs.size] do
      if idx.isNone && (← xs[j]!.fvarId!.getBinderInfo).isExplicit then idx := some j
    let some i := idx | return none
    unless xs.size == i + 3 && args.size ≥ i + 3 do return none
    let t := args[i]!
    let alt := args[i+1]!
    let els := args[i+2]!
    let extra := args.extract (i + 3) args.size
    let ctor ← forallTelescope (← inferType xs[i+1]!) fun _ r => do
      let r ← whnfR r
      return r.appArg!.getAppFn.constName?
    let elseB := (mkAppN (mkApp els (erasedProof (← inferType xs[i+2]!).bindingDomain!)) extra).headBeta
    match ctor with
    | some ``Nat.zero => return some (.isZero t, (mkAppN alt extra).headBeta, elseB)
    | some ``Nat.succ => do
      let tPred ← mkAppM ``HSub.hSub #[t, mkNatLit 1]
      return some (.isZero t, elseB, (mkAppN (mkApp alt tPred) extra).headBeta)
    | some ``Bool.true => return some (.bool t, (mkAppN alt extra).headBeta, elseB)
    | some ``Bool.false => return some (.bool t, elseB, (mkAppN alt extra).headBeta)
    | some ``List.nil => return some (.isNil t, (mkAppN alt extra).headBeta, elseB)
    | some ``List.cons => do
      let lTy ← whnfR (← inferType t)
      let α := lTy.getArg! 0
      let hd := mkApp3 (mkConst ``List.headD [← getLevel α]) α t
        (mkApp (mkConst ``WFLang.Ty.default) (← tyOf α))
      let tl ← mkAppM ``List.tail #[t]
      return some (.isNil t, elseB, (mkAppN alt (#[hd, tl] ++ extra)).headBeta)
    | some ``Option.none => return some (.isSome t, elseB, (mkAppN alt extra).headBeta)
    | some ``Option.some => do
      let α := (← whnfR (← inferType t)).getArg! 0
      return some (.isSome t, (mkAppN alt (#[← optVal α t] ++ extra)).headBeta, elseB)
    | some ``Sum.inl => do
      let ty ← whnfR (← inferType t)
      return some (.isLeft t,
        (mkAppN alt (#[← sumLeft (ty.getArg! 0) (ty.getArg! 1) t] ++ extra)).headBeta, elseB)
    | some ``Sum.inr => do
      let ty ← whnfR (← inferType t)
      return some (.isLeft t, elseB,
        (mkAppN alt (#[← sumRight (ty.getArg! 0) (ty.getArg! 1) t] ++ extra)).headBeta)
    | some ``Except.ok => do
      let ty ← whnfR (← inferType t)
      return some (.isOk t,
        (mkAppN alt (#[← excOk (ty.getArg! 0) (ty.getArg! 1) t] ++ extra)).headBeta, elseB)
    | some ``Except.error => do
      let ty ← whnfR (← inferType t)
      return some (.isOk t, elseB,
        (mkAppN alt (#[← excError (ty.getArg! 0) (ty.getArg! 1) t] ++ extra)).headBeta)
    | some ``Int.ofNat =>
      return some (.nonneg t, (mkAppN alt (#[← intOfNatArg t] ++ extra)).headBeta, elseB)
    | some ``Int.negSucc =>
      return some (.nonneg t, elseB, (mkAppN alt (#[← intNegSuccArg t] ++ extra)).headBeta)
    | _ => return none

/-- A two-way branch `(test, then-branch, else-branch)`.  With `shortCircuit`, `a && b` and
`a || b` are branches too.  The control forms may be applied to further arguments (as the
unfolded `match h : e with` is), which are passed to both branches. -/
def branch? (e : Lean.Expr) (shortCircuit := true) :
    MetaM (Option (Test × Lean.Expr × Lean.Expr)) := do
  let args := e.getAppArgs
  if let some b ← sparseBranch? e then return some b
  if e.isAppOf ``Nat.casesOn && args.size ≥ 4 then
    let t := args[1]!
    let extra := args.extract 4 args.size
    let tPred ← mkAppM ``HSub.hSub #[t, mkNatLit 1]
    return some (.isZero t, (mkAppN args[2]! extra).headBeta,
      (mkAppN (mkApp args[3]! tPred) extra).headBeta)
  if e.isAppOf ``List.casesOn && args.size ≥ 5 then
    -- `@List.casesOn α motive l x (fun y ys => z)`, i.e. `match l with | [] => x | y :: ys => z`:
    -- `z` sees the head and the tail of `l`
    let α := args[0]!
    let l := args[2]!
    let extra := args.extract 5 args.size
    let hd := mkApp3 (mkConst ``List.headD [← getLevel α]) α l
      (mkApp (mkConst ``WFLang.Ty.default) (← tyOf α))
    let tl ← mkAppM ``List.tail #[l]
    return some (.isNil l, (mkAppN args[3]! extra).headBeta,
      (mkAppN args[4]! (#[hd, tl] ++ extra)).headBeta)
  if e.isAppOf ``Option.casesOn && args.size ≥ 5 then
    -- `@Option.casesOn α motive o x (fun y => z)`
    let α := args[0]!
    let o := args[2]!
    let extra := args.extract 5 args.size
    return some (.isSome o, (mkAppN args[4]! (#[← optVal α o] ++ extra)).headBeta,
      (mkAppN args[3]! extra).headBeta)
  if e.isAppOf ``Sum.casesOn && args.size ≥ 6 then
    -- `@Sum.casesOn α β motive x (fun a => …) (fun b => …)`
    let (α, β, x) := (args[0]!, args[1]!, args[3]!)
    let extra := args.extract 6 args.size
    return some (.isLeft x, (mkAppN args[4]! (#[← sumLeft α β x] ++ extra)).headBeta,
      (mkAppN args[5]! (#[← sumRight α β x] ++ extra)).headBeta)
  if e.isAppOf ``Except.casesOn && args.size ≥ 6 then
    -- `@Except.casesOn ε α motive x (fun e => …) (fun a => …)`
    let (ε, α, x) := (args[0]!, args[1]!, args[3]!)
    let extra := args.extract 6 args.size
    return some (.isOk x, (mkAppN args[5]! (#[← excOk ε α x] ++ extra)).headBeta,
      (mkAppN args[4]! (#[← excError ε α x] ++ extra)).headBeta)
  if e.isAppOf ``Int.casesOn && args.size ≥ 4 then
    -- `@Int.casesOn motive i (fun n => …) (fun n => …)`
    let i := args[1]!
    let extra := args.extract 4 args.size
    return some (.nonneg i, (mkAppN args[2]! (#[← intOfNatArg i] ++ extra)).headBeta,
      (mkAppN args[3]! (#[← intNegSuccArg i] ++ extra)).headBeta)
  if e.isAppOf ``Bool.casesOn && args.size ≥ 4 then
    -- `match b with | false => x | true => y`: the minor premises are in the order `false, true`
    let extra := args.extract 4 args.size
    return some (.bool args[1]!, (mkAppN args[3]! extra).headBeta,
      (mkAppN args[2]! extra).headBeta)
  if e.isAppOf ``ite && args.size ≥ 5 then
    let extra := args.extract 5 args.size
    return some (.prop args[1]!, (mkAppN args[3]! extra).headBeta,
      (mkAppN args[4]! extra).headBeta)
  if e.isAppOf ``dite && args.size ≥ 5 then
    -- `let`/`have` are inlined (as by `unfoldStep?`), so that a hypothesis `h` used only by a
    -- `have` (e.g. a termination proof) disappears from the branches
    let extra := args.extract 5 args.size
    let p := args[1]!
    let np := mkApp (mkConst ``Not) p
    return some (.prop p, diteBranch p args[3]! extra, diteBranch np args[4]! extra)
  if e.isAppOf ``cond && args.size ≥ 4 then
    let extra := args.extract 4 args.size
    return some (.bool args[1]!, (mkAppN args[2]! extra).headBeta,
      (mkAppN args[3]! extra).headBeta)
  if shortCircuit && e.isAppOfArity ``and 2 then
    return some (.bool (e.getArg! 0), e.getArg! 1, mkConst ``Bool.false)
  if shortCircuit && e.isAppOfArity ``or 2 then
    return some (.bool (e.getArg! 0), mkConst ``Bool.true, e.getArg! 1)
  return none

/-- A binary operator of the grammar. -/
def bop (n : Name) : MetaM BOp := return { name := n, stx := mkIdent n }

/-- A binary operator of the grammar with type arguments (`beq t`, `pair s t`, `cons t`,
`append t`). -/
def bopT (n : Name) (tys : Array Stx) : MetaM BOp :=
  return { name := n, stx := ← `($(mkIdent n) $tys*) }

/-- A unary operator of the grammar, with its type arguments. -/
def uop (n : Name) (tys : Array Stx := #[]) : MetaM UOp :=
  return { name := n, stx := ← if tys.isEmpty then pure (mkIdent n : Stx) else `($(mkIdent n) $tys*) }

/-- A unary operator of the grammar with type arguments, given by the Lean types `tys`
(recorded, for constant folding). -/
def uopT (n : Name) (tys : Array Lean.Expr) : MetaM UOp := do
  let otys ← tys.mapM tyOf
  let stxs ← otys.mapM PE.tyExprStx
  return { name := n, stx := ← `($(mkIdent n) $stxs*), tys := otys }

mutual
/-- A call-free Lean expression as a (simplified) `PE`: every operator is built by the smart
constructors of `Capture/Optimize.lean`, so the result is in optimised normal form. -/
partial def pexprE (c : Ctx) (e : Lean.Expr) : MetaM PE := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isFVar then
    if let some i := c.vars.findIdx? (· == e.fvarId!) then
      return .var i
  -- `Int` literals
  if (e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``Neg.neg 3) &&
      (e.getArg! 0).isConstOf ``Int then
    if let some i := e.int? then return .lit (.int i)
  if let some n := e.nat? then return PE.natLit n
  if let some n := e.rawNatLit? then return PE.natLit n
  if e.isConstOf ``Nat.zero then return PE.natLit 0
  if e.isConstOf ``Bool.true then return PE.boolLit true
  if e.isConstOf ``Bool.false then return PE.boolLit false
  if e.isAppOfArity ``Nat.succ 1 then
    return PE.mkBin (← bop ``WFLang.BinOp.add) (← pexprE c (e.getArg! 0)) (PE.natLit 1)
  if let some e' ← unfoldStep? e then return ← pexprE c e'
  if let some (t, a, b) ← branch? e (shortCircuit := false) then
    return PE.mkIte (← testE c t) (← pexprE c a) (← pexprE c b)
  if let some (op, a, b) := natBin? e then
    return PE.mkBin (← bop op) (← pexprE c a) (← pexprE c b)
  if let some (op, a, b) := intBin? e then
    return PE.mkBin (← bop op) (← pexprE c a) (← pexprE c b)
  -- subtypes: a value is represented by its carrier value, the property is dropped
  if e.isAppOfArity ``Subtype.val 3 then return ← pexprE c (e.getArg! 2)
  if e.isAppOfArity ``Subtype.mk 4 then return ← pexprE c (e.getArg! 2)
  -- `()`
  if e.isConstOf ``Unit.unit then return .lit .unit
  if let .const ``PUnit.unit [u] := e then
    if u == Level.one then return .lit .unit
  -- options, sums, `Except`
  if e.isAppOfArity ``Option.none 1 then return .lit (.opt (← tyOf (e.getArg! 0)) none)
  if e.isAppOfArity ``Option.some 2 then
    return PE.mkUn (← uopT ``WFLang.UnOp.some #[e.getArg! 0]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Option.isSome 2 then
    return PE.mkUn (← uopT ``WFLang.UnOp.isSome #[e.getArg! 0]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Option.isNone 2 then
    return PE.mkNot (PE.mkUn (← uopT ``WFLang.UnOp.isSome #[e.getArg! 0]) (← pexprE c (e.getArg! 1)))
  if e.isAppOfArity ``Option.getD 3 then
    let o ← pexprE c (e.getArg! 1)
    if (e.getArg! 2).isAppOfArity ``WFLang.Ty.default 1 then
      return PE.mkUn (← uopT ``WFLang.UnOp.optGet #[e.getArg! 0]) o
    return PE.mkBin (← bopT ``WFLang.BinOp.optGetD #[← tyStx (e.getArg! 0)]) o
      (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Option.get! 3 then
    return PE.mkBin (← bopT ``WFLang.BinOp.optGetD #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 2)) (← pexprE c (← mkAppOptM ``Inhabited.default #[e.getArg! 0, e.getArg! 1]))
  -- the default value of an object type (padding in the results of a group of mutually
  -- recursive functions)
  if e.isAppOfArity ``WFLang.Ty.default 1 then
    if let some v := LitVal.default (e.getArg! 0) then return .lit v
  if e.isAppOfArity ``Inhabited.default 2 then
    let v ← whnfD e
    if v != e then return ← pexprE c v
  if e.isAppOfArity ``Sum.inl 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.inl #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Sum.inr 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.inr #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Sum.isLeft 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.isLeft #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Sum.isRight 3 then
    return PE.mkNot (PE.mkUn (← uopT ``WFLang.UnOp.isLeft #[e.getArg! 0, e.getArg! 1])
      (← pexprE c (e.getArg! 2)))
  for (n, op) in [(``WFLang.sumGetLeftD, ``WFLang.UnOp.getLeft),
      (``WFLang.sumGetRightD, ``WFLang.UnOp.getRight),
      (``WFLang.exceptGetOkD, ``WFLang.UnOp.getOk),
      (``WFLang.exceptGetErrorD, ``WFLang.UnOp.getError)] do
    if e.isAppOfArity n 4 && (e.getArg! 2).isAppOfArity ``WFLang.Ty.default 1 then
      return PE.mkUn (← uopT op #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 3))
  if e.isAppOfArity ``Except.ok 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.ok #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Except.error 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.error #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Except.toBool 3 || e.isAppOfArity ``Except.isOk 3 then
    return PE.mkUn (← uopT ``WFLang.UnOp.isOk #[e.getArg! 0, e.getArg! 1]) (← pexprE c (e.getArg! 2))
  -- strings and characters
  if let .lit (.strVal str) := e then return .lit (.str str)
  if e.isAppOfArity ``String.length 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.strLength) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``String.toList 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.strToList) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``String.ofList 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.strOfList) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``String.push 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.strPush) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``String.append 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.strAppend) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``HAppend.hAppend 6 && (← whnfR (e.getArg! 0)).isConstOf ``String then
    return PE.mkBin (← bop ``WFLang.BinOp.strAppend) (← pexprE c (e.getArg! 4)) (← pexprE c (e.getArg! 5))
  if e.isAppOfArity ``Char.ofNat 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.charOfNat) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``Char.toNat 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.charToNat) (← pexprE c (e.getArg! 0))
  -- arrays
  if e.isAppOfArity ``Array.size 2 then
    return PE.mkUn (← uopT ``WFLang.UnOp.arrSize #[e.getArg! 0]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Array.toList 2 then
    return PE.mkUn (← uopT ``WFLang.UnOp.arrToList #[e.getArg! 0]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``List.toArray 2 then
    return PE.mkUn (← uopT ``WFLang.UnOp.arrOfList #[e.getArg! 0]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Array.push 3 then
    return PE.mkBin (← bopT ``WFLang.BinOp.arrPush #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 1)) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Array.range 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.arrRange) (← pexprE c (e.getArg! 0))
  -- indexing: `xs[i]?`, `xs[i]!`, `xs[i]` on lists and arrays, `List.getD`, `List.head?`
  if e.isAppOfArity ``GetElem?.getElem? 7 || e.isAppOfArity ``GetElem?.getElem! 8 ||
      e.isAppOfArity ``GetElem.getElem 8 then
    let coll ← whnfR (e.getArg! 0)
    let n := e.getAppNumArgs
    let isBang := e.isAppOfArity ``GetElem?.getElem! 8
    let isGet := e.isAppOfArity ``GetElem.getElem 8
    let (xs, i) := if isGet then (e.getArg! 5, e.getArg! 6) else (e.getArg! (n - 2), e.getArg! (n - 1))
    let some (α, op) := (if coll.isAppOfArity ``List 1 then some (coll.getArg! 0, ``WFLang.BinOp.getElem?)
      else if coll.isAppOfArity ``Array 1 then some (coll.getArg! 0, ``WFLang.BinOp.arrGetElem?)
      else none) | throwError "#lean_wf_func_to_term: unsupported expression{indentExpr e}"
    let o := PE.mkBin (← bopT op #[← tyStx α]) (← pexprE c xs) (← pexprE c i)
    if isBang then
      return PE.mkBin (← bopT ``WFLang.BinOp.optGetD #[← tyStx α]) o
        (← pexprE c (← mkAppOptM ``Inhabited.default #[α, e.getArg! 5]))
    if isGet then return PE.mkUn (← uopT ``WFLang.UnOp.optGet #[α]) o
    return o
  if e.isAppOfArity ``List.getD 4 then
    let o := PE.mkBin (← bopT ``WFLang.BinOp.getElem? #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 1)) (← pexprE c (e.getArg! 2))
    return PE.mkBin (← bopT ``WFLang.BinOp.optGetD #[← tyStx (e.getArg! 0)]) o (← pexprE c (e.getArg! 3))
  if e.isAppOfArity ``List.head? 2 then
    -- `if l.isEmpty then none else some (l.headD default)`
    let α := e.getArg! 0
    let l ← pexprE c (e.getArg! 1)
    return PE.mkIte (PE.mkUn (← uop ``WFLang.UnOp.isNil #[← tyStx α]) l) (.lit (.opt (← tyOf α) none))
      (PE.mkUn (← uopT ``WFLang.UnOp.some #[α]) (PE.mkUn (← uop ``WFLang.UnOp.head #[← tyStx α]) l))
  if e.isAppOfArity ``List.take 3 then
    return PE.mkBin (← bopT ``WFLang.BinOp.take #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 1)) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``List.drop 3 then
    return PE.mkBin (← bopT ``WFLang.BinOp.drop #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 1)) (← pexprE c (e.getArg! 2))
  -- `Int` operators and conversions
  if e.isAppOfArity ``Neg.neg 3 && (e.getArg! 0).isConstOf ``Int then
    return PE.mkUn (← uop ``WFLang.UnOp.ineg) (← pexprE c (e.getArg! 2))
  if (e.isAppOfArity ``Nat.cast 3 && (e.getArg! 0).isConstOf ``Int) ||
      (e.isAppOfArity ``NatCast.natCast 3 && (e.getArg! 0).isConstOf ``Int) then
    return PE.mkUn (← uop ``WFLang.UnOp.ofNat) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Int.ofNat 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.ofNat) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``Int.toNat 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.toNat) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``Int.natAbs 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.natAbs) (← pexprE c (e.getArg! 0))
  -- pairs
  if e.isAppOfArity ``Prod.mk 4 then
    return PE.mkBin (← bopT ``WFLang.BinOp.pair #[← tyStx (e.getArg! 0), ← tyStx (e.getArg! 1)])
      (← pexprE c (e.getArg! 2)) (← pexprE c (e.getArg! 3))
  if e.isAppOfArity ``Prod.fst 3 then
    return PE.mkUn (← uop ``WFLang.UnOp.fst #[← tyStx (e.getArg! 0), ← tyStx (e.getArg! 1)])
      (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``Prod.snd 3 then
    return PE.mkUn (← uop ``WFLang.UnOp.snd #[← tyStx (e.getArg! 0), ← tyStx (e.getArg! 1)])
      (← pexprE c (e.getArg! 2))
  -- lists
  if e.isAppOfArity ``List.nil 1 then
    return .lit (.list (← tyOf (e.getArg! 0)) [])
  if e.isAppOfArity ``List.cons 3 then
    return PE.mkBin (← bopT ``WFLang.BinOp.cons #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 1)) (← pexprE c (e.getArg! 2))
  if e.isAppOfArity ``HAppend.hAppend 6 && (← whnfR (e.getArg! 0)).isAppOfArity ``List 1 then
    return PE.mkBin (← bopT ``WFLang.BinOp.append #[← elemTyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 4)) (← pexprE c (e.getArg! 5))
  if e.isAppOfArity ``List.length 2 then
    return PE.mkUn (← uop ``WFLang.UnOp.length #[← tyStx (e.getArg! 0)]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``List.range 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.range) (← pexprE c (e.getArg! 0))
  if e.isAppOfArity ``List.sum 4 && (← whnfR (e.getArg! 0)).isConstOf ``Nat then
    return PE.mkUn (← uop ``WFLang.UnOp.sum) (← pexprE c (e.getArg! 3))
  if e.isAppOfArity ``List.isEmpty 2 then
    return PE.mkUn (← uop ``WFLang.UnOp.isNil #[← tyStx (e.getArg! 0)]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``List.tail 2 then
    return PE.mkUn (← uop ``WFLang.UnOp.tail #[← tyStx (e.getArg! 0)]) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``List.headD 3 then
    let t ← tyStx (e.getArg! 0)
    let l ← pexprE c (e.getArg! 1)
    let hd := PE.mkUn (← uop ``WFLang.UnOp.head #[t]) l
    if (e.getArg! 2).isAppOfArity ``WFLang.Ty.default 1 then return hd
    return PE.mkIte (PE.mkUn (← uop ``WFLang.UnOp.isNil #[t]) l) (← pexprE c (e.getArg! 2)) hd
  if e.isAppOfArity ``BEq.beq 4 then
    return PE.mkBin (← bopT ``WFLang.BinOp.beq #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 2)) (← pexprE c (e.getArg! 3))
  if e.isAppOfArity ``Decidable.decide 2 then return ← ppropE c (e.getArg! 0)
  if e.isAppOfArity ``and 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.and) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``or 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.or) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``not 1 then return PE.mkNot (← pexprE c (e.getArg! 0))
  -- operators translated into the existing ones
  if e.isAppOfArity ``bne 4 then
    return PE.mkNot (PE.mkBin (← bopT ``WFLang.BinOp.beq #[← tyStx (e.getArg! 0)])
      (← pexprE c (e.getArg! 2)) (← pexprE c (e.getArg! 3)))
  if e.isAppOfArity ``Nat.pred 1 then
    return PE.mkBin (← bop ``WFLang.BinOp.sub) (← pexprE c (e.getArg! 0)) (PE.natLit 1)
  for (n, isMin) in [(``Min.min, true), (``Max.max, false)] do
    if e.isAppOfArity n 4 && (e.getArg! 0).isConstOf ``Nat then
      let a ← pexprE c (e.getArg! 2)
      let b ← pexprE c (e.getArg! 3)
      let le := PE.mkBin (← bop ``WFLang.BinOp.le) a b
      return if isMin then PE.mkIte le a b else PE.mkIte le b a
  -- library functions that are operators of the grammar
  if e.isAppOfArity ``xor 2 || e.isAppOfArity ``Bool.xor 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.bxor) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Nat.gcd 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.gcd) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Nat.lcm 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.lcm) (← pexprE c (e.getArg! 0)) (← pexprE c (e.getArg! 1))
  if e.isAppOfArity ``Nat.log2 1 then
    return PE.mkUn (← uop ``WFLang.UnOp.log2) (← pexprE c (e.getArg! 0))
  if let .const g _ := e.getAppFn then
    unless (← isLibraryConst g) || g == c.fn do
      throwError "#lean_wf_func_to_term: unsupported call of {g} (only first-order functions on the object types, fully applied, can be called){indentExpr e}"
  throwError "#lean_wf_func_to_term: unsupported expression{indentExpr e}"

/-- A decidable proposition as a (simplified) boolean expression. -/
partial def ppropE (c : Ctx) (p : Lean.Expr) : MetaM PE := do
  let p := (← instantiateMVars p).consumeMData
  let beq (t a b : Lean.Expr) : MetaM PE := do
    return PE.mkBin (← bopT ``WFLang.BinOp.beq #[← tyStx t]) (← pexprE c a) (← pexprE c b)
  if p.isAppOfArity ``Eq 3 then
    if (p.getArg! 2).isConstOf ``Bool.true then return ← pexprE c (p.getArg! 1)
    return ← beq (p.getArg! 0) (p.getArg! 1) (p.getArg! 2)
  if p.isAppOfArity ``Ne 3 then
    return PE.mkNot (← beq (p.getArg! 0) (p.getArg! 1) (p.getArg! 2))
  if p.isAppOfArity ``Not 1 then return PE.mkNot (← ppropE c (p.getArg! 0))
  if p.isAppOfArity ``And 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.and) (← ppropE c (p.getArg! 0)) (← ppropE c (p.getArg! 1))
  if p.isAppOfArity ``Or 2 then
    return PE.mkBin (← bop ``WFLang.BinOp.or) (← ppropE c (p.getArg! 0)) (← ppropE c (p.getArg! 1))
  if p.isAppOfArity ``Dvd.dvd 4 && (p.getArg! 0).isConstOf ``Nat then
    -- `a ∣ b` iff `b % a = 0` (also for `a = 0`, since `b % 0 = b`)
    return PE.mkBin (← bopT ``WFLang.BinOp.beq #[← `(WFLang.Ty.nat)])
      (PE.mkBin (← bop ``WFLang.BinOp.mod) (← pexprE c (p.getArg! 3)) (← pexprE c (p.getArg! 2)))
      (PE.natLit 0)
  for (n, lt, swap) in [(``LT.lt, true, false), (``LE.le, false, false),
      (``GT.gt, true, true), (``GE.ge, false, true)] do
    for (T, ltOp, leOp) in [(``Nat, ``WFLang.BinOp.lt, ``WFLang.BinOp.le),
        (``Int, ``WFLang.BinOp.ilt, ``WFLang.BinOp.ile)] do
      if p.isAppOfArity n 4 && (p.getArg! 0).isConstOf T then
        let (a, b) := if swap then (p.getArg! 3, p.getArg! 2) else (p.getArg! 2, p.getArg! 3)
        return PE.mkBin (← bop (if lt then ltOp else leOp)) (← pexprE c a) (← pexprE c b)
  throwError "#lean_wf_func_to_term: unsupported condition{indentExpr p}"

/-- A branch test as a (simplified) boolean expression. -/
partial def testE (c : Ctx) : Test → MetaM PE
  | .prop p => ppropE c p
  | .bool b => pexprE c b
  | .isZero t => do
    return PE.mkBin (← bopT ``WFLang.BinOp.beq #[← `(WFLang.Ty.nat)]) (← pexprE c t) (PE.natLit 0)
  | .isNil l => do
    return PE.mkUn (← uop ``WFLang.UnOp.isNil #[← elemTyStx (← inferType l)]) (← pexprE c l)
  | .isSome o => do
    let ty ← whnfR (← inferType o)
    return PE.mkUn (← uopT ``WFLang.UnOp.isSome #[ty.getArg! 0]) (← pexprE c o)
  | .isLeft x => do
    let ty ← whnfR (← inferType x)
    return PE.mkUn (← uopT ``WFLang.UnOp.isLeft #[ty.getArg! 0, ty.getArg! 1]) (← pexprE c x)
  | .isOk x => do
    let ty ← whnfR (← inferType x)
    return PE.mkUn (← uopT ``WFLang.UnOp.isOk #[ty.getArg! 0, ty.getArg! 1]) (← pexprE c x)
  | .nonneg i => do
    return PE.mkBin (← bop ``WFLang.BinOp.ile) (.lit (.int 0)) (← pexprE c i)
end

/-- A call-free Lean expression as `PExpr` syntax (in optimised normal form). -/
def pexpr (c : Ctx) (e : Lean.Expr) : MetaM Stx := do (← pexprE c e).render

/-- A branch test as `PExpr` syntax (in optimised normal form). -/
def test (c : Ctx) (t : Test) : MetaM Stx := do (← testE c t).render

/-- The statement `if t then a else b` in normal form: a test that simplifies to a literal
keeps only the branch it selects (the other one is not translated at all), and a negated test
`!c` becomes `if c then b else a`, so that the test of every `Expr.ite` is a condition
(`PExpr.isCond`). -/
def iteStx (c : Ctx) (t : Test) (a b : TermElabM Stx) : TermElabM Stx := do
  match ← testE c t with
  | .lit (.bool true) => a
  | .lit (.bool false) => b
  | .not c' => do
    let cs ← c'.render
    let as ← a
    let bs ← b
    `($(mkIdent `WFLang.PCL.Expr.ite) $cs (by decide) $bs $as)
  | cp => do
    let cs ← cp.render
    let as ← a
    let bs ← b
    `($(mkIdent `WFLang.PCL.Expr.ite) $cs (by decide) $as $bs)

/-- Argument tuple syntax (`PExprs`). -/
def pargs (c : Ctx) : List Lean.Expr → MetaM Stx
  | [] => `(WFLang.PExprs.nil)
  | a :: as => do `(WFLang.PExprs.cons $(← pexpr c a) $(← pargs c as))

/-- Argument tuple syntax, where `none` is a default value (padding). -/
def pargsOpt (c : Ctx) : List (Option Lean.Expr) → MetaM Stx
  | [] => `(WFLang.PExprs.nil)
  | some a :: as => do `(WFLang.PExprs.cons $(← pexpr c a) $(← pargsOpt c as))
  | none :: as => do
    `(WFLang.PExprs.cons (WFLang.PExpr.lit _ (WFLang.Ty.default _)) $(← pargsOpt c as))

/-- The proof of one decrease obligation: `c.decTac` (default `wf_dec`), with the decreasing
lemmas of the Lean definition as hypotheses.  The same tactic proves the preconditions of the
calls and the postconditions at the `ret`s (from the path condition). -/
def decStx (c : Ctx) : MetaM Stx := do
  let mut tac ← c.decTac.getDM `(tactic| wf_dec)
  for l in c.lemmas.reverse do
    tac ← `(tactic| (have := $l; $tac))
  `(by $tac:tactic)

/-- The proof of the precondition of a call (trivial if the callee has none). -/
def hpreStx (c : Ctx) (sig : FnSig) : MetaM Stx := do
  if sig.prfPos.isEmpty then `(fun _ _ => trivial) else decStx c

/-- The proof of the postcondition at a `ret` (trivial if there is none). -/
def postStx (c : Ctx) : MetaM Stx := do
  if c.hasPost then decStx c else `(fun _ _ => trivial)

/-- A Lean term `t` over the variables of the program, as a function of the environment:
`fun (e : Env Γ) => t[x_i := e.i]`, as syntax.  Used for the relation, the invariant and the
proofs of a `while` loop, which are Lean terms (not call-free expressions of the language). -/
def envFunStx (c : Ctx) (t : Lean.Expr) : TermElabM Stx := do
  let tys ← c.vars.mapM fun v => do tyOf (← v.getType)
  let gam := WFLang.Meta.mkTyList tys
  let f ← withLocalDeclD `e (mkApp (mkConst ``WFLang.Env) gam) fun env => do
    let projs ← (List.range c.vars.length).mapM (WFLang.Meta.envProj env ·)
    let t' := (← instantiateMVars t).replaceFVars (c.vars.map mkFVar).toArray projs.toArray
    mkLambdaFVars #[env] t'
  if f.hasFVar then
    throwError "#lean_wf_func_to_term: the termination argument of a `while` loop uses a local hypothesis (not supported){indentExpr t}"
  Term.exprToSyntax f

end WFLang.Translate
