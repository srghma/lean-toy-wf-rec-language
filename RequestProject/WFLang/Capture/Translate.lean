import RequestProject.WFLang.Capture.Optimize
import RequestProject.WFLang.Core.PExpr

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

/-- `set_option wfLang.joinPoints false` makes the capture copy the rest of the computation
into both branches of a non-tail `if`/`match` containing calls, instead of making it a join
point. -/
register_option wfLang.joinPoints : Bool := {
  defValue := true
  descr := "#lean_wf_func_to_term: capture the continuation of a non-tail if/match containing calls as a join point (otherwise it is copied into both branches)"
}

/-- Surface syntax of a term. -/
abbrev Stx := TSyntax `term

/-- The object type of a Lean type, as syntax. -/
def tyStx (t : Lean.Expr) : MetaM Stx := do PE.tyExprStx (← tyOf t)

/-- The object type of the elements of a Lean list type, as syntax. -/
def elemTyStx (listTy : Lean.Expr) : MetaM Stx := do
  let t ← whnfR listTy
  unless t.isAppOfArity ``List 1 do throwError "#lean_wf_func_to_term: not a list type {t}"
  tyStx (t.getArg! 0)

/-- Capture of a function `f` whose body calls a function `g` with a function argument that
calls `f` again (e.g. a `for` loop whose body calls `f`): `f` and the copy of `g` specialised to
that argument are captured as **one** local recursive function with parameters
`tag :: (f's parameters ++ g's lifted variables ++ g's parameters)`, where `tag = 0` selects
`f` and `tag = 1` selects `g` (the unused parameters are padded with default values).  Its
relation is `WFLang.hoRel`. -/
structure HOInfo where
  fName : Name
  fSig : FnSig
  gRef : FnRef
  gSig : FnSig

/-- How a call of another recursive user function (not a global function by its attribute) is
captured. -/
inductive CalleeKind where
  /-- as a call of a global function (`gCall`): the function is added to the global context of
  the program the first time it is called (`@[inlinable]` functions that are not
  tail-recursive, groups of mutually recursive functions, functions calling themselves inside a
  function argument) -/
  | global
  /-- inlined as a **recursive join point** at the call site (a tail-recursive `@[inlinable]`
  function): a loop inside the caller -/
  | loop
  deriving Inhabited, BEq

/-- What the translation needs to know about a global function it calls: its position in the
global context (see `gvarStx`), whether its first parameter is the tag `0` (a function captured
together with a specialised function, see `HOInfo`) and the number of padded parameters after
its own. -/
structure GInfo where
  pos : Nat
  tag0 : Bool := false
  pad : Nat := 0
  deriving Inhabited

/-- Inside the body of a recursive join point `L` capturing a tail-recursive function `ref`
(signature `sig`): a tail call of `ref` is a back edge `jump L`.  `dL` is the number of join
points in scope outside `L` and `vL` the number of variables in scope at the definition of
`L` (its parameter included). -/
structure LoopInfo where
  ref : FnRef
  sig : FnSig
  dL : Nat
  vL : Nat
  /-- the lifted variables of a specialised `ref` (projections of the parameter of `L`), passed
  again at each back edge -/
  extra : List Lean.Expr := []

structure Ctx where
  fn : Name
  /-- The local variables, innermost first (the de Bruijn order of the object context). -/
  vars : List FVarId
  /-- Decreasing lemmas to offer to the decrease tactic. -/
  lemmas : Array Stx := #[]
  /-- The tactic proving one decrease obligation (default `wf_dec`). -/
  decTac : Option (TSyntax `tactic) := none
  /-- Other recursive functions that may be called, each with its signature (at the call site:
  tag, padding) and how its calls are captured. -/
  callees : Array (Name × FnSig × CalleeKind) := #[]
  /-- The signature of `fn`, when its recursive calls are captured (inside its body). -/
  fnSig? : Option FnSig := none
  /-- Must each `ret` prove a postcondition (inside the body of a function with a subtype
  result)? -/
  hasPost : Bool := false
  /-- If `fn` is captured with the other members of its group of mutually recursive functions:
  the group (a call of `group[i]` is a recursive call with the tag `i` as first argument). -/
  group : Array Name := #[]
  /-- Recursive functions with function (or type) parameters that may be called: each call
  is a call of the copy specialised to its function arguments (a recursive join point if it is
  tail-recursive, a global function otherwise). -/
  specFns : Array Name := #[]
  /-- The global context under construction: the position of the global function capturing a
  function (registered on first use). -/
  gref : FnRef → TermElabM GInfo := fun f =>
    throwError "#lean_wf_func_to_term: unexpected call of {f.name}"
  /-- Save the state of the global context under construction; the action returned restores
  it (after a failed attempt, e.g. a function that turns out not to be a loop). -/
  gcheckpoint : TermElabM (TermElabM Unit) := pure (pure ())
  /-- The lifted variables of `fn`, if it is a specialised copy: its first (fixed) parameters,
  passed again at each recursive call. -/
  selfExtra : List Lean.Expr := []
  /-- The specialised values of `fn` (at its specialised positions), if it is a specialised
  copy: its recursive calls must pass the same ones. -/
  selfSpec : List Lean.Expr := []
  /-- Inside the global function capturing `f` together with a specialised `g` whose
  function argument calls `f` (see `HOInfo`). -/
  ho : Option HOInfo := none
  /-- Discovery mode: a call of a function with a function argument that calls `fn` is recorded
  here (and aborts the translation), instead of being rejected. -/
  hoFound : Option (IO.Ref (Option FnRef)) := none
  /-- The join points in scope, innermost first: for each, the number of variables in scope at
  its definition.  Empty in the body of each global function. -/
  joins : List Nat := []
  /-- The global functions (by attribute) visible here, each with its signature: a call of one
  of them is `Expr.gCall`. -/
  globals : Array (Name × FnSig) := #[]
  /-- Inside the body of a recursive join point capturing a tail-recursive function. -/
  loop? : Option LoopInfo := none
  /-- Inside the body of a recursive join point: the join point `K` (the rest of the
  computation after the loop) that each tail position jumps to, instead of returning: the
  number of join points in scope outside `K` and the number of variables in scope at its
  definition. -/
  exitK : Option (Nat × Nat) := none

/-- A `Ctx` over the parameters `xs` of the captured function (its object parameters: the
proof parameters are not variables of the object language). -/
def Ctx.ofParams (fn : Name) (xs : Array Lean.Expr) (sig? : Option FnSig := none)
    (ys : Array Lean.Expr := #[]) : Ctx :=
  let objs := match sig? with
    | some sig => sig.objPos.map (xs[·]!)
    | none => xs.toList
  { fn, vars := (ys.toList ++ objs).map (·.fvarId!), fnSig? := sig?, selfExtra := ys.toList,
    selfSpec := match sig? with
      | some sig => sig.specPos.map (xs[·]!)
      | none => [] }

/-- The object arguments of a call of a function with signature `sig`. -/
def objArgs (sig : FnSig) (args : Array Lean.Expr) : List Lean.Expr :=
  sig.objPos.map (args[·]!)

/-- Does `e` call the function being captured, or one of the recursive callees, or contain a
well-founded `while` loop (which becomes a statement, like a call)? -/
def hasCall (c : Ctx) (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOf c.fn || x.isAppOf ``WFLang.whileWF || c.callees.any (x.isAppOf ·.1) ||
    c.specFns.any (x.isAppOf ·) || c.group.any (x.isAppOf ·) || c.globals.any (x.isAppOf ·.1) ||
    c.ho.any (fun h => x.isAppOf h.fName || x.isAppOf h.gRef.name)).isSome

/-- If `e` is a call of a recursive function with function arguments: the reference to the copy
specialised to these arguments, and the lifted variables (the free variables of the function
arguments, passed as extra arguments). -/
def specCall? (c : Ctx) (e : Lean.Expr) : MetaM (Option (FnRef × Array Lean.Expr)) := do
  let .const g lvls := e.getAppFn | return none
  unless c.specFns.contains g do return none
  let args := e.getAppArgs
  unless args.size == (← constArity (mkConst g lvls)) do
    throwError "#lean_wf_func_to_term: partial application of {g} (function values are not supported){indentExpr e}"
  let sp ← specPosAt (mkConst g lvls) args
  for p in sp do
    if hasCall c args[p]! then
      if let some r := c.hoFound then
        let (ref, _) ← mkSpecRef g lvls args sp
        r.set (some ref)
        throwError "#lean_wf_func_to_term: (discovered a recursive call inside a function argument)"
      throwError "#lean_wf_func_to_term: a recursive call inside a function argument (e.g. a loop body) of {g} is not supported{indentExpr e}"
  let (ref, ys) ← mkSpecRef g lvls args sp
  for y in ys do
    unless c.vars.contains y.fvarId! do
      throwError "#lean_wf_func_to_term: the function argument of {g} uses {y}, which is not a variable of the program"
  return some (ref, ys)

/-- If `e` is a (full) call of one of the recursive callees: its signature and how it is
captured. -/
def calleeCall? (c : Ctx) (e : Lean.Expr) : Option (FnSig × CalleeKind) :=
  match e.getAppFn with
  | .const g _ => (c.callees.find? fun (g', sig, _) => g' == g && e.getAppNumArgs == sig.arity).map
      (·.2)
  | _ => none

/-- If `e` is a (full) call of one of the global functions (by attribute) visible here: its
name and signature. -/
def globalCall? (c : Ctx) (e : Lean.Expr) : Option (Name × FnSig) :=
  match e.getAppFn with
  | .const g _ => c.globals.find? fun (g', sig) => g' == g && e.getAppNumArgs == sig.arity
  | _ => none

/-- The placeholder for the index (`PCL.FnVar`) of the global function at position `j` of the
global context under construction.  The index itself depends on the number of global functions
before the one whose body contains the call (or on their total number, in the main statement),
which is only known when that body is complete: `resolveGRefs` replaces the placeholders then. -/
def gvarStx (j : Nat) : Stx := mkIdent (Name.mkNum `_wfLangGRef j)

/-- Replace the placeholders `gvarStx j` in `stx` by the indices of the global functions `j`, in
a global context of `n` functions (the function at position `j` is `there^(n-1-j) here`: the
context lists the functions innermost, i.e. last defined, first). -/
partial def resolveGRefs (n : Nat) (stx : Syntax) : TermElabM Syntax :=
  stx.replaceM fun s => do
    let .ident _ _ (.num p j) _ := s | return none
    unless p == `_wfLangGRef do return none
    unless j < n do throwError "#lean_wf_func_to_term: internal error: global function {j} is not visible here"
    let mut v : Stx := mkIdent `WFLang.PCL.FnVar.here
    for _ in [0:n - 1 - j] do
      v ← `($(mkIdent `WFLang.PCL.FnVar.there) $v)
    return some v.raw

/-- A placeholder for an erased proof of `p`.  It only occurs in proof positions, which the
translation ignores (the capture writes its own proofs); if it ever reached a translated
position, the translation would reject it as an unsupported expression. -/
def erasedProof (p : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``sorryAx [levelZero]) p (toExpr false)

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

/-- The Lean term inspected by a test. -/
def Test.expr : Test → Lean.Expr
  | .prop e | .bool e | .isZero e | .isNil e => e

/-- The same test on another term. -/
def Test.withExpr : Test → Lean.Expr → Test
  | .prop _, e => .prop e
  | .bool _, e => .bool e
  | .isZero _, e => .isZero e
  | .isNil _, e => .isNil e

/-- Erase the casts `h ▸ m` (`Eq.ndrec`, `Eq.rec`, `Eq.mpr`, `cast`) that the compilation of
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
    if (f.isConstOf ``Eq.ndrec || f.isConstOf ``Eq.rec) && args.size ≥ 6 then strip 3 6
    else if (f.isConstOf ``Eq.mpr || f.isConstOf ``cast) && args.size ≥ 4 then strip 3 4
    else none

/-- The body of the branch `fun h => b` of a `dite` on the proposition `p`, applied to
`extra` arguments, with casts erased.  The hypothesis `h` is
replaced by an erased proof: it may only be used in proofs (termination proofs, subtype
properties, preconditions of calls, casts), which the translation ignores. -/
def diteBranch (p a : Lean.Expr) (extra : Array Lean.Expr) : Lean.Expr :=
  eraseCasts (mkAppN (mkApp a (erasedProof p)) extra).headBeta

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
