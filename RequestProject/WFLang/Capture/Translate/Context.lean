import RequestProject.WFLang.Capture.Optimize
import RequestProject.WFLang.Core.PExpr

/-!
# Translating Lean terms into `PCL` surface syntax: the translation context

The option `wfLang.joinPoints`, the information the translation keeps about the captured
function and its callees (`HOInfo`, `CalleeKind`, `GInfo`, `LoopInfo`, `Ctx`), the recognition of
calls (`specCall?`, `calleeCall?`, `globalCall?`), the placeholders for global function indices
(`gvarStx`, `resolveGRefs`) and erased proofs (`erasedProof`).
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
that argument are captured as **one** global function with parameters
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
  /-- Inside the body of the global function capturing a group of mutually recursive functions
  (with different parameter or result types): its layout. -/
  groupLay? : Option GroupLayout := none
  /-- In the body of member `i` of such a group, when the members have different result types:
  each value in tail position is returned as component `i` of the tuple of results. -/
  retInj? : Option Nat := none

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

/-- Is `e` a fold over `l.attach` (`List.foldl f init l.attach`, or `WFLang.listFoldl f init
l.attach` from a `for x in l.attach` loop)?  It becomes a `foldl` statement, whose body knows
`x ∈ l` (like `List.map`). -/
def isAttachFoldl (e : Lean.Expr) : Bool :=
  (e.isAppOfArity ``List.foldl 5 || e.isAppOfArity ``WFLang.listFoldl 5) &&
    (e.getArg! 4).consumeMData.isAppOfArity ``List.attach 2

/-- Does `e` call the function being captured, or one of the recursive callees, or contain a
well-founded `while` loop or a `List.map` (which become statements, like a call)? -/
def hasCall (c : Ctx) (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOf c.fn || x.isAppOf ``WFLang.whileWF ||
    x.isAppOfArity ``List.map 4 || isAttachFoldl x || c.callees.any (x.isAppOf ·.1) ||
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
  mkApp2 (mkConst ``sorryAx [Level.zero]) p (toExpr false)

end WFLang.Translate
