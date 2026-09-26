import RequestProject.WFLang.Capture.Meta.Calls

/-!
# Capture metaprogramming: classifying callees and global functions

Specialised and higher-order callees (`isSpecFn`, `hoCandidate`), global functions
(`isGlobalFn`, `collectGlobals`), specialised references (`specRefsIn`), the right-hand side
of the unfolding equation (`withEqnRhs`) and the transitive callees (`calleeInfo`).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-- The combinators of this project that are captured by specialisation (bounded loops and list
combinators, `Core/Loops.lean`, `Core/ListLoops.lean`). -/
def specCombinators : List Name :=
  [``WFLang.rangeLoop, ``WFLang.listFoldl, ``WFLang.listFoldr, ``WFLang.listAny, ``WFLang.listAll,
   ``WFLang.listFind?, ``WFLang.listFilter, ``WFLang.rangeLoopN, ``WFLang.listLoopN,
   ``WFLang.listZipWith]

/-- Is `c` a recursive function (other than `fn`) with specialised parameters (function, type
or instance parameters), to be captured by specialisation at each call site? -/
def isSpecFn (fn c : Name) : MetaM Bool := do
  if c == fn || isInternalName c || (← isMatcher c) then return false
  -- the library, and the definitions of this project (except the loop combinator)
  if (← isLibraryConst c) then return false
  if (`WFLang).isPrefixOf c && !specCombinators.contains c then return false
  unless (← getConstInfo c).isDefinition do return false
  unless ← isWFRec c do return false
  forallTelescope (← inferType (← mkConstWithLevelParams c)) fun xs _ =>
    xs.anyM fun x => do
      let d ← x.fvarId!.getDecl
      isSpecBinder d.type d.binderInfo

/-- A quick syntactic test: does `rhs` apply a recursive function with function parameters to
a function argument that mentions `fn`? -/
def hoCandidate (fn : Name) (rhs : Lean.Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  Meta.forEachExpr rhs fun e => do
    let .const g _ := e.getAppFn | return
    if g == fn then return
    if e.getAppArgs.any (fun a => (a.find? (·.isConstOf fn)).isSome) then
      if ← isSpecFn fn g then found.set true
  found.get

/-- Does the recursive function `g` call itself inside a function argument (e.g. in the body
of a `for` loop)?  Such a function is captured together with the specialised loop (`HOInfo`),
always at its call site. -/
def callsSelfInFnArg (g : Name) : MetaM Bool := do
  let some eqn ← getUnfoldEqnFor? g (nonRec := true) | return false
  forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
    let some (_, _, rhs) := eq.eq? | return false
    hoCandidate g (← normLoops (← Core.betaReduce rhs))

/-- Is the call of `c` (from the capture of `fn`) a call of a **global function**?  That is the
case of every first-order user-defined function not marked `@[inlinable]`, except the members
of a group of mutually recursive functions and the functions calling themselves inside a
function argument, which are always captured at their call sites (as are the functions with
function parameters, which are specialised to the arguments of each call). -/
def isGlobalFn (fn c : Name) : MetaM Bool := do
  unless ← isUserFn fn c do return false
  if ← isInlinable c then return false
  if (← mutualGroup? c).isSome then return false
  if (← isWFRec c) && (← callsSelfInFnArg c) then return false
  return true

/-- The recursive user-defined functions called in `e` (other than `fn`) that are not global by
attribute: those marked `@[inlinable]` (loops at the call site if tail-recursive), and those
that are handled specially (see `isGlobalFn`). -/
def localRecCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) := do
  (← userCallees fn e).filterM fun c => return (← isWFRec c) && !(← isGlobalFn fn c)

/-- The user-defined functions called in `e` (other than `fn`) that are not inlined into a plain
expression: the loops and the global functions.  Their values appear in the agreement proofs as
`fixFn …` / `joinFn …` terms, identified by uniqueness (`rewriteCalleesWith`). -/
def recCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) := do
  (← userCallees fn e).filterM fun c => return (← isWFRec c) || !(← isInlinable c)

/-- Can the definition of `c` contain calls to take into account when collecting the global
functions (a user definition of this project, not an auxiliary one)? -/
def isTraversable (c : Name) : MetaM Bool := do
  if isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  if (`WFLang).isPrefixOf c then return false
  return (← getConstInfo c).isDefinition

/-- The global functions of the capture of `root`, callees first: every function `g` with
`isGlobalFn root g` reachable from `root` through the definitions that are captured (`root`,
its group, the inlined, local and specialised functions, and the global functions
themselves).  Each global function only calls global functions that come before it. -/
partial def collectGlobals (root : Name) (extra : Array Name := #[]) : MetaM (Array Name) := do
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array Name)
  let rec visit (f : Name) : MetaM Unit := do
    if (← visited.get).contains f then return
    visited.modify (·.insert f)
    let some eqn ← (try getUnfoldEqnFor? f (nonRec := true) catch _ => pure none) | return
    let consts ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
      let some (_, _, rhs) := eq.eq? | return #[]
      let (rhs, _) ← inlineCalls f (← normLoops (← Core.betaReduce rhs))
      return rhs.getUsedConstants
    for c in consts do
      if c == root || c == f then continue
      unless ← isTraversable c do continue
      visit c
      if (← isGlobalFn root c) && !(← out.get).contains c then out.modify (·.push c)
  let group := (← mutualGroup? root).getD #[root]
  visited.modify fun v => group.foldl (·.insert ·) v
  for g in group do
    visited.modify (·.erase g)
    visit g
  -- the constants of the function arguments of a specialised root
  for c in extra do
    if c == root || !(← isTraversable c) then continue
    visit c
    if (← isGlobalFn root c) && !(← out.get).contains c then out.modify (·.push c)
  out.get

/-- The reference to the specialised copy of `g` called with the arguments `args` (the
specialised positions `sp`), and the lifted variables (the free variables of the specialised
arguments, in context order). -/
def mkSpecRef (g : Name) (lvls : List Level) (args : Array Lean.Expr) (sp : List Nat) :
    MetaM (FnRef × Array Lean.Expr) := do
  let specArgs := sp.toArray.map (args[·]!)
  let set := specArgs.foldl (fun s a => collectFVars s a) {}
  let lctx ← getLCtx
  let ys := lctx.foldl (init := #[]) fun arr d =>
    if set.fvarSet.contains d.fvarId then arr.push (mkFVar d.fvarId) else arr
  let tys ← ys.mapM inferType
  let spec ← specArgs.mapM (mkLambdaFVars ys ·)
  return ({ name := g, levels := lvls, extraTys := tys, spec }, ys)

/-- The number of parameters of the constant `c`. -/
def constArity (c : Lean.Expr) : MetaM Nat := do
  forallTelescopeReducing (← inferType c) fun xs _ => pure xs.size

/-- The references to specialised copies of recursive functions called (fully applied, outside
binders) in `e`. -/
def specRefsIn (fn : Name) (e : Lean.Expr) : MetaM (Array FnRef) := do
  let out ← IO.mkRef (#[] : Array FnRef)
  Meta.forEachExpr e fun x => do
    if x.hasLooseBVars then return
    let .const g lvls := x.getAppFn | return
    unless ← isSpecFn fn g do return
    let args := x.getAppArgs
    unless args.size == (← constArity (mkConst g lvls)) do return
    let (ref, _) ← mkSpecRef g lvls args (← specPosAt (mkConst g lvls) args)
    unless (← out.get).any (·.beq ref) do out.modify (·.push ref)
  out.get

/-- Run `k ys xs rhs` on the lifted variables `ys`, the arguments `xs` and the right-hand side
of the unfolding equation `fn.eq_def : ∀ xs, fn xs = rhs` (at the specialised values, for a
specialised reference), in which bounded loops are rewritten (`normLoops`) and the calls of
non-recursive `@[inlinable]` functions are inlined (`inlineCalls`). -/
def withEqnRhs' {α : Type} (fn : FnRef)
    (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → TermElabM α) : TermElabM α := do
  let some eqn ← getUnfoldEqnFor? fn.name (nonRec := true) |
    throwError "#lean_wf_func_to_term: no unfolding equation for {fn.name}"
  -- a function-valued right-hand side (`f : α → (β → γ)`) is eta-expanded, so that the
  -- parameters are those of the type of `f`
  let finish (ys xs : Array Lean.Expr) (rhs : Lean.Expr) : TermElabM α := do
    forallTelescope (← inferType rhs) fun zs _ => do
      let rhs ← Core.betaReduce (mkAppN rhs zs)
      k ys (xs ++ zs) (← inlineCalls fn.name (← normLoops rhs)).1
  if !fn.isSpec then
    return ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun xs eq => do
      let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
      finish #[] xs rhs
  fn.telescope fun ys xs _ => do
    let eqC ← if fn.levels.isEmpty then mkConstWithLevelParams eqn
      else pure (Lean.mkConst eqn fn.levels)
    let eq ← instantiateForall (← inferType eqC) xs
    let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
    finish ys xs (← Core.betaReduce rhs)

/-- Run `k xs rhs` on the parameters and the right-hand side of the unfolding equation
`fn.eq_def : ∀ xs, fn xs = rhs` (see `withEqnRhs'`). -/
def withEqnRhs {α : Type} (fn : FnRef) (k : Array Lean.Expr → Lean.Expr → TermElabM α) :
    TermElabM α :=
  withEqnRhs' fn fun _ xs rhs => k xs rhs

/-- The unfolding equations inlined into the right-hand side of `fn.eq_def`, and the recursive
functions it calls (other than `fn`), transitively through the latter. -/
partial def calleeInfo (fn : Name) : MetaM (Array Name × Array Name) := do
  let rec go (todo : List Name) (eqns recs : Array Name) : MetaM (Array Name × Array Name) := do
    match todo with
    | [] => return (eqns, recs)
    | f :: rest =>
      let some eqn ← getUnfoldEqnFor? f (nonRec := true) | go rest eqns recs
      let (es, rs) ← forallTelescope (← inferType (← mkConstWithLevelParams eqn)) fun _ eq => do
        let some (_, _, rhs) := eq.eq? | return (#[], #[])
        let (rhs, es) ← inlineCalls f rhs
        return (es, ← recCallees f rhs)
      let eqns := es.foldl (fun acc e => if acc.contains e then acc else acc.push e) eqns
      let new := rs.filter fun r => r != fn && !recs.contains r
      go (rest ++ new.toList) eqns (recs ++ new)
  go [fn] #[] #[]

end WFLang.Meta
