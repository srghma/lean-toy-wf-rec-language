import RequestProject.WFLang.Capture.Stmt

/-!
# `#lean_wf_func_to_term f` — capture a well-founded Lean function as a `PCL.Term`

```
def gcd_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, PCL.Term.eval gcd_term m n = gcd m n := by wf_agree
```

For a function with a subtype result the agreement is `PCL.Term.eval f_term xs = (f xs).val`,
and for a function with proof parameters (a precondition) it is
`PCL.PTerm.run f_term (x₁, …, ()) h = f x₁ … h`.

The elaborator reads `f.eq_def` and writes the program as *surface syntax* of `PCL`, which Lean
then elaborates against the expected type (the translation of right-hand sides into statements
is in `Capture/Stmt.lean`):

* a recursive `f` is the last global function of the program, called once by the main
  statement (`PTerm.ofFix R wf body`); its relation and well-foundedness proof are the ones Lean
  built for `f` (from `WellFounded.fix`), pulled back along the packing of the arguments, and
  each `by wf_dec …` proves that one recursive call goes down, from the path condition, using the
  decreasing proofs Lean extracted for `f` (in particular the user's `decreasing_by`), `omega`,
  or `decreasing_tactic`;
* the **global context** is built on demand (`registerGlobal`): the first call of a function
  that is not inlined adds it to the global context (after the global functions its own body
  calls), and every call is `Expr.gCall i args`.  Global functions are the functions not marked
  `@[inlinable]`, and the `@[inlinable]` functions that cannot be loops: those with non-tail
  recursive calls, members of a group of mutually recursive functions (one global function with
  a tag parameter), functions calling themselves inside a function argument (one global
  function together with the specialised function), and the specialised copies of functions
  with function arguments that are not tail-recursive;
* a tail-recursive `@[inlinable]` function, and a tail-recursive function with function
  arguments (e.g. the loop of a `for`), is inlined at each call site as a **recursive join
  point** (a loop inside the caller, `loopStx`);
* calls with known arguments (closed calls of user functions, `@[inlinable]` or not) are
  evaluated at capture time and replaced by their values (`foldCall?`, `inlineCalls`);
  `wf_agree` proves these equations by kernel evaluation (`wfFoldCalls`).
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- An entry of the global context under construction: the function it captures (`key`), how
it is called (`info`), and its definition (signature `⟨params, ret, pre, post⟩`, relation,
well-foundedness proof, body). -/
structure GEntry where
  key : FnRef
  info : GInfo
  fnStx : Stx
  R : Stx
  wf : Stx
  body : Stx

/-- The global context under construction: its entries (in order: each entry may only call the
entries before it), the functions whose definition is being captured (to detect cycles), and the
global functions by attribute (not `@[inlinable]`) reachable from the captured function. -/
structure GReg where
  entries : IO.Ref (Array GEntry)
  busy : IO.Ref (Array FnRef)
  names : Array (Name × FnSig)

/-- Save the state of the global context; the action returned restores it. -/
def GReg.checkpoint (reg : GReg) : TermElabM (TermElabM Unit) := do
  let es ← reg.entries.get
  let bs ← reg.busy.get
  return do reg.entries.set es; reg.busy.set bs

/-- A fresh global context, for the capture of `root` (`collectGlobals`). -/
def GReg.new (root : FnRef) : TermElabM GReg := do
  let extra := root.spec.foldl (fun acc a => acc ++ a.getUsedConstants) #[]
  let names ← (← collectGlobals root.name extra).mapM fun (g : Name) => do
    return (g, ← fnSig { name := g })
  return { entries := ← IO.mkRef #[], busy := ← IO.mkRef #[], names }

/-- The pieces of a global function capturing a Lean function: its parameter types, result
type, relation, well-foundedness proof, precondition, postcondition and body. -/
structure FixParts where
  gam : Stx
  ret : Stx
  R : Stx
  wf : Stx
  pre : Stx
  post : Stx
  body : Stx
  /-- for the global function capturing a function together with a specialised function whose
  function argument calls it (`HOInfo`): the number of padded parameters after the function's
  own ones (it is called with tag `0`) -/
  hoPad : Option Nat := none

mutual
/-- The position of the global function capturing `key` in the global context `reg`: an
existing entry, or a new one, added after the global functions its body calls. -/
partial def registerGlobal (reg : GReg) (key : FnRef) : TermElabM GInfo := do
  for e in ← reg.entries.get do
    if ← specRefEq e.key key then return e.info
  for b in ← reg.busy.get do
    if ← specRefEq b key then
      throwError "#lean_wf_func_to_term: {key.name} calls itself through other global functions (mutual recursion outside a `mutual` block is not supported)"
  reg.busy.modify (·.push key)
  try
    let (info, fnStx, R, wf, body) ← globalPieces reg key
    let pos := (← reg.entries.get).size
    let body ← resolveGRefs pos body
    let info := { info with pos }
    reg.entries.modify (·.push { key, info, fnStx, R, wf, body := ⟨body⟩ })
    return info
  finally
    reg.busy.modify (·.pop)

/-- The definition of the global function capturing `key`: a recursive function (or group, or
specialised copy) is captured by `fixParts`; a non-recursive one has the empty relation
`emptyRelation` and its body is captured like a non-recursive program. -/
partial def globalPieces (reg : GReg) (key : FnRef) :
    TermElabM (GInfo × Stx × Stx × Stx × Stx) := do
  if !key.group.isEmpty || key.isSpec || (← isWFRec key.name) then
    let p ← fixParts key reg
    let info : GInfo := match p.hoPad with
      | some n => { pos := 0, tag0 := true, pad := n }
      | none => { pos := 0 }
    return (info, ← `(⟨$(p.gam), $(p.ret), $(p.pre), $(p.post)⟩), p.R, p.wf, p.body)
  let g := key.name
  let sig ← fnSig key
  withEqnRhs' key fun ys xs rhs => do
    let gC ← mkConstWithLevelParams g
    let (pre?, post?) ← prePostOf key xs (← inferType (mkAppN gC xs)) ys
    let c : Ctx := { (Ctx.ofParams g xs sig ys) with
      callees := ← calleeKinds g rhs, fnSig? := none, hasPost := post?.isSome,
      specFns := ← specFnsIn g rhs, gref := registerGlobal reg, gcheckpoint := reg.checkpoint, globals := reg.names }
    let body ← stmt c rhs
    let pre ← match pre? with
      | some p => exprToSyntax p
      | none => `(fun _ => True)
    let post ← match post? with
      | some p => exprToSyntax p
      | none => `(fun _ _ => True)
    return ({ pos := 0 },
      ← `(⟨$(← exprToSyntax (mkTyList sig.argTys)), $(← exprToSyntax sig.retTy), $pre, $post⟩),
      ← `(emptyRelation), ← `(emptyWf.wf), body)

/-- The pieces of the global function capturing the recursive Lean function `f`. -/
partial def fixParts (f : FnRef) (reg : GReg) : TermElabM FixParts := do
  if !f.group.isEmpty then return ← groupParts f.group reg
  let fn := f.name
  let sig ← fnSig f
  let some (R, wf, lemmasE) ← closedFixOf f |
    throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
  let lemmas ← lemmasE.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
  let res ← withEqnRhs' f fun ys xs rhs => do
    let (pre?, post?) ← prePostOf f xs (← inferType (mkAppN (← f.const) xs)) ys
    let c : Ctx := { (Ctx.ofParams fn xs sig ys) with
      lemmas := lemmas, decTac := decTac, callees := ← calleeKinds fn rhs,
      hasPost := post?.isSome, specFns := ← specFnsIn fn rhs, gref := registerGlobal reg, gcheckpoint := reg.checkpoint,
      globals := reg.names }
    -- a call of a function with a function argument that calls `fn`: `fn` and the specialised
    -- function are captured together
    if let some gRef ← hoRefIn? f c rhs then
      unless pre?.isNone && post?.isNone do
        throwError "#lean_wf_func_to_term: {fn} calls itself inside a function argument; this is not supported together with proof parameters or a subtype result"
      return Sum.inr (← hoParts fn sig xs rhs c gRef R wf)
    let body ← stmt c rhs
    let pre ← match pre? with
      | some p => exprToSyntax p
      | none => `(fun _ => True)
    let post ← match post? with
      | some p => exprToSyntax p
      | none => `(fun _ _ => True)
    return Sum.inl (pre, post, body)
  match res with
  | .inr p => return p
  | .inl (pre, post, body) =>
    return { gam := ← exprToSyntax (mkTyList sig.argTys), ret := ← exprToSyntax sig.retTy,
             R := ← exprToSyntax R, wf := ← exprToSyntax wf, pre, post, body }

/-- If the right-hand side `rhs` of `f` calls a recursive function `g` with a function argument
that calls `f` (e.g. a `for` loop whose body calls `f`): the reference to the copy of `g`
specialised to that argument.  Found by a trial translation of `rhs` in discovery mode. -/
partial def hoRefIn? (f : FnRef) (c : Ctx) (rhs : Lean.Expr) : TermElabM (Option FnRef) := do
  if f.isSpec || !f.group.isEmpty then return none
  unless ← hoCandidate f.name rhs do return none
  let r ← IO.mkRef none
  let saved ← saveState
  let restoreG ← c.gcheckpoint
  try discard <| stmt { c with hoFound := some r } rhs catch _ => pure ()
  restoreState saved
  restoreG
  r.get

/-- The pieces of the global function capturing `fn` (signature `sig`, parameters `xs`,
right-hand side `rhs`, relation `Rf`) together with the copy `gRef` of a function `g`
specialised to a function argument that calls `fn` (see `HOInfo`).  Its parameters are
`tag :: fn's parameters ++ g's lifted variables ++ g's parameters`, its body
`if tag = 0 then ⟦rhs⟧ else ⟦rhs of g⟧`, and its relation `WFLang.hoRel` (`hoRelOf`). -/
partial def hoParts (fn : Name) (sig : FnSig) (xs : Array Lean.Expr) (rhs : Lean.Expr) (c : Ctx)
    (gRef : FnRef) (Rf wff : Lean.Expr) : TermElabM FixParts := do
  let gSig ← fnSig gRef
  unless ← isDefEq gSig.retTy sig.retTy do
    throwError "#lean_wf_func_to_term: {fn} calls itself inside a function argument of {gRef.name}, whose result type differs from that of {fn} (not supported)"
  unless gSig.prfPos.isEmpty && !gSig.subtypeRet do
    throwError "#lean_wf_func_to_term: {gRef.name} has proof parameters or a subtype result (not supported)"
  let some (Rg, wfg, glemmas) ← closedFixOf gRef |
    throwError "#lean_wf_func_to_term: {gRef.name} is not defined by well-founded recursion"
  let (R, wf) ← hoRelOf fn sig gRef gSig Rf wff Rg wfg
  let glemmas ← glemmas.mapM exprToSyntax
  let h : HOInfo := { fName := fn, fSig := sig, gRef, gSig }
  let body ← withEqnRhs' gRef fun ysG xsG rhsG => do
    withLocalDeclD `tag (Lean.mkConst ``Nat) fun t => do
      let fObjs := sig.objPos.map (xs[·]!)
      let gObjs := gSig.objPos.map (xsG[·]!)
      let vars := (t :: fObjs ++ ysG.toList ++ gObjs).map (·.fvarId!)
      let gCallees ← calleeKinds gRef.name rhsG #[fn]
      let gSpecFns ← specFnsIn gRef.name rhsG
      let decTac ← `(tactic| wf_dec_ho [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
      let c' : Ctx := { c with
        vars, ho := some h, hoFound := none, selfExtra := [], selfSpec := [],
        callees := c.callees ++ gCallees.filter (fun g => !c.callees.any (·.1 == g.1)),
        specFns := c.specFns ++ gSpecFns.filter (!c.specFns.contains ·),
        lemmas := c.lemmas ++ glemmas, decTac := some decTac }
      let a ← stmt c' rhs
      let b ← stmt c' rhsG
      let tst ← test c' (.prop (← mkEq t (mkNatLit 0)))
      `(WFLang.PCL.Expr.ite $tst (by decide) $a $b)
  return { gam := ← exprToSyntax (mkTyList (Lean.mkConst ``WFLang.Ty.nat :: sig.argTys ++ gSig.argTys)),
           ret := ← exprToSyntax sig.retTy, R := ← exprToSyntax R, wf := ← exprToSyntax wf,
           pre := ← `(fun _ => True), post := ← `(fun _ _ => True), body,
           hoPad := some gSig.argTys.length }

/-- The pieces of the global function capturing a group of mutually recursive functions
`group` (with the same parameter and result types): its first parameter is a tag `t`, and its
body is `if t = 0 then ⟦rhs of group[0]⟧ else if t = 1 then … else ⟦rhs of group[k-1]⟧`, where a
call of `group[i]` is a recursive call with tag `i`. -/
partial def groupParts (group : Array Name) (reg : GReg) : TermElabM FixParts := do
  let ref : FnRef := { name := group[0]!, group }
  let sig ← fnSig ref
  let (R, wf, lemmas) ← groupFixOf group
  let lemmas ← lemmas.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec_tag [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
  let body ← withEqnRhs group[0]! fun xs _ => do
    withLocalDeclD `tag (Lean.mkConst ``Nat) fun t => do
      let rhss ← group.mapM fun g => do
        let some eqn ← getUnfoldEqnFor? g (nonRec := true) |
          throwError "#lean_wf_func_to_term: no unfolding equation for {g}"
        let eq ← instantiateForall (← inferType (← mkConstWithLevelParams eqn)) xs
        let some (_, _, rhs) := eq.eq? | throwError "unexpected equation shape"
        return (← inlineCalls g (← normLoops (← Core.betaReduce rhs))).1
      let mut callees := #[]
      let mut specFns := #[]
      for (g, rhs) in group.zip rhss do
        for (h, hs, hk) in ← calleeKinds g rhs group do
          unless callees.any (·.1 == h) do callees := callees.push (h, hs, hk)
        for h in ← specFnsIn g rhs do
          unless specFns.contains h do specFns := specFns.push h
      let objs := sig.objPos.map (xs[·]!)
      let vars := (t :: objs).map (·.fvarId!)
      let c0 : Ctx := { fn := group[0]!, vars := vars, fnSig? := some sig, globals := reg.names }
      let c : Ctx := { c0 with group := group, lemmas := lemmas, decTac := some decTac }
      let c : Ctx := { c with callees := callees, specFns := specFns, gref := registerGlobal reg, gcheckpoint := reg.checkpoint }
      let mut acc ← stmt c rhss.back!
      for i in (List.range (group.size - 1)).reverse do
        let tst ← test c (.prop (← mkEq t (mkNatLit i)))
        acc ← `(WFLang.PCL.Expr.ite $tst (by decide) $(← stmt c rhss[i]!) $acc)
      return acc
  return { gam := ← exprToSyntax (mkTyList sig.argTys), ret := ← exprToSyntax sig.retTy,
           R := ← exprToSyntax R, wf := ← exprToSyntax wf, pre := ← `(fun _ => True),
           post := ← `(fun _ _ => True), body }
end

/-- The syntax of the global context `reg` (`Globals.defn … (Globals.defn Globals.nil …)`). -/
def GReg.stx (reg : GReg) : TermElabM Stx := do
  let mut gs ← `(WFLang.PCL.Globals.nil)
  for e in ← reg.entries.get do
    gs ← `(WFLang.PCL.Globals.defn $gs $(e.fnStx) $(e.R) $(e.wf) $(e.body))
  return gs

/-- The number of entries of the global context `reg`. -/
def GReg.size (reg : GReg) : TermElabM Nat := return (← reg.entries.get).size

/-- The main statement `let v := g args in v`, a call of the global function `gi` capturing the
recursive function `fn` (with the tag `tag` and the padding of `gi`) on the parameters. -/
def callMainStx (fn : FnRef) (gi : GInfo) (tag : Option Nat) (reg : GReg) : TermElabM Stx := do
  let sig ← fnSig fn
  withEqnRhs fn fun xs _ => do
    let c := { Ctx.ofParams fn.name xs sig with globals := reg.names }
    let tags := (if gi.tag0 then [mkNatLit 0] else []) ++ (tag.map mkNatLit).toList
    let args ← pargsOpt c ((tags ++ objArgs sig xs).map some ++ List.replicate gi.pad none)
    let retTy ← inferType (mkAppN (← fn.const) xs)
    withLocalDeclD `r retTy fun v => do
      let c' := { c with vars := v.fvarId! :: c.vars }
      `(WFLang.PCL.Expr.gCall $(gvarStx gi.pos) $args (by decide) $(← hpreStx c sig)
          $(← retStx c' v))

/-- Build the surface syntax of the program capturing `fn`: `PTerm.ofFix gs R wf ⟦rhs⟧` for a
recursive function (the function is the last global function, called by the main statement),
`PTerm.mk gs (call of the global function)` for a member of a group or a function captured
together with a specialised function, and `PTerm.mk gs ⟦rhs⟧` for a non-recursive function. -/
def captureStx (fn : FnRef) : TermElabM Stx := do
  let reg ← GReg.new fn
  let prog (main : Stx) : TermElabM Stx := do
    let main ← resolveGRefs (← reg.size) main
    `(WFLang.PCL.PTerm.mk $(← reg.stx) $(⟨main⟩))
  let isRec ← withEqnRhs fn fun _ rhs => return hasCall { fn := fn.name, vars := [] } rhs
  if let some grp ← mutualGroup? fn.name then
    -- a member of a group of mutually recursive functions: one call of the global function
    -- capturing the group, with the tag of `fn`
    let gi ← registerGlobal reg { name := grp[0]!, group := grp }
    return ← prog (← callMainStx fn gi (grp.findIdx? (· == fn.name)) reg)
  if isRec && (← isWFRec fn.name) then
    let p ← fixParts fn reg
    if let some n := p.hoPad then
      -- `fn` captured together with a specialised function: one global function, called with
      -- tag `0`
      let pos ← reg.size
      let body ← resolveGRefs pos p.body
      let info : GInfo := { pos, tag0 := true, pad := n }
      let fnStx ← `(⟨$(p.gam), $(p.ret), $(p.pre), $(p.post)⟩)
      let entry : GEntry := { key := fn, info := info, fnStx := fnStx, R := p.R, wf := p.wf,
                              body := ⟨body⟩ }
      reg.entries.modify (·.push entry)
      return ← prog (← callMainStx fn info none reg)
    let body ← resolveGRefs (← reg.size) p.body
    return ← `(@WFLang.PCL.PTerm.ofFix _ ⟨$(p.gam), $(p.ret)⟩ $(p.pre) $(p.post) $(← reg.stx)
      $(p.R) $(p.wf) $(⟨body⟩))
  -- not recursive: the program is just the body
  let sig ← fnSig fn
  withEqnRhs' fn fun ys xs rhs => do
    let c : Ctx := { (Ctx.ofParams fn.name xs sig ys) with
      callees := ← calleeKinds fn.name rhs, fnSig? := none, specFns := ← specFnsIn fn.name rhs,
      gref := registerGlobal reg, gcheckpoint := reg.checkpoint, globals := reg.names }
    prog (← stmt c rhs)

/-- The global functions by attribute visible in the capture of `root` (`collectGlobals`). -/
def globalsOf (root : FnRef) : MetaM (Array Name) := do
  let extra := root.spec.foldl (fun acc a => acc ++ a.getUsedConstants) #[]
  collectGlobals root.name extra

/-- The function to capture, from the argument of `#lean_wf_func_to_term`: a constant `f`, or
`(f a₁ … aₖ)` where the `aᵢ` are closed values of the function (or type) parameters of `f`:
then the copy of `f` specialised to them is captured. -/
def captureTarget (stx : Syntax) : TermElabM FnRef := do
  if stx.isIdent then return { name := ← realizeGlobalConstNoOverloadWithInfo stx }
  let e ← instantiateMVars (← elabTerm stx none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let .const g lvls := e.getAppFn |
    throwError "#lean_wf_func_to_term: expected a function, or a function applied to function arguments"
  let args := e.getAppArgs
  let arity ← constArity (mkConst g lvls)
  let sp ← specPosAt (mkConst g lvls) (args ++ (Array.replicate (arity - args.size) (Lean.mkConst ``Unit.unit)))
  unless (List.range args.size).all sp.contains && sp.all (· < args.size) do
    throwError "#lean_wf_func_to_term: the arguments given to {g} must be exactly its function (and type) arguments{indentExpr e}"
  if e.hasFVar || e.hasMVar then
    throwError "#lean_wf_func_to_term: the function arguments of {g} must be closed{indentExpr e}"
  return { name := g, levels := lvls, spec := args }

/-- `#lean_wf_func_to_term f`: capture the well-founded Lean function `f` (with parameters and
result of object types, possibly proof parameters and a subtype result) as a `PCL` program.
`#lean_wf_func_to_term (f a₁ … aₖ)` captures the copy of `f` specialised to the closed
function arguments `aᵢ`. -/
syntax (name := wfToTerm) "#lean_wf_func_to_term " term:max : term

@[term_elab wfToTerm] def elabWfToTerm : TermElab := fun stx expectedType? => do
  let fn ← captureTarget stx[1]
  elabTerm (← captureStx fn) expectedType?

/-- `wf_agree` proves the agreement theorem of a program produced by
`#lean_wf_func_to_term f`: `∀ xs, PCL.Term.eval f_term xs = f xs` (or `= (f xs).val` for a
subtype result, or `∀ xs hs, PCL.PTerm.run f_term ⟨xs⟩ ⟨hs⟩ = f xs hs` with a precondition).
By uniqueness of the solution of the recursive equation of each global function
(`fixFn_unique`, `PTerm.ofFix_run`) and of each recursive join point (`joinFn_unique`), it
suffices that the Lean functions satisfy these equations, which follows from their `eq_def`. -/
syntax (name := wfAgree) "wf_agree" : tactic

/-- The simplification step of the PCL agreement proofs. -/
def pclSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default, WFLang.PCL.Self.top,
        WFLang.PCL.Self.push, WFLang.PCL.Handler.push, WFLang.PCL.toEnv_cons, WFLang.PCL.toEnv_one,
        WFLang.uncurryEnv,
        Nat.pred_eq_sub_one, bne, Nat.min_def, Nat.max_def, Nat.dvd_iff_mod_eq_zero,
        WFLang.foldl_range'_eq_rangeLoop, WFLang.rangeLoop_add_sub, WFLang.fold_eq_rangeLoop,
        WFLang.ite_pure_yield, WFLang.PCL.eval_whileLoop,
        WFLang.whileWF_eq_loopVal, WFLang.whileMeasure_eq_loopVal, WFLang.Meta.wfFoldCalls])

/-- If `f` calls itself inside a function argument of another recursive function `g`: the
reference to the copy of `g` specialised to that argument (see `hoRefIn?`). -/
def hoRefOf? (f : FnRef) : TermElabM (Option FnRef) := do
  if f.isSpec || !f.group.isEmpty || !(← isWFRec f.name) then return none
  let sig ← fnSig f
  withEqnRhs' f fun ys xs rhs => do
    unless ← hoCandidate f.name rhs do return none
    let reg ← GReg.new f
    let c : Ctx := { (Ctx.ofParams f.name xs sig ys) with
      callees := ← calleeKinds f.name rhs, specFns := ← specFnsIn f.name rhs,
      gref := registerGlobal reg, gcheckpoint := reg.checkpoint, globals := reg.names }
    hoRefIn? f c rhs

mutual
/-- Replace every value `(fixFn wf body x hx).1` of a nested `fix` node capturing a recursive
callee in the main goal by the callee's value (`rewriteCalleesWith`, uniqueness lemma
`fixFn_unique`). -/
partial def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit := do
  rewriteHOCallees callees
  rewriteCalleesWith calleeStep callees
    (Tactic.evalTactic (← `(tactic| all_goals try $(← pclSimp):tactic)))

/-- The rest of the proof that the callee `g` satisfies the equation of the body of its `fix`
node, after unfolding `g` once. -/
partial def calleeStep (g : FnRef) : Tactic.TacticM Unit := do
  unfoldInlined g
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  rewriteCallees (← calleeInfo g.name).2
  Tactic.evalTactic (← `(tactic| wf_close))

/-- `rewriteCallees` for the callees that call themselves inside a function argument: their
`fix` nodes (with parameters `tag :: …`, see `HOInfo`) compute `fnSolutionHO`. -/
partial def rewriteHOCallees (callees : Array Name) : Tactic.TacticM Unit := do
  for g in callees do
    let some gRef ← hoRefOf? { name := g } | continue
    let sig ← fnSig g
    let gSig ← fnSig gRef
    let tys := mkTyList (Lean.mkConst ``WFLang.Ty.nat :: sig.argTys ++ gSig.argTys)
    repeat
      if (← Tactic.getGoals).isEmpty then return
      let fx? ← Tactic.withMainContext do
        let tgt ← instantiateMVars (← Tactic.getMainTarget)
        let found ← IO.mkRef (#[] : Array Lean.Expr)
        Meta.forEachExpr tgt fun x => do
          if x.isAppOfArity `WFLang.PCL.fixFn 11 && !x.hasLooseBVars then found.modify (·.push x)
        (← found.get).findM? fun x => isDefEq (x.getArg! 2) tys
      let some fx := fx? | break
      let fnStx ← Tactic.withMainContext do exprToSyntax fx.appFn!.appFn!
      let F ← Tactic.withMainContext do exprToSyntax (← fnSolutionHO g sig gRef gSig)
      Tactic.withMainContext do
        let hTy ← Term.withoutErrToSorry do
          let t ← Term.elabTerm (← `(∀ x hx, ($fnStx x hx).1 = ($F x hx).1))
            (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars t
        let pf ← mkFreshExprSyntheticOpaqueMVar hTy
        let rest ← Term.withoutErrToSorry <| Tactic.run pf.mvarId! <| Tactic.withoutRecover do
          Tactic.evalTactic (← `(tactic| refine $(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?_))
          hoEqProof { name := g } gRef
        unless rest.isEmpty do throwError "wf_agree: could not prove the equation of {g}"
        let (_, mvarId) ← (← (← Tactic.getMainGoal).assert `hcallee hTy
          (← instantiateMVars pf)).intro1P
        Tactic.replaceMainGoal [mvarId]
      let h := mkIdent `hcallee
      Tactic.evalTactic (← `(tactic| (simp only [$h:ident] at *); try clear $h))

/-- The proof that `F = fnSolutionHO f gRef` satisfies the equation of the body of the local
recursive function capturing `f` with the specialised `gRef` (goal
`∀ x hx, (F x hx).1 = (body.eval x hx (fun y _ hy => F y hy)).1`): by unfolding `f` (tag `0`)
or `g` (tag `t + 1`) once. -/
partial def hoEqProof (f gRef : FnRef) : Tactic.TacticM Unit := do
  let sig ← fnSig f
  let gSig ← fnSig gRef
  let fEq := mkIdent (f.name ++ `eq_def)
  let gEq := mkIdent (gRef.name ++ `eq_def)
  Tactic.evalTactic (← `(tactic| (
      intro x hx
      dsimp only
      obtain ⟨t, x⟩ := x)))
  for _ in [0:sig.argTys.length + gSig.argTys.length] do
    Tactic.evalTactic (← `(tactic| obtain ⟨_, x⟩ := x))
  Tactic.evalTactic (← `(tactic| rcases t with _ | t))
  let [g0, g1] ← Tactic.getGoals | throwError "wf_agree: unexpected goals"
  -- tag `0`: the equation of `f`
  Tactic.setGoals [g0]
  Tactic.evalTactic (← `(tactic| (
      simp only [↓reduceIte]
      rw [$fEq:ident]
      try simp only [WFLang.fold_eq_rangeLoop])))
  unfoldInlined f
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  rewriteCallees (← calleeInfo f.name).2
  Tactic.evalTactic (← `(tactic| wf_close))
  let rest0 ← Tactic.getGoals
  -- tag `t + 1`: the equation of `g`
  Tactic.setGoals [g1]
  Tactic.evalTactic (← `(tactic| (
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [$gEq:ident]
      try simp only [WFLang.fold_eq_rangeLoop])))
  unfoldInlined gRef
  Tactic.evalTactic (← `(tactic| all_goals $(← pclSimp):tactic))
  Tactic.evalTactic (← `(tactic| wf_close))
  Tactic.setGoals (rest0 ++ (← Tactic.getGoals))
end

/-- The agreement proof for a function `f` captured together with the copy `gRef` of a function
specialised to a function argument that calls `f` (`HOInfo`): the program is one call (tag `0`)
of the local recursive function, which computes
`F (t, xs, ys, zs) = if t = 0 then f xs else g (spec ys) zs` (`fnSolutionHO`) by uniqueness
(`fixFn_unique`, `hoEqProof`). -/
def hoAgree (f gRef : FnRef) (t : Ident) : Tactic.TacticM Unit := do
  let sig ← fnSig f
  let gSig ← fnSig gRef
  let F ← Tactic.withMainContext do exprToSyntax (← fnSolutionHO f.name sig gRef gSig)
  Tactic.evalTactic (← `(tactic| (
      intros
      simp only [$t:ident, WFLang.PCL.Term.eval, WFLang.PCL.Term.run, WFLang.PCL.PTerm.run,
        WFLang.curryEnv, WFLang.PCL.eval_gCall, WFLang.PCL.Globals.env_defn,
        WFLang.PCL.FnVar.get_here, WFLang.PCL.eval_ret, WFLang.PExpr.eval,
        WFLang.PExprs.eval, WFLang.Var.get]
      refine Eq.trans ($(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?hF _ _) ?heq
      case heq => simp)))
  hoEqProof f gRef

@[tactic wfAgree] def evalWfAgree : Tactic.Tactic := fun _ => do
  let (t, f, eqDef, _) ← agreeTarget "wf_agree"
  -- the functions whose values are identified in the proof: the local recursive callees and
  -- the global functions (also those called only from the function arguments of a
  -- specialised `f`)
  let callees := (← globalsOf f).foldl (fun acc g => if acc.contains g then acc else acc.push g)
    (← calleeInfo f.name).2
  if (← mutualGroup? f.name).isSome then
    -- a member of a group of mutually recursive functions: the program is one call of the
    -- node capturing the group, whose function is identified like a callee's
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.PCL.Term.eval, WFLang.PCL.Term.run, WFLang.PCL.PTerm.run,
        WFLang.curryEnv, WFLang.PExpr.eval, WFLang.PExprs.eval, WFLang.Var.get,
        WFLang.PCL.Handler.push, WFLang.Meta.wfFoldCalls])))
    rewriteCallees (callees.push f.name)
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  if let some gRef ← hoRefOf? f then
    return ← hoAgree f gRef t
  if !(← isWFRec f.name) then
    let f := mkIdent f.name
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.PCL.Term.eval, WFLang.PCL.Term.run, WFLang.PCL.PTerm.run,
        WFLang.curryEnv, WFLang.PExpr.eval, WFLang.PExprs.eval, WFLang.Var.get,
        WFLang.BinOp.eval, WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default,
        WFLang.PCL.Handler.push, WFLang.PCL.toEnv_cons, WFLang.PCL.toEnv_one,
        Nat.pred_eq_sub_one, bne, Nat.min_def,
        Nat.max_def, Nat.dvd_iff_mod_eq_zero, WFLang.foldl_range'_eq_rangeLoop,
        WFLang.rangeLoop_add_sub, WFLang.fold_eq_rangeLoop, WFLang.ite_pure_yield,
        WFLang.PCL.eval_whileLoop, WFLang.whileWF_eq_loopVal,
        WFLang.whileMeasure_eq_loopVal, WFLang.Meta.wfFoldCalls, $f:ident])))
    unfoldInlined f.getId
    rewriteCallees callees
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  agreeRec f t eqDef (← pclSimp) (rewriteCallees callees)

end WFLang.Capture
