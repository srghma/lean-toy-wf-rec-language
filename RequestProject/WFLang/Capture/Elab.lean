import RequestProject.WFLang.PCL.Lang
import RequestProject.WFLang.Capture.Translate

/-!
# `#lean_wf_func_to_term f` — capture a well-founded Lean function as a `PCL.Term`

```
def gcd_term : PCL.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term gcd
theorem gcd_agree : ∀ m n, PCL.Term.eval gcd_term m n = gcd m n := by wf_agree
```

For a function with a subtype result the agreement is `PCL.Term.eval f_term xs = (f xs).val`,
and for a function with proof parameters (a precondition) it is
`PCL.PTerm.run f_term (x₁, …, ()) h = f x₁ … h`.

The elaborator reads `f.eq_def`, and writes the program (`PTerm.ofFix`)

```
fix self xs. ⟦rhs⟧   applied to xs
```

as *surface syntax* of `PCL.Expr`, which Lean then elaborates against the expected type:

* control flow (`if`, `match` on `Nat`/`Bool`/lists, `&&`/`||` with a call on the right)
  becomes `Expr.ite`, so each branch records its test in the path condition;
* every recursive call is lifted out (A-normal form) into
  `Expr.fixSelfCall args (by wf_dec …) hpre k`, and a `let` whose value calls is evaluated
  once, before its body;
* an `if`/`match` containing a call in *non-tail* position is compiled by duplicating the rest
  of the computation into both branches, so that `ite` stays in tail position (strict ANF);
* the relation and its well-foundedness proof are the ones Lean built for `f`
  (from `WellFounded.fix`), pulled back along the packing of the arguments;
* each `by wf_dec …` proves that one call goes down, from the path condition, using the
  decreasing proofs Lean extracted for `f` (in particular the user's `decreasing_by`),
  `omega`, or `decreasing_tactic`.
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- Is `e` a control-flow node whose branches must not be evaluated eagerly? -/
def isControl (e : Lean.Expr) : MetaM Bool := do
  if e.isAppOf ``ite || e.isAppOf ``dite || e.isAppOf ``cond || e.isAppOf ``Nat.casesOn ||
    e.isAppOf ``Bool.casesOn || e.isAppOf ``List.casesOn || e.isAppOf ``and ||
    e.isAppOf ``or then return true
  if let .const n _ := e.getAppFn then return (← isMatcher n) || isSparseCasesOn n
  return false

/-- Are two references to specialised copies of the same function equal (up to definitional
equality of their function arguments)? -/
def specRefEq (a b : FnRef) : MetaM Bool := do
  if a.beq b then return true
  unless a.name == b.name && a.spec.size == b.spec.size && a.extraTys.size == b.extraTys.size do
    return false
  for (x, y) in a.extraTys.zip b.extraTys do
    unless ← isDefEq x y do return false
  for (x, y) in a.spec.zip b.spec do
    unless ← isDefEq x y do return false
  return true

/-- Inside the local recursive function capturing `f` together with the specialised `g` (see
`HOInfo`): if `e` is a call of `f` or of the specialised `g`, the arguments of the corresponding
recursive call (`tag :: f's arguments ++ g's lifted variables ++ g's arguments`, `none` for
padding). -/
def hoSelfArgs? (c : Ctx) (h : HOInfo) (e : Lean.Expr) : MetaM (Option (List (Option Lean.Expr))) := do
  let nF := h.fSig.argTys.length
  let nE := h.gSig.nExtra
  let nG := h.gSig.argTys.length - nE
  if e.isAppOf h.fName && e.getAppNumArgs == h.fSig.arity then
    return some (some (mkNatLit 0) :: (objArgs h.fSig e.getAppArgs).map some ++
      List.replicate (nE + nG) none)
  let .const g lvls := e.getAppFn | return none
  unless g == h.gRef.name do return none
  let args := e.getAppArgs
  unless args.size == h.gSig.arity do
    throwError "#lean_wf_func_to_term: partial application of {g} (function values are not supported){indentExpr e}"
  let (ref, ys) ← mkSpecRef g lvls args (← specPosAt (mkConst g lvls) args)
  unless ← specRefEq ref h.gRef do
    throwError "#lean_wf_func_to_term: {g} is called with several different function arguments that call {h.fName} (not supported){indentExpr e}"
  for y in ys do
    unless c.vars.contains y.fvarId! do
      throwError "#lean_wf_func_to_term: the function argument of {g} uses {y}, which is not a variable of the program"
  return some (some (mkNatLit 1) :: List.replicate nF none ++ ys.toList.map some ++
    (objArgs h.gSig args).map some)

/-- The de Bruijn index (`PCL.JVar`) of a join point defined when `v0` variables were in scope,
from a point with `vc` variables in scope, where `later` (innermost first) are the numbers of
variables in scope at the definitions of the join points defined after it: each join point
defined after it is crossed by `there`, each variable bound after it by `wk`. -/
partial def jvarStx (later : List Nat) (vc v0 : Nat) : MetaM Stx :=
  match later with
  | l :: ls =>
    if l == vc then do `(WFLang.PCL.JVar.there $(← jvarStx ls vc v0))
    else do `(WFLang.PCL.JVar.wk $(← jvarStx later (vc - 1) v0))
  | [] =>
    if vc ≤ v0 then `(WFLang.PCL.JVar.here)
    else do `(WFLang.PCL.JVar.wk $(← jvarStx [] (vc - 1) v0))

/-- Must the continuation of a non-tail `if`/`match` be duplicated into its branches rather
than become a join point?  Only when a call may have a postcondition (a function with a subtype
result), which the rest of the computation may need: the parameter of a join point does not
record which call produced it. -/
def needsDup (c : Ctx) : Bool :=
  c.hasPost || c.fnSig?.any (·.subtypeRet) || c.callees.any (·.2.1.subtypeRet)

/-- Put the values `vs` in the `some` positions of `xs`. -/
def fillOpt : List (Option Lean.Expr) → List Lean.Expr → List (Option Lean.Expr)
  | [], _ => []
  | none :: xs, vs => none :: fillOpt xs vs
  | some _ :: xs, v :: vs => some v :: fillOpt xs vs
  | some x :: xs, [] => some x :: fillOpt xs []

mutual
/-- Evaluate the calls inside `e` first (A-normal form), then continue with the call-free
remainder. -/
partial def lift (c : Ctx) (e : Lean.Expr) (k : Ctx → Lean.Expr → TermElabM Stx) :
    TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← k c e
  -- `let x := v; b` whose value calls: evaluate `v` once, then `b`
  if e.isLet && hasCall c e.letValue! then
    return ← lift c e.letValue! fun c v => lift c (e.letBody!.instantiate1 v) k
  if let some e' ← unfoldStep? e then return ← lift c e' k
  -- a call of `f` or of the specialised `g`, in the local recursive function capturing both
  if let some h := c.ho then
    if let some args ← hoSelfArgs? c h e then
      return ← liftMany c (args.filterMap id) [] fun c vals => do
        let retTy ← inferType e
        withLocalDeclD `r retTy fun v => do
          let rest ← k { c with vars := v.fvarId! :: c.vars } v
          `(WFLang.PCL.Expr.fixSelfCall $(← pargsOpt c (fillOpt args vals)) $(← decStx c)
              (fun _ _ => trivial) $rest)
  if e.isApp && (e.getAppFn.isConstOf c.fn || c.group.any e.getAppFn.isConstOf) then
    let some sig := c.fnSig? |
      throwError "#lean_wf_func_to_term: recursive call of {c.fn} outside its definition"
    -- in a group of mutually recursive functions: the tag of the callee comes first
    let tag := (c.group.findIdx? e.getAppFn.isConstOf).map mkNatLit
    unless e.getAppNumArgs == sig.arity do
      throwError "#lean_wf_func_to_term: partial application of {c.fn} (function values are not supported){indentExpr e}"
    -- a specialised copy: the recursive call must pass the same function arguments
    for (p, v) in sig.specPos.zip c.selfSpec do
      unless ← isDefEq e.getAppArgs[p]! v do
        throwError "#lean_wf_func_to_term: the recursive call changes the function argument of {c.fn}{indentExpr e}"
    return ← liftMany c (tag.toList ++ c.selfExtra ++ objArgs sig e.getAppArgs) [] fun c args => do
      let retTy ← inferType e
      withLocalDeclD `r retTy fun v => do
        let rest ← k { c with vars := v.fvarId! :: c.vars } v
        `(WFLang.PCL.Expr.fixSelfCall $(← pargs c args) $(← decStx c) $(← hpreStx c sig)
            $rest)
  -- a call of another recursive function: a nested `fix` node
  if let some (sig, head) := calleeCall? c e then
    return ← liftMany c ((sig.tag.map mkNatLit).toList ++ objArgs sig e.getAppArgs) [] fun c args => do
      let retTy ← inferType e
      withLocalDeclD `r retTy fun v => do
        let rest ← k { c with vars := v.fvarId! :: c.vars } v
        let pa ← pargsOpt c (args.map some ++ List.replicate sig.pad none)
        `($head (WFLang.PCL.Expr.fnCall WFLang.PCL.FnVar.here $pa $(← hpreStx c sig) $rest))
  -- a call of a function with function arguments: a nested `fix` node capturing the copy
  -- specialised to these arguments, which takes the lifted variables as extra arguments
  if let some (ref, ys) ← specCall? c e then
    let sig ← fnSig ref
    let head ← c.specHead ref
    return ← liftMany c (ys.toList ++ objArgs sig e.getAppArgs) [] fun c args => do
      let retTy ← inferType e
      withLocalDeclD `r retTy fun v => do
        let rest ← k { c with vars := v.fvarId! :: c.vars } v
        `($head (WFLang.PCL.Expr.fnCall WFLang.PCL.FnVar.here $(← pargs c args) $(← hpreStx c sig)
          $rest))
  if e.isApp && !(← isControl e) && !hasCall c e.getAppFn then
    return ← liftMany c e.getAppArgs.toList [] fun c args => k c (mkAppN e.getAppFn args.toArray)
  -- a control-flow node containing a call, in non-tail position: the rest of the computation
  -- (the continuation `k`) becomes a join point `j`, then the test is evaluated, and each
  -- branch ends with `jump j v` (strict A-normal form: `ite` and `join` stay in tail position,
  -- and `k` is written once)
  if let some (t, a, b) ← branch? e then
    if needsDup c || !wfLang.joinPoints.get (← getOptions) then
      -- the continuation may need the postconditions of the calls made in the branches:
      -- it is duplicated into both branches instead
      return ← lift c t.expr fun c cnd => do
        `(WFLang.PCL.Expr.ite $(← test c (t.withExpr cnd)) $(← lift c a k) $(← lift c b k))
    let d := c.joins.length
    let v0 := c.vars.length
    let ty ← inferType e
    let body ← withLocalDeclD `v ty fun v => k { c with vars := v.fvarId! :: c.vars } v
    let jumpK : Ctx → Lean.Expr → TermElabM Stx := fun c' v => do
      let later := c'.joins.take (c'.joins.length - d - 1)
      `(WFLang.PCL.Expr.jump $(← jvarStx later c'.vars.length v0) $(← pexpr c' v)
          (fun _ _ => trivial) (fun _ _ _ h => h))
    let m ← lift { c with joins := v0 :: c.joins } t.expr fun c cnd => do
      `(WFLang.PCL.Expr.ite $(← test c (t.withExpr cnd)) $(← lift c a jumpK) $(← lift c b jumpK))
    return ← `(WFLang.PCL.Expr.join $(← tyStx ty) (fun _ _ => True) $body $m)
  -- a call of another recursive function inside a control-flow node that is not a branch:
  -- evaluate it first (all functions are total, so this does not change the result)
  let hoistable (x : Lean.Expr) : Bool :=
    ((calleeCall? c x).isSome || c.specFns.any (x.isAppOf ·)) && !x.hasLooseBVars &&
      (x.find? (·.isAppOf c.fn)).isNone
  if let some s := e.find? hoistable then
    return ← lift c s fun c v =>
      lift c (e.replace fun x => if x == s then some v else none) k
  throwError "#lean_wf_func_to_term: recursive call in an unsupported position{indentExpr e}"

partial def liftMany (c : Ctx) (es : List Lean.Expr) (acc : List Lean.Expr)
    (k : Ctx → List Lean.Expr → TermElabM Stx) : TermElabM Stx :=
  match es with
  | [] => k c acc.reverse
  | e :: es => lift c e fun c e' => liftMany c es (e' :: acc) k
end

/-- `ret e`, with the proof of the postcondition (if any). -/
def retStx (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  `(WFLang.PCL.Expr.ret $(← pexpr c e) $(← postStx c))

/-- A Lean expression in tail position, as a statement. -/
partial def stmt (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← retStx c e
  if e.isLet && hasCall c e.letValue! then
    return ← lift c e.letValue! fun c v => stmt c (e.letBody!.instantiate1 v)
  if let some e' ← unfoldStep? e then return ← stmt c e'
  if let some (t, a, b) ← branch? e then
    return ← lift c t.expr fun c cnd => do
      `(WFLang.PCL.Expr.ite $(← test c (t.withExpr cnd)) $(← stmt c a) $(← stmt c b))
  lift c e retStx

/-- The recursive functions with function parameters called in `rhs` (to be specialised at each
call site). -/
def specFnsIn (fn : Name) (rhs : Lean.Expr) : MetaM (Array Name) :=
  rhs.getUsedConstants.filterM (isSpecFn fn)

/-- The pieces of the local recursive function capturing `fn`: its parameter types, result
type, relation, well-foundedness proof, precondition, postcondition and body. -/
structure FixParts where
  gam : Stx
  ret : Stx
  R : Stx
  wf : Stx
  pre : Stx
  post : Stx
  body : Stx
  /-- for the local recursive function capturing a function together with a specialised
  function whose function argument calls it (`HOInfo`): the number of padded parameters after
  the function's own ones (it is called with tag `0`) -/
  hoPad : Option Nat := none

mutual
/-- The pieces of the local recursive function capturing the recursive Lean function `fn`.
`visiting` are the functions whose capture is in progress. -/
partial def fixParts (f : FnRef) (visiting : List Name := []) : TermElabM FixParts := do
  if !f.group.isEmpty then return ← groupParts f.group visiting
  let fn := f.name
  if visiting.contains fn then
    throwError "#lean_wf_func_to_term: mutual recursion through {fn} is not supported"
  let sig ← fnSig f
  let some (R, wf, lemmasE) ← closedFixOf f |
    throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
  let lemmas ← lemmasE.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
  let res ← withEqnRhs' f fun ys xs rhs => do
    let (pre?, post?) ← prePostOf f xs (← inferType (mkAppN (← f.const) xs)) ys
    let callees ← calleeHeads fn rhs (fn :: visiting)
    let c : Ctx := { (Ctx.ofParams fn xs sig ys) with
      lemmas := lemmas, decTac := decTac, callees := callees, hasPost := post?.isSome,
      specFns := ← specFnsIn fn rhs, specHead := fun r => fixHead r (fn :: visiting) }
    -- a call of a function with a function argument that calls `fn`: `fn` and the specialised
    -- function are captured together
    if let some gRef ← hoRefIn? f c rhs then
      unless pre?.isNone && post?.isNone do
        throwError "#lean_wf_func_to_term: {fn} calls itself inside a function argument; this is not supported together with proof parameters or a subtype result"
      return Sum.inr (← hoParts fn sig xs rhs c gRef R wf visiting)
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
  try discard <| stmt { c with hoFound := some r } rhs catch _ => pure ()
  restoreState saved
  r.get

/-- The pieces of the local recursive function capturing `fn` (signature `sig`, parameters
`xs`, right-hand side `rhs`, relation `Rf`) together with the copy `gRef` of a function `g`
specialised to a function argument that calls `fn` (see `HOInfo`).  Its parameters are
`tag :: fn's parameters ++ g's lifted variables ++ g's parameters`, its body
`if tag = 0 then ⟦rhs⟧ else ⟦rhs of g⟧`, and its relation `WFLang.hoRel` (`hoRelOf`). -/
partial def hoParts (fn : Name) (sig : FnSig) (xs : Array Lean.Expr) (rhs : Lean.Expr) (c : Ctx)
    (gRef : FnRef) (Rf wff : Lean.Expr) (visiting : List Name) : TermElabM FixParts := do
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
      let gCallees ← calleeHeads gRef.name rhsG (fn :: gRef.name :: visiting)
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
      `(WFLang.PCL.Expr.ite $tst $a $b)
  return { gam := ← exprToSyntax (mkTyList (Lean.mkConst ``WFLang.Ty.nat :: sig.argTys ++ gSig.argTys)),
           ret := ← exprToSyntax sig.retTy, R := ← exprToSyntax R, wf := ← exprToSyntax wf,
           pre := ← `(fun _ => True), post := ← `(fun _ _ => True), body,
           hoPad := some gSig.argTys.length }

/-- The pieces of the local recursive function capturing a group of mutually recursive functions
`group` (with the same parameter and result types): its first parameter is a tag `t`, and its
body is `if t = 0 then ⟦rhs of group[0]⟧ else if t = 1 then … else ⟦rhs of group[k-1]⟧`, where a
call of `group[i]` is a recursive call with tag `i`. -/
partial def groupParts (group : Array Name) (visiting : List Name) : TermElabM FixParts := do
  if group.any visiting.contains then
    throwError "#lean_wf_func_to_term: mutual recursion through {group} is not supported"
  let ref : FnRef := { name := group[0]!, group }
  let sig ← fnSig ref
  let (R, wf, lemmas) ← groupFixOf group
  let lemmas ← lemmas.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec_tag [WFLang.PCL.Self.top, WFLang.PCL.Self.push])
  let visiting' := group.toList ++ visiting
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
        for (h, hs, hd) in ← calleeHeads g rhs visiting' do
          unless group.contains h || callees.any (·.1 == h) do callees := callees.push (h, hs, hd)
        for h in ← specFnsIn g rhs do
          unless specFns.contains h do specFns := specFns.push h
      let objs := sig.objPos.map (xs[·]!)
      let vars := (t :: objs).map (·.fvarId!)
      let hd : FnRef → TermElabM Stx := fun r => fixHead r visiting'
      let c0 : Ctx := { fn := group[0]!, vars := vars, fnSig? := some sig }
      let c : Ctx := { c0 with group := group, lemmas := lemmas, decTac := some decTac }
      let c : Ctx := { c with callees := callees, specFns := specFns, specHead := hd }
      let mut acc ← stmt c rhss.back!
      for i in (List.range (group.size - 1)).reverse do
        let tst ← test c (.prop (← mkEq t (mkNatLit i)))
        acc ← `(WFLang.PCL.Expr.ite $tst $(← stmt c rhss[i]!) $acc)
      return acc
  return { gam := ← exprToSyntax (mkTyList sig.argTys), ret := ← exprToSyntax sig.retTy,
           R := ← exprToSyntax R, wf := ← exprToSyntax wf, pre := ← `(fun _ => True),
           post := ← `(fun _ _ => True), body }

/-- The head `PCL.Expr.fix ps r R wf pre post body` (still to be applied to its scope,
`fnCall FnVar.here args hpre k`) of the local recursive function capturing
`fn` (still to be applied to the arguments, the precondition proof and the continuation). -/
partial def fixHead (fn : FnRef) (visiting : List Name := []) : TermElabM Stx := do
  let p ← fixParts fn visiting
  if p.hoPad.isSome then
    throwError "#lean_wf_func_to_term: {fn.name} calls itself inside a function argument; calling such a function from another function is not supported (capture it on its own)"
  `(WFLang.PCL.Expr.fix $(p.gam) $(p.ret) $(p.R) $(p.wf) $(p.pre) $(p.post) $(p.body))

/-- The recursive functions called by `rhs` (other than `fn`), with their `fix` heads. -/
partial def calleeHeads (fn : Name) (rhs : Lean.Expr) (visiting : List Name) :
    TermElabM (Array (Name × FnSig × Stx)) := do
  -- (the functions being captured, e.g. the other members of a group of mutually recursive
  -- functions, are not callees)
  ((← recCallees fn rhs).filter (!visiting.contains ·)).mapM fun (g : Name) => do
    -- a member of a group of mutually recursive functions: the node capturing the group, called
    -- with the tag of `g`
    if let some grp ← mutualGroup? g then
      let sig ← fnSig g
      return (g, { sig with tag := grp.findIdx? (· == g) },
        ← fixHead { name := grp[0]!, group := grp } visiting)
    let p ← fixParts { name := g } visiting
    let head ← `(WFLang.PCL.Expr.fix $(p.gam) $(p.ret) $(p.R) $(p.wf) $(p.pre) $(p.post) $(p.body))
    let sig ← fnSig { name := g }
    if let some n := p.hoPad then
      -- `g` calls itself inside a function argument: its node is called with tag `0` and
      -- padding
      return (g, { sig with tag := some 0, pad := n }, head)
    return (g, sig, head)
end

/-- Build the surface syntax of `PTerm.ofFix R wf (⟦rhs of f.eq_def⟧)` (or of the body alone
if `f` is not recursive). -/
def captureStx (fn : FnRef) : TermElabM Stx := do
  let isRec ← withEqnRhs fn fun _ rhs => return hasCall { fn := fn.name, vars := [] } rhs
  if let some grp ← mutualGroup? fn.name then
    -- a member of a group of mutually recursive functions: one call of the node capturing the
    -- group, with the tag of `fn`
    let head ← fixHead { name := grp[0]!, group := grp }
    let sig ← fnSig fn.name
    return ← withEqnRhs fn fun xs _ => do
      let c := Ctx.ofParams fn.name xs sig
      let args ← pargs c (mkNatLit (grp.findIdx? (· == fn.name)).get! :: objArgs sig xs)
      let retTy ← inferType (mkAppN (← mkConstWithLevelParams fn.name) xs)
      withLocalDeclD `r retTy fun v => do
        let c' := { c with vars := v.fvarId! :: c.vars }
        `($head (WFLang.PCL.Expr.fnCall WFLang.PCL.FnVar.here $args $(← hpreStx c sig)
          $(← retStx c' v)))
  if isRec && (← isWFRec fn.name) then
    let p ← fixParts fn
    if let some n := p.hoPad then
      -- `fn` captured together with a specialised function: one call of the local recursive
      -- function, with tag `0`
      let sig ← fnSig fn
      return ← withEqnRhs fn fun xs _ => do
        let c := Ctx.ofParams fn.name xs sig
        let args ← pargsOpt c (some (mkNatLit 0) :: (objArgs sig xs).map some ++
          List.replicate n none)
        `(WFLang.PCL.Expr.fix $(p.gam) $(p.ret) $(p.R) $(p.wf) $(p.pre) $(p.post) $(p.body)
            (WFLang.PCL.Expr.fnCall WFLang.PCL.FnVar.here $args (fun _ _ => trivial)
              (WFLang.PCL.Expr.ret (WFLang.PExpr.var WFLang.Var.here) (fun _ _ => trivial))))
    `(@WFLang.PCL.PTerm.ofFix ⟨$(p.gam), $(p.ret)⟩ $(p.pre) $(p.post) $(p.R) $(p.wf) $(p.body))
  else
    -- not recursive: the program is just the body
    let sig ← fnSig fn
    withEqnRhs' fn fun ys xs rhs => do
      let callees ← calleeHeads fn.name rhs [fn.name]
      let c : Ctx := { (Ctx.ofParams fn.name xs sig ys) with
        callees := callees, fnSig? := none, specFns := ← specFnsIn fn.name rhs,
        specHead := fun r => fixHead r [fn.name] }
      stmt c rhs

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
By uniqueness of the solution of the `fix` equation (`PTerm.ofFix_run`) it suffices that `f`
satisfies the equation of the body, which follows from `f.eq_def`. -/
syntax (name := wfAgree) "wf_agree" : tactic

/-- The simplification step of the PCL agreement proofs. -/
def pclSimp : Tactic.TacticM (TSyntax `tactic) :=
  `(tactic| simp [WFLang.PExprs.eval, WFLang.PExpr.eval, WFLang.Var.get, WFLang.BinOp.eval,
        WFLang.UnOp.eval, WFLang.Ty.beq, WFLang.Ty.default, WFLang.PCL.Self.top,
        WFLang.PCL.Self.push, WFLang.PCL.eval_fix, WFLang.PCL.eval_fnCall_here, WFLang.PCL.Handler.push,
        WFLang.uncurryEnv,
        Nat.pred_eq_sub_one, bne, Nat.min_def, Nat.max_def, Nat.dvd_iff_mod_eq_zero,
        WFLang.foldl_range'_eq_rangeLoop, WFLang.rangeLoop_add_sub, WFLang.fold_eq_rangeLoop,
        WFLang.ite_pure_yield])

/-- If `f` calls itself inside a function argument of another recursive function `g`: the
reference to the copy of `g` specialised to that argument (see `hoRefIn?`). -/
def hoRefOf? (f : FnRef) : TermElabM (Option FnRef) := do
  if f.isSpec || !f.group.isEmpty || !(← isWFRec f.name) then return none
  let sig ← fnSig f
  withEqnRhs' f fun ys xs rhs => do
    unless ← hoCandidate f.name rhs do return none
    let callees ← calleeHeads f.name rhs [f.name]
    let c : Ctx := { (Ctx.ofParams f.name xs sig ys) with
      callees, specFns := ← specFnsIn f.name rhs, specHead := fun r => fixHead r [f.name] }
    hoRefIn? f c rhs

mutual
/-- Replace every value `(fixFn wf body x hx).1` of a nested `fix` node capturing a recursive
callee in the main goal by the callee's value (`rewriteCalleesWith`, uniqueness lemma
`fixFn_unique`). -/
partial def rewriteCallees (callees : Array Name) : Tactic.TacticM Unit := do
  rewriteHOCallees callees
  rewriteCalleesWith calleeStep callees

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
        (← found.get).findM? fun x => isDefEq (x.getArg! 0) tys
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
        WFLang.curryEnv, WFLang.PCL.eval_fix, WFLang.PCL.eval_fnCall_here,
        WFLang.PCL.eval_ret, WFLang.PExpr.eval,
        WFLang.PExprs.eval, WFLang.Var.get]
      refine Eq.trans ($(mkIdent `WFLang.PCL.fixFn_unique) _ _ _ $F ?hF _ _) ?heq
      case heq => simp)))
  hoEqProof f gRef

@[tactic wfAgree] def evalWfAgree : Tactic.Tactic := fun _ => do
  let (t, f, eqDef, _) ← agreeTarget "wf_agree"
  let callees := (← calleeInfo f.name).2
  if (← mutualGroup? f.name).isSome then
    -- a member of a group of mutually recursive functions: the program is one call of the
    -- node capturing the group, whose function is identified like a callee's
    Tactic.evalTactic (← `(tactic| (
      intros
      simp [$t:ident, WFLang.PCL.Term.eval, WFLang.PCL.Term.run, WFLang.PCL.PTerm.run,
        WFLang.curryEnv, WFLang.PExpr.eval, WFLang.PExprs.eval, WFLang.Var.get,
        WFLang.PCL.eval_fix, WFLang.PCL.Handler.push])))
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
        WFLang.PCL.eval_fix, WFLang.PCL.Handler.push, Nat.pred_eq_sub_one, bne, Nat.min_def,
        Nat.max_def, Nat.dvd_iff_mod_eq_zero, WFLang.foldl_range'_eq_rangeLoop,
        WFLang.rangeLoop_add_sub, WFLang.fold_eq_rangeLoop, WFLang.ite_pure_yield, $f:ident])))
    unfoldInlined f.getId
    rewriteCallees callees
    return ← Tactic.evalTactic (← `(tactic| wf_close))
  agreeRec f t eqDef (← pclSimp) (rewriteCallees callees)

end WFLang.Capture
