import RequestProject.WFLang.Capture.Stmt.Basic

/-!
# Translating the right-hand side of a Lean function into `PCL` statements

`stmt c rhs` translates a Lean term in tail position into the surface syntax of a `PCL.Expr`;
`lift c e k` evaluates the calls inside `e` first (A-normal form) and continues with `k`.

* control flow (`if`, `match` on `Nat`/`Bool`/lists, `&&`/`||` with a call on the right)
  becomes `Expr.ite`, so each branch records its test in the path condition;
* every recursive call is lifted out into `Expr.fixSelfCall args (by wf_dec …) hpre k`, and a
  `let` whose value calls is evaluated once, before its body;
* an `if`/`match` containing a call in *non-tail* position is compiled with a join point:
  `join j (v) := ⟦rest⟧ in if c then (…; jump j a) else (…; jump j b)`;
* a call of a **global function** is `Expr.gCall i args` (the function is added to the global
  context the first time it is called, `Ctx.gref`);
* a call of a **tail-recursive** `@[inlinable]` function `g` (or of a tail-recursive function
  with function arguments, specialised to them, e.g. the loop of a `for`) is **inlined as a
  loop** (`loopStx`):

  ```
  join K (v) := ⟦rest⟧ in
  joinrec L (x) [R] := ⟦rhs of g⟧[params := x; g args ↦ jump L args; tail value p ↦ jump K p] in
  jump L args
  ```

  The loop lives inside the caller: its body sees the caller's variables, path condition,
  enclosing recursive function and join points.  Each back edge `jump L args` proves that
  `args` goes down along Lean's relation for `g` (`wf_dec`, with Lean's decreasing proofs for
  `g`);
* a well-founded `while` loop (`WFLang.whileWF`) is `Expr.whileLoop`, itself a `join` for the
  exit and a `joinrec` for the loop.
-/

namespace WFLang.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

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
  -- a well-founded `while` loop: `let v := while … in k`
  if e.isAppOfArity ``WFLang.whileWF 9 then return ← whileStx c e k
  -- `List.map f l` (also `l.attach.map f`): `let v := map (fun x => ⟦f x⟧) l in k`
  if e.isAppOfArity ``List.map 4 then return ← mapStx c e k
  -- a call of `f` or of the specialised `g`, in the global function capturing both
  if let some h := c.ho then
    if let some args ← hoSelfArgs? c h e then
      return ← liftMany c (args.filterMap id) [] fun c vals => do
        let retTy ← inferType e
        withLocalDeclD `r retTy fun v => do
          let rest ← k { c with vars := v.fvarId! :: c.vars } v
          `(WFLang.PCL.Expr.fixSelfCall $(← pargsOpt c (fillOpt args vals)) (by decide) $(← decStx c)
              (fun _ _ => trivial) $rest)
  -- inside a loop: a call of the looping function that is not a tail call
  if c.loop?.isSome && e.getAppFn.isConstOf c.fn then
    throwError "#lean_wf_func_to_term: {c.fn} calls itself in a non-tail position (it cannot be a loop){indentExpr e}"
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
        `(WFLang.PCL.Expr.fixSelfCall $(← pargs c args) (by decide) $(← decStx c) $(← hpreStx c sig)
            $rest)
  -- a call of a global function (by attribute): `let v := g args in k`
  if let some (g, sig) := globalCall? c e then
    let gi ← c.gref { name := g }
    return ← gCallStx c gi sig (objArgs sig e.getAppArgs) e k
  -- a call of another recursive function: a loop, or a global function
  if let some (sig, kind) := calleeCall? c e then
    let .const g _ := e.getAppFn | throwError "#lean_wf_func_to_term: unexpected call{indentExpr e}"
    if kind == .loop then
      return ← loopStx c { name := g } sig (objArgs sig e.getAppArgs) e k
    let gi ← c.gref (← calleeKey g)
    return ← gCallStx c gi sig ((sig.tag.map mkNatLit).toList ++ objArgs sig e.getAppArgs) e k
  -- a call of a function with function arguments: the copy specialised to these arguments,
  -- which takes the lifted variables as extra arguments (a loop if it is tail-recursive)
  if let some (ref, ys) ← specCall? c e then
    let sig ← fnSig ref
    let args := ys.toList ++ objArgs sig e.getAppArgs
    if ← loopableSig ref sig then return ← loopStx c ref sig args e k
    return ← gCallStx c (← c.gref ref) sig args e k
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
        iteStx c (t.withExpr cnd) (lift c a k) (lift c b k)
    let d := c.joins.length
    let v0 := c.vars.length
    let ty ← inferType e
    let body ← withLocalDeclD `v ty fun v => k { c with vars := v.fvarId! :: c.vars } v
    let jumpK : Ctx → Lean.Expr → TermElabM Stx := fun c' v => do
      `(WFLang.PCL.Expr.jump $(← jvarAt c' d v0) $(← pexpr c' v) (by decide)
          (fun _ _ => trivial) (fun _ _ _ h => h))
    let m ← lift { c with joins := v0 :: c.joins } t.expr fun c cnd => do
      iteStx c (t.withExpr cnd) (lift c a jumpK) (lift c b jumpK)
    return ← `(WFLang.PCL.Expr.join $(← tyStx ty) (fun _ _ => True) $body $m)
  -- a call of another recursive function inside a control-flow node that is not a branch:
  -- evaluate it first (all functions are total, so this does not change the result)
  let hoistable (x : Lean.Expr) : Bool :=
    ((calleeCall? c x).isSome || (globalCall? c x).isSome || c.specFns.any (x.isAppOf ·)) &&
      !x.hasLooseBVars &&
      (x.find? (·.isAppOf c.fn)).isNone
  if let some s := e.find? hoistable then
    return ← lift c s fun c v =>
      lift c (e.replace fun x => if x == s then some v else none) k
  throwError "#lean_wf_func_to_term: call in an unsupported position{indentExpr e}"

/-- `let v := g args in k` for the global function `gi` (signature `sig`): the arguments `pre`
(tag and object arguments) are evaluated first; the padding of a function captured together
with a specialised function is added. -/
partial def gCallStx (c : Ctx) (gi : GInfo) (sig : FnSig) (pre : List Lean.Expr) (e : Lean.Expr)
    (k : Ctx → Lean.Expr → TermElabM Stx) : TermElabM Stx := do
  let pre := (if gi.tag0 then [mkNatLit 0] else []) ++ pre
  liftMany c pre [] fun c vals => do
    let retTy ← inferType e
    withLocalDeclD `r retTy fun v => do
      let rest ← k { c with vars := v.fvarId! :: c.vars } v
      let pa ← pargsOpt c (vals.map some ++ List.replicate gi.pad none)
      `(WFLang.PCL.Expr.gCall $(gvarStx gi.pos) $pa (by decide) $(← hpreStx c sig) $rest)

/-- A call `e` of the tail-recursive function `ref` (signature `sig`, arguments `args`: the
lifted variables and the object arguments), followed by the rest of the computation `k`, as a
**loop inside the caller**:

```
join K (v) := ⟦k v⟧ in
joinrec L (x) [R] := ⟦rhs of ref⟧ in
jump L (args)
```

The parameter `x` of `L` is the tuple of the parameters of `ref` (`PCL.tupleTy`); its relation
is Lean's relation for `ref`, read through `PCL.toEnv`.  If the body cannot be translated as a
loop (e.g. a recursive call is not a tail call), the call is a call of a global function
instead. -/
partial def loopStx (c : Ctx) (ref : FnRef) (sig : FnSig) (args : List Lean.Expr)
    (e : Lean.Expr) (k : Ctx → Lean.Expr → TermElabM Stx) : TermElabM Stx := do
  liftMany c args [] fun c vals => do
    let d := c.joins.length
    let v0 := c.vars.length
    let saved ← saveState
    let restoreG ← c.gcheckpoint
    let parts? ← try some <$> loopParts c ref sig d v0 catch _ => do
      restoreState saved
      restoreG
      pure none
    let some (R, wf, body) := parts? |
      -- not a loop after all: a global function
      gCallStx c (← c.gref ref) sig vals e k
    let retTy ← inferType e
    let ps ← exprToSyntax (mkTyList sig.argTys)
    let kBody ← withLocalDeclD `v retTy fun v => k { c with vars := v.fvarId! :: c.vars } v
    let entry ← `(WFLang.PCL.Expr.jump WFLang.PCL.JVar.here $(← pexpr c (← mkTuple vals))
      (by decide) (fun _ _ => trivial) (fun _ _ _ h => h))
    `(WFLang.PCL.Expr.join $(← tyStx retTy) (fun _ _ => True) $kBody
        (WFLang.PCL.Expr.joinrec (WFLang.PCL.tupleTy $ps) (fun _ _ => True)
          (fun _ x y => $R (WFLang.PCL.toEnv $ps x) (WFLang.PCL.toEnv $ps y))
          (fun _ => InvImage.wf _ $wf) $body $entry))

/-- The relation, well-foundedness proof and body of the recursive join point `L` capturing the
tail-recursive function `ref`, called from the context `c` (with `d` join points and `v0`
variables in scope; the join point `K` of the rest of the computation is the `d`-th). -/
partial def loopParts (c : Ctx) (ref : FnRef) (sig : FnSig) (d v0 : Nat) :
    TermElabM (Stx × Stx × Stx) := do
  let some (R, wf, lemmasE) ← closedFixOf ref |
    throwError "#lean_wf_func_to_term: {ref.name} is not defined by well-founded recursion"
  let lemmas ← lemmasE.mapM exprToSyntax
  let decTac ← `(tactic| wf_dec [WFLang.PCL.JVar.pre, WFLang.PCL.toEnv_cons, WFLang.PCL.toEnv_one])
  let body ← withEqnRhs' ref fun ys xs rhs => do
    let params := ys ++ (sig.objPos.map (xs[·]!)).toArray
    let T ← mkTupleTy (← params.toList.mapM fun p => inferType p)
    withLocalDeclD `x T fun st => do
      let projs ← tupleProjs st params.size
      let rhs := rhs.replaceFVars params projs
      unless ← tailRecOnly ref.name rhs do
        throwError "#lean_wf_func_to_term: {ref.name} is not tail-recursive"
      let c' : Ctx := { c with
        fn := ref.name, vars := st.fvarId! :: c.vars, lemmas, decTac := some decTac,
        callees := ← calleeKinds ref.name rhs, fnSig? := none, hasPost := false, group := #[],
        specFns := ← specFnsIn ref.name rhs, selfExtra := [],
        selfSpec := (sig.specPos.map (xs[·]!)).map (·.replaceFVars params projs),
        ho := none, hoFound := none, joins := (v0 + 1) :: v0 :: c.joins,
        loop? := some { ref, sig, dL := d + 1, vL := v0 + 1,
                        extra := (projs.extract 0 ys.size).toList },
        exitK := some (d, v0) }
      stmt c' rhs
  return (← exprToSyntax R, ← exprToSyntax wf, body)

/-- `WFLang.whileWF R wf inv cond body step init hinit` (a well-founded `while` loop) in
non-tail position, followed by the rest of the computation `k`:
`Expr.whileLoop s init c R wf inv hinit body step (k v)`.  The initial state is evaluated first
(it may contain calls); the test and the body must be call-free.  The relation, the invariant and
the proofs are the Lean ones, as functions of the environment (`envFunStx`): the proof that the
body keeps the invariant and goes down is the Lean proof `step`, and the initial state satisfies
the invariant by the Lean proof `hinit`. -/
partial def whileStx (c : Ctx) (e : Lean.Expr) (k : Ctx → Lean.Expr → TermElabM Stx) :
    TermElabM Stx := do
  let args := e.getAppArgs
  let (β, R, wf, inv, cf, bf, step, init, hb) :=
    (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!, args[8]!)
  lift c init fun c init' => do
    let sTy ← tyStx β
    let (cStx, bStx) ← withLocalDeclD `x β fun x => do
      let c' := { c with vars := x.fvarId! :: c.vars }
      let cx := (mkApp cf x).headBeta
      let bx := (mkApp bf x).headBeta
      if hasCall c' cx || hasCall c' bx then
        throwError "#lean_wf_func_to_term: a call (or a loop) inside the test or the body of a `while` loop is not supported{indentExpr e}"
      return (← pexpr c' cx, ← pexpr c' bx)
    let initStx ← pexpr c init'
    let RStx ← envFunStx c R
    let wfStx ← envFunStx c wf
    let invStx ← envFunStx c inv
    let stepStx ← envFunStx c step
    -- `hinit` of the Lean loop, for the initial state (after its calls have been evaluated)
    let hbStx ← envFunStx c (hb.replace fun x => if x == init then some init' else none)
    let hinit ← `(fun e _ => by
      have h := $hbStx e
      first
        | exact h
        | (simp only [wflang_eval] at h ⊢; first | exact h | simpa using h)
        | simp_all [wflang_eval])
    let post ← `(fun e g => by
      obtain ⟨x, e⟩ := e
      have hc : _ = true := g.2.2
      have h := $stepStx e x g.2.1 (by first | exact hc | simpa [wflang_eval] using hc)
      first
        | exact h
        | simpa [wflang_eval] using h)
    let rest ← withLocalDeclD `v β fun v => k { c with vars := v.fvarId! :: c.vars } v
    `(WFLang.PCL.Expr.whileLoop $sTy $initStx (by decide) $cStx (by decide) $RStx $wfStx $invStx
        $hinit $bStx (by decide) $post $rest)

/-- `List.map f l` in non-tail position, followed by the rest of the computation `k`:
`Expr.map s u l (⟦f x⟧) (k v)`.  The list is evaluated first (it may contain calls); the body
`f x` is a statement over one more variable `x`, which may make calls (recursive calls
included), with no join point in scope.

**Proofs are erased.**  For `l.attach.map f` (`f : {x // x ∈ l} → β`, whose argument carries
the membership proof that a termination proof needs), the program maps over `l` itself: the
body is `f ⟨x, hx⟩` for a local hypothesis `hx : x ∈ l`, with the matches on the pair and the
projections `⟨x, hx⟩.1` reduced, so that `hx` only remains in proofs.  The membership is part of
the path condition of the body of `Expr.map`, where the decrease proofs find it. -/
partial def mapStx (c : Ctx) (e : Lean.Expr) (k : Ctx → Lean.Expr → TermElabM Stx) :
    TermElabM Stx := do
  let args := e.getAppArgs
  let (β, f, l) := (args[1]!, args[2]!, args[3]!)
  let l := (← instantiateMVars l).consumeMData
  let attach := l.isAppOfArity ``List.attach 2
  let (α, l0) := if attach then (l.getArg! 0, l.getArg! 1) else (args[0]!, l)
  lift c l0 fun c l' => do
    let rest ← withLocalDeclD `v (← mkAppM ``List #[β]) fun v =>
      k { c with vars := v.fvarId! :: c.vars } v
    let body ← withLocalDeclD `x α fun x => do
      let c' : Ctx := { c with
        vars := x.fvarId! :: c.vars, joins := [], exitK := none, hasPost := false,
        loop? := none }
      if attach then
        let memTy ← mkAppM ``Membership.mem #[l', x]
        withLocalDeclD `hx memTy fun hx => do
          let arg ← mkAppOptM ``Subtype.mk #[α, some (← mkLambdaFVars #[x]
            (← mkAppM ``Membership.mem #[l', x])), x, hx]
          let b ← eraseSubtypeArg hx (mkApp f arg).headBeta
          stmt c' b
      else
        stmt c' (mkApp f x).headBeta
    `(WFLang.PCL.Expr.map $(← tyStx α) $(← tyStx β) $(← pexpr c l') (by decide) $body $rest)

partial def liftMany (c : Ctx) (es : List Lean.Expr) (acc : List Lean.Expr)
    (k : Ctx → List Lean.Expr → TermElabM Stx) : TermElabM Stx :=
  match es with
  | [] => k c acc.reverse
  | e :: es => lift c e fun c e' => liftMany c es (e' :: acc) k

/-- A value in tail position: `ret e` (with the proof of the postcondition, if any), or, in the
body of a loop, `jump K e` (the rest of the computation after the loop). -/
partial def tailStx (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  match c.exitK with
  | some (dK, vK) =>
    `(WFLang.PCL.Expr.jump $(← jvarAt c dK vK) $(← pexpr c e) (by decide) (fun _ _ => trivial)
        (fun _ _ _ h => h))
  | none => `(WFLang.PCL.Expr.ret $(← pexpr c e) (by decide) $(← postStx c))

/-- In the body of a loop capturing `li.ref`: the tail call `e` of `li.ref` is a back edge
`jump L args`, with the proof that `args` goes down along the relation of the loop. -/
partial def backEdgeStx (c : Ctx) (li : LoopInfo) (e : Lean.Expr) : TermElabM Stx := do
  let args := e.getAppArgs
  unless args.size == li.sig.arity do
    throwError "#lean_wf_func_to_term: partial application of {li.ref.name} (function values are not supported){indentExpr e}"
  for (p, v) in li.sig.specPos.zip c.selfSpec do
    unless ← isDefEq args[p]! v do
      throwError "#lean_wf_func_to_term: the recursive call changes the function argument of {li.ref.name}{indentExpr e}"
  liftMany c (li.extra ++ objArgs li.sig args) [] fun c vals => do
    `(WFLang.PCL.Expr.jump $(← jvarAt c li.dL li.vL) $(← pexpr c (← mkTuple vals)) (by decide)
        $(← decStx c) (fun _ _ _ h => h))

/-- A Lean expression in tail position, as a statement. -/
partial def stmt (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if !hasCall c e then return ← tailStx c e
  if let some li := c.loop? then
    if e.getAppFn.isConstOf li.ref.name then return ← backEdgeStx c li e
  if e.isLet && hasCall c e.letValue! then
    return ← lift c e.letValue! fun c v => stmt c (e.letBody!.instantiate1 v)
  if let some e' ← unfoldStep? e then return ← stmt c e'
  if let some (t, a, b) ← branch? e then
    return ← lift c t.expr fun c cnd => do
      iteStx c (t.withExpr cnd) (stmt c a) (stmt c b)
  lift c e tailStx
end

/-- `ret e`, with the proof of the postcondition (if any). -/
def retStx (c : Ctx) (e : Lean.Expr) : TermElabM Stx := do
  `(WFLang.PCL.Expr.ret $(← pexpr c e) (by decide) $(← postStx c))

end WFLang.Capture
