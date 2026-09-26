import RequestProject.WFLang.Capture.Meta.Fix
import RequestProject.WFLang.Core.ListLoops
import RequestProject.WFLang.Core.MoreCombinators

/-!
# Capture metaprogramming: calls to other functions and bounded loops

The attribute `@[inlinable]`, user-defined callees (`userCallees`), the evaluation of calls
with known arguments (`foldCall?`, `foldCalls`), the inlining of non-recursive functions
(`inlineCalls`), and the normalisation of bounded loops (`normLoops`).
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-! ## Calls to other functions -/

/-- `@[inlinable]` marks a function whose calls `#lean_wf_func_to_term` inlines: a
non-recursive function is replaced by its body, a tail-recursive one becomes a loop (a
recursive join point) at the call site, and a recursive one with non-tail self calls becomes a
global function after all.  The calls of the functions *not* marked `@[inlinable]` are
calls of **global functions**: each such function is captured once, as an entry of the global
context of the program, and called from there (`Expr.gCall`). -/
initialize inlinableAttr : TagAttribute ←
  registerTagAttribute `inlinable
    "#lean_wf_func_to_term inlines the calls of this function (otherwise it is a global function of the captured program)"

/-- Is `c` marked `@[inlinable]`? -/
def isInlinable (c : Name) : CoreM Bool :=
  return inlinableAttr.hasTag (← getEnv) c


/-- Is `c` a constant of a library (`Init`, `Std`, `Lean`, `Mathlib`, `Batteries`)?  Library
functions are primitives of the translation or unsupported, never inlined. -/
def isLibraryConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? c | return false
  let mod := env.header.moduleNames[idx.toNat]!
  return [`Init, `Std, `Lean, `Mathlib, `Batteries].contains mod.getRoot

/-- Is `c` an internal name (an auxiliary definition)?  Private names count as user names. -/
def isInternalName (c : Name) : Bool :=
  ((privateToUserName? c).getD c).isInternal

/-- Is `c` a user-defined first-order function (`Nat`/`Bool` parameters and result), other
than `fn`? -/
def isUserFn (fn c : Name) : MetaM Bool := do
  if c == fn || isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  unless (← getConstInfo c).isDefinition do return false
  try discard <| signatureOf c; return true catch _ => return false

/-- The user-defined first-order functions (other than `fn`) that occur in `e`. -/
def userCallees (fn : Name) (e : Lean.Expr) : MetaM (Array Name) :=
  e.getUsedConstants.filterM (isUserFn fn)

/-! ## Calls with known arguments -/

/-- `set_option wfLang.foldCalls false` turns off the evaluation, at capture time, of the calls
of user-defined functions whose arguments are all known (see `foldCall?`). -/
register_option wfLang.foldCalls : Bool := {
  defValue := true
  descr := "#lean_wf_func_to_term evaluates the calls of user functions whose arguments are all known (closed terms)"
}

/-- The value of the closed term `e` of an object type (`Nat`, `Bool`, `Int`, pairs, lists), as a
literal, computed by the kernel (the same evaluation that checks `decide +kernel`), if the
kernel reduces it to constructors. -/
partial def kernelValue? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty ← whnfR (← inferType e)
  let env ← getEnv
  let whnfK (x : Lean.Expr) : Option Lean.Expr :=
    match Kernel.whnf env {} x with
    | .ok v => some v
    | .error _ => none
  let rec natVal? (x : Lean.Expr) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match whnfK x with
      | some (.lit (.natVal n)) => some n
      | some v =>
        if v.isConstOf ``Nat.zero then some 0
        else if v.isAppOfArity ``Nat.succ 1 then (natVal? (v.getArg! 0) fuel).map (· + 1)
        else none
      | none => none
  if ty.isConstOf ``Nat then
    return (natVal? e 64).map mkNatLit
  if ty.isConstOf ``Bool then
    let some v := whnfK e | return none
    return if v.isConstOf ``Bool.true || v.isConstOf ``Bool.false then some v else none
  if ty.isConstOf ``Int then
    let some v := whnfK e | return none
    if v.isAppOfArity ``Int.ofNat 1 then
      return (natVal? (v.getArg! 0) 64).map fun n => toExpr (n : Int)
    if v.isAppOfArity ``Int.negSucc 1 then
      return (natVal? (v.getArg! 0) 64).map fun n => toExpr (-((n : Int) + 1))
    return none
  if ty.isAppOfArity ``Prod 2 then
    let some v := whnfK e | return none
    unless v.isAppOfArity ``Prod.mk 4 do return none
    let some a ← kernelValue? (v.getArg! 2) | return none
    let some b ← kernelValue? (v.getArg! 3) | return none
    return some (mkApp4 v.getAppFn (ty.getArg! 0) (ty.getArg! 1) a b)
  if ty.isAppOfArity ``List 1 then
    let some v := whnfK e | return none
    if v.isAppOfArity ``List.nil 1 then return some (mkApp v.getAppFn (ty.getArg! 0))
    unless v.isAppOfArity ``List.cons 3 do return none
    let some h ← kernelValue? (v.getArg! 1) | return none
    let some t ← kernelValue? (v.getArg! 2) | return none
    return some (mkApp3 v.getAppFn (ty.getArg! 0) h t)
  return none

/-- Is `c` a user-defined first-order function whose calls with known arguments can be
evaluated: a function of the user (not of a library, nor of this project's own definitions),
not a matcher, with object parameters and an object result that is not a subtype. -/
def isFoldableFn (c : Name) : MetaM Bool := do
  if isInternalName c || (← isLibraryConst c) || (← isMatcher c) then return false
  if (`WFLang).isPrefixOf c then return false
  unless (← getConstInfo c).isDefinition do return false
  try
    let sig ← fnSig c
    return !sig.subtypeRet && sig.specPos.isEmpty && sig.prfPos.isEmpty
  catch _ => return false

/-- **Evaluation of calls with known arguments.**  If `e` is a fully applied call `g a₁ … aₙ` of
a user-defined function `g` (other than `fn`, whether `g` is `@[inlinable]`, a global function
or a loop) whose arguments are all known (`e` is a closed term), the value
of `e` as a literal.  The capture replaces such a call by its value (so `g` is neither inlined
nor put in the global context for that call), and the agreement tactic proves the equation
`g a₁ … aₙ = v` by kernel evaluation (`wfFoldCalls`).  Turned off by
`set_option wfLang.foldCalls false`. -/
def foldCall? (fn : Name) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless wfLang.foldCalls.get (← getOptions) do return none
  let .const c _ := e.getAppFn | return none
  if c == fn then return none
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  unless ← isFoldableFn c do return none
  unless e.getAppNumArgs == (← fnSig c).arity do return none
  kernelValue? e

/-- The simplification procedure of the agreement proofs matching the evaluation of calls with
known arguments by the capture (`foldCall?`): it rewrites `g a₁ … aₙ` (closed) to its value
`v`, with the proof `of_decide_eq_true rfl`, checked by the kernel. -/
simproc_decl wfFoldCalls (_) := fun e => do
  let some v ← foldCall? .anonymous e | return .continue
  let p ← mkEq e v
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  return .done { expr := v, proof? := some pf }

/-- Replace the calls with known arguments in `e` by their values (`foldCall?`), outside
proofs. -/
def foldCalls (fn : Name) (e : Lean.Expr) : MetaM Lean.Expr := do
  unless wfLang.foldCalls.get (← getOptions) do return e
  Meta.transform e
    (pre := fun e => do
      if e.isApp && !e.hasLooseBVars then
        if (← try isProof e catch _ => pure false) then return .done e
      return .continue)
    (post := fun e => do
      if let some v ← foldCall? fn e then return .done v
      return .continue)

/-- Inline the fully applied calls of the *non-recursive* user-defined functions marked
`@[inlinable]` in `e` (using their unfolding equations `g.eq_def`, transitively), and replace
the calls with known arguments by their values (`foldCall?`, outside proofs).  Returns the new
term and the unfolding equations used.  The calls of the other non-recursive functions stay:
they become calls of global functions. -/
def inlineCalls (fn : Name) (e : Lean.Expr) : MetaM (Lean.Expr × Array Name) := do
  let used ← IO.mkRef (#[] : Array Name)
  let e ← foldCalls fn e
  let e ← Meta.transform e (post := fun e => do
    let .const c _ := e.getAppFn | return .continue
    unless ← isUserFn fn c do return .continue
    unless ← isInlinable c do return .continue
    if ← isWFRec c then return .continue
    let (argTys, _) ← signatureOf c
    unless e.getAppNumArgs == argTys.length do return .continue
    let some eqn ← getUnfoldEqnFor? c (nonRec := true) | return .continue
    let ty ← instantiateForall (← inferType (← mkConstWithLevelParams eqn)) e.getAppArgs
    let some (_, _, rhs) := ty.eq? | return .continue
    if (rhs.find? (·.isConstOf c)).isSome then return .continue
    used.modify fun u => if u.contains eqn then u else u.push eqn
    return .visit rhs)
  return (← foldCalls fn e, ← used.get)

/-! ## Bounded loops -/

/-- The value `t` of a loop body that always continues with `ForInStep.yield t` (through
`let`s and `if`s), if it does. -/
partial def yieldVal? (m : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let m := m.consumeMData
  if m.isLet then return ← yieldVal? (m.letBody!.instantiate1 m.letValue!)
  if m.isAppOfArity ``ForInStep.yield 2 then return some (m.getArg! 1)
  if m.isAppOfArity ``ite 5 then
    let some a ← yieldVal? (m.getArg! 3) | return none
    let some b ← yieldVal? (m.getArg! 4) | return none
    return some (mkAppN m.getAppFn #[← inferType a, m.getArg! 1, m.getArg! 2, a, b])
  return none

/-- `for i in [a:b] do …` (in `Id`, step `1`, a body that always continues) as
`WFLang.rangeLoop (fun i s => …) b a init`. -/
def rangeLoopOfForIn? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless (e.getArg! 1).isConstOf ``Std.Legacy.Range do return none
  let r ← whnfD (e.getArg! 5)
  unless r.isAppOfArity ``Std.Legacy.Range.mk 4 do return none
  unless (← evalNat (r.getArg! 2)) == some 1 do return none
  let body := e.getArg! 7
  lambdaBoundedTelescope body 2 fun zs m => do
    unless zs.size == 2 do return none
    let some t ← yieldVal? m | return none
    return some (← mkAppM ``WFLang.rangeLoop
      #[← mkLambdaFVars zs t, r.getArg! 1, r.getArg! 0, e.getArg! 6])

/-- `Nat.fold n (fun i _ acc => …) init` (the body does not use the proof `i < n`) as
`WFLang.rangeLoop (fun i acc => …) n 0 init`. -/
def rangeLoopOfFold? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  lambdaBoundedTelescope (e.getArg! 2) 3 fun zs b => do
    unless zs.size == 3 do return none
    if b.containsFVar zs[1]!.fvarId! then return none
    return some (← mkAppM ``WFLang.rangeLoop
      #[← mkLambdaFVars #[zs[0]!, zs[2]!] b, e.getArg! 1, mkNatLit 0, e.getArg! 3])

/-- `for x in l do …` over a list (in `Id`, a body that always continues) as
`WFLang.listFoldl (fun s x => …) init l`. -/
def listLoopOfForIn? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless (← whnfR (e.getArg! 1)).isAppOfArity ``List 1 do return none
  let body := e.getArg! 7
  lambdaBoundedTelescope body 2 fun zs m => do
    unless zs.size == 2 do return none
    let some t ← yieldVal? m | return none
    return some (← mkAppM ``WFLang.listFoldl #[← mkLambdaFVars #[zs[1]!, zs[0]!] t, e.getArg! 6, e.getArg! 5])

/-- `for i in [a:b:s] do …` (in `Id`) whose body may stop early (`break`, `return`) or whose range
has a step `s ≠ 1`, as `WFLang.rangeLoopN (fun i r => …) size s a init`, where `size` is the number
of iterations `(b - a + s - 1) / s` (`Std.Legacy.Range.size`). -/
def rangeLoopNOfForIn? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless (e.getArg! 1).isConstOf ``Std.Legacy.Range do return none
  let r ← whnfD (e.getArg! 5)
  unless r.isAppOfArity ``Std.Legacy.Range.mk 4 do return none
  let start := r.getArg! 0
  let stop := r.getArg! 1
  let step := r.getArg! 2
  let size ← if (← evalNat step) == some 1 then mkAppM ``HSub.hSub #[stop, start] else
    mkAppM ``HDiv.hDiv #[← mkAppM ``HSub.hSub #[← mkAppM ``HAdd.hAdd
      #[← mkAppM ``HSub.hSub #[stop, start], step], mkNatLit 1], step]
  return some (← mkAppM ``WFLang.rangeLoopN #[e.getArg! 7, size, step, start, e.getArg! 6])

/-- `for x in l do …` over a list (in `Id`) whose body may stop early, as
`WFLang.listLoopN (fun x r => …) l init`. -/
def listLoopNOfForIn? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless (← whnfR (e.getArg! 1)).isAppOfArity ``List 1 do return none
  return some (← mkAppM ``WFLang.listLoopN #[e.getArg! 7, e.getArg! 5, e.getArg! 6])

/-- The library combinators on lists with a function argument, rewritten into the first-order
recursive functions of `Core/ListLoops.lean` (whose function argument is then specialised). -/
def listCombinator? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let args := e.getAppArgs
  -- (a fold over `l.attach` stays: it becomes a `foldl` statement, see `Capture/Stmt.lean`)
  if e.isAppOfArity ``List.foldl 5 && (args[4]!).consumeMData.isAppOfArity ``List.attach 2 then
    return none
  if e.isAppOfArity ``List.foldl 5 then
    return some (← mkAppM ``WFLang.listFoldl #[args[2]!, args[3]!, args[4]!])
  if e.isAppOfArity ``List.foldr 5 then
    return some (← mkAppM ``WFLang.listFoldr #[args[2]!, args[3]!, args[4]!])
  if e.isAppOfArity ``List.any 3 then return some (← mkAppM ``WFLang.listAny #[args[2]!, args[1]!])
  if e.isAppOfArity ``List.all 3 then return some (← mkAppM ``WFLang.listAll #[args[2]!, args[1]!])
  if e.isAppOfArity ``List.find? 3 then
    return some (← mkAppM ``WFLang.listFind? #[args[1]!, args[2]!])
  if e.isAppOfArity ``List.filter 3 then
    return some (← mkAppM ``WFLang.listFilter #[args[1]!, args[2]!])
  -- `l.contains a`, `List.elem a l`: `listAny (fun x => a == x) l`
  let beqAny (α inst a l : Lean.Expr) : MetaM Lean.Expr := do
    let p ← withLocalDeclD `x α fun x => do
      mkLambdaFVars #[x] (mkApp4 (mkConst ``BEq.beq [← getLevel α]) α inst a x)
    mkAppM ``WFLang.listAny #[p, l]
  if e.isAppOfArity ``List.contains 4 then
    return some (← beqAny args[0]! args[1]! args[3]! args[2]!)
  if e.isAppOfArity ``List.elem 4 then
    return some (← beqAny args[0]! args[1]! args[2]! args[3]!)
  -- `Core/MoreCombinators.lean`
  if e.isAppOfArity ``List.zipWith 6 then
    return some (← mkAppM ``WFLang.listZipWith #[args[3]!, args[4]!, args[5]!])
  if e.isAppOfArity ``List.partition 3 then
    let p := args[1]!
    let np ← withLocalDeclD `x args[0]! fun x => do
      mkLambdaFVars #[x] (← mkAppM ``not #[(mkApp p x).headBeta])
    return some (← mkAppM ``Prod.mk #[← mkAppM ``WFLang.listFilter #[p, args[2]!],
      ← mkAppM ``WFLang.listFilter #[np, args[2]!]])
  if e.isAppOfArity ``List.countP 3 then
    let p := args[1]!
    let nat := Lean.mkConst ``Nat
    let f ← withLocalDeclD `n nat fun n => withLocalDeclD `x args[0]! fun x => do
      let c ← mkEq (mkApp p x).headBeta (Lean.mkConst ``Bool.true)
      mkLambdaFVars #[n, x] (← mkAppOptM ``ite #[nat, c, none,
        ← mkAppM ``HAdd.hAdd #[n, mkNatLit 1], n])
    return some (← mkAppM ``WFLang.listFoldl #[f, mkNatLit 0, args[2]!])
  -- the array combinators, on the whole array (default bounds)
  let wholeArray (a start stop : Lean.Expr) : MetaM Bool := do
    unless (← evalNat start) == some 0 do return false
    isDefEq stop (← mkAppM ``Array.size #[a])
  if e.isAppOfArity ``Array.foldl 7 then
    if ← wholeArray args[4]! args[5]! args[6]! then
      return some (← mkAppM ``WFLang.listFoldl #[args[2]!, args[3]!, ← mkAppM ``Array.toList #[args[4]!]])
  if e.isAppOfArity ``Array.foldr 7 then
    if ← wholeArray args[4]! args[6]! args[5]! then
      return some (← mkAppM ``WFLang.listFoldr #[args[2]!, args[3]!, ← mkAppM ``Array.toList #[args[4]!]])
  if e.isAppOfArity ``Array.map 4 then
    return some (← mkAppM ``List.toArray #[← mkAppM ``List.map #[args[2]!, ← mkAppM ``Array.toList #[args[3]!]]])
  if e.isAppOfArity ``Array.any 5 then
    if ← wholeArray args[1]! args[3]! args[4]! then
      return some (← mkAppM ``WFLang.listAny #[args[2]!, ← mkAppM ``Array.toList #[args[1]!]])
  if e.isAppOfArity ``Array.all 5 then
    if ← wholeArray args[1]! args[3]! args[4]! then
      return some (← mkAppM ``WFLang.listAll #[args[2]!, ← mkAppM ``Array.toList #[args[1]!]])
  if e.isAppOfArity ``Array.contains 4 then
    return some (← beqAny args[0]! args[1]! args[3]! (← mkAppM ``Array.toList #[args[2]!]))
  return none

/-- A proposition with a bounded quantifier, `∀ i < n, P i`, `∃ i < n, P i`, `∀ x ∈ l, P x` or
`∃ x ∈ l, P x` (with `P` decidable), as the boolean `listAll (fun i => decide (P i)) (List.range n)`
(resp. `listAny`, on `l`): see `Core/ListLoops.lean`. -/
def boundedQuant? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  -- `(forall, bound, P)`: `bound` is `some n` for `i < n`, `none` with the list `l` for `x ∈ l`
  let mk (isAll : Bool) (x : Lean.Expr) (dom : Lean.Expr) (bound : Lean.Expr) (isRange : Bool)
      (P : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some _ ← (try some <$> tyOf dom catch _ => pure none) | return none
    let p ← (try some <$> mkLambdaFVars #[x] (← mkDecide P) catch _ => pure none)
    let some p := p | return none
    let l ← if isRange then mkAppM ``List.range #[bound] else pure bound
    return some (← mkAppM (if isAll then ``WFLang.listAll else ``WFLang.listAny) #[p, l])
  if let .forallE n dom (.forallE _ hyp body _) bi := e then
    if body.hasLooseBVar 0 then return none
    return ← withLocalDecl n bi dom fun x => do
      let hyp := hyp.instantiate1 x
      let P := body.lowerLooseBVars 1 1 |>.instantiate1 x
      if hyp.isAppOfArity ``LT.lt 4 && (hyp.getArg! 0).isConstOf ``Nat && hyp.getArg! 2 == x &&
          !(hyp.getArg! 3).containsFVar x.fvarId! then
        return ← mk true x dom (hyp.getArg! 3) true P
      if hyp.isAppOfArity ``Membership.mem 5 && hyp.getArg! 4 == x &&
          (← whnfR (hyp.getArg! 1)).isAppOfArity ``List 1 && !(hyp.getArg! 3).containsFVar x.fvarId! then
        return ← mk true x dom (hyp.getArg! 3) false P
      return none
  if e.isAppOfArity ``Exists 2 then
    let .lam n dom body bi := e.getArg! 1 | return none
    return ← withLocalDecl n bi dom fun x => do
      let b := body.instantiate1 x
      unless b.isAppOfArity ``And 2 do return none
      let hyp := b.getArg! 0
      let P := b.getArg! 1
      if hyp.isAppOfArity ``LT.lt 4 && (hyp.getArg! 0).isConstOf ``Nat && hyp.getArg! 2 == x &&
          !(hyp.getArg! 3).containsFVar x.fvarId! then
        return ← mk false x dom (hyp.getArg! 3) true P
      if hyp.isAppOfArity ``Membership.mem 5 && hyp.getArg! 4 == x &&
          (← whnfR (hyp.getArg! 1)).isAppOfArity ``List 1 && !(hyp.getArg! 3).containsFVar x.fvarId! then
        return ← mk false x dom (hyp.getArg! 3) false P
      return none
  return none

/-- Remove the `Id` monad (`Id.run`, `bind`, `pure`) and rewrite bounded loops (`for` over a
range, `Nat.fold`) into `WFLang.rangeLoop`, whose function argument is then specialised, and
`while` loops with a measure (`WFLang.whileMeasure`, the notation `wf_while`) into the general
well-founded loop `WFLang.whileWF`, which becomes a `PCL` `while` statement. -/
def normLoops (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let isId (m : Lean.Expr) := m.isConstOf ``Id
    if e.isAppOfArity ``Id.run 2 then return .visit (e.getArg! 1)
    if e.isAppOfArity ``Bind.bind 6 && isId (e.getArg! 0) then
      return .visit (mkApp (e.getArg! 5) (e.getArg! 4)).headBeta
    if e.isAppOfArity ``Pure.pure 4 && isId (e.getArg! 0) then return .visit (e.getArg! 3)
    if e.isAppOfArity ``ForIn.forIn 8 && isId (e.getArg! 0) then
      if let some r ← rangeLoopOfForIn? e then return .visit r
      if let some r ← listLoopOfForIn? e then return .visit r
      if let some r ← rangeLoopNOfForIn? e then return .visit r
      if let some r ← listLoopNOfForIn? e then return .visit r
    if let some r ← listCombinator? e then return .visit r
    -- bounded quantifiers, in `decide` and in the test of an `if`
    if e.isAppOfArity ``Decidable.decide 2 then
      if let some r ← boundedQuant? (e.getArg! 0) then return .visit r
    if e.isAppOfArity ``ite 5 then
      if let some r ← boundedQuant? (e.getArg! 1) then
        let c ← mkEq r (mkConst ``Bool.true)
        return .visit (← mkAppOptM ``ite #[e.getArg! 0, c, none, e.getArg! 3, e.getArg! 4])
    if e.isAppOfArity ``Nat.fold 4 then
      if let some r ← rangeLoopOfFold? e then return .visit r
    -- a `while` loop with a measure: the general well-founded loop `whileWF`
    if e.isAppOfArity ``WFLang.whileMeasure 6 then
      if let some r ← unfoldDefinition? e then return .visit r.headBeta
    return .continue)

end WFLang.Meta
