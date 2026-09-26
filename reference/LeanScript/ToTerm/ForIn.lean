module

public import Lean.Meta

@[expose] public section

meta section

/-!
# `for` loops in the identity monad

A `for` loop in `Id` whose body never leaves the loop early is a fold: its value is the
state after the last iteration.  `do` compiles the body to a function answering
`Id (ForInStep β)`, in which every path ends in `pure (ForInStep.yield s')`, possibly
under `let`s (`let mut` updates), join points (`have __do_jp := fun … => …`, which `do`
introduces after an `if` without `else` or with a `continue`), `if`/`if h :`/`match`, and
`>>=` in `Id`.

* `forInYieldValue β e` turns such a body into the **new state** itself, a Lean
  expression of type `β`: `pure (yield s')` becomes `s'`, and the constructs above are kept,
  re-typed at `β`.
* A body some path of which reaches `ForInStep.done s'` (`break`, or `return` out of the
  loop) is still a fold, of the **step** `ForInStep β` rather than the state: it starts
  from `yield init`, a `done` step is kept as it is, from `yield s` the body's step at `s`
  is taken, and the value of the loop is the state of the last step.  `forInBody` reads
  such a body as its step (an expression of type `ForInStep β`, the constructs above
  re-typed at it), and tells which of the two kinds of body it has.
* `listForInAsFoldl` uses it for a loop over a **list**: `for x in l do body` with initial
  state `init` is `l.foldl (fun s x => body' x s) init` (or the fold of the step), and
  `for h : x in l do body` is the same fold over `l.attach` when the body reads the
  membership proof `h` (the language erases proofs, and `l.attach` is translated as `l`).
  The translator then translates this `List.foldl` as any other.
* `rangeForInBreakAsNatRec` is the fold of the step for `for i in [:n]`, as `Nat.rec`.
* `rangeForInReindex` turns a range with a start or a step into the loop over `[:size]`,
  and `rangeForIn'AsForIn` turns `for h : i in r` over a range into a loop that does not
  name the membership proof (guarded by `if hj : j < size` when the body reads `h`).

Each rewriting is proved an equation of Lean's logic in `LeanScript/ListLibraryFacts.lean`.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- The error for a loop body that does not end in a step of the loop. -/
def forInBodyError {α} (e : Expr) : MetaM α :=
  throwError "`#leanscript_to_term`: the body of this `for` does not end in a step of the \
    loop (`ForInStep.yield` or `ForInStep.done`):{indentExpr e}"

/-- The body of a `for` in `Id`, an expression of type `Id (ForInStep β)`, pushed down to
    its steps.

    With `step := false`, every path must yield, and the answer is the state it yields
    (an expression of type `β`); a path that reaches `ForInStep.done` is refused.  With
    `step := true` the answer is the step itself, an expression of type `ForInStep β`
    whose paths end in `ForInStep.yield s'` or `ForInStep.done s'`.  See the module
    header. -/
partial def forInBodyAux (β : Expr) (step : Bool) (e0 : Expr) : MetaM Expr := do
  let ρ ← if step then mkAppM ``ForInStep #[β] else pure β
  let e := e0.consumeMData.headBeta
  match e with
  | .letE n t v b nonDep =>
      -- a join point is a function: substitute it, so that each call to it becomes a
      -- β-redex whose body is a path of the loop
      if v.consumeMData.isLambda then
        return ← forInBodyAux β step (b.instantiate1 v)
      return ← withLetDecl n t v (nondep := nonDep) fun x => do
        let b' ← forInBodyAux β step (b.instantiate1 x)
        return .letE n t v (b'.abstract #[x]) nonDep
  | _ => pure ()
  match e.getAppFnArgs with
  | (``Pure.pure, #[_, _, _, v]) => return ← forInBodyAux β step v
  | (``Bind.bind, #[_, _, _, _, x, f]) => return ← forInBodyAux β step (mkApp f x)
  | (``ForInStep.yield, #[_, v]) => return if step then e else v
  | (``ForInStep.done, #[_, _]) =>
      if step then return e
      throwError "`#leanscript_to_term`: internal: a `break` read as a state"
  | (``ite, #[_, c, inst, a, b]) =>
      let u ← getLevel ρ
      return mkApp5 (mkConst ``ite [u]) ρ c inst (← forInBodyAux β step a)
        (← forInBodyAux β step b)
  | (``dite, #[_, c, inst, a, b]) =>
      let u ← getLevel ρ
      let branch (f : Expr) : MetaM Expr := do
        let f ← if f.isLambda then pure f else etaExpand f
        lambdaBoundedTelescope f 1 fun hs body => do
          mkLambdaFVars hs (← forInBodyAux β step body)
      return mkApp5 (mkConst ``dite [u]) ρ c inst (← branch a) (← branch b)
  | _ => pure ()
  if let some mapp ← matchMatcherApp? e then
    let motive ← lambdaTelescope mapp.motive fun xs _ => mkLambdaFVars xs ρ
    let alts ← mapp.alts.mapIdxM fun i alt =>
      lambdaBoundedTelescope alt (mapp.altNumParams[i]!) fun xs body => do
        mkLambdaFVars xs (← forInBodyAux β step body)
    let uElim ← getLevel ρ
    let mapp := { mapp with motive, alts }
    let mapp ← match mapp.uElimPos? with
      | some pos => pure { mapp with matcherLevels := mapp.matcherLevels.set! pos uElim }
      | none => pure mapp
    return mapp.toExpr
  -- anything else: unfold it one step and look again
  let e' ← whnfCore e
  if e' != e then return ← forInBodyAux β step e'
  let e' ← whnf e
  if e' != e then return ← forInBodyAux β step e'
  forInBodyError e

/-- The body of a `for` in `Id` that always yields, as the state it yields (an expression
    of type `β`).  See `forInBodyAux`. -/
def forInYieldValue (β : Expr) (e : Expr) : MetaM Expr :=
  forInBodyAux β false e

/-- The body of a `for` in `Id`, read as the loop needs it: when no path leaves the loop,
    the state it yields (of type `β`) and `false`; otherwise the step it answers (of type
    `ForInStep β`, a `ForInStep.done` on the paths that `break` or `return`) and
    `true`. -/
def forInBody (β : Expr) (e : Expr) : MetaM (Expr × Bool) := do
  let stepE ← forInBodyAux β true e
  if (stepE.find? (·.isConstOf ``ForInStep.done)).isSome then
    return (stepE, true)
  return (← forInBodyAux β false e, false)

/-- `ForInStep.casesOn t done yield`, at the non-dependent motive `ρ`. -/
def mkForInStepCases (β ρ t done yield : Expr) : MetaM Expr := do
  let u ← getDecLevel β
  let w ← getLevel ρ
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  let motive := mkLambda `_ .default stepTy ρ
  return mkAppN (mkConst ``ForInStep.casesOn [w, u]) #[β, motive, t, done, yield]

/-- The state a step carries, whether the loop goes on or stops (`ForInStep.value`, as a
    case analysis). -/
def mkForInStepState (β t : Expr) : MetaM Expr := do
  let idβ := mkLambda `s .default β (.bvar 0)
  mkForInStepCases β β t idβ idβ

/-- The step of a loop that can stop, as a function of the step before it: a loop that
    has stopped stays stopped (`ForInStep.done s` is kept), and one that goes on with the
    state `s` takes the step `next` (an expression in the free variable `s`).  `k` gets
    the free variable of the step before and this step. -/
def withForInStepAfter {γ} (β s next : Expr) (k : Expr → Expr → MetaM γ) : MetaM γ := do
  let stepTy ← mkAppM ``ForInStep #[β]
  withLocalDeclD `step stepTy fun st => do
    let u ← getDecLevel β
    let done := mkLambda `s .default β (mkApp2 (mkConst ``ForInStep.done [u]) β (.bvar 0))
    let yield ← mkLambdaFVars #[s] next
    k st (← mkForInStepCases β stepTy st done yield)

/-- `for x in l do body` (`forIn l init body`, `withProof := false`) or
    `for h : x in l do body` (`forIn' l init body`, `withProof := true`), in `Id`, over a
    list `l : List α`, as the `List.foldl` it computes.  See the module header. -/
def listForInAsFoldl (α β l init body : Expr) (withProof : Bool) : MetaM Expr := do
  let u ← getDecLevel β
  let v ← getDecLevel α
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  -- the fold over the elements `xs : List γ` whose element is the free variable `x` and
  -- whose body, read with the state `s`, is `next` (a state, or a step when `breaks`)
  let fold (s next : Expr) (breaks : Bool) (γ x xs : Expr) : MetaM Expr := do
    let w ← getDecLevel γ
    unless breaks do
      return mkApp5 (mkConst ``List.foldl [u, w]) β γ (← mkLambdaFVars #[s, x] next) init xs
    withForInStepAfter β s next fun st after => do
      let f ← mkLambdaFVars #[st, x] after
      let init' := mkApp2 (mkConst ``ForInStep.yield [u]) β init
      mkForInStepState β (mkApp5 (mkConst ``List.foldl [u, w]) stepTy γ f init' xs)
  withLocalDeclD `x α fun x => withLocalDeclD `state β fun s => do
    if !withProof then
      let (next, breaks) ← forInBody β (mkApp2 body x s)
      return ← fold s next breaks α x l
    let hTy := (← whnf (← inferType body)).bindingBody!.bindingDomain!
    withLocalDeclD `h (hTy.instantiate1 x) fun h => do
      let (next, breaks) ← forInBody β (mkApp3 body x h s)
      unless next.containsFVar h.fvarId! do
        return ← fold s next breaks α x l
      -- the proof is read: fold over `l.attach`, whose elements carry it
      let attached := mkApp2 (mkConst ``List.attach [v]) α l
      let γ := (← whnf (← inferType attached)).appArg!
      withLocalDeclD `p γ fun p => do
        let pv ← mkAppM ``Subtype.val #[p]
        let ph ← mkAppM ``Subtype.property #[p]
        let next' := (next.replaceFVar x pv).replaceFVar h ph
        fold s next' breaks γ p attached

/-- `for i in [:n] do body` in `Id` whose body can leave the loop, with initial state
    `init : β`, as a Lean expression: the recursion on `n` whose value is the step after
    `n` iterations — `ForInStep.yield init` at `0`, and after it, the step of the body at
    the index `i` if the loop has not stopped — of which the state is read. -/
def rangeForInBreakAsNatRec (β stop init i s next : Expr) : MetaM Expr := do
  let u ← getDecLevel β
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  let branch ← withForInStepAfter β s next fun st after => mkLambdaFVars #[i, st] after
  let motive := mkLambda `_ .default (mkConst ``Nat) stepTy
  let init' := mkApp2 (mkConst ``ForInStep.yield [u]) β init
  let r := mkApp4 (mkConst ``Nat.rec [← getLevel stepTy]) motive init' branch stop
  mkForInStepState β r

/-- The number of indices of the range `[start:stop:step]`,
    `(stop - start + step - 1) / step` (`Std.Legacy.Range.size`), written without the
    parts that cancel when the start is known to be `0` or the step `1`. -/
def rangeSizeExpr (startE stopE stepE : Expr) (start step : Option Nat) : MetaM Expr := do
  let add (a b : Expr) := mkAppM ``HAdd.hAdd #[a, b]
  let sub (a b : Expr) := mkAppM ``HSub.hSub #[a, b]
  let span ← if start == some 0 then pure stopE else sub stopE startE
  if step == some 1 then return span
  let num ← match step with
    | some k => add span (mkNatLit (k - 1))
    | none => do sub (← add span stepE) (mkNatLit 1)
  mkAppM ``HDiv.hDiv #[num, stepE]

/-- The `j`-th index of the range `[start:stop:step]`, `start + j * step`, written without
    the start when it is known to be `0` and without the step when it is known to be
    `1`. -/
def rangeIndexExpr (startE stepE : Expr) (start step : Option Nat) (j : Expr) :
    MetaM Expr := do
  let scaled ← if step == some 1 then pure j else mkAppM ``HMul.hMul #[j, stepE]
  if start == some 0 then return scaled
  mkAppM ``HAdd.hAdd #[startE, scaled]

/-- `for h : i in r do body` (`forIn' r init body`) in `Id`, over a range
    `r = [start:stop:step]`, as a loop `for j in [:size] do body'` that does not name the
    membership proof: the body, a function `fun i h s => …` of the index, the proof
    `h : i ∈ r` and the state, is read at the index `start + j * step`, with the proof
    `Std.Legacy.Range.mem_start_add_mul_step r hj` built from the test `hj : j < size` of
    an `if hj : j < size then … else pure (.yield s)` around it.  The test always holds,
    since `j` runs over `[:size]`; it is there because the body needs a proof, and the
    language erases proofs.  Answers the bound `size` and the body `body'`, a function of
    `j` and the state.  The rewriting is
    `LeanScript.ListLibrary.forIn'_range_eq_forIn_guard`.

    When the body does not read `h`, no test is needed: the answer is `none` and the body
    without `h`, and the loop is `forIn r init body'`, over `r` itself. -/
def rangeForIn'AsForIn (β coll startE stopE stepE : Expr) (start step : Option Nat)
    (body : Expr) : MetaM (Option Expr × Expr) := do
  let nat := mkConst ``Nat
  -- the body with the proof dropped, when it does not read it
  let dropped? ← withLocalDeclD `i nat fun i => do
    let bi ← whnfCore (mkApp body i).headBeta
    let .lam _ _ b _ := bi | return none
    if b.hasLooseBVar 0 then return none
    return some (← mkLambdaFVars #[i] (b.lowerLooseBVars 1 1))
  if let some body' := dropped? then return (none, body')
  let size ← rangeSizeExpr startE stopE stepE start step
  let u ← getDecLevel β
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  let idTy := mkApp (mkConst ``Id [u]) stepTy
  let body' ← withLocalDeclD `j nat fun j => withLocalDeclD `state β fun s => do
    let cond ← mkAppM ``LT.lt #[j, size]
    let idx ← rangeIndexExpr startE stepE start step j
    let yes ← withLocalDeclD `hj cond fun hj => do
      let mem := mkApp3 (mkConst `Std.Legacy.Range.mem_start_add_mul_step) coll j hj
      mkLambdaFVars #[hj] (mkApp3 body idx mem s).headBeta
    let no ← withLocalDeclD `hj (mkNot cond) fun hj => do
      let stay := mkApp2 (mkConst ``ForInStep.yield [u]) β s
      mkLambdaFVars #[hj] (← mkAppOptM ``Pure.pure
        #[mkConst ``Id [u], none, stepTy, stay])
    let inst ← synthInstance (mkApp (mkConst ``Decidable) cond)
    let guarded := mkApp5 (mkConst ``dite [← getLevel idTy]) idTy cond inst yes no
    mkLambdaFVars #[j, s] guarded
  return (some size, body')

/-- `for i in [start:stop:step] do body` as a loop over `[:size]`: its iterations are
    the indices `start + j * step` for `j < size`, with
    `size = (stop - start + step - 1) / step` (`Std.Legacy.Range.size`).  Answers the
    bound `size` and the body `fun j => body (start + j * step)`, both Lean expressions;
    the rewriting is `LeanScript.ListLibrary.forIn_range_step_eq`.  A start known to be
    `0` and a step known to be `1` are left out of both (`start`, `step` are the values
    when known). -/
def rangeForInReindex (startE stopE stepE : Expr) (start step : Option Nat) (body : Expr) :
    MetaM (Expr × Expr) := do
  let nat := mkConst ``Nat
  let size ← rangeSizeExpr startE stopE stepE start step
  let body' ← withLocalDeclD `j nat fun j => do
    mkLambdaFVars #[j] (mkApp body (← rangeIndexExpr startE stepE start step j)).headBeta
  return (size, body')

end LeanScript.ToTerm
