import RequestProject.WFLang.Capture.Meta
import RequestProject.WFLang.Core.LeanWhile

/-!
# Capturing Lean's own `while` loops: recognising loops and building the tail-recursive functions

The helpers of `lean_while_to_wf` (`Capture/LeanWhile.lean`): recognising Lean's `while` loops,
tuples of mutable variables, simplification of the generated code, and the loop as a
tail-recursive function.
-/

namespace WFLang.LeanWhile

open Lean Meta Elab Term

/-! ## Recognising loops -/

/-- `@forIn Id Lean.Loop Unit inst β Lean.Loop.mk init body`: `(β, init, body)`. -/
def loopForIn? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``ForIn.forIn 8 && (e.getArg! 0).isConstOf ``Id &&
      (e.getArg! 1).isConstOf ``Lean.Loop then
    some (e.getArg! 4, e.getArg! 6, e.getArg! 7)
  else none

/-- Does `e` contain a Lean `while` loop? -/
def hasLoop (e : Lean.Expr) : Bool :=
  (e.find? fun x => (loopForIn? x).isSome).isSome

/-- `@Bind.bind Id _ α γ x k`: `(α, γ, x, k)`. -/
def idBind? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``Bind.bind 6 && (e.getArg! 0).isConstOf ``Id then
    some (e.getArg! 2, e.getArg! 3, e.getArg! 4, e.getArg! 5)
  else none

/-- `@Pure.pure Id _ α x`: `x`. -/
def idPure? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``Pure.pure 4 && (e.getArg! 0).isConstOf ``Id then some (e.getArg! 3)
  else none

/-! ## Tuples of mutable variables -/

/-- How the mutable variables of a loop are packed into its state `β`: nested `MProd`s (the
legacy `do` elaborator) or nested pairs (the `do` elaborator of Lean ≥ v4.34), with the types
of the variables. -/
structure Layout where
  /-- `MProd τ₁ (MProd τ₂ …)` (otherwise `τ₁ × (τ₂ × …)`) -/
  isM : Bool
  /-- the types of the mutable variables -/
  tys : List Lean.Expr

/-- The number of mutable variables. -/
def Layout.size (l : Layout) : Nat := l.tys.length

/-- The pair constructor and projections of a layout. -/
def Layout.mkN (l : Layout) : Name := if l.isM then ``MProd.mk else ``Prod.mk
/-- The first projection of a layout. -/
def Layout.fstN (l : Layout) : Name := if l.isM then ``MProd.fst else ``Prod.fst
/-- The second projection of a layout. -/
def Layout.sndN (l : Layout) : Name := if l.isM then ``MProd.snd else ``Prod.snd

/-- The types of the nested `MProd τ₁ (MProd τ₂ …)`. -/
partial def mprodTys (β : Lean.Expr) : List Lean.Expr :=
  let β := β.consumeMData
  if β.isAppOfArity ``MProd 2 then β.getArg! 0 :: mprodTys (β.getArg! 1) else [β]

/-- The types `τ₁, …, τₖ` of `τ₁ × (τ₂ × (… × τₖ))`, with at most `k` components. -/
def prodTys (β : Lean.Expr) : Nat → List Lean.Expr
  | 0 | 1 => [β]
  | k + 1 =>
    let β' := β.consumeMData
    if β'.isAppOfArity ``Prod 2 then β'.getArg! 0 :: prodTys (β'.getArg! 1) k else [β]

/-- The projection chains `r.1, r.2.1, …, r.2…2` of the `n` components of a state `r`. -/
def compPaths (fstN sndN : Name) (r : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  let mut paths : Array Lean.Expr := #[]
  let mut cur := r
  for i in [0:n] do
    if i + 1 == n then paths := paths.push cur
    else
      paths := paths.push (← mkAppM fstN #[cur])
      cur ← mkAppM sndN #[cur]
  return paths

/-- The values of the `have`/`let` bindings at the start of `b`. -/
partial def leadingLetValues (b : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out := #[]
  let mut e := b
  repeat
    let .letE _ _ v bd _ := e.consumeMData | break
    out := out.push v.consumeMData
    e := bd.instantiate1 v
  return out

/-- The layout of the state `β` of a loop with body `body` (`fun _ r => …`).  With pairs, the
number of mutable variables is read off the destructuring `have x := r.1`, `have y := r.2.1`, …
at the start of the body (a single mutable variable may itself be a pair). -/
def stateLayout (β body : Lean.Expr) : MetaM Layout := do
  if β.consumeMData.isAppOfArity ``MProd 2 then return { isM := true, tys := mprodTys β }
  let full := prodTys β 1000
  if full.length ≤ 1 then return { isM := false, tys := [β] }
  lambdaBoundedTelescope body 2 fun zs b => do
    unless zs.size == 2 do return { isM := false, tys := [β] }
    let vals := leadingLetValues b
    let mut k := full.length
    while k ≥ 2 do
      let paths ← compPaths ``Prod.fst ``Prod.snd zs[1]! k
      if paths.all (vals.contains ·) then return { isM := false, tys := prodTys β k }
      k := k - 1
    return { isM := false, tys := [β] }

/-- The state `⟨v₁, ⟨v₂, …⟩⟩` of the layout `l`. -/
def mkState (l : Layout) (vs : List Lean.Expr) : MetaM Lean.Expr := do
  let rec go : List Lean.Expr → List Lean.Expr → MetaM Lean.Expr
    | [v], _ => return v
    | v :: vs, _ :: ts => do
      let rest ← go vs ts
      mkAppM l.mkN #[v, rest]
    | _, _ => throwError "lean_while_to_wf: empty loop state"
  go vs l.tys

/-- The components of a loop state `e` of layout `l` (the fields of a literal constructor
application, projections otherwise). -/
def stateComps (l : Layout) (e : Lean.Expr) : MetaM (List Lean.Expr) := do
  let rec go (e : Lean.Expr) : Nat → MetaM (List Lean.Expr)
    | 0 | 1 => return [e]
    | n + 1 => do
      let e' := e.consumeMData.headBeta
      if e'.isAppOfArity l.mkN 4 then
        return e'.getArg! 2 :: (← go (e'.getArg! 3) n)
      return (← mkAppM l.fstN #[e]) :: (← go (← mkAppM l.sndN #[e]) n)
  go e l.size

/-- The tuple `(v₁, (v₂, …))`. -/
def mkTuple : List Lean.Expr → MetaM Lean.Expr
  | [v] => return v
  | v :: vs => do mkAppM ``Prod.mk #[v, ← mkTuple vs]
  | [] => throwError "lean_while_to_wf: empty loop state"

/-- The type `τ₁ × (τ₂ × …)`. -/
def mkTupleTy : List Lean.Expr → MetaM Lean.Expr
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← mkTupleTy ts]
  | [] => throwError "lean_while_to_wf: empty loop state"

/-- The components of a tuple `p` of `n` values. -/
def tupleComps (p : Lean.Expr) (n : Nat) : MetaM (List Lean.Expr) := do
  let mut out := #[]
  let mut cur := p
  for i in [0:n] do
    if i + 1 == n then out := out.push cur
    else
      out := out.push (← mkAppM ``Prod.fst #[cur])
      cur ← mkAppM ``Prod.snd #[cur]
  return out.toList

/-- The names of the mutable variables, read off the `have x := r.fst` bindings at the start of
the loop body `fun _ r => …` (`s₁, s₂, …` if not found). -/
partial def stateNames (l : Layout) (body : Lean.Expr) : MetaM (List Name) := do
  let n := l.size
  let dflt := (List.range n).map fun i => Name.mkSimple s!"s{i + 1}"
  lambdaBoundedTelescope body 2 fun zs b => do
    unless zs.size == 2 do return dflt
    -- the projection chains of `r` for each component
    let paths ← compPaths l.fstN l.sndN zs[1]! n
    let mut found : Array (Option Name) := Array.replicate n none
    let mut e := b
    repeat
      let e' := e.consumeMData
      let .letE nm _ v bd _ := e' | break
      let v := v.consumeMData
      if let some i := paths.findIdx? (· == v) then
        if found[i]!.isNone then found := found.set! i (some nm)
      e := bd.instantiate1 v
    return (List.range n).map fun i => (found[i]!).getD dflt[i]!

/-! ## Simplification of the generated code -/

/-- Reduce projections of constructor applications (`(MProd.mk a b).fst`, `(a, b).2`),
matchers applied to constructors and `have x := y` with `y` a variable, in the generated code. -/
def cleanup (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    -- the `Id` monad
    if e.isAppOfArity ``Id.run 2 then return .visit (e.getArg! 1)
    if let some x := idPure? e then return .visit x
    if let some (α, _, x, k) := idBind? e then
      if let .lam n _ b _ := k.consumeMData then
        if !b.hasLooseBVars then return .visit b
        return .visit (Lean.mkLet n α x b (nondep := true))
      return .visit (mkApp k x).headBeta
    if (e.isAppOfArity ``MProd.fst 3 || e.isAppOfArity ``Prod.fst 3) then
      let a := (e.getArg! 2).consumeMData
      if a.isAppOfArity ``MProd.mk 4 || a.isAppOfArity ``Prod.mk 4 then
        return .visit (a.getArg! 2)
    if (e.isAppOfArity ``MProd.snd 3 || e.isAppOfArity ``Prod.snd 3) then
      let a := (e.getArg! 2).consumeMData
      if a.isAppOfArity ``MProd.mk 4 || a.isAppOfArity ``Prod.mk 4 then
        return .visit (a.getArg! 3)
    if let .proj _ i a := e then
      let a := a.consumeMData
      if a.isAppOfArity ``MProd.mk 4 || a.isAppOfArity ``Prod.mk 4 then
        return .visit (a.getArg! (2 + i))
    if let .letE _ _ v b _ := e then
      -- the destructuring of the loop state: variables, tuples and projections
      let v' := v.consumeMData
      if v'.isFVar || v'.isAppOfArity ``MProd.mk 4 || v'.isAppOfArity ``MProd.fst 3 ||
          v'.isAppOfArity ``MProd.snd 3 || v'.isAppOfArity ``Prod.fst 3 ||
          v'.isAppOfArity ``Prod.snd 3 || v'.isAppOfArity ``Prod.mk 4 ||
          (v'.isAppOfArity ``PUnit.unit 0) || v'.isConstOf ``PUnit.unit || v'.isConstOf ``Unit.unit then
        return .visit (b.instantiate1 v)
    if (← matchMatcherApp? e).isSome then
      if let .reduced r ← withReducible (Meta.reduceMatcher? e) then
        return .visit r.headBeta
    return .continue)

/-! ## The loop as a tail-recursive function -/

/-- The loop body `e : Id (ForInStep β)` as the body of the tail-recursive loop function:
`ForInStep.yield b` becomes `rec b` (the recursive call on the components of `b`), and
`ForInStep.done b` becomes `ret b` (the tuple of the components of `b`), through `let`s, `if`s,
`match`es and `Id` binds.  `γ` is the result type of the loop function. -/
partial def toTail (rec ret : Lean.Expr → MetaM Lean.Expr) (γ : Lean.Expr) (e : Lean.Expr) :
    MetaM Lean.Expr := do
  let go := toTail rec ret γ
  let e := e.consumeMData.headBeta
  if let some x := idPure? e then return ← go x
  if e.isAppOfArity ``Id.run 2 then return ← go (e.getArg! 1)
  if e.isAppOfArity ``ForInStep.yield 2 then return ← rec (e.getArg! 1)
  if e.isAppOfArity ``ForInStep.done 2 then return ← ret (e.getArg! 1)
  -- a jump to a join point of the loop body (already turned into the loop's result type)
  if let some (α, _, x, k) := idBind? e then
    let k := k.consumeMData
    if let .lam n _ b _ := k then
      if !b.hasLooseBVars then return ← go b
      return ← withLetDecl n α x fun v => do
        let b' ← go (b.instantiate1 v)
        return Lean.mkLet n α x (b'.abstract #[v]) (nondep := true)
    return ← go (mkApp k x)
  if let .letE n t v b nd := e then
    -- a join point of the loop body (`let __do_jp := fun … => …` of `do` notation)
    let arity ← forallTelescope t fun xs r => do
      let r := r.consumeMData
      let isStep := r.isAppOfArity ``ForInStep 1 ||
        (r.isAppOfArity ``Id 1 && (r.getArg! 0).consumeMData.isAppOfArity ``ForInStep 1)
      return if isStep then xs.size else 0
    if arity > 0 then
      -- inlined: the join point generalises the mutable variables, which would hide from the
      -- termination proof how they relate to the loop state
      return ← go (b.instantiate1 v)
    return ← withLetDecl n t v fun x => do
      let b' ← go (b.instantiate1 x)
      return Lean.mkLet n t v (b'.abstract #[x]) nd
  if e.isAppOfArity ``ite 5 then
    let u ← getLevel γ
    return mkApp5 (mkConst ``ite [u]) γ (e.getArg! 1) (e.getArg! 2)
      (← go (e.getArg! 3)) (← go (e.getArg! 4))
  if e.isAppOfArity ``dite 5 then
    let u ← getLevel γ
    let br (f : Lean.Expr) : MetaM Lean.Expr := do
      let f := f.consumeMData
      let .lam n d _ _ := f | throwError "lean_while_to_wf: unexpected branch of `dite`{indentExpr f}"
      withLocalDecl n .default d fun h => do
        mkLambdaFVars #[h] (← go (mkApp f h).headBeta)
    return mkApp5 (mkConst ``dite [u]) γ (e.getArg! 1) (e.getArg! 2)
      (← br (e.getArg! 3)) (← br (e.getArg! 4))
  if let some m ← matchMatcherApp? e then
    unless m.remaining.isEmpty do
      throwError "lean_while_to_wf: unsupported `match` in a loop body{indentExpr e}"
    let motive ← lambdaTelescope m.motive fun xs _ => mkLambdaFVars xs γ
    let nums := m.altNumParams
    let alts ← (m.alts.zip nums).mapM fun (alt, k) =>
      lambdaBoundedTelescope alt k fun zs b => do
        unless zs.size == k do throwError "lean_while_to_wf: unexpected `match` alternative"
        mkLambdaFVars zs (← go b)
    return { m with motive, alts }.toExpr
  throwError "lean_while_to_wf: unsupported construct in the body of a `while` loop{indentExpr e}"

end WFLang.LeanWhile
