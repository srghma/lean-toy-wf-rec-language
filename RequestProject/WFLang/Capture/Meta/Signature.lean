import Lean
import Mathlib.Tactic.CasesM
import RequestProject.WFLang.Core.PExpr
import RequestProject.WFLang.Core.Loops
import RequestProject.WFLang.Core.While

/-!
# Capture metaprogramming: types, signatures and specialisation

The object types of Lean types (`tyOf`), the signature of a Lean function (`fnSig`,
`signatureOf`), references to (possibly specialised) functions (`FnRef`), pre- and
postconditions (`prePostOf`), and the recognition of `Nat`/`Int` binary operators.
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-- `set_option trace.wfLang.agree true` reports why `wf_agree` rejected each candidate
function when it identifies the value of a loop or of a global function. -/
initialize registerTraceClass `wfLang.agree

/-! ## Types and signatures -/

/-- The object type of a Lean type (`Nat`, `Bool`, `Int`, `String`, `Char`, pairs, lists,
arrays, `Option`, `Sum`, `Except`).  A subtype
`{x : α // P x}` is represented by its carrier `α` (its property becomes a postcondition). -/
partial def tyOf (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfR e
  if e.isConstOf ``Nat then return mkConst ``WFLang.Ty.nat
  if e.isConstOf ``Bool then return mkConst ``WFLang.Ty.bool
  if e.isConstOf ``Int then return mkConst ``WFLang.Ty.int
  if e.isAppOfArity ``Prod 2 then
    return mkApp2 (mkConst ``WFLang.Ty.prod) (← tyOf (e.getArg! 0)) (← tyOf (e.getArg! 1))
  if e.isAppOfArity ``List 1 then return mkApp (mkConst ``WFLang.Ty.list) (← tyOf (e.getArg! 0))
  if e.isAppOfArity ``Option 1 then return mkApp (mkConst ``WFLang.Ty.option) (← tyOf (e.getArg! 0))
  if e.isAppOfArity ``Sum 2 then
    return mkApp2 (mkConst ``WFLang.Ty.sum) (← tyOf (e.getArg! 0)) (← tyOf (e.getArg! 1))
  if e.isAppOfArity ``Except 2 then
    return mkApp2 (mkConst ``WFLang.Ty.except) (← tyOf (e.getArg! 0)) (← tyOf (e.getArg! 1))
  if e.isConstOf ``String then return mkConst ``WFLang.Ty.string
  if e.isConstOf ``Char then return mkConst ``WFLang.Ty.char
  if let .const ``PUnit [u] := e then
    if u == Level.one then return mkConst ``WFLang.Ty.unit
  if e.isAppOfArity ``Array 1 then return mkApp (mkConst ``WFLang.Ty.array) (← tyOf (e.getArg! 0))
  if e.isAppOfArity ``Subtype 2 then return ← tyOf (e.getArg! 0)
  throwError "#lean_wf_func_to_term: unsupported type {e} (only Nat, Bool, Int, String, Char, pairs, lists, arrays, Option, Sum, Except, Unit and subtypes of them)"

/-- Build a list literal of object types. -/
def mkTyList (ts : List Lean.Expr) : Lean.Expr :=
  ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``WFLang.Ty) t acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``WFLang.Ty))

/-- The parameters of a Lean function, split into *object* parameters (of an object type) and
*proof* parameters (of a `Prop` type: a precondition), and its result. -/
structure FnSig where
  /-- positions of the object parameters -/
  objPos : List Nat
  /-- positions of the proof parameters -/
  prfPos : List Nat
  /-- object types of the object parameters -/
  argTys : List Lean.Expr
  /-- object type of the result (the carrier of a subtype) -/
  retTy : Lean.Expr
  /-- total number of parameters -/
  arity : Nat
  /-- is the result a subtype (i.e. is there a postcondition)? -/
  subtypeRet : Bool
  /-- number of *lifted* variables (free variables of the function arguments of a
  specialised function), which come first in the parameters of the global function -/
  nExtra : Nat := 0
  /-- positions of the specialised parameters (function, type and instance parameters) -/
  specPos : List Nat := []
  /-- for a member of a group of mutually recursive functions: its index in the group (the tag
  passed as the first argument of the global function capturing the group) -/
  tag : Option Nat := none
  /-- for a function that calls itself inside a function argument (captured together with the
  specialised function, see `Translate.HOInfo`): the number of padded parameters after its own -/
  pad : Nat := 0
  deriving Inhabited

/-! ## Specialisation of function parameters -/

/-- Is a parameter with binder type `d` and binder info `bi` *specialised* when a function is
captured at a call site: a type, an instance, or a function (a non-`Prop` `∀`)? -/
def isSpecBinder (d : Lean.Expr) (bi : BinderInfo) : MetaM Bool := do
  if bi.isInstImplicit then return true
  let d' ← whnfR d
  if d'.isSort then return true
  if d'.isForall then return !(← isProp d)
  return false

/-- A function to capture, possibly *specialised*: its specialised parameters
(`isSpecBinder`: function, type and instance parameters) are replaced by the values `spec` (in
order), which are abstracted over the *lifted* variables (of types `extraTys`): the free
variables of the function arguments at the call site.  The lifted variables become the first
(fixed) parameters of the loop or global function capturing the specialised copy.  E.g.
`Tco.iter Tco.mc91`, or `WFLang.rangeLoop (fun i s => s + i * n)` with `n` lifted. -/
structure FnRef where
  name : Name
  /-- universe levels of the constant (`[]`: its level parameters) -/
  levels : List Level := []
  /-- Lean types of the lifted variables -/
  extraTys : Array Lean.Expr := #[]
  /-- values of the specialised parameters, as `fun ys => v` over the lifted variables -/
  spec : Array Lean.Expr := #[]
  /-- if non-empty: the group of mutually recursive functions `name` belongs to, captured as one
  global function whose first parameter (a tag `i`) selects the function `group[i]` -/
  group : Array Name := #[]
  deriving Inhabited

instance : Coe Name FnRef := ⟨fun n => { name := n }⟩

/-- Is this a specialised copy? -/
def FnRef.isSpec (f : FnRef) : Bool := !f.spec.isEmpty

/-- The constant of `f`, at its universe levels. -/
def FnRef.const (f : FnRef) : MetaM Lean.Expr := do
  if f.levels.isEmpty then mkConstWithLevelParams f.name else return mkConst f.name f.levels

/-- Structural equality of two references (up to binder names). -/
def FnRef.beq (f g : FnRef) : Bool :=
  f.name == g.name && f.levels == g.levels && f.extraTys == g.extraTys && f.spec == g.spec &&
    f.group == g.group

/-- Adapt the value `v` of a specialised parameter to the binder type `d`: a `λ` gets the binder
types of `d` (they may mention other parameters, e.g. `i < n` in `Nat.fold`). -/
def respec (d v : Lean.Expr) : MetaM Lean.Expr := do
  let n := v.getNumHeadLambdas
  if n == 0 then return v
  forallBoundedTelescope d (some n) fun zs _ => do
    mkLambdaFVars zs (v.beta zs).headBeta

/-- The positions of the specialised parameters of the constant `fn` applied to `args`. -/
def specPosAt (fn : Lean.Expr) (args : Array Lean.Expr) : MetaM (List Nat) := do
  let mut ty ← inferType fn
  let mut out := #[]
  for i in [0:args.size] do
    ty ← whnfR ty
    let .forallE _ d b bi := ty | break
    if ← isSpecBinder d bi then out := out.push i
    ty := b.instantiate1 args[i]!
  return out.toList

def FnRef.telescopeAux {n : Type → Type} [MonadControlT MetaM n] [Monad n]
    [MonadLiftT MetaM n] {α : Type} (f : FnRef) (ys : Array Lean.Expr) (ty : Lean.Expr)
    (xs : Array Lean.Expr) (j : Nat)
    (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → n α) : (fuel : Nat) → n α
  | 0 => k ys xs ty
  | fuel + 1 => do
  let ty ← if ty.isForall then pure ty else liftM (m := MetaM) (whnfR ty)
  match ty with
  | .forallE nm d b bi =>
    if f.isSpec && (← liftM (m := MetaM) (isSpecBinder d bi)) then
      let some v := f.spec[j]? |
        liftM (m := MetaM) (throwError "#lean_wf_func_to_term: missing function argument of {f.name}")
      let v ← liftM (m := MetaM) (respec d (v.beta ys))
      f.telescopeAux ys (b.instantiate1 v) (xs.push v) (j + 1) k fuel
    else
      withLocalDecl nm bi d fun x => f.telescopeAux ys (b.instantiate1 x) (xs.push x) j k fuel
  | _ => k ys xs ty

/-- Run `k ys xs r` where `ys` are (fresh) lifted variables, `xs` the arguments of `f.name`:
the specialised values at the specialised positions and fresh variables elsewhere, and `r` the
result type. -/
def FnRef.telescope {n : Type → Type} [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
    {α : Type} (f : FnRef) (k : Array Lean.Expr → Array Lean.Expr → Lean.Expr → n α) : n α := do
  let ty ← liftM (m := MetaM) (do inferType (← f.const))
  let rec withYs (tys : List Lean.Expr) (ys : Array Lean.Expr) : n α :=
    match tys with
    | [] => f.telescopeAux ys ty #[] 0 k 1000
    | t :: ts => withLocalDeclD (Name.mkSimple s!"y{ys.size}") t fun y => withYs ts (ys.push y)
  withYs f.extraTys.toList #[]

/-- The object type `ts₀ × (ts₁ × …)` of a tuple. -/
def tyTuple : List Lean.Expr → Lean.Expr
  | [] => mkConst ``WFLang.Ty.unit
  | [t] => t
  | t :: ts => mkApp2 (mkConst ``WFLang.Ty.prod) t (tyTuple ts)

/-- The signature of `fn` (of its specialised copy, for a specialised reference; of the local
recursive function capturing the group, for a group of mutually recursive functions: a tag
parameter in front of the common parameters). -/
partial def fnSig (f : FnRef) : MetaM FnSig := do
  if !f.group.isEmpty then
    let sigs ← f.group.mapM fun n => fnSig { name := n }
    let s0 := sigs[0]!
    for (n, s) in f.group.zip sigs do
      unless s.prfPos.isEmpty && !s.subtypeRet do
        throwError "#lean_wf_func_to_term: the mutually recursive functions {f.group} must not have proof parameters or subtype results ({n} has)"
    let shared := sigs.all fun s => s.argTys == s0.argTys && s.objPos == s0.objPos
    let sameRet := sigs.all (·.retTy == s0.retTy)
    let argTys := if shared then s0.argTys else sigs.toList.flatMap (·.argTys)
    let retTy := if sameRet then s0.retTy else tyTuple (sigs.toList.map (·.retTy))
    return { s0 with argTys := mkConst ``WFLang.Ty.nat :: argTys, retTy }
  if f.isSpec then
    return ← f.telescope fun ys xs r => do
      let mut objPos := #[]
      let mut prfPos := #[]
      let mut specPos := #[]
      let mut argTys := #[]
      for y in ys do argTys := argTys.push (← tyOf (← inferType y))
      let ty0 ← inferType (← f.const)
      let mut ty := ty0
      for i in [0:xs.size] do
        ty ← whnfR ty
        let .forallE _ d b bi := ty | break
        if ← isSpecBinder d bi then specPos := specPos.push i
        else if ← isProp d then prfPos := prfPos.push i
        else
          objPos := objPos.push i
          argTys := argTys.push (← tyOf d)
        ty := b.instantiate1 xs[i]!
      let r' ← whnfR r
      return { objPos := objPos.toList, prfPos := prfPos.toList, argTys := argTys.toList,
               retTy := ← tyOf r, arity := xs.size, subtypeRet := r'.isAppOfArity ``Subtype 2,
               nExtra := ys.size, specPos := specPos.toList }
  let fn := f.name
  let fnTy ← inferType (← mkConstWithLevelParams fn)
  forallTelescope fnTy fun xs r => do
    let mut objPos := #[]
    let mut prfPos := #[]
    let mut argTys := #[]
    for i in [0:xs.size] do
      let ty ← inferType xs[i]!
      let d ← xs[i]!.fvarId!.getDecl
      if ← isSpecBinder d.type d.binderInfo then
        throwError "#lean_wf_func_to_term: {fn} has a function (or type) parameter; capture a copy specialised to a closed function instead: `#lean_wf_func_to_term ({fn} f)`"
      if ← isProp ty then prfPos := prfPos.push i
      else
        objPos := objPos.push i
        argTys := argTys.push (← tyOf ty)
    let r' ← whnfR r
    return { objPos := objPos.toList, prfPos := prfPos.toList, argTys := argTys.toList,
             retTy := ← tyOf r, arity := xs.size, subtypeRet := r'.isAppOfArity ``Subtype 2 }

/-- The layout of the global function capturing a group of mutually recursive functions.  Its
first parameter is a tag `i`, selecting the member `group[i]`.  If the members have the same
parameter types, they share the parameters after the tag; otherwise the parameters after the tag
are those of all the members, one after the other (member `i` reads its own, at offset
`offs[i]`, and the others are padded with default values).  If the members have the same result
type, it is the result type; otherwise the result is a tuple with one component per member
(member `i` fills component `i`, the others hold default values). -/
structure GroupLayout where
  sigs : Array FnSig
  shared : Bool
  sameRet : Bool
  offs : Array Nat
  /-- the Lean result types of the members -/
  retLean : Array Lean.Expr
  deriving Inhabited

/-- The layout of the global function capturing `group`. -/
def groupLayout (group : Array Name) : MetaM GroupLayout := do
  let sigs ← group.mapM fun n => fnSig { name := n }
  let s0 := sigs[0]!
  let shared := sigs.all fun s => s.argTys == s0.argTys && s.objPos == s0.objPos
  let sameRet := sigs.all (·.retTy == s0.retTy)
  let mut offs := #[]
  let mut o := 0
  for s in sigs do
    offs := offs.push (if shared then 0 else o)
    o := o + s.argTys.length
  let retLean ← group.mapM fun n => do
    forallTelescope (← inferType (← mkConstWithLevelParams n)) fun _ r => pure r
  return { sigs, shared, sameRet, offs, retLean }

/-- The Lean result type of the global function capturing a group. -/
def GroupLayout.retLeanTy (l : GroupLayout) : MetaM Lean.Expr :=
  if l.sameRet then return l.retLean[0]! else mkTupleLean l.retLean.toList
where
  mkTupleLean : List Lean.Expr → MetaM Lean.Expr
    | [] => return mkConst ``Unit
    | [t] => return t
    | t :: ts => do mkAppM ``Prod #[t, ← mkTupleLean ts]

/-- The arguments (after the tag) of a call of member `i` of a group on the object arguments
`args`: `none` for the padding. -/
def GroupLayout.callArgs {α : Type} (l : GroupLayout) (i : Nat) (args : List α) : List (Option α) :=
  if l.shared then args.map some else
    List.replicate l.offs[i]! none ++ args.map some ++
      List.replicate (l.sigs.foldl (· + ·.argTys.length) 0 - l.offs[i]! - args.length) none

/-- The value of member `i` in the result `v` of the global function capturing a group. -/
def GroupLayout.proj (l : GroupLayout) (i : Nat) (v : Lean.Expr) : MetaM Lean.Expr := do
  if l.sameRet then return v
  let mut v := v
  for _ in [0:i] do v ← mkAppM ``Prod.snd #[v]
  if i + 1 < l.sigs.size then v ← mkAppM ``Prod.fst #[v]
  return v

/-- The result of the global function capturing a group, for the value `v` of member `i`: the
tuple with `v` in component `i` and default values (`WFLang.Ty.default`) elsewhere. -/
def GroupLayout.inj (l : GroupLayout) (i : Nat) (v : Lean.Expr) : MetaM Lean.Expr := do
  if l.sameRet then return v
  let comp (j : Nat) : Lean.Expr :=
    if j == i then v else mkApp (mkConst ``WFLang.Ty.default) l.sigs[j]!.retTy
  let k := l.sigs.size
  let mut t := comp (k - 1)
  let mut tTy := l.retLean[k - 1]!
  for j in (List.range (k - 1)).reverse do
    t := mkApp4 (mkConst ``Prod.mk [0, 0]) l.retLean[j]! tTy (comp j) t
    tTy := mkApp2 (mkConst ``Prod [0, 0]) l.retLean[j]! tTy
  return t

/-- The object types of the (object) arguments and of the result of `fn`. -/
def signatureOf (fn : FnRef) : MetaM (List Lean.Expr × Lean.Expr) := do
  let s ← fnSig fn
  return (s.argTys, s.retTy)

/-- The `i`-th component of an environment `e`. -/
def envProj (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
  let mut v := e
  for _ in [0:i] do v ← mkAppM ``Prod.snd #[v]
  mkAppM ``Prod.fst #[v]

/-- The `i`-th of `n` components of a proof of a right-nested conjunction. -/
def conjProj (h : Lean.Expr) (i n : Nat) : MetaM Lean.Expr := do
  let mut v := h
  for _ in [0:i] do v ← mkAppM ``And.right #[v]
  if i + 1 < n then mkAppM ``And.left #[v] else return v

/-- The right-nested conjunction of `ps` (`True` if empty). -/
def mkConj : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``And) p (mkConj ps)

/-- For `fn` with parameters `xs` (a telescope of its type): its precondition, as a predicate
on environments of its object parameters (`none` if it has no proof parameter), and its
postcondition, as a relation between environments and results (`none` if the result is not a
subtype).  Proof parameters may depend on object parameters only. -/
def prePostOf (fn : FnRef) (xs : Array Lean.Expr) (resTy : Lean.Expr)
    (ys : Array Lean.Expr := #[]) : MetaM (Option Lean.Expr × Option Lean.Expr) := do
  let sig ← fnSig fn
  let gam := mkTyList sig.argTys
  let objXs := ys ++ (sig.objPos.map (xs[·]!)).toArray
  let prfXs := (sig.prfPos.map (xs[·]!)).toArray
  withLocalDeclD `e (mkApp (mkConst ``WFLang.Env) gam) fun e => do
    let vals ← (List.range sig.argTys.length).toArray.mapM (envProj e)
    let pre ← if sig.prfPos.isEmpty then pure none else do
      let props ← prfXs.toList.mapM fun h => do
        let ty := (← inferType h).replaceFVars objXs vals
        if ty.hasAnyFVar (prfXs.contains <| mkFVar ·) then
          throwError "#lean_wf_func_to_term: a proof parameter of {fn.name} depends on another one"
        pure ty
      pure (some (← mkLambdaFVars #[e] (mkConj props)))
    let r ← whnfR resTy
    let post ← if !r.isAppOfArity ``Subtype 2 then pure none else do
      let P := (r.getArg! 1).replaceFVars objXs vals
      if P.hasAnyFVar (prfXs.contains <| mkFVar ·) then
        throwError "#lean_wf_func_to_term: the result type of {fn.name} depends on a proof parameter"
      let vTy := mkApp (mkConst ``WFLang.Ty.denote) sig.retTy
      pure (some (← withLocalDeclD `v vTy fun v => do
        mkLambdaFVars #[e, v] (P.beta #[v]).headBeta))
    return (pre, post)

/-- Binary `Nat` operators, as `(BinOp constructor, lhs, rhs)`. -/
def natBin? (e : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) :=
  let ops : List (Name × Name) := [(``HAdd.hAdd, ``WFLang.BinOp.add),
    (``HSub.hSub, ``WFLang.BinOp.sub), (``HMul.hMul, ``WFLang.BinOp.mul),
    (``HDiv.hDiv, ``WFLang.BinOp.div), (``HMod.hMod, ``WFLang.BinOp.mod),
    (``HPow.hPow, ``WFLang.BinOp.pow), (``HShiftLeft.hShiftLeft, ``WFLang.BinOp.shiftLeft),
    (``HShiftRight.hShiftRight, ``WFLang.BinOp.shiftRight), (``HAnd.hAnd, ``WFLang.BinOp.land),
    (``HOr.hOr, ``WFLang.BinOp.lor), (``HXor.hXor, ``WFLang.BinOp.xor)]
  ops.findSome? fun (n, op) =>
    if e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Nat && (e.getArg! 1).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5) else none

/-- Binary `Int` operators, as `(BinOp constructor, lhs, rhs)`. -/
def intBin? (e : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) :=
  let ops : List (Name × Name) := [(``HAdd.hAdd, ``WFLang.BinOp.iadd),
    (``HSub.hSub, ``WFLang.BinOp.isub), (``HMul.hMul, ``WFLang.BinOp.imul),
    (``HDiv.hDiv, ``WFLang.BinOp.idiv), (``HMod.hMod, ``WFLang.BinOp.imod)]
  ops.findSome? fun (n, op) =>
    if e.isAppOfArity n 6 && (e.getArg! 0).isConstOf ``Int && (e.getArg! 1).isConstOf ``Int then
      some (op, e.getArg! 4, e.getArg! 5) else none

end WFLang.Meta
