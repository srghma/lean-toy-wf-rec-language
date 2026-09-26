module

public import Lean.Meta.Basic
public import LeanScript.Expr.Build

@[expose] public section

meta section

/-!
# Normalizing a translated term once, when it is defined

The translation writes a term in **direct style**: it applies the builders of
`LeanScript.Expr.Build` (`Term.ap`, `Term.letE'`, `Term.nat_rec'`, …), and those functions
put the term in A-normal form — they name every operand with a `let`, rename the terms
they move under those `let`s (`Term.rename`) and turn a dispatch in operand position into
a join point (`Term.toJump`).  Those functions are ordinary Lean functions, so the
A-normal term is only *computed* when something reduces the definition.

Left alone, that computation is done by the kernel **every time** a proof reduces the
term — every `decide +kernel` and every `kernel_rfl` that runs it — and it is expensive:
each step of `Term.rename`, `Term.toJump`, `Term.bindAtom` or `Term.bind` is a match on a
constructor of `LeanScript.Term`, whose mutual block has 23 types and 127 constructors,
and the kernel pays for that size on every match (about half a millisecond each).  For a
test that runs a translated function on a few inputs, renaming the term again for each
input was most of the time the kernel spent.

`normalizeTerm` does it once instead: it reduces the translated term with the kernel's own
weak head normalization, constructor by constructor, into the constructors of the grammar
(`Term.letE`, `Comp.ap`, `Atom.var`, `DeBruijnProj.tail`, …).  The result is
definitionally equal to what the builders give — it is what the kernel would compute from
them — so every equation that held of the term still holds.  `#leanscript_to_term`
normalizes its result unless `leanscript.toTerm.normalize` is `false`.

Normalizing is not free: it does, once and for the whole term, the work that a proof
running the term does only for the branches it takes.  For a small term that is run on
several inputs it pays for itself many times over (in `TermTests/StructRecTest/Existential.lean`
it halves the kernel's time); for a very large term with many branches — a deep `match`
translated into thousands of nodes, of which each run visits a few — it can cost more
than it saves.  So a term is normalized only if it has at most
`leanscript.toTerm.normalizeMaxNodes` nodes of the grammar (`grammarNodeCount`).

`#leanscript_fold_branch` and `#leanscript_fold_bases` read the fold of a normalized term
as well as of a direct-style one; of a normalized `nat_rec` the bases are atoms (an
`Args`), not terms (a `Spine`), so a test that needs the latter turns normalization off.

Only the arguments that hold syntax are normalized (terms, computations, atoms, variables,
lists and pairs of them): the types (`Ctx`, `TyWf`), the proofs and the literals are left
as the translation wrote them.  An argument the normalization cannot reduce (one that
mentions a free variable in head position, or a metavariable) is left as it is; the
result is then still correct, only less reduced.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- The type formers whose values are syntax of the grammar, besides the mutual block of
    `LeanScript.Term`: their arguments are normalized too. -/
def syntaxTypeHeads : List Name :=
  [``LeanScript.Atom, ``LeanScript.Args, ``LeanScript.FamilyMemberArgs, ``LeanScript.Dest,
   ``LeanScript.DeBruijnProj, ``LeanScript.Spine, ``LeanScript.Terms,
   ``LeanScript.FamilyMemberValue, ``List, ``Prod, ``PProd, ``Option]

/-- Unfold the reducible definitions (`abbrev`s such as `LeanScript.Var` or
    `LeanScript.TaggedUnionCases`) at the head of the type `ty`.  This is done by hand,
    rather than by `whnfR`, so that normalizing a large term spends no heartbeats. -/
partial def unfoldReducibleHead (ty : Expr) : MetaM Expr := do
  let ty := ty.headBeta
  match ty.getAppFn with
  | .const n lvls =>
    if (← getReducibilityStatus n) != .reducible then return ty
    match (← getEnv).find? n with
    | some (.defnInfo dv) =>
      unfoldReducibleHead ((dv.value.instantiateLevelParams dv.levelParams lvls).beta
        ty.getAppArgs)
    | _ => return ty
  | _ => return ty

/-- Whether a value of the type `ty` is syntax of the grammar (see `syntaxTypeHeads`). -/
def isSyntaxType (ty : Expr) : MetaM Bool := do
  match (← unfoldReducibleHead ty).getAppFn with
  | .const n _ =>
    if syntaxTypeHeads.contains n then return true
    match (← getEnv).find? n with
    | some (.inductInfo iv) => return iv.all.contains ``LeanScript.Term
    | _ => return false
  | _ => return false

/-- The number of nodes of the grammar in the translated term `e`: the applications of the
    constructors and builders of `LeanScript.Term` and `LeanScript.Comp`, each shared
    subterm counted once. -/
def grammarNodeCount (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[e]
  let mut n := 0
  while h : todo.size > 0 do
    let x := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app .. =>
      let f := x.getAppFn
      if let .const c _ := f then
        if c.getPrefix == ``LeanScript.Term || c.getPrefix == ``LeanScript.Comp then n := n + 1
      else todo := todo.push f
      todo := todo ++ x.getAppArgs
    | .lam _ _ b _ => todo := todo.push b
    | .letE _ _ v b _ => todo := (todo.push v).push b
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  return n

/-- Weak head normal form, by the kernel; `e` itself when the kernel cannot reduce it. -/
def kernelWhnf (e : Expr) : MetaM Expr := do
  if e.hasMVar then return e
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e' => return e'
  | .error _ => return e

/-- Normalize `e` into constructors of the grammar (see the module doc).  A `fun` at the
    top (a term generic in hidden types, `LeanScript.ToTerm.ExistentialArgs`) is
    normalized under its binders. -/
partial def normalizeTerm (e : Expr) : MetaM Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  let rec
    /-- Normalize the arguments of `f` from the `start`-th on that hold syntax; their types
        are read off the type of `f`, instantiated with the arguments before them. -/
    normArgs (f : Expr) (args : Array Expr) (start : Nat) : MetaM (Array Expr) := do
      let .const c lvls := f | return args
      let info ← getConstInfo c
      let mut args := args
      let mut ty := info.type.instantiateLevelParams info.levelParams lvls
      for i in [0:args.size] do
        let .forallE _ dom body _ := ty | break
        if i ≥ start then
          if ← isSyntaxType dom then
            args := args.set! i (← go args[i]!)
        ty := body.instantiate1 args[i]!
      return args,
    go (e : Expr) : MetaM Expr := do
      if e.isLambda then
        return ← lambdaTelescope e fun xs b => do mkLambdaFVars xs (← go b)
      let closed := !e.hasFVar
      if closed then
        if let some r := (← cache.get)[e]? then return r
      -- a builder applied to operands: the operands first (innermost first), so that the
      -- builder is reduced on constructors and a lazily built operand is not rebuilt by
      -- every reduction that looks at it
      let e ← match e.getAppFn with
        | f@(.const c _) =>
          match (← getEnv).find? c with
          | some (.defnInfo _) => pure (mkAppN f (← normArgs f e.getAppArgs 0))
          | _ => pure e
        | _ => pure e
      let e' ← kernelWhnf e
      let r ← match e'.getAppFn with
        | f@(.const c _) =>
          match (← getEnv).find? c with
          | some (.ctorInfo cv) => pure (mkAppN f (← normArgs f e'.getAppArgs cv.numParams))
          | _ => pure e'
        | _ => pure e'
      if closed then cache.modify (·.insert e r)
      return r
  -- the work is the kernel's reduction, not elaboration: it is not counted against the
  -- heartbeats of the command that asked for the translation
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
    go (← instantiateMVars e)

end LeanScript.ToTerm

end

end
