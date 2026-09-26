module

public meta import LeanScript.ToTerm.Trans
public meta import LeanScript.ToTerm.ExistentialArgs
public meta import LeanScript.ToTerm.Normalize
public meta import LeanScript.ToTerm.Options
public import LeanScript.CtorFn
public import LeanScript.RangeFacts

@[expose] public section

meta section

/-!
# The elaborator

`#leanscript_to_term`, and the two commands that report on and empty its cache.  This is
the module to import to use the translation.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The elaborator -/

/-- The empty signature, as an expression. -/
def emptySigE : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``LeanScript.GlobalDecl)
  mkApp2 (mkConst ``LeanScript.Sig.mk) nil
    (mkApp (mkConst ``List.nodup_nil [Level.zero]) (mkConst ``String))

/-- The signature and the context the expected type asks for. -/
def sigAndCtxOf? (expected? : Option Expr) : MetaM (Expr × Expr) := do
  match expected? with
  | none => return (emptySigE, nilCtxE)
  | some t =>
    match (← whnf (← instantiateMVars t)).getAppFnArgs with
    | (``LeanScript.Term, #[sg, γ, _, _]) => return (sg, γ)
    | _ => return (emptySigE, nilCtxE)

/-- Translate `e` — the value of a definition, or an expression written out. -/
def translate (sg base : Expr) (e : Expr) : MetaM Expr := do
  let globals ← parseSig sg
  let c : TCtx := { sg := sg, globals := globals, base := base }
  match e with
  | .const n lvls =>
      checkConst n
      let info ← getConstInfo n
      let some val := info.value?
        | throwError "`#leanscript_to_term`: `{n}` has no definition to translate"
      let val := val.instantiateLevelParams info.levelParams lvls
      -- a function of a structure with an existential type field is generic in its
      -- hidden types (`LeanScript.ToTerm.ExistentialArgs`)
      if let some t ← translateGeneric? c val then return t
      transClosedCached trans c val
  | _ =>
      if let some t ← translateGeneric? c (← etaExpand e) then return t
      trans c e

/-- `#leanscript_to_term e`: the `LeanScript.Term` that means what the Lean definition
    `e` means.  See this module's header.

    The signature the translation resolves top-level names against is the one of the
    expected type; `#leanscript_to_term (sig := s) e` names it instead, which is what
    lets the type of the translation be *inferred* rather than written out. -/
syntax (name := leanscriptToTerm) "#leanscript_to_term " ("(" &"sig" " := " term ")")?
  term : term

@[term_elab leanscriptToTerm]
def elabLeanscriptToTerm : TermElab := fun stx expected? => do
  let sigStx := stx[1]
  let arg := stx[2]
  let e ← instantiateMVars (← elabTerm arg none)
  let (sgOfExpected, base) ← sigAndCtxOf? expected?
  let sg ← if sigStx.isNone then pure sgOfExpected else
    instantiateMVars (← elabTerm sigStx[3] (mkConst ``LeanScript.Sig))
  let t ← translate sg base e
  let opts ← getOptions
  let t ← instantiateMVars t
  let t ← if leanscript.toTerm.normalize.get opts &&
      grammarNodeCount t ≤ leanscript.toTerm.normalizeMaxNodes.get opts then
    normalizeTerm t else pure t
  match expected? with
  | some ty => Term.ensureHasType ty t
  | none => return t

/-- The folds of the grammar, with the number of arguments of each: the last one is the
    branch (or the cases) of the fold. -/
def foldNodes : List (Name × Nat) :=
  [(`LeanScript.Term.nat_rec', 7), (`LeanScript.Term.array_rec', 8),
   (`LeanScript.Term.recTaggedUnion_rec', 8), (`LeanScript.Term.recObject_rec', 8),
   (`LeanScript.Term.recAlias_rec', 8), (`LeanScript.Term.mutualRecursiveFamily_rec', 9)]

/-- The folds of the grammar as constructors, with the number of arguments of each: the
    last one is the fold's `Dest`, and the one before it is the branch (or the cases). -/
def foldCtors : List (Name × Nat) :=
  [(``LeanScript.Term.nat_rec, 10), (``LeanScript.Term.array_rec, 11),
   (``LeanScript.Term.recTaggedUnion_rec, 11), (``LeanScript.Term.recObject_rec, 11),
   (``LeanScript.Term.recAlias_rec, 11), (``LeanScript.Term.mutualRecursiveFamily_rec, 12)]

/-- Unfold the definitions at the head of `e`, beta-reducing on the way. -/
partial def unfoldHeadConsts (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e.getAppFn with
  | .const n _ =>
      if foldNodes.any (·.1 == n) || foldCtors.any (·.1 == n) then return e
      match ← withTransparency .all (unfoldDefinition? e) with
      | some e' => unfoldHeadConsts e'
      | none => return e
  | _ => return e

/-- `#leanscript_fold_branch t`: the branch of the first fold in the term `t` (a
    definition, typically one built by `#leanscript_to_term`), outermost first.  It is
    what a proof about the fold's step names: the translation builds the whole function,
    and this reads the branch back out of it, in the context the fold gives it. -/
syntax (name := leanscriptFoldBranch) "#leanscript_fold_branch " term : term

@[term_elab leanscriptFoldBranch]
def elabLeanscriptFoldBranch : TermElab := fun stx expected? => do
  let t ← instantiateMVars (← elabTerm stx[1] none)
  let v ← unfoldHeadConsts t
  let isFold (s : Expr) : Bool :=
    foldNodes.any fun (n, k) => s.isAppOfArity n k
  let isFoldCtor (s : Expr) : Bool :=
    foldCtors.any fun (n, k) => s.isAppOfArity n k
  -- a direct-style fold (`Term.nat_rec'`, …) has its branch last; a fold of a normalized
  -- term (`Term.nat_rec`, …, `LeanScript.ToTerm.Normalize`) has it just before its `Dest`
  let b ← match v.find? fun s => isFold s && !s.hasLooseBVars with
    | some node => pure node.appArg!
    | none => match v.find? fun s => isFoldCtor s && !s.hasLooseBVars with
      | some node => pure node.appFn!.appArg!
      | none => throwError "`#leanscript_fold_branch`: no fold in{indentExpr v}"
  match expected? with
  | some ty => Term.ensureHasType ty b
  | none => return b

/-- `#leanscript_fold_bases t`: the answers for the short arguments of the first fold in
    the term `t` — the `NatRecBases` of a `nat_rec k`, the `ArrayRecBases` of an
    `array_rec k` — which is the argument of the fold just before its branch. -/
syntax (name := leanscriptFoldBases) "#leanscript_fold_bases " term : term

@[term_elab leanscriptFoldBases]
def elabLeanscriptFoldBases : TermElab := fun stx expected? => do
  let t ← instantiateMVars (← elabTerm stx[1] none)
  let v ← unfoldHeadConsts t
  let isBasesFold (s : Expr) : Bool :=
    s.isAppOfArity `LeanScript.Term.nat_rec' 7 || s.isAppOfArity `LeanScript.Term.array_rec' 8
  let isBasesFoldCtor (s : Expr) : Bool :=
    s.isAppOfArity ``LeanScript.Term.nat_rec 10 || s.isAppOfArity ``LeanScript.Term.array_rec 11
  -- as in `#leanscript_fold_branch`: of a normalized term, the bases are the argument
  -- before the branch and its `Dest` (for a `nat_rec`, atoms rather than terms)
  let b ← match v.find? fun s => isBasesFold s && !s.hasLooseBVars with
    | some node => pure node.appFn!.appArg!
    | none => match v.find? fun s => isBasesFoldCtor s && !s.hasLooseBVars with
      | some node => pure node.appFn!.appFn!.appArg!
      | none =>
        throwError "`#leanscript_fold_bases`: no `nat_rec` or `array_rec` in{indentExpr v}"
  match expected? with
  | some ty => Term.ensureHasType ty b
  | none => return b

/-- `#leanscript_to_term_cache_stats`: how many definitions the translation cache holds,
    how often one was reused, and how often two definitions turned out to have the same
    shape and were merged into one tree. -/
syntax (name := toTermCacheStats) "#leanscript_to_term_cache_stats" : command

@[command_elab toTermCacheStats]
def elabToTermCacheStats : Command.CommandElab := fun _ => do
  let st ← cacheRef.get
  logInfo m!"entries: {st.entries.size}, hits: {st.hits}, shape merges: {st.shared}"

/-- `#leanscript_to_term_cache_clear`: empty the translation cache. -/
syntax (name := toTermCacheClear) "#leanscript_to_term_cache_clear" : command

@[command_elab toTermCacheClear]
def elabToTermCacheClear : Command.CommandElab := fun _ => cacheRef.set {}

end LeanScript.ToTerm

end

end
