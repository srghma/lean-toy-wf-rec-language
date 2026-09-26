module

public meta import LeanScript.ToTerm.ObjectExpr

@[expose] public section

meta section

/-!
# The cache, and what may be translated at all

The cache of translated definitions, which survives between calls, and the tests that
refuse a constant the language has no total value for.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The cache of translated definitions -/

/-- One definition that has been translated: the value it was translated from, and the
    translation, as a function of the context it is used in. -/
structure CacheEntry where
  /-- The signature it was translated against. -/
  sg : Expr
  /-- The closed Lean value that was translated. -/
  src : Expr
  /-- The translation: `fun (Γ : Ctx) => …`. -/
  fn : Expr
  /-- The hash of the translation, for the shape lookup. -/
  hash : UInt64
  deriving Inhabited, BEq, Repr

/-- What the cache holds, and what it has done. -/
structure CacheState where
  /-- The definitions translated so far. -/
  entries : Array CacheEntry := #[]
  /-- How often a definition was found already translated. -/
  hits : Nat := 0
  /-- How often a *new* definition turned out to have the shape of one already
      translated, and was replaced by it. -/
  shared : Nat := 0
  deriving Inhabited, BEq, Repr

/-- The cache of translated definitions.  It survives between calls of
    `#leanscript_to_term`, so a function called from two definitions is translated
    once. -/
initialize cacheRef : IO.Ref CacheState ← IO.mkRef {}

/-! ## What may be translated at all -/

/-- Is this constant part of a well-founded recursion — the fixpoint operator, its
    companions, or a recursion on an accessibility proof? -/
def isWfRecursion (n : Name) : Bool :=
  n.components.any (fun p => p == `WellFounded || p == `WellFoundedRecursion) ||
    n == ``Acc.rec || n == ``invImage

/-- Is this the fixpoint a `partial_fixpoint` definition is built from? -/
def isPartialFixpoint (n : Name) : Bool :=
  n.getString! == "fix" && n.getPrefix == `Lean.Order

/-- Is this the compiled form of a structural recursion — `X.brecOn`, `X.binductionOn`,
    the `below` motive, or the unsafe companion of a `partial` definition?

    `Nat.brecOn` and `List.brecOn` are **not** among them: those two are the compiled form
    of a recursion over the two types the grammar has a fold for, and
    `LeanScript.ToTerm.transBrecOn` turns them into that fold. -/
def isCompiledRecursion (n : Name) : Bool :=
  if n == ``Nat.brecOn || n == ``List.brecOn then false else
  let s := n.getString!
  s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
    s == "_unsafe_rec"

/-- Refuse a constant the language has no total value for. -/
def checkConst (n : Name) : MetaM Unit := do
  if isPartialFixpoint n then
    throwError "`#leanscript_to_term`: a partial fixpoint ({n}) is not supported: the \
      grammar has no fixpoint that does not descend"
  if isWfRecursion n then
    throwError "`#leanscript_to_term`: well-founded recursion ({n}) is not supported — \
      the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so \
      write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive"
  if isCompiledRecursion n then
    throwError "`#leanscript_to_term`: {n} is the compiled form of a recursion the \
      grammar cannot express — write the recursion as `Nat.rec` or `List.rec` with a \
      non-dependent motive, which are `nat_rec` and `recTaggedUnion_rec`"
  match ← getConstInfo n with
  | .defnInfo d =>
      if d.safety == .partial then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      if d.safety == .unsafe then
        throwError "`#leanscript_to_term`: `{n}` is `unsafe`"
  | .opaqueInfo _ =>
      if ((← getEnv).find? (n ++ `_unsafe_rec)).isSome then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      throwError "`#leanscript_to_term`: `{n}` is opaque, so there is nothing to \
        translate"
  | .axiomInfo _ =>
      throwError "`#leanscript_to_term`: `{n}` is an axiom, so there is nothing to \
        translate"
  | _ => pure ()

/-- Is a call of this constant inlined?  A constructor and a projection always are, and
    so is anything the author marked inlinable or reducible. -/
def isInlinable (n : Name) : MetaM Bool := do
  if (← getEnv).find? n matches some (.ctorInfo _) then return true
  if (← getProjectionFnInfo? n).isSome then return true
  if ← Lean.isReducible n then return true
  let env ← getEnv
  return Compiler.hasInlineAttribute env n
    || Compiler.hasMacroInlineAttribute env n
    || Compiler.hasInlineIfReduceAttribute env n

/-- Is this constant the recursor of a **recursive** inductive type (`Nat.rec`,
    `List.rec`, the `rec` of a user tree or of a `mutual` block), or its `recOn`?  The
    recursors of non-recursive types (`Eq.rec` in a cast, `False.rec`, `And.rec`) are not:
    they are case analyses, not recursions, and neither is the recursor of the
    accessibility predicate a well-founded recursion is built on. -/
def isRecursiveRecursor (n : Name) : MetaM Bool := do
  if n.isAnonymous || isWfRecursion n then return false
  let env ← getEnv
  let ind? : Option Name := match env.find? n with
    | some (.recInfo r) => some r.getMajorInduct
    | _ => match n with
      | .str ind@(.str _ _) "recOn" => if isAuxRecursor env n then some ind else none
      | _ => none
  let some ind := ind? | return false
  let some (.inductInfo iv) := env.find? ind | return false
  return iv.isRec

/-- Is this constant part of the machinery Lean generates for a type or a `match` — an
    auxiliary recursor (`casesOn`, `recOn`, `brecOn`, `below`, …), a `noConfusion`, or the
    auxiliary definition of a `match`?  Their bodies apply a recursor, but they are not
    recursions of the program. -/
def isRecursionMachinery (n : Name) : MetaM Bool := do
  let env ← getEnv
  if isAuxRecursor env n || isNoConfusion env n then return true
  if ← Meta.isMatcher n then return true
  let .str (.str _ _) s := n | return false
  return s == "casesOn" || s == "recOn" || s == "brecOn" || s == "binductionOn" ||
    s == "below" || s == "ibelow" || s == "noConfusion" || s == "noConfusionType" ||
    s == "ctorIdx" || s == "toCtorIdx"

/-- Is this constant a **structural recursion** — a safe definition that Lean compiled
    through a `brecOn` (its own, or that of a `mutual` block), or one whose body applies
    the recursor of a recursive type directly (`natFold n := Nat.rec 0 (fun _ ih => ih + 2)
    n`)?  A call of one is inlined even when it is neither marked inlinable nor declared in
    the signature, so that a recursion split across two top-level definitions (`f n := go n
    0`, with `go` the recursion) is translated: the recursion is the fold it compiles to,
    at the call site. -/
def isStructuralRecursion (n : Name) : MetaM Bool := do
  let some (.defnInfo d) := (← getEnv).find? n | return false
  unless d.safety == .safe do return false
  if ← isRecursionMachinery n then return false
  if Compiler.hasNoInlineAttribute (← getEnv) n then return false
  if (d.value.find? fun s => match s with
      | .const m _ => !m.isAnonymous && !m.isNum && m.getString! == "brecOn"
      | _ => false).isSome then
    return true
  d.value.getUsedConstants.anyM isRecursiveRecursor

/-- The first component of the name of the module that declares `n` (`TermTests` for a
    declaration of `TermTests.StructRecTest.SplitRecursion`); for a declaration of the
    file being elaborated, that of the file. -/
def declModuleRoot (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]?.getD .anonymous).getRoot
  | none => env.mainModule.getRoot

/-- `callsStructuralRecursion`, remembering the definitions already looked at. -/
partial def callsStructuralRecursionAux (n : Name) : StateRefT NameSet MetaM Bool := do
  if (← get).contains n then return false
  modify (·.insert n)
  if ← isStructuralRecursion n then return true
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return false
  unless d.safety == .safe do return false
  if Compiler.hasNoInlineAttribute env n then return false
  let root := declModuleRoot env n
  d.value.getUsedConstants.anyM fun m => do
    if m == n then return false
    if ← isStructuralRecursion m then return true
    -- a wrapper is followed only within the program's own modules, never into the
    -- libraries it builds on
    if declModuleRoot env m != root then return false
    callsStructuralRecursionAux m

/-- Is this constant a structural recursion, or a **wrapper** of one — a safe definition
    whose body calls a structural recursion (of any module), directly or through any
    number of further wrappers (`f n := g (n + 1)`, `g n := go n 0`)?  The wrappers
    followed are those of the program's own modules (the modules whose name starts as the
    wrapper's does: `TermTests.…` for a wrapper of `TermTests.A`), so a chain of wrappers
    may be split across files, but a definition of a library the program imports
    (`Init`, `Std`, `Mathlib`) is not taken for a wrapper because something it calls
    recurses. -/
def callsStructuralRecursion (n : Name) : MetaM Bool :=
  (callsStructuralRecursionAux n).run' {}

end LeanScript.ToTerm

end

end
