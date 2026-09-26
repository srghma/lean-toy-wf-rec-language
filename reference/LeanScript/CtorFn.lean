module

public import LeanScript.Expr.Build
public import LeanScript.Ty.Class
public import LeanScript.Ty.Instances
public import LeanScript.CtorFn.AsType
public meta import LeanScript.CtorFn.Emit

@[expose] public section

/-!
# `#leanscript_ctor`: a constructor of any datatype, as a function on terms

```lean
#leanscript_ctor `Process `halt      -- the constructor `Process.halt`
#leanscript_ctor `ProcessOption `some
#leanscript_ctor `Option `some
#leanscript_ctor `Prod               -- a type with one constructor names it
#leanscript_layout `Process `step    -- the type of what that constructor builds
```

`#leanscript_ctor I c` is a **term**: the function that builds a `LeanScript.Term` out of the
terms of the fields of the constructor `I.c`.  `#leanscript_layout I c` is the function that
gives the `TyWf` of what it builds.  Both are generated the first time they are asked for,
as the definitions

| name | what it is |
| :-- | :-- |
| `I.c.leanScriptCtor` | the constructor function |
| `I.c.leanScriptLayout`, or `I.leanScriptLayout` | its layout (see *two kinds of datatype*) |

and are **cached**: the table of generated functions is an environment extension, so a later
`#leanscript_ctor` of the same constructor — in the same module or in any module that imports
it — is the constant already there, and nothing is generated twice.  When `I` belongs to
another module the names are put under the current module's name, so that two modules that do
not import each other can both ask for `Option.some` without a clash.

## The arguments of the function

The function takes the arguments the Lean constructor takes, in the same order, with a
**type** replaced by its `TyWf` and a **value** replaced by a `Term`:

```lean
Process.halt  : (α : Type) → (HaltedState : Type) → (HaltedState → Nat) → Process α
#leanscript_ctor `Process `halt :
  {Sg : Sig} → {Γ : Ctx} → (α HaltedState : TyWf) →
    Term Sg Γ (HaltedState ⇒ .prim .nat) →
      Term Sg Γ (Process.halt.leanScriptLayout α HaltedState)
```

A type is a parameter of the datatype, one of its type indices, or a type field of the
constructor (an existential).  A field whose type the language has **no tree for** — first of
all an occurrence of the datatype itself or of a member of its `mutual` block, but also a
type without a `LeanScriptTyWf` instance or a type that depends on a value — gets its tree
from one more `TyWf` argument, named after the field (`procTy`, `transTy`, …) and placed after
the type arguments.  Two fields of the same Lean type share that argument.  So a recursive
datatype is built **one layer at a time**: `List.cons` takes the tree of its tail, whatever it
is; this is exactly how a closed value of a datatype with existentials (`Process`) is written
down, where every layer may choose different types.

Every other field type is translated: a type argument is its `TyWf`, a function type is
`TyWf.fn` (a domain the language erases — `Unit`, a proof, an instance — is dropped), and an
application of a type former (`Option S`, `S × Nat`, `Array S`, `List S`, …) is the tree of
the former's own `LeanScriptTyWf` instance with the arguments' trees in place — rebuilt with
the bundled smart constructors (`TyWf.taggedUnion`, `TyWf.record`, …) when the instance's tree
is not recursive, and `tyWfOf (List S.AsType)` otherwise (`LeanScript.TyWf.AsType`).  A field
the language erases is not an argument at all.

Note that a recursive datatype built one layer at a time is **not** the type its
`LeanScriptTyWf` instance gives it: `tyWfOf (List α)` is a recursive tagged union, and a list
of it is built by `#leanscript_to_term`, not by `List.cons`'s constructor function.

## Two kinds of datatype

* **No existentials** (every type field of every constructor is one of the type indices of
  its result, as `ProcessOption`'s `State` is): the datatype is one type of the language,
  shared by all its constructors — its record, its tagged union, its enum, `Bool`, or its
  one field — and each constructor builds that type, with its constructor number.  Its layout
  is `I.leanScriptLayout`, which takes the trees of **all** constructors' fields, so
  `ProcessOption.none` takes the tree of `proc` too.
* **With existentials** (`Process`): each constructor application may choose different types,
  so each constructor builds its own layout, `I.c.leanScriptLayout`: its record, or its one
  field.  Where values built with different choices meet, the caller puts them into a union
  of its own — `#leanscript_to_term` uses `TyWf.oneOf` (`LeanScript.ToTerm.Existential`).

`ensureCtorFn` can also generate the function for a use at which some type variables are
`Unit`: the language has no `Unit` to pass, so those are not arguments, and the `Unit` fields
and binders they give rise to are dropped (the names get the suffix `_erased…`).
`#leanscript_to_term` asks for these; the syntax `#leanscript_ctor I c` always gives the
general function.

A datatype whose model is a terminal type (`Nat`, `String`, `Char`, …) or a built-in type
former (`Array`, `Thunk`) has no constructor function — its values are literals, or have an
introduction form of their own; `Bool` is the enum of its two constructors, and an enum
whose instance chooses its own numbering (`Ordering`) keeps it.  A constructor that carries
no value (`Unit.unit`, `PUnit.unit`, a structure without fields), a proposition, and a
datatype that hides a *family* of types (`Elem : State → Type`) are refused.

## Commands

* `#leanscript_ctor I c`, written as a command, generates (or finds) the two definitions and
  shows the signature of the constructor function.
* `#leanscript_ctor_cache` lists every generated definition, here and in the imported
  modules.
-/


meta section

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType?)

/-! ## The elaborators -/

/-- `#leanscript_ctor I c`: the constructor function of the constructor `I.c`, generated the
    first time and cached.  `#leanscript_ctor I.c` names the constructor in full, and
    `#leanscript_ctor I` names the only constructor of `I`. -/
syntax:max (name := leanscriptCtor) "#leanscript_ctor " name (ppSpace name)? : term

/-- `#leanscript_layout I c`: the layout of what `#leanscript_ctor I c` builds, as a function
    of its type arguments. -/
syntax:max (name := leanscriptLayout) "#leanscript_layout " name (ppSpace name)? : term

/-- A name as written, resolved against the open namespaces. -/
def resolveName (n : Name) : TermElabM Name := do
  try resolveGlobalConstNoOverload (mkIdent n)
  catch _ =>
    if (← getEnv).contains n then return n
    throwError "`#leanscript_ctor`: unknown constant `{n}`"

/-- A type written through an abbreviation (`Unit` is `PUnit`) is the datatype it unfolds
    to. -/
def unfoldToInductive (n : Name) : MetaM Name := do
  match (← getEnv).find? n with
  | some (.defnInfo d) =>
      let v ← lambdaTelescope d.value fun _ b => whnf b
      match v.getAppFn with
      | .const m _ => if (← getEnv).find? m matches some (.inductInfo _) then return m else return n
      | _ => return n
  | _ => return n

/-- The constructor the syntax names. -/
def ctorOfSyntax (stx : Syntax) : TermElabM Name := do
  let some n1 := stx[1].isNameLit? | throwUnsupportedSyntax
  let n2? := stx[2].getOptional?.bind (·.isNameLit?)
  let env ← getEnv
  match n2? with
  | some n2 =>
      let i ← unfoldToInductive (← resolveName n1)
      let some (.inductInfo ind) := env.find? i
        | throwError "`#leanscript_ctor`: `{i}` is not an inductive type"
      if ind.ctors.contains (i ++ n2) then return i ++ n2
      let c ← try resolveName n2 catch _ =>
        throwError "`#leanscript_ctor`: `{i}` has no constructor `{n2}`"
      unless ind.ctors.contains c do
        throwError "`#leanscript_ctor`: `{c}` is not a constructor of `{i}`"
      return c
  | none =>
      let x ← unfoldToInductive (← resolveName n1)
      match env.find? x with
      | some (.ctorInfo _) => return x
      | some (.inductInfo ind) =>
          match ind.ctors with
          | [c] => return c
          | _ => throwError "`#leanscript_ctor`: `{x}` has {ind.ctors.length} constructors; \
              name the one you mean"
      | _ => throwError "`#leanscript_ctor`: `{x}` is not a constructor"

@[term_elab leanscriptCtor]
def elabLeanscriptCtor : TermElab := fun stx expected? => do
  let c ← ctorOfSyntax stx
  let (_, fn) ← ensureCtorFn c
  elabTerm (mkCIdentFrom stx fn) expected?

@[term_elab leanscriptLayout]
def elabLeanscriptLayout : TermElab := fun stx expected? => do
  let c ← ctorOfSyntax stx
  let (lay, _) ← ensureCtorFn c
  elabTerm (mkCIdentFrom stx lay) expected?

/-- `#leanscript_ctor I c`, as a **command**: generate (or find in the cache) the constructor
    function of `I.c` and its layout, and show the signature of the function. -/
syntax (name := leanscriptCtorCmd) "#leanscript_ctor " name (ppSpace name)? : command

@[command_elab leanscriptCtorCmd]
def elabLeanscriptCtorCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let c ← ctorOfSyntax stx
  let (_, fn) ← ensureCtorFn c
  logInfo (MessageData.signature fn)

/-- `#leanscript_ctor_cache`: the constructor functions and layouts generated so far, here
    and in the imported modules — what a later `#leanscript_ctor` reuses. -/
syntax (name := leanscriptCtorCache) "#leanscript_ctor_cache" : command

@[command_elab leanscriptCtorCache]
def elabLeanscriptCtorCache : Command.CommandElab := fun _ => do
  let env ← getEnv
  let es := (ctorFnExt.getState env).filter (env.contains ·.decl)
  if es.isEmpty then
    logInfo m!"no constructor function has been generated"
  else
    logInfo (MessageData.joinSep (es.toList.map fun e =>
      m!"{e.kind} of {e.key}: {e.decl}") "\n")

end LeanScript.CtorFn

end

end
