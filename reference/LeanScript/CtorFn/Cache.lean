module

public import LeanScript.ExprCtx
public import LeanScript.Ty.Class
public import LeanScript.Ty.Instances
public import LeanScript.CtorFn.AsType
public meta import LeanScript.Ty.Deriving.Build

@[expose] public section

/-!
# `#leanscript_ctor`: the cache of generated definitions

Every definition `#leanscript_ctor` generates is recorded in an environment extension, so
that it is generated once and reused, here and in every importing module.
-/

meta section

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType?)

/-- `LeanScript.TyWf`, as an expression. -/
def tyWfE : Expr := mkConst ``LeanScript.TyWf


/-! ## The cache -/

/-- One generated definition: what it was generated for (`kind` is `"fn"` for a constructor
    function and `"layout"` for a layout) and its name. -/
structure CtorFnEntry where
  /-- The constructor, or the datatype, it was generated for. -/
  key : Name
  /-- `"fn"` or `"layout"`. -/
  kind : String
  /-- The generated definition. -/
  decl : Name
  deriving Inhabited, BEq, Repr

/-- Every definition `#leanscript_ctor` has generated, here and in every imported module. -/
initialize ctorFnExt : SimplePersistentEnvExtension CtorFnEntry (Array CtorFnEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.flatten }

/-- The definition already generated for `key`, if there is one. -/
def cached? (key : Name) (kind : String) : CoreM (Option Name) := do
  let env ← getEnv
  for e in ctorFnExt.getState env do
    if e.key == key && e.kind == kind && env.contains e.decl then return some e.decl
  return none

/-- The name a generated definition gets: `base ++ suffix`, under the current module's name
    when `owner` was declared in another module. -/
def declNameFor (owner base : Name) (suffix : String) : CoreM Name := do
  let env ← getEnv
  let n := Name.str base suffix
  if (env.getModuleIdxFor? owner).isNone then return n
  return (← getMainModule) ++ n


end LeanScript.CtorFn

end

end
