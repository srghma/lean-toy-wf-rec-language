module

public meta import Lean.Elab.Command

public section

/-!
# `derive_catalogue_shorthands`: one shorthand per entry of a two-level catalogue

A *two-level catalogue* is an inductive `Outer` each of whose constructors wraps one entry
of a *family*, another inductive:

```
inductive Outer : MyTy → Type where
  | fooExtern {τ : MyTy} : FooExtern … τ → Outer τ
  | barExtern {τ : MyTy} : BarExtern … τ → Outer τ
```

(`LeanScript.LeanInitPureExtern` is one.)  `derive_catalogue_shorthands Outer` adds, for
every constructor `FooExtern.c` of every family, the definition `Outer.c`, which builds the
entry and wraps it in the constructor of its family:

```
@[match_pattern, reducible] def Outer.c : <the arguments of FooExtern.c> → Outer … τ :=
  fun x₁ … xₙ => .fooExtern (.c x₁ … xₙ)
```

So an entry is written `.c x₁ … xₙ` wherever an `Outer` is expected (and matched on as
well, since the shorthand is `@[match_pattern]`).  Each shorthand takes all the parameters
of `Outer` but its index first, implicitly and in their order, whichever of them its family
uses, so a shorthand can be applied to the parameters of `Outer` like a constructor of
`Outer`; its explicit arguments are the ones of `FooExtern.c`.

The shorthands are computed from the constructors themselves, so they never need to be
regenerated when an entry is added to, changed in or removed from a family.
-/

namespace LeanScript

open Lean Meta Elab Command

/-- The leading `fun`s of `e`, with the `autoParam`/`optParam` annotations of their binder
    types removed (they belong in the type of a definition, not in its value). -/
meta def dropBinderAnnotations : Expr → Expr
  | .lam n d b bi => .lam n d.cleanupAnnotations (dropBinderAnnotations b) bi
  | e => e

/-- Add the shorthand `outer.c` of the entry `c` of the family that the constructor `wrap`
    of `outer` wraps. -/
meta def addCatalogueShorthand (outer wrap c : Name) : MetaM Unit := do
  let wrapInfo ← getConstInfoCtor wrap
  let cInfo ← getConstInfoCtor c
  unless wrapInfo.levelParams.isEmpty && cInfo.levelParams.isEmpty do
    throwError "`derive_catalogue_shorthands`: `{.ofConstName wrap}` or `{.ofConstName c}` \
      is universe polymorphic, which is not supported"
  let name := outer ++ Name.mkSimple c.getString!
  forallTelescope wrapInfo.type fun xs _ => do
    -- `xs` are the parameters of `outer` and the entry of the family
    let params := xs.extract 0 wrapInfo.numParams
    let some entry := xs.back? | throwError "`derive_catalogue_shorthands`: \
      the constructor `{.ofConstName wrap}` holds no entry"
    -- the family, applied to (some of) the parameters of `outer` and to the index of
    -- `outer` (which Lean promotes to a parameter, since it is the same in the type of
    -- every constructor of `outer`)
    let famArgs := (← whnf (← inferType entry)).getAppArgs
    let some outerIdx := famArgs.back? | throwError "`derive_catalogue_shorthands`: \
      the family of `{.ofConstName wrap}` has no index"
    let famParams := famArgs.extract 0 cInfo.numParams
    -- if Lean promoted the index of the family to a parameter too (every entry of the
    -- family binds it the same way), the entry takes it as its first argument
    let idxArgs := if famParams.contains outerIdx then #[outerIdx] else #[]
    forallTelescope (← instantiateForall cInfo.type famParams) fun args _ => do
      let e := mkAppN (mkConst c) (famParams ++ args)
      -- `wrap` applied to `e`: its parameters are the ones of the entry, and those the
      -- family does not use are the shorthand's own; the index is fixed by the entry
      let (ms, _, _) ← forallMetaTelescope wrapInfo.type
      unless ← isDefEq (← inferType ms.back!) (← inferType e) do
        throwError "`derive_catalogue_shorthands`: `{.ofConstName wrap}` cannot hold{indentExpr e}"
      let mut own := #[]
      for i in [0:wrapInfo.numParams] do
        let p := params[i]!
        let m ← instantiateMVars ms[i]!
        if m.isMVar then
          m.mvarId!.assign p
        if (m.isMVar || m == p) && p != outerIdx then
          own := own.push p
      let body ← instantiateMVars (mkAppN (mkConst wrap) ((ms.extract 0 wrapInfo.numParams).push e))
      if body.hasMVar then
        throwError "`derive_catalogue_shorthands`: internal: {body} is not determined"
      let xs := own ++ idxArgs ++ args
      let (value, type) ← withNewBinderInfos (idxArgs.map (·.fvarId!, .default)) do
        return (dropBinderAnnotations (← mkLambdaFVars xs body),
          ← mkForallFVars xs (← inferType body))
      let decl := Declaration.defnDecl
        { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
      withExporting do
        addDecl decl
        setReducibleAttribute name
        matchPatternAttr.setTag name
        addDocStringCore name s!"`{c.getPrefix.getString!}.{c.getString!}`, \
          as an entry of the catalogue `{outer}`."
      compileDecl decl

/-- `derive_catalogue_shorthands Outer`: for every entry `FooExtern.c` of every family
    wrapped by a constructor `Outer.fooExtern` of `Outer`, the shorthand
    `Outer.c x₁ … xₙ := .fooExtern (.c x₁ … xₙ)`, reducible and usable in patterns (see the
    module doc). -/
syntax (name := deriveCatalogueShorthands) "derive_catalogue_shorthands " ident : command

@[command_elab deriveCatalogueShorthands]
meta def elabDeriveCatalogueShorthands : CommandElab
  | `(derive_catalogue_shorthands $id) => liftTermElabM do
      let outer ← realizeGlobalConstNoOverloadWithInfo id
      let outerInfo ← getConstInfoInduct outer
      for wrap in outerInfo.ctors do
        let wrapInfo ← getConstInfoCtor wrap
        -- the family is the type of the last field of the constructor
        let fam ← forallTelescope wrapInfo.type fun xs _ => do
          let some entry := xs.back? | throwError "`derive_catalogue_shorthands`: \
            the constructor `{.ofConstName wrap}` holds no entry"
          let some fam := (← whnf (← inferType entry)).getAppFn.constName? |
            throwError "`derive_catalogue_shorthands`: the entry of `{.ofConstName wrap}` \
              is not an inductive"
          pure fam
        for c in (← getConstInfoInduct fam).ctors do
          addCatalogueShorthand outer wrap c
  | _ => throwUnsupportedSyntax

end LeanScript

end
