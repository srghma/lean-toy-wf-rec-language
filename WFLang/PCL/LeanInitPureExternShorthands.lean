module
prelude
public import LeanScript.LeanInitPureExterns
meta import LeanScript.CatalogueShorthands

set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The entries of the catalogue, as values of `LeanInitPureExtern`

The catalogue is in two levels: an entry is a constructor of its family (`PreludeExtern`,
`StringBasicExtern`, ...), and `LeanInitPureExtern` has one constructor per family.  For
each entry this module gives a shorthand in `LeanInitPureExtern`'s namespace, which builds
the entry and wraps it in the constructor of its family:
`LeanInitPureExtern.lean_nat_add a b` is `.preludeExtern (.lean_nat_add a b)`.  So an entry is
written `.lean_nat_add a b` wherever a `LeanInitPureExtern` (or `LeanScript.Extern`) is
expected, and the shorthands are `@[match_pattern]`, so they can be matched on as well.
They are reducible: they unfold to the two constructors.

Every shorthand takes the parameters of `LeanInitPureExtern` first (implicitly, in its
order), whichever of them its family uses: `#leanscript_to_term` applies a shorthand to
them.

The shorthands are computed from the constructors of the families by
`derive_catalogue_shorthands` (`LeanScript.CatalogueShorthands`), so nothing here needs to
be regenerated when the catalogue changes.

A coercion from each family to `LeanInitPureExtern` would not replace them: `.lean_nat_add`
is looked up by name in the namespace of the expected type, a pattern cannot go through a
coercion, and `#leanscript_to_term` finds an entry by the name of its shorthand.
-/

derive_catalogue_shorthands LeanInitPureExtern

end LeanScript

end
