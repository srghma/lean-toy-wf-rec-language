module

public import LeanScript.Ty.Shape

/-!
# The traversable laws of the schemas and of `TyShape`

Every schema (`LeanRecordSchema`, `CtorsWithPayload`, `LeanTaggedUnionSchema`,
`LeanFamMemberSchema`, `LeanMutualRecFamily`), `LeanPrimTyCovariant` and `TyShape` derives
`Traversable` where it is declared, which gives it its `map` (the derived `Functor.map`)
and `traverse`.  The laws — `LawfulTraversable`, and so `LawfulFunctor`, whose `id_map`
and `comp_map` are the functor laws of `map` — are derived here, all in one module.

They are derived together, and outside an exposed section, because of how Mathlib's
derive handler proves them: it uses auxiliary lemmas private to the module it runs in, so
the laws of a type that has a field of another schema can only be derived in the module
where the laws of that schema are.
-/

public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

deriving instance LawfulTraversable for NonEmptyList
deriving instance LawfulTraversable for LeanScript.LeanRecordSchema
deriving instance LawfulTraversable for LeanScript.CtorsWithPayload
deriving instance LawfulTraversable for LeanScript.LeanTaggedUnionSchema
deriving instance LawfulTraversable for LeanScript.LeanFamMemberSchema
deriving instance LawfulTraversable for LeanScript.LeanMutualRecFamily
deriving instance LawfulFunctor for LeanScript.LeanPrimTyCovariant
deriving instance LawfulTraversable for LeanScript.LeanPrimTyCovariant
deriving instance LawfulTraversable for LeanScript.TyShape

end
