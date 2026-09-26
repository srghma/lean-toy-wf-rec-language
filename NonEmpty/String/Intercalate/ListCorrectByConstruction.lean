module

public import NonEmpty.String.Basic
public import NonEmpty.ListCorrectByConstruction.Basic
public import NonEmpty.ListCorrectByConstruction.Ops
public import NonEmpty.ListCorrectByConstruction.Instances
public import NonEmpty.ListCorrectByConstruction.Notation

@[expose] public section

namespace NonEmpty.String

open NonEmpty.ListCorrectByConstruction

def intercalateListCBC (s : String) (xs : NonEmptyList NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => acc ++ s ++ x) xs.head
