module

public import NonEmpty.String.Basic
public import NonEmpty.ArrayCorrectByConstruction.Basic
public import NonEmpty.ArrayCorrectByConstruction.Ops
public import NonEmpty.ArrayCorrectByConstruction.Instances
public import NonEmpty.ArrayCorrectByConstruction.Notation

@[expose] public section

namespace NonEmpty.String

open NonEmpty.ArrayCorrectByConstruction

def intercalateArrayCBC (s : String) (xs : NonEmptyArray NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => acc ++ s ++ x) xs.head
