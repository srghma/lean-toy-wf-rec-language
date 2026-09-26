module

public import LeanScript.Expr.Build
public meta import LeanScript.ToTerm.Elab

/-!
# The translator's names of `LeanScript.Term` exist

The translator (`LeanScript/ToTerm/`) and the constructor functions
(`LeanScript/CtorFn/Emit.lean`) do not import `LeanScript.Expr.Term`, so that they build in
parallel with it.  They therefore write the names of the types of `Expr/Term.lean` and of
their constructors with a **single** backquote (`` `LeanScript.Term.lam ``), which Lean does
not check, instead of a double one (``` ``LeanScript.Term.lam ```), which would need the
declaration in scope.

This file puts the check back: it reads those source files and fails if one of them names
a declaration `LeanScript.X.…` of a type `X` of `Expr/Term.lean` that does not exist.  It
imports `LeanScript.ToTerm.Elab`, so it is rebuilt whenever the translator changes.
-/

namespace TermTests.ToTermNames

open Lean Elab Command

/-- The types declared by the `mutual` block of `LeanScript/Expr/Term.lean`, and the
    plain-dispatch abbreviations (`TaggedUnionCases`, …) declared after it. -/
meta def termTypes : List String :=
  ["Term", "Terms", "ArrayRecBases", "Spine", "TaggedUnionCases", "CtorsWithPayloadCases",
   "TaggedUnionCasesRest", "TaggedUnionSomeCases", "EnumCases", "EnumSomeCases",
   "TaggedUnionFoldCases", "CtorsWithPayloadFoldCases", "TaggedUnionFoldCasesRest",
   "FoldKBranch", "TaggedUnionFoldKCases", "CtorsWithPayloadFoldKCases",
   "TaggedUnionFoldKCasesRest", "FamilyMemberValue", "FamilyMemberCases",
   "FamilyMemberSomeCases", "FamilyMemberFoldCases", "FamilyFoldCases", "FamilyFoldKBranch",
   "FamilyMemberFoldKCases", "FamilyTaggedUnionFoldKCases",
   "FamilyCtorsWithPayloadFoldKCases", "FamilyTaggedUnionFoldKCasesRest", "FamilyFoldKCases"]

/-- A character of a (non-escaped) identifier. -/
meta def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '?' || c == '!'

/-- The names `` `LeanScript.X.… `` in `src`, for `X` one of `termTypes`, that are written in
    code: a name directly followed by a closing backquote is a name in a doc comment, and
    is skipped. -/
meta def termNamesIn (src : String) : List String := Id.run do
  let mut out := []
  for piece in (src.splitOn "`LeanScript.").drop 1 do
    let ident := (piece.takeWhile isIdChar).toString
    let rest := (piece.drop ident.length).toString
    let ident := if ident.endsWith "." then (ident.dropEnd 1).toString else ident
    if rest.startsWith "`" then continue
    match ident.splitOn "." with
    | ty :: _ => if termTypes.contains ty then out := ("LeanScript." ++ ident) :: out
    | [] => pure ()
  return out

/-- The source files that write the names with a single backquote. -/
meta def sourceFiles : IO (Array System.FilePath) := do
  let toTerm ← System.FilePath.readDir "LeanScript/ToTerm"
  return (toTerm.map (·.path)).filter (·.extension == some "lean") |>.push
    "LeanScript/CtorFn/Emit.lean"

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for file in ← sourceFiles do
    for n in termNamesIn (← IO.FS.readFile file) do
      checked := checked + 1
      unless env.contains n.toName do
        throwError "`{file}` names `{n}`, which is not a declaration of `LeanScript.Expr.Term`"
  if checked < 100 then
    throwError "only {checked} names found: the scan of the translator's sources is broken"

end TermTests.ToTermNames
