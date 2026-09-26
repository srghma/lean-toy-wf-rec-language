import Lean
import LeanScript.Term.Elab
import LeanScript.Term.Compile
open Lean Elab Command

/-! Scratch file: declare one inductive of each shape the type language distinguishes,
    and list every constant Lean puts in the environment under that name. -/

-- 1. two-constructor enum
inductive Dir where
  | north
  | south

-- 2. three-constructor enum
inductive Dir3 where
  | n
  | s
  | e

-- 3. record
structure Point where
  x : Nat
  y : Nat

-- 4. newtype
structure Wrap where
  v : Nat

-- 5. Option Nat  (Option is built in; scanned separately).  `Opt` is a fresh copy of it,
--    so that the generated constants can be seen without the core library around them.
inductive Opt (α : Type) where
  | none
  | some : α → Opt α

-- 6. recursive tagged union
inductive T where
  | leaf
  | node : T → T → T

-- 7. recursive object (nested through Array)
structure Tree where
  n : Nat
  kids : Array Tree

-- 8. recursive alias (newtype, nested through Array)
structure Rose where
  kids : Array Rose

-- 9. mutual family
mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

-- 10. the original example
inductive Foo where
  | a : Foo
  | b : Nat → Foo → Foo

-- TODO
/-
-/
-- #guard_msgs in
-- def dir_schema : Ty TODO := #leanscript_schema_for_inductive Dir

-- TODO same for all

-- def dumpFor (p : Name) : CommandElabM Unit := do
--   let env ← getEnv
--   let mut acc : Array String := #[]
--   for (n, ci) in env.constants.toList do
--     if p.isPrefixOf n then
--       let kind :=
--         match ci with
--         | .axiomInfo _ => "axiom"
--         | .defnInfo _ => "def"
--         | .thmInfo _ => "theorem"
--         | .opaqueInfo _ => "opaque"
--         | .quotInfo _ => "quot"
--         | .inductInfo _ => "inductive"
--         | .ctorInfo _ => "ctor"
--         | .recInfo _ => "recursor"
--       let t ← liftTermElabM do
--         let fmt ← Meta.ppExpr ci.type
--         pure (toString fmt)
--       let t := t.replace "\n" " "
--       acc := acc.push s!"{kind} {n} : {t}"
--   logInfo m!"===== {p} ({acc.size}) =====\n{String.intercalate "\n" (acc.qsort (· < ·)).toList}"
--
-- #eval dumpFor `Array
-- #eval dumpFor `Dir
-- #eval dumpFor `Dir3
-- #eval dumpFor `Point
-- #eval dumpFor `Wrap
-- #eval dumpFor `Opt
-- #eval dumpFor `Option
-- #eval dumpFor `T
-- #eval dumpFor `Tree
-- #eval dumpFor `Rose
-- #eval dumpFor `Ev
-- #eval dumpFor `Od
-- #eval dumpFor `Foo

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: no public function in this module
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for_all

/-! ## The compiled terms

`#leanjs_compile_term_for_all` compiles every public function of this file into a
`LeanScript.Expr.Term`, bound to `<f>.leanTerm`, and `<f>.leanFn` is that term run by
`LeanScript.Term.evalClosed`.  The report says which functions were compiled and, for
the ones that were refused, why. -/

/--
info: no public function in this module
---
info: LeanTerms of this module
-/
#guard_msgs in
#leanjs_compile_term_for_all
