module

public import LeanScript.Expr.Build
public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude
public meta import LeanScript.KernelRfl

/-!
# Externs as terms

`Term.extern` holds a pure extern of `Init` applied to its arguments (and to the proofs it
takes), and `Term.eval` gives it the value of the Lean function it implements, called on
them.  Each check below is settled by the kernel.

The catalogue is in two levels (a family of entries per section of `Init`, and
`LeanInitPureExtern` with one constructor per family), so no inductive has more
constructors than compiled code can build (the runtime keeps a constructor's number in
8 bits, and only `0 … 243` are for ordinary constructors): a *definition* may build any
entry, `lean_string_compare` included (`externCompare` below).
-/

namespace TermTests

open LeanScript

/-- `Nat.add 2 3`, as a term. -/
def externAdd : Term ⟨[], List.nodup_nil⟩ [] (.prim .nat) := .extern (.lean_nat_add 2 3)

-- [SKIPPED BY PROFILE_LAKE] example : Term.run' externAdd = 5 := by decide +kernel

/-- An extern used inside a larger term: `if 2 < 3 then 7 * 6 else 0`. -/
def externIf : Term ⟨[], List.nodup_nil⟩ [] (.prim .nat) :=
  .bool_casesOn' (.extern (.lean_nat_dec_lt 2 3)) (.extern (.lean_nat_mul 7 6)) (.nat_mk 0)

-- [SKIPPED BY PROFILE_LAKE] example : Term.run' externIf = 42 := by decide +kernel

/-- An extern applied through a `let`: the bound value is an extern, the body a variable. -/
def externLet : Term ⟨[], List.nodup_nil⟩ [] (.prim .string) :=
  .letE' (.extern (.lean_string_append__String_append "lean" "script")) (.var .head)

-- [SKIPPED BY PROFILE_LAKE] example : Term.run' externLet = "leanscript" := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- An extern of `UInt32`. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_uint32_add 4000000000 500000000) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.prim .uint32)) = 205032704 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- An extern whose result is an array: arrays denote Lean arrays. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_array_push (TyWf.prim .nat) #[1, 2] 3) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.array (.prim .nat))) = #[1, 2, 3] := by kernel_rfl

/-- `String.compare "a" "b"`, as a (compiled) definition.  `lean_string_compare` is the last
    entry of the catalogue; with the catalogue in one inductive of 460 constructors, its
    number (459) was too big for compiled code, and this definition did not compile. -/
def externCompare : Term ⟨[], List.nodup_nil⟩ [] TyWf.ordering := .extern (.lean_string_compare "a" "b")

-- [SKIPPED BY PROFILE_LAKE] example : Term.run' externCompare = TyWf.Den.ofOrdering (String.compare "a" "b") := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An entry is written through its shorthand, `.lean_nat_add 2 3`, which unfolds to the
-- [SKIPPED BY PROFILE_LAKE]     constructor of its family wrapped in the one of the catalogue. -/
-- [SKIPPED BY PROFILE_LAKE] example : (.lean_nat_add 2 3 : Extern (.prim .nat)) = .preludeExtern (.lean_nat_add 2 3) := by kernel_rfl

/-- The shorthands are patterns too. -/
def isNatAdd : {τ : TyWf} → Extern τ → Bool
  | _, .lean_nat_add _ _ => true
  | _, _ => false

-- [SKIPPED BY PROFILE_LAKE] example : isNatAdd (.lean_nat_add 2 3 : Extern (.prim .nat)) = true := by decide +kernel
-- [SKIPPED BY PROFILE_LAKE] example : isNatAdd (.lean_nat_sub 2 3 : Extern (.prim .nat)) = false := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- An extern whose result is an `Ordering`: the enum with three constructors. -/
-- [SKIPPED BY PROFILE_LAKE] example (a b : String) : Term.run' (.extern (.lean_string_compare a b) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] TyWf.ordering) = TyWf.Den.ofOrdering (String.compare a b) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An extern whose result is an `Option`: the tagged union `none | some α`. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_string_utf8_get_opt__String_Pos_Raw_get? "ab" ⟨1⟩) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (TyWf.option (.prim .char))) = TyWf.Den.ofOption (α := .prim .char) (some 'b') :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An extern that takes a proof holds it: `Array.getInternal #[1, 2, 3] 1 h`, with the
-- [SKIPPED BY PROFILE_LAKE]     proof `h : 1 < #[1, 2, 3].size`, is `Array.getInternal` called with that proof. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_array_fget (TyWf.prim .nat) #[1, 2, 3] 1 (by decide)) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.prim .nat)) = 2 := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] /-- `String.Pos.next`: its argument is a position into the string `s`, whose type names
-- [SKIPPED BY PROFILE_LAKE]     `s`, so `s` is a parameter of the entry, fixed where the term is written. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_string_utf8_next_fast__String_Pos_next
-- [SKIPPED BY PROFILE_LAKE]       ("ab" : String).startPos (by decide)) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.prim (.stringPos "ab"))) = ("ab" : String).startPos.next (by decide) :=
-- [SKIPPED BY PROFILE_LAKE]   by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `Lean.Name.beq`: a `Lean.Name` is the recursive tagged union
-- [SKIPPED BY PROFILE_LAKE]     `anonymous | str self String | num self Nat` (`TyWf.leanName`). -/
-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.b)) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.prim .bool)) = true := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : Term.run' (.extern (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.«1»)) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (.prim .bool)) = false := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf Lean.Name = TyWf.leanName := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An extern whose result is a pair: the record of its two fields.  `Float.frExp` does not
-- [SKIPPED BY PROFILE_LAKE]     reduce in the kernel, so this only checks that the value is the pair `Float.frExp`
-- [SKIPPED BY PROFILE_LAKE]     answers with. -/
-- [SKIPPED BY PROFILE_LAKE] example (x : Float) : Term.run' (.extern (.lean_float_frexp x) :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (TyWf.prod (.prim .float) (.prim .int))) =
-- [SKIPPED BY PROFILE_LAKE]       TyWf.Den.ofProd (α := .prim .float) (β := .prim .int) (Float.frExp x) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An extern whose result is a list: the recursive tagged union `nil | cons α self`, the
-- [SKIPPED BY PROFILE_LAKE]     model of `List`; `Ty.DenRec.toList` reads it back. -/
-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .nat) (Term.run' (.extern (.lean_array_to_list (TyWf.prim .nat)
-- [SKIPPED BY PROFILE_LAKE]     #[1, 2, 3]) : Term ⟨[], List.nodup_nil⟩ [] (TyWf.list (.prim .nat)))) = [1, 2, 3] := by decide +kernel

-- [SKIPPED BY PROFILE_LAKE] example : Ty.DenRec.toList (.prim .char) (Term.run' (.extern (.lean_string_data__String_toList "ab") :
-- [SKIPPED BY PROFILE_LAKE]     Term ⟨[], List.nodup_nil⟩ [] (TyWf.list (.prim .char)))) = ['a', 'b'] := by decide +kernel

/-! ## The derived type formers are the models of the Lean types

The externs use the same model of `List`, `Option`, `×` and `Ordering` as the rest of the
language: the model `LeanScriptTyWf` gives the Lean type. -/

-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf (List Nat) = TyWf.list (.prim .nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf (Option Char) = TyWf.option (.prim .char) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf (Float × Int) = TyWf.prod (.prim .float) (.prim .int) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyWfOf Ordering = TyWf.ordering := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : tyOf Ordering = .enum ⟨0, -1⟩ := by kernel_rfl

end TermTests
