import RequestProject.WFLang.Core.PExprMap
import RequestProject.WFLang.PCL.Lang

/-!
# Tests for the instances of the grammar datatypes

Checks that the derived instances are found (`DecidableEq`, `BEq`, `ReflBEq`, `LawfulBEq`,
`Repr`, `Hashable`, `LawfulHashable`, `Ord`, `Inhabited`, `IsEmpty`), that decidable equality
evaluates (both by `decide` in the kernel and by `#eval`), and exercises renaming and traversal.
-/

namespace WFLang.InstanceTests

open WFLang WFLang.PCL

/-! ## Instances are found -/

section Found
variable (Γ : List Ty) (t a b c : Ty) (ts : List Ty) (fs : List Fn) (f : Fn) (js : JScope Γ t)

example : DecidableEq Ty := inferInstance
example : LawfulBEq Ty := inferInstance
example : ReflBEq Ty := inferInstance
example : LawfulHashable Ty := inferInstance
example : Ord Ty := inferInstance
example : Inhabited Ty := inferInstance
example : Repr Ty := inferInstance

example : DecidableEq t.denote := inferInstance
example : LawfulBEq t.denote := inferInstance
example : Repr t.denote := inferInstance
example : Hashable t.denote := inferInstance

example : DecidableEq Sig := inferInstance
example : LawfulBEq Sig := inferInstance
example : LawfulHashable Sig := inferInstance
example : Inhabited Sig := inferInstance
example : Repr Sig := inferInstance

example : DecidableEq (Var Γ t) := inferInstance
example : LawfulBEq (Var Γ t) := inferInstance
example : LawfulHashable (Var Γ t) := inferInstance
example : Repr (Var Γ t) := inferInstance
example : IsEmpty (Var [] t) := inferInstance

example : DecidableEq (BinOp a b c) := inferInstance
example : LawfulBEq (BinOp a b c) := inferInstance
example : LawfulHashable (BinOp a b c) := inferInstance
example : Repr (BinOp a b c) := inferInstance

example : DecidableEq (UnOp a b) := inferInstance
example : LawfulBEq (UnOp a b) := inferInstance
example : LawfulHashable (UnOp a b) := inferInstance
example : Repr (UnOp a b) := inferInstance

example : DecidableEq (PExpr Γ t) := inferInstance
example : LawfulBEq (PExpr Γ t) := inferInstance
example : ReflBEq (PExpr Γ t) := inferInstance
example : LawfulHashable (PExpr Γ t) := inferInstance
example : Repr (PExpr Γ t) := inferInstance
example : Inhabited (PExpr Γ t) := inferInstance

example : DecidableEq (PExprs Γ ts) := inferInstance
example : LawfulBEq (PExprs Γ ts) := inferInstance
example : LawfulHashable (PExprs Γ ts) := inferInstance
example : Repr (PExprs Γ ts) := inferInstance
example : Inhabited (PExprs Γ ts) := inferInstance

example : DecidableEq (FnVar fs f) := inferInstance
example : LawfulBEq (FnVar fs f) := inferInstance
example : Repr (FnVar fs f) := inferInstance

example : DecidableEq (JVar js) := inferInstance
example : LawfulBEq (JVar js) := inferInstance
example : Repr (JVar js) := inferInstance
example : IsEmpty (FnVar [] f) := inferInstance
example : Inhabited (JScope Γ t) := inferInstance

end Found

/-! ## Decidable equality computes -/

/-- `x % y` over the context `[x, y]`. -/
def modXY : PExpr [.nat, .nat] .nat := .bin .mod (.var .here) (.var (.there .here))

example : modXY = .bin .mod (.var .here) (.var (.there .here)) := by decide
example : modXY ≠ .bin .mod (.var (.there .here)) (.var .here) := by decide
example : (PExpr.lit (.list .int) [1, -2] : PExpr [] _) ≠ .lit _ [1, 2] := by decide
example : (Ty.prod .nat (.list .bool)) ≠ Ty.prod .nat (.list .int) := by decide
example : (⟨[.nat, .nat], .nat⟩ : Sig) = ⟨[.nat, .nat], .nat⟩ := by decide

/-- info: true -/
#guard_msgs in
#eval modXY == .bin .mod (.var .here) (.var (.there .here))

/-- info: false -/
#guard_msgs in
#eval modXY == .bin .div (.var .here) (.var (.there .here))

/-- info: true -/
#guard_msgs in
#eval hash modXY == hash (PExpr.bin .mod (.var .here) (.var (.there .here)) : PExpr [.nat, .nat] _)

/--
info: WFLang.PExpr.bin
  (WFLang.BinOp.mod)
  (WFLang.PExpr.var (WFLang.Var.here))
  (WFLang.PExpr.var (WFLang.Var.there (WFLang.Var.here)))
-/
#guard_msgs in
#eval modXY

/-- info: WFLang.PExpr.lit (WFLang.Ty.prod (WFLang.Ty.nat) (WFLang.Ty.list (WFLang.Ty.int))) (3, [-1]) -/
#guard_msgs in
#eval (PExpr.lit (.prod .nat (.list .int)) (3, [-1]) : PExpr [] _)

/-- info: Ordering.lt -/
#guard_msgs in
#eval compare Ty.nat Ty.bool

/-! ## Renaming and traversal -/

/-- Swap the two variables of `[x, y]` (both of type `nat`). -/
def swap : ∀ {t : Ty}, Var [.nat, .nat] t → Var [.nat, .nat] t
  | _, .here => .there .here
  | _, .there .here => .here

example : modXY.rename swap = .bin .mod (.var (.there .here)) (.var .here) := by decide
example : (modXY.rename swap).rename swap = modXY := by decide
example : (modXY.rename swap).eval ((7, 3, ()) : Env [.nat, .nat]) = 3 % 7 := rfl

/-- A traversal in `Option` that fails on the variable `y`. -/
def noY : ∀ {t : Ty}, Var [.nat, .nat] t → Option (Var [.nat] t)
  | _, .here => some .here
  | _, .there _ => none

/-- info: none -/
#guard_msgs in
#eval modXY.traverseVars noY

/-- info: some (WFLang.PExpr.bin (WFLang.BinOp.add) (WFLang.PExpr.var (WFLang.Var.here)) (WFLang.PExpr.lit (WFLang.Ty.nat) 1)) -/
#guard_msgs in
#eval (PExpr.bin .add (.var .here) (.lit .nat 1) : PExpr [.nat, .nat] .nat).traverseVars noY

end WFLang.InstanceTests
