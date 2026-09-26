module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# Strict A-normal form, pinned

`LeanScript.Term` is in **strict A-normal form by construction**: the operands of a step
are atoms, and atoms are variables only — a declaration and a literal are steps, named by
a `let` like any other; a `let` binds one computation step (`LeanScript.Comp`), never a
mere variable, a dispatch or a fold; a block ends by returning a variable; and a dispatch
or a fold is always the last thing a block does.  A dispatch or a
fold whose value is *used* is written with a **join point** (`Term.letJ`) that its tails
jump to (`Term.jump`, `LeanScript.Dest.jump`); join points live in their own context
(`LeanScript.JCtx`), apart from the variables.

The functions named like the direct-style constructors (`Term.ap`, `Term.bool_casesOn'`,
`Term.nat_rec'`, `Term.letE'`, …) put arbitrary terms in that form.  Each example below
states, by `rfl`, the exact A-normal term such a function builds, and then checks by the
kernel that it computes what the direct-style term means.
-/

namespace TermTests.Anf

open LeanScript

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The value of `double`. -/
def doubleEnv : GlobalEnv doubleSig.decls := (fun n => 2 * n, PUnit.unit)

abbrev natT : TyWf := TyWf.prim .nat
abbrev boolT : TyWf := TyWf.prim .bool

/-! ## A nested application: the inner call is named by a `let` -/

/-- `double (double 1)`. -/
def doubleTwice : Term doubleSig [] natT :=
  .ap (.global .here) (.ap (.global .here) (.nat_mk 1))

-- [SKIPPED BY PROFILE_LAKE] example : doubleTwice =
-- [SKIPPED BY PROFILE_LAKE]     .letE (.nat_mk 1)
-- [SKIPPED BY PROFILE_LAKE]       (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1)))
-- [SKIPPED BY PROFILE_LAKE]         (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1)))
-- [SKIPPED BY PROFILE_LAKE]           (.ret (.var (v♯0))))))) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv doubleTwice = 4 := by kernel_rfl

/-! ## A dispatch used as an operand: it becomes the tail, and what uses it a join point -/

/-- `fun b => double (if b then 1 else 2)`. -/
def doubleIf : Term doubleSig [] (boolT ⇒ natT) :=
  .lam (.ap (.global .here) (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 2)))

-- [SKIPPED BY PROFILE_LAKE] example : doubleIf =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.letJ (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1))) (.ret (.var (v♯0)))))
-- [SKIPPED BY PROFILE_LAKE]       (.bool_casesOn (.var (v♯0))
-- [SKIPPED BY PROFILE_LAKE]         (.letE (.nat_mk 1) (.jump .head (.var (v♯0))))
-- [SKIPPED BY PROFILE_LAKE]         (.letE (.nat_mk 2) (.jump .head (.var (v♯0)))))) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv doubleIf true = 2 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv doubleIf false = 4 := by kernel_rfl

/-! ## A dispatch bound by a `let`: the body becomes the join point -/

/-- `fun n => let m := (match n with | 0 => 10 | k + 1 => k); double m`. -/
def letOfMatch : Term doubleSig [] (natT ⇒ natT) :=
  .lam (.letE' (.nat_casesOn' (.var (v♯0)) (.nat_mk 10) (.var (v♯0)))
    (.ap (.global .here) (.var (v♯0))))

-- [SKIPPED BY PROFILE_LAKE] example : letOfMatch =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.letJ (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1))) (.ret (.var (v♯0)))))
-- [SKIPPED BY PROFILE_LAKE]       (.nat_casesOn (.var (v♯0))
-- [SKIPPED BY PROFILE_LAKE]         (.letE (.nat_mk 10) (.jump .head (.var (v♯0))))
-- [SKIPPED BY PROFILE_LAKE]         (.jump .head (.var (v♯0))))) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv letOfMatch 0 = 20 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv letOfMatch 8 = 14 := by kernel_rfl

/-! ## A fold used as an operand: its answer is sent to a join point -/

/-- `fun n => double (Nat.rec 0 (fun _ ih => ih + 1) n)`, with the successor written as an
    extern call. -/
def doubleFold : Term doubleSig [] (natT ⇒ natT) :=
  .lam (.ap (.global .here)
    (.nat_rec' 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil)
      (.externCall (.cons (.var (v♯1)) .nil) fun vs => .lean_nat_add vs.1 1)))

-- [SKIPPED BY PROFILE_LAKE] example : doubleFold =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.letE (.nat_mk 0)
-- [SKIPPED BY PROFILE_LAKE]       (.letJ (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1))) (.ret (.var (v♯0)))))
-- [SKIPPED BY PROFILE_LAKE]         (.nat_rec 0 (.var (v♯1)) (.cons (.var (v♯0)) .nil)
-- [SKIPPED BY PROFILE_LAKE]           (.letE (.externCall (.cons (.var (v♯1)) .nil) fun vs => .lean_nat_add vs.1 1)
-- [SKIPPED BY PROFILE_LAKE]             (.ret (.var (v♯0))))
-- [SKIPPED BY PROFILE_LAKE]           (.jump .head)))) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv doubleFold 5 = 10 := by kernel_rfl

/-! ## Naming a variable is renaming: there is no copy `let`

A `let` never binds a mere variable, so `let m := n; double m` is `double n`: the body is
renamed, and nothing is bound for `m`.  A step whose value is the term's is bound too,
and the term returns its name. -/

/-- `fun n => let m := n; double m`. -/
def letOfVar : Term doubleSig [] (natT ⇒ natT) :=
  .lam (.letE' (.var (v♯0)) (.ap (.global .here) (.var (v♯0))))

-- [SKIPPED BY PROFILE_LAKE] example : letOfVar =
-- [SKIPPED BY PROFILE_LAKE]     .lam (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1))) (.ret (.var (v♯0))))) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv letOfVar 7 = 14 := by kernel_rfl

/-! ## Two dispatches in a row: two join points, each in its own context -/

/-- `fun b => (if b then 1 else 2) + (if b then 3 else 4)`, written with an extern call:
    both operands are dispatches, so each one ends a block and jumps to the join point
    that holds the rest. -/
def sumOfIfs : Term doubleSig [] (boolT ⇒ natT) :=
  .lam (.externCall
    (.cons (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 2))
      (.cons (.bool_casesOn' (.var (v♯0)) (.nat_mk 3) (.nat_mk 4)) .nil))
    fun vs => .lean_nat_add vs.1 vs.2.1)

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv sumOfIfs true = 4 := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv sumOfIfs false = 6 := by kernel_rfl

/-! ## Redexes are taken apart while building

An abstraction applied to an operand is β-reduced: the operand is bound, and the body
runs on it, with no closure built and no call.  A dispatch on a literal is the branch the
literal selects. -/

/-- `(fun x => double x) 3`. -/
def betaRedex : Term doubleSig [] natT :=
  .ap (.lam (.ap (.global .here) (.var (v♯0)))) (.nat_mk 3)

-- [SKIPPED BY PROFILE_LAKE] example : betaRedex =
-- [SKIPPED BY PROFILE_LAKE]     .letE (.nat_mk 3)
-- [SKIPPED BY PROFILE_LAKE]       (.letE (.global .here) (.letE (.ap (.var (v♯0)) (.var (v♯1))) (.ret (.var (v♯0))))) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv betaRedex = 6 := by kernel_rfl

/-- `if true then 1 else 2`. -/
def ifTrue : Term doubleSig [] natT :=
  .bool_casesOn' (.bool_mk true) (.nat_mk 1) (.nat_mk 2)

-- [SKIPPED BY PROFILE_LAKE] example : ifTrue = .letE (.nat_mk 1) (.ret (.var (v♯0))) := rfl

/-- `match 5 with | 0 => 10 | k + 1 => k`. -/
def matchFive : Term doubleSig [] natT :=
  .nat_casesOn' (.nat_mk 5) (.nat_mk 10) (.var (v♯0))

-- [SKIPPED BY PROFILE_LAKE] example : matchFive = .letE (.nat_mk 4) (.ret (.var (v♯0))) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : Term.run doubleEnv matchFive = 4 := by kernel_rfl

end TermTests.Anf

end
