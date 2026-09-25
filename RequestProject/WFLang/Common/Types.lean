/-!
# Shared core of every language: types, environments, variables, operators

* object types `Ty` (`nat`, `bool`) and their denotation,
* environments `Env Γ` (right-nested tuples) and typed de Bruijn variables `Var Γ t`,
* signatures `Sig` of recursive functions, curried function types `FnType` and
  (un)currying,
* the primitive binary operators `BinOp` (`+ - * / %`, `<`, `≤`, `bool_eq`, `&&`, `||`).

Every grammar (`Wrapper`, `PCL`, `Tail`, `Meas`) is built on top of this file.
-/

namespace WFLang

/-- Object-language types. -/
inductive Ty where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- Denotation of object types. -/
@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

/-- A default value of each type (returned by evaluators that check calls at runtime). -/
def Ty.default : (t : Ty) → t.denote
  | .nat => (0 : Nat)
  | .bool => false

/-- `bool_eq` at every object type. -/
def Ty.beq : (t : Ty) → t.denote → t.denote → Bool
  | .nat, a, b => @BEq.beq Nat _ a b
  | .bool, a, b => @BEq.beq Bool _ a b

/-- Environments: right-nested tuples `(v₁, (v₂, … , ()))`. -/
@[reducible] def Env : List Ty → Type
  | [] => Unit
  | t :: ts => t.denote × Env ts

/-- Typed de Bruijn variables. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {t : Ty} : Var (t :: Γ) t
  | there {Γ : List Ty} {s t : Ty} : Var Γ t → Var (s :: Γ) t

/-- Variable lookup. -/
def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.denote
  | _ :: _, _, .here, env => env.1
  | _ :: _, _, .there v, env => v.get env.2

/-- Signature of a recursive function. -/
structure Sig where
  args : List Ty
  ret : Ty

/-- Curried Lean function type `a₁ → … → aₙ → r`. -/
@[reducible] def FnType : List Ty → Ty → Type
  | [], r => r.denote
  | t :: ts, r => t.denote → FnType ts r

/-- Curry a function on environments. -/
def curryEnv : {ts : List Ty} → {r : Ty} → (Env ts → r.denote) → FnType ts r
  | [], _, f => f ()
  | _ :: _, _, f => fun a => curryEnv (fun e => f (a, e))

/-- Uncurry. -/
def uncurryEnv : {ts : List Ty} → {r : Ty} → FnType ts r → Env ts → r.denote
  | [], _, f, _ => f
  | _ :: _, _, f, e => uncurryEnv (f e.1) e.2

theorem curryEnv_congr : ∀ {ts : List Ty} {r : Ty} (f g : Env ts → r.denote),
    (∀ x, f x = g x) → curryEnv f = curryEnv g
  | [], _, _, _, h => h ()
  | _ :: _, _, _, _, h => by
    funext a
    exact curryEnv_congr _ _ (fun e => h (a, e))

theorem curryEnv_uncurryEnv : ∀ {ts : List Ty} {r : Ty} (f : FnType ts r),
    curryEnv (uncurryEnv f) = f
  | [], _, _ => rfl
  | _ :: _, _, f => by
    funext a
    exact curryEnv_uncurryEnv (f a)

/-- A function on environments that agrees pointwise with `uncurryEnv f` curries to `f`.
Every evaluator's agreement theorem ends with this step. -/
theorem curryEnv_eq {ts : List Ty} {r : Ty} (g : Env ts → r.denote) (f : FnType ts r)
    (h : ∀ x, g x = uncurryEnv f x) : curryEnv g = f := by
  rw [← curryEnv_uncurryEnv f]
  exact curryEnv_congr _ _ h

/-- Primitive binary operators, typed. -/
inductive BinOp : Ty → Ty → Ty → Type where
  | add : BinOp .nat .nat .nat
  | sub : BinOp .nat .nat .nat
  | mul : BinOp .nat .nat .nat
  | div : BinOp .nat .nat .nat
  | mod : BinOp .nat .nat .nat
  | lt : BinOp .nat .nat .bool
  | le : BinOp .nat .nat .bool
  | beq (t : Ty) : BinOp t t .bool
  | and : BinOp .bool .bool .bool
  | or : BinOp .bool .bool .bool

/-- Meaning of the primitive operators. -/
def BinOp.eval : {a b c : Ty} → BinOp a b c → a.denote → b.denote → c.denote
  | _, _, _, .add, x, y => @HAdd.hAdd Nat Nat Nat _ x y
  | _, _, _, .sub, x, y => @HSub.hSub Nat Nat Nat _ x y
  | _, _, _, .mul, x, y => @HMul.hMul Nat Nat Nat _ x y
  | _, _, _, .div, x, y => @HDiv.hDiv Nat Nat Nat _ x y
  | _, _, _, .mod, x, y => @HMod.hMod Nat Nat Nat _ x y
  | _, _, _, .lt, x, y => decide (@LT.lt Nat _ x y)
  | _, _, _, .le, x, y => decide (@LE.le Nat _ x y)
  | _, _, _, .beq t, x, y => t.beq x y
  | _, _, _, .and, x, y => (x && y : Bool)
  | _, _, _, .or, x, y => (x || y : Bool)

/-! ## Relations with fixed parameters -/

/-- A relation on `Env (t :: ts)` whose first component is a *fixed parameter*: related
environments agree on it, and their tails are related by `R a`, where `a` is that fixed value.
The capture elaborators use it for functions such as `def f (k : Nat) : Nat → Nat`, where `k`
is passed unchanged to every recursive call (Lean keeps such parameters outside the
`WellFounded.fix`). -/
def fixedRel {t : Ty} {ts : List Ty} (R : t.denote → Env ts → Env ts → Prop) :
    Env (t :: ts) → Env (t :: ts) → Prop :=
  fun x y => x.1 = y.1 ∧ R y.1 x.2 y.2

theorem fixedRel_wf {t : Ty} {ts : List Ty} {R : t.denote → Env ts → Env ts → Prop}
    (h : ∀ a, WellFounded (R a)) : WellFounded (fixedRel R) := by
  refine ⟨fun ⟨a, x⟩ => ?_⟩
  induction x using (h a).induction with
  | _ x IH =>
    refine Acc.intro _ fun ⟨b, y⟩ hy => ?_
    obtain ⟨hb, hr⟩ := hy
    simp only at hb hr
    subst hb
    exact IH y hr

end WFLang
