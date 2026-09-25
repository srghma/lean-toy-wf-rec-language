import RequestProject.WFLang.Common.Types

/-!
# The `Wrapper` grammar: one self-recursive function, certificate outside the grammar

Intrinsically typed expressions `Expr s Γ τ` (de Bruijn variables, literals, the binary
operators, `!`, `if-then-else`, and a recursive self call `call`) of the body of a function
with signature `s`.

* `Expr.evalWith o` is the *reference* one-step semantics, in which the recursive call is
  answered by an arbitrary oracle `o`;
* `IsFix body f` is the soundness specification: `f` is a correct meaning of `body` iff it
  satisfies the recursive defining equation `f x = body.evalWith f x`.

No fuel, no measure and no `AccT` appear: syntax is plain data.  Each evaluator design in this
directory (`Guarded`, `GuardedAcc`, `FreeCall`, `Checked`) wraps a body together with a
well-founded relation and a `Prop`-level certificate.
-/

namespace WFLang

mutual
/-- Expressions of type `τ` in context `Γ`, inside the body of a function with
signature `s`.  `call` is the recursive self call. -/
inductive Expr (s : Sig) (Γ : List Ty) : Ty → Type where
  | var {t : Ty} : Var Γ t → Expr s Γ t
  | lit (t : Ty) : t.denote → Expr s Γ t
  | bin {a b c : Ty} : BinOp a b c → Expr s Γ a → Expr s Γ b → Expr s Γ c
  | not : Expr s Γ .bool → Expr s Γ .bool
  | ite {t : Ty} : Expr s Γ .bool → Expr s Γ t → Expr s Γ t → Expr s Γ t
  | call : Exprs s Γ s.args → Expr s Γ s.ret
/-- Argument lists of a call. -/
inductive Exprs (s : Sig) (Γ : List Ty) : List Ty → Type where
  | nil : Exprs s Γ []
  | cons {t : Ty} {ts : List Ty} : Expr s Γ t → Exprs s Γ ts → Exprs s Γ (t :: ts)
end

/-- The body of a function of signature `s`: an expression over its arguments. -/
abbrev Body (s : Sig) := Expr s s.args s.ret

section evalWith
variable {s : Sig} (o : Env s.args → s.ret.denote)

mutual
/-- Reference semantics: evaluation where the recursive call is answered by the
oracle `o`.  This is structural recursion on syntax, trivially terminating. -/
def Expr.evalWith {Γ : List Ty} (env : Env Γ) : {t : Ty} → Expr s Γ t → t.denote
  | _, .var v => v.get env
  | _, .lit _ v => v
  | _, .bin op a b => op.eval (a.evalWith env) (b.evalWith env)
  | _, .not a => !(a.evalWith env)
  | _, .ite c a b => if c.evalWith env then a.evalWith env else b.evalWith env
  | _, .call args => o (args.evalWith env)
/-- Reference semantics of argument lists. -/
def Exprs.evalWith {Γ : List Ty} (env : Env Γ) : {ts : List Ty} → Exprs s Γ ts → Env ts
  | _, .nil => ()
  | _, .cons a as => (a.evalWith env, as.evalWith env)
end

end evalWith

/-- **Soundness specification.**  `f` is a meaning of `body` iff it satisfies
the recursive defining equation of the function. -/
def IsFix {s : Sig} (body : Body s) (f : Env s.args → s.ret.denote) : Prop :=
  ∀ x, f x = body.evalWith f x

/-- If the defining equation has at most one solution (`unique`), then an evaluator `run`
agrees with every Lean function satisfying that equation.  Shared by all wrapper designs. -/
theorem curryEnv_eq_of_isFix_unique {s : Sig} {body : Body s} {run : Env s.args → s.ret.denote}
    (unique : ∀ f, IsFix body f → ∀ x, run x = f x) (f : FnType s.args s.ret)
    (hf : IsFix body (uncurryEnv f)) : curryEnv run = f :=
  curryEnv_eq _ _ (unique _ hf)

end WFLang
