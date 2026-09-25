import RequestProject.WFLang.Core.Types

/-!
# Call-free expressions

`PExpr Γ t` are the expressions without recursive calls: variables, literals, the binary
operators, `!` and `if-then-else`.  They are the leaves of the `PCL` grammar (returned values,
branch tests and call arguments).  `PExprs.ids Γ` is the argument tuple made of all the variables of `Γ`.
-/

namespace WFLang

/-- Call-free expressions. -/
inductive PExpr (Γ : List Ty) : Ty → Type where
  | var {t : Ty} : Var Γ t → PExpr Γ t
  | lit (t : Ty) : t.denote → PExpr Γ t
  | bin {a b c : Ty} : BinOp a b c → PExpr Γ a → PExpr Γ b → PExpr Γ c
  | not : PExpr Γ .bool → PExpr Γ .bool
  | un {a b : Ty} : UnOp a b → PExpr Γ a → PExpr Γ b
  | ite {t : Ty} : PExpr Γ .bool → PExpr Γ t → PExpr Γ t → PExpr Γ t
  deriving DecidableEq, Repr, Hashable

/-- Lists of call-free expressions (argument tuples). -/
inductive PExprs (Γ : List Ty) : List Ty → Type where
  | nil : PExprs Γ []
  | cons {t : Ty} {ts : List Ty} : PExpr Γ t → PExprs Γ ts → PExprs Γ (t :: ts)
  deriving DecidableEq, Repr, Hashable

def PExpr.eval {Γ : List Ty} (env : Env Γ) : {t : Ty} → PExpr Γ t → t.denote
  | _, .var v => v.get env
  | _, .lit _ v => v
  | _, .bin op a b => op.eval (a.eval env) (b.eval env)
  | _, .not a => !(a.eval env)
  | _, .un op a => op.eval (a.eval env)
  | _, .ite c a b => if c.eval env then a.eval env else b.eval env

def PExprs.eval {Γ : List Ty} (env : Env Γ) : {ts : List Ty} → PExprs Γ ts → Env ts
  | _, .nil => ()
  | _, .cons a as => (a.eval env, as.eval env)

/-- Weaken an expression by one variable. -/
def PExpr.wk {s : Ty} {Γ : List Ty} : {t : Ty} → PExpr Γ t → PExpr (s :: Γ) t
  | _, .var v => .var (.there v)
  | _, .lit t v => .lit t v
  | _, .bin op a b => .bin op a.wk b.wk
  | _, .not a => .not a.wk
  | _, .un op a => .un op a.wk
  | _, .ite c a b => .ite c.wk a.wk b.wk

/-- Weaken an argument tuple by one variable. -/
def PExprs.wk {s : Ty} {Γ : List Ty} : {ts : List Ty} → PExprs Γ ts → PExprs (s :: Γ) ts
  | _, .nil => .nil
  | _, .cons a as => .cons a.wk as.wk

/-- The variables of `Γ`, as an argument tuple (used to call a function on its own
parameters). -/
def PExprs.ids : (Γ : List Ty) → PExprs Γ Γ
  | [] => .nil
  | _ :: ts => .cons (.var .here) (PExprs.ids ts).wk

theorem PExpr.wk_eval {s : Ty} {Γ : List Ty} (v : s.denote) (env : Env Γ) :
    ∀ {t : Ty} (e : PExpr Γ t), (e.wk (s := s)).eval ((v, env) : Env (s :: Γ)) = e.eval env
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, .bin op a b => by simp only [wk, eval, wk_eval v env a, wk_eval v env b]
  | _, .not a => by simp only [wk, eval, wk_eval v env a]
  | _, .un op a => by simp only [wk, eval, wk_eval v env a]
  | _, .ite c a b => by simp only [wk, eval, wk_eval v env c, wk_eval v env a, wk_eval v env b]

theorem PExprs.wk_eval {s : Ty} {Γ : List Ty} (v : s.denote) (env : Env Γ) :
    ∀ {ts : List Ty} (e : PExprs Γ ts), (e.wk (s := s)).eval ((v, env) : Env (s :: Γ)) = e.eval env
  | _, .nil => rfl
  | _, .cons a as => by simp only [wk, eval, PExpr.wk_eval v env a, wk_eval v env as]

@[simp] theorem PExprs.ids_eval : ∀ (Γ : List Ty) (env : Env Γ), (PExprs.ids Γ).eval env = env
  | [], () => rfl
  | _ :: ts, (v, env) => by
      simp only [PExprs.ids, PExprs.eval, PExpr.eval, Var.get, PExprs.wk_eval, ids_eval ts env]

end WFLang
