import RequestProject.WFLang.Core.PExpr

/-!
# Optimised normal form of call-free expressions

A call-free expression is in *optimised normal form* (`PExpr.isNF`) when none of the
simplifications that the capture performs applies any more:

* **constant folding**: no operator (binary, unary, `!`) is applied to literals only;
* **algebraic identities**: no `x + 0`, `0 + x`, `x - 0`, `0 - x`, `x * 1`, `1 * x`, `x * 0`,
  `0 * x`, `x / 1`, `x / 0`, `0 / x`, `x % 1`, `x % 0`, `0 % x`, `x ^ 0`, `x ^ 1`, `1 ^ x`,
  `b && lit`, `lit && b`, `b || lit`, `lit || b`, `xor` with a literal, `l ++ []`, `[] ++ l`
  (and the same identities on `Int`);
* **no redundant unary operators**: no `!!b`, no `- - i`, no `(a, b).1` / `(a, b).2`;
* **branches**: the test of an `if` is neither a literal (dead branch) nor a negation
  `!c` (the branches are swapped instead), and an `if` does not choose between two literals
  that are equal, or between two boolean literals (`if c then true else false` is `c`).

The statements of `PCL.Expr` require every call-free expression they contain to be in this
normal form (`ret`, calls, `jump`), and every `if` test to be a *condition*
(`PExpr.isCond`: in normal form, not a literal, not a negation).  So a program that could still
be simplified this way is not well typed: the optimisation is part of the grammar.
-/

namespace WFLang

variable {Γ : List Ty}

/-- Is the expression a literal? -/
def PExpr.isLit {t : Ty} : PExpr Γ t → Bool
  | .lit _ _ => true
  | _ => false

/-- Is the expression the literal `v`? -/
def PExpr.isLitOf {t : Ty} (v : t.denote) : PExpr Γ t → Bool
  | .lit _ w => @decide (w = v) (Ty.decEq t w v)
  | _ => false

/-- Are both expressions the same literal? -/
def PExpr.sameLit {t : Ty} : PExpr Γ t → PExpr Γ t → Bool
  | .lit _ v, .lit _ w => @decide (v = w) (Ty.decEq t v w)
  | _, _ => false

/-- Is the expression a negation `!b`? -/
def PExpr.isNot {t : Ty} : PExpr Γ t → Bool
  | .not _ => true
  | _ => false

/-- Is the expression a pair `(a, b)`? -/
def PExpr.isPair {t : Ty} : PExpr Γ t → Bool
  | .bin (.pair _ _) _ _ => true
  | _ => false

/-- Is the expression an `Int` negation `-i`? -/
def PExpr.isNeg {t : Ty} : PExpr Γ t → Bool
  | .un .ineg _ => true
  | _ => false

/-- Does an algebraic identity simplify `op x y` (one argument is a neutral or absorbing
literal)? -/
def BinOp.simplifies : {a b c : Ty} → BinOp a b c → PExpr Γ a → PExpr Γ b → Bool
  | _, _, _, .add, x, y => x.isLitOf (0 : Nat) || y.isLitOf (0 : Nat)
  | _, _, _, .sub, x, y => x.isLitOf (0 : Nat) || y.isLitOf (0 : Nat)
  | _, _, _, .mul, x, y =>
      x.isLitOf (0 : Nat) || y.isLitOf (0 : Nat) || x.isLitOf (1 : Nat) || y.isLitOf (1 : Nat)
  | _, _, _, .div, x, y => x.isLitOf (0 : Nat) || y.isLitOf (0 : Nat) || y.isLitOf (1 : Nat)
  | _, _, _, .mod, x, y => x.isLitOf (0 : Nat) || y.isLitOf (0 : Nat) || y.isLitOf (1 : Nat)
  | _, _, _, .pow, x, y => x.isLitOf (1 : Nat) || y.isLitOf (0 : Nat) || y.isLitOf (1 : Nat)
  | _, _, _, .and, x, y => x.isLit || y.isLit
  | _, _, _, .or, x, y => x.isLit || y.isLit
  | _, _, _, .bxor, x, y => x.isLit || y.isLit
  | _, _, _, .iadd, x, y => x.isLitOf (0 : Int) || y.isLitOf (0 : Int)
  | _, _, _, .isub, _, y => y.isLitOf (0 : Int)
  | _, _, _, .imul, x, y =>
      x.isLitOf (0 : Int) || y.isLitOf (0 : Int) || x.isLitOf (1 : Int) || y.isLitOf (1 : Int)
  | _, _, _, .append _, x, y => x.isLitOf [] || y.isLitOf []
  | _, _, _, _, _, _ => false

/-- Does `op x` simplify (a projection of a pair, a double negation)? -/
def UnOp.simplifies : {a b : Ty} → UnOp a b → PExpr Γ a → Bool
  | _, _, .fst _ _, x => x.isPair
  | _, _, .snd _ _, x => x.isPair
  | _, _, .ineg, x => x.isNeg
  | _, _, _, _ => false

/-- **Optimised normal form** of a call-free expression (see the module documentation). -/
def PExpr.isNF : {t : Ty} → PExpr Γ t → Bool
  | _, .var _ => true
  | _, .lit _ _ => true
  | _, .bin op a b => a.isNF && b.isNF && !(a.isLit && b.isLit) && !op.simplifies a b
  | _, .not a => a.isNF && !a.isLit && !a.isNot
  | _, .un op a => a.isNF && !a.isLit && !op.simplifies a
  | t, .ite c a b => c.isNF && !c.isLit && !c.isNot && a.isNF && b.isNF &&
      !(a.isLit && b.isLit && (a.sameLit b || t == .bool))

/-- A **condition**: the test of an `if`, in normal form, neither a literal (the branch would
be dead) nor a negation (the branches would be swapped). -/
def PExpr.isCond (c : PExpr Γ .bool) : Bool :=
  c.isNF && !c.isLit && !c.isNot

/-- A **loop test**: the test of a `while` loop, in normal form and not a literal (a loop on
`false` is dead code, and a loop on `true` cannot terminate).  Unlike the test of an `if`, it
may be a negation: the body and the exit of a loop cannot be swapped. -/
def PExpr.isLoopCond (c : PExpr Γ .bool) : Bool :=
  c.isNF && !c.isLit

/-- Normal form of every expression of an argument tuple. -/
def PExprs.isNF : {ts : List Ty} → PExprs Γ ts → Bool
  | _, .nil => true
  | _, .cons a as => a.isNF && as.isNF

/-- Is every expression of the tuple a variable? -/
def PExprs.allVars : {ts : List Ty} → PExprs Γ ts → Bool
  | _, .nil => true
  | _, .cons (.var _) as => as.allVars
  | _, .cons _ _ => false

theorem PExprs.isNF_of_allVars : ∀ {ts : List Ty} (es : PExprs Γ ts), es.allVars = true →
    es.isNF = true
  | _, .nil, _ => rfl
  | _, .cons (.var _) as, h => by
    simp only [allVars] at h
    simp only [isNF, PExpr.isNF, Bool.true_and]
    exact isNF_of_allVars as h
  | _, .cons (.lit _ _) _, h | _, .cons (.bin _ _ _) _, h | _, .cons (.not _) _, h
  | _, .cons (.un _ _) _, h | _, .cons (.ite _ _ _) _, h => by simp [allVars] at h

theorem PExprs.wk_allVars {s : Ty} : ∀ {ts : List Ty} (es : PExprs Γ ts), es.allVars = true →
    (es.wk (s := s)).allVars = true
  | _, .nil, _ => rfl
  | _, .cons (.var _) as, h => by
    simp only [allVars] at h
    simp only [wk, PExpr.wk, allVars]
    exact wk_allVars as h
  | _, .cons (.lit _ _) _, h | _, .cons (.bin _ _ _) _, h | _, .cons (.not _) _, h
  | _, .cons (.un _ _) _, h | _, .cons (.ite _ _ _) _, h => by simp [allVars] at h

theorem PExprs.ids_allVars : ∀ Γ : List Ty, (PExprs.ids Γ).allVars = true
  | [] => rfl
  | _ :: ts => by
    simp only [PExprs.ids, allVars]
    exact wk_allVars _ (ids_allVars ts)

/-- The tuple of all the variables is in normal form. -/
theorem PExprs.ids_isNF (Γ : List Ty) : (PExprs.ids Γ).isNF = true :=
  isNF_of_allVars _ (ids_allVars Γ)

end WFLang
