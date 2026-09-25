import RequestProject.WFLang.Common.PExpr

/-!
# Language `Meas`: well-founded recursion by an in-language measure

Here the grammar carries no proofs at all.  Well-founded recursion is the constructor

```
| fix ps r μ₁ μ₂ body args      -- (fix self ps. body) args,  decreasing on (μ₁, μ₂)
```

where the measure `(μ₁, μ₂)` is itself a pair of (call-free) object-language expressions
over the parameters, compared lexicographically.  Calls are written in direct style
(`call args`, possibly nested, anywhere in the body).  The evaluator computes the measure of
every recursive call and only performs it if the measure went down; otherwise the call
returns the default value of its type.  So the evaluator is total for **every** program,
with termination justified by the lexicographic order on `ℕ × ℕ` — at the price of a
runtime check per call.  For the programs produced by the capture macro the check always
succeeds, and this is part of the agreement proof.
-/

namespace WFLang.Meas

/-- Signature of the innermost enclosing recursive function (if any). -/
abbrev SelfSig := Option (List Ty × Ty)

mutual
/-- Expressions in direct style.  `sf` is the enclosing recursive function. -/
inductive Expr : (Γ : List Ty) → SelfSig → Ty → Type where
  | var {Γ : List Ty} {sf : SelfSig} {t : Ty} : Var Γ t → Expr Γ sf t
  | lit {Γ : List Ty} {sf : SelfSig} (t : Ty) : t.denote → Expr Γ sf t
  | bin {Γ : List Ty} {sf : SelfSig} {a b c : Ty} :
      BinOp a b c → Expr Γ sf a → Expr Γ sf b → Expr Γ sf c
  | not {Γ : List Ty} {sf : SelfSig} : Expr Γ sf .bool → Expr Γ sf .bool
  | ite {Γ : List Ty} {sf : SelfSig} {t : Ty} :
      Expr Γ sf .bool → Expr Γ sf t → Expr Γ sf t → Expr Γ sf t
  /-- Recursive call of the innermost `fix`. -/
  | call {Γ : List Ty} {ps : List Ty} {r : Ty} : Exprs Γ (some (ps, r)) ps → Expr Γ (some (ps, r)) r
  /-- A local recursive function, decreasing on the measure `(μ₁, μ₂)`, applied to `args`. -/
  | fix {Γ : List Ty} {sf : SelfSig} (ps : List Ty) (r : Ty) (μ₁ μ₂ : PExpr ps .nat)
      (body : Expr ps (some (ps, r)) r) (args : Exprs Γ sf ps) : Expr Γ sf r
/-- Argument lists. -/
inductive Exprs : (Γ : List Ty) → SelfSig → List Ty → Type where
  | nil {Γ : List Ty} {sf : SelfSig} : Exprs Γ sf []
  | cons {Γ : List Ty} {sf : SelfSig} {t : Ty} {ts : List Ty} :
      Expr Γ sf t → Exprs Γ sf ts → Exprs Γ sf (t :: ts)
end

/-- What a recursive call is answered with. -/
def Handler : SelfSig → Type
  | none => Unit
  | some (ps, r) => Env ps → r.denote

/-- Strict lexicographic order on measures, as a boolean test. -/
def lexLt (a b : Nat × Nat) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

section
variable {ps : List Ty} {r : Ty}

/-- The measure of an argument tuple. -/
def measure (μ₁ μ₂ : PExpr ps .nat) (x : Env ps) : Nat × Nat := (μ₁.eval x, μ₂.eval x)

/-- The recursion of a `fix` node: each recursive call is performed only if the measure
decreases (otherwise it returns the default value). -/
def measFix (μ₁ μ₂ : PExpr ps .nat) (F : Env ps → (Env ps → r.denote) → r.denote)
    (x : Env ps) : r.denote :=
  F x (fun y => if lexLt (measure μ₁ μ₂ y) (measure μ₁ μ₂ x) then measFix μ₁ μ₂ F y
    else r.default)
termination_by measure μ₁ μ₂ x
decreasing_by
  simp only [lexLt, decide_eq_true_eq] at *
  exact Prod.lex_def.mpr ‹_›

theorem measFix_eq (μ₁ μ₂ : PExpr ps .nat) (F : Env ps → (Env ps → r.denote) → r.denote)
    (x : Env ps) :
    measFix μ₁ μ₂ F x = F x (fun y => if lexLt (measure μ₁ μ₂ y) (measure μ₁ μ₂ x) then
      measFix μ₁ μ₂ F y else r.default) := by
  rw [measFix]

/-- Uniqueness of the solution of the guarded equation. -/
theorem measFix_unique (μ₁ μ₂ : PExpr ps .nat) (F : Env ps → (Env ps → r.denote) → r.denote)
    (f : Env ps → r.denote)
    (hf : ∀ x, f x = F x (fun y => if lexLt (measure μ₁ μ₂ y) (measure μ₁ μ₂ x) then f y
      else r.default)) : ∀ x, measFix μ₁ μ₂ F x = f x := by
  intro x
  induction x using (measureWf μ₁ μ₂).induction with
  | _ x IH =>
    rw [measFix_eq, hf x]
    congr 1
    funext y
    split
    · rename_i h
      simp only [lexLt, decide_eq_true_eq] at h
      exact IH y (Prod.lex_def.mpr h)
    · rfl
where
  /-- The relation "smaller measure" is well-founded. -/
  measureWf (μ₁ μ₂ : PExpr ps .nat) :
      WellFounded (fun y x : Env ps => Prod.Lex (· < ·) (· < ·) (measure μ₁ μ₂ y) (measure μ₁ μ₂ x)) :=
    InvImage.wf _ (WellFoundedRelation.wf (α := Nat × Nat))

end

mutual
/-- The evaluator (structural recursion on the syntax; `fix` runs `measFix`). -/
def Expr.eval {Γ : List Ty} {sf : SelfSig} : {t : Ty} → Expr Γ sf t → Env Γ → Handler sf → t.denote
  | _, .var v, e, _ => v.get e
  | _, .lit _ v, _, _ => v
  | _, .bin op a b, e, h => op.eval (a.eval e h) (b.eval e h)
  | _, .not a, e, h => !(a.eval e h)
  | _, .ite c a b, e, h => if c.eval e h then a.eval e h else b.eval e h
  | _, .call args, e, h => h (args.eval e h)
  | _, .fix _ _ μ₁ μ₂ body args, e, h => measFix μ₁ μ₂ (fun x h' => body.eval x h') (args.eval e h)
def Exprs.eval {Γ : List Ty} {sf : SelfSig} : {ts : List Ty} → Exprs Γ sf ts → Env Γ → Handler sf → Env ts
  | _, .nil, _, _ => ()
  | _, .cons a as, e, h => (a.eval e h, as.eval e h)
end

/-- Closed programs of signature `s`. -/
abbrev Term (s : Sig) := Expr s.args none s.ret

def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv (fun x => Expr.eval t x ())

/-- Agreement for a program of the shape produced by the capture macro,
`(fix self xs. body) xs`: it computes any Lean function `f` satisfying the guarded recursive
equation of `body`. -/
theorem Term.eval_fix_eq {s : Sig} (μ₁ μ₂ : PExpr s.args .nat)
    (body : Expr s.args (some (s.args, s.ret)) s.ret) (args : Exprs s.args none s.args)
    (hargs : ∀ x, args.eval x () = x) (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x = body.eval x (fun y =>
      if lexLt (measure μ₁ μ₂ y) (measure μ₁ μ₂ x) then uncurryEnv f y else s.ret.default)) :
    Term.eval (Expr.fix s.args s.ret μ₁ μ₂ body args : Term s) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  show measFix μ₁ μ₂ (fun x h' => body.eval x h') (args.eval x ()) = _
  rw [hargs]
  exact measFix_unique μ₁ μ₂ _ _ hf x

end WFLang.Meas
