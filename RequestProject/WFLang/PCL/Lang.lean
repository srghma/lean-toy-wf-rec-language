import RequestProject.WFLang.Core.PExpr

/-!
# Language `PCL`: well-founded recursion as a construct of the grammar (proof-carrying calls)

In this language well-founded recursion is a constructor of `Expr` itself:

```
| fix params r R wf body args k      -- let v := (fix self params. body) args in k
| fixSelfCall args dec k             -- let v := self args in k    (inside a fix body)
```

* `fix` carries the relation `R` and `wf : WellFounded R` (a `Prop`).
* Every recursive call carries its **own** decrease proof `dec`, stating that the argument
  tuple is `R`-smaller than the current parameters *whenever the call is reached*.
  "Whenever the call is reached" is expressed by the index `G : Env Γ → Prop` of `Expr`: the
  path condition, strengthened by each `ite` branch.
* Expressions are in A-normal form: arithmetic, comparisons, `bool_eq`, `&&`, `||`, `!` are
  in the call-free `PExpr` layer (`Core/PExpr.lean`); the result of a call is bound to a new
  variable.

The path condition and the decrease proofs only mention `PExpr.eval`, which is defined
before `Expr`, so no induction–recursion is needed.  All proofs are `Prop`s and are erased by
code generation: the evaluator never checks anything at runtime and has no fuel.
-/

namespace WFLang.PCL

/-! ## Statements, with `fix` and `fixSelfCall` -/

/-- The innermost enclosing recursive function: its parameters, result type, well-founded
relation, and how to read its current parameters from the environment. -/
structure Self (Γ : List Ty) where
  params : List Ty
  ret : Ty
  R : Env params → Env params → Prop
  cur : Env Γ → Env params

/-- The same function, seen under one more local variable. -/
def Self.push {Γ : List Ty} (sf : Self Γ) (t : Ty) : Self (t :: Γ) :=
  { params := sf.params, ret := sf.ret, R := sf.R, cur := fun e => sf.cur e.2 }

/-- The function whose body is being defined: its parameters are the whole context. -/
def Self.top (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) : Self params :=
  { params := params, ret := r, R := R, cur := id }

/-- Statements of result type `t` in context `Γ`, reached under the path condition `G`,
inside the recursive function `sf` (if any). -/
inductive Expr : (Γ : List Ty) → (Env Γ → Prop) → Option (Self Γ) → Ty → Type where
  /-- Return a call-free value. -/
  | ret {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      (p : PExpr Γ t) : Expr Γ G sf t
  /-- `if c then a else b`; each branch knows the outcome of the test. -/
  | ite {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      (c : PExpr Γ .bool)
      (a : Expr Γ (fun e => G e ∧ c.eval e = true) sf t)
      (b : Expr Γ (fun e => G e ∧ c.eval e = false) sf t) : Expr Γ G sf t
  /-- `let v := self args in k`, with the proof that the call goes down. -/
  | fixSelfCall {Γ : List Ty} {G : Env Γ → Prop} {sf : Self Γ} {t : Ty}
      (args : PExprs Γ sf.params)
      (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
      (k : Expr (sf.ret :: Γ) (fun e => G e.2) (some (sf.push sf.ret)) t) : Expr Γ G (some sf) t
  /-- `let v := (fix self params. body) args in k`: a local well-founded recursive function
  with relation `R` (proved well-founded by `wf`), applied once. -/
  | fix {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) (wf : WellFounded R)
      (body : Expr params (fun _ => True) (some (Self.top params r R)) r)
      (args : PExprs Γ params)
      (k : Expr (r :: Γ) (fun e => G e.2) (sf.map (·.push r)) t) : Expr Γ G sf t

/-! ## The evaluator -/

/-- What a statement may use to perform a recursive call: a function defined on the
arguments that are `R`-below the current parameters. -/
def Handler {Γ : List Ty} : Option (Self Γ) → Env Γ → Type
  | none, _ => Unit
  | some sf, e => (y : Env sf.params) → sf.R y (sf.cur e) → sf.ret.denote

/-- Moving a handler under a new local variable. -/
def Handler.push {Γ : List Ty} {r : Ty} {v : r.denote} {e : Env Γ} :
    {sf : Option (Self Γ)} → Handler sf e → Handler (sf.map (·.push r)) ((v, e) : Env (r :: Γ))
  | none, h => h
  | some _, h => h

/-- The evaluator: structural recursion on the syntax; a `fix` node is run by
`WellFounded.fix` on its own relation.  No fuel, no runtime checks. -/
def Expr.eval : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    Expr Γ G sf t → (e : Env Γ) → G e → Handler sf e → t.denote
  | _, _, _, _, .ret p, e, _, _ => p.eval e
  | _, _, _, _, .ite c a b, e, g, h =>
      if hc : c.eval e = true then a.eval e ⟨g, hc⟩ h
      else b.eval e ⟨g, Bool.eq_false_iff.mpr hc⟩ h
  | _, _, _, _, .fixSelfCall args dec k, e, g, h =>
      k.eval (h (args.eval e) (dec e g), e) g h
  | _, _, _, _, .fix _ _ _ wf body args k, e, g, h =>
      k.eval (wf.fix (fun x ih => body.eval x trivial ih) (args.eval e), e) g (Handler.push h)

/-- Closed programs of signature `s`: statements over the parameters, outside any recursive
function. -/
abbrev Term (s : Sig) := Expr s.args (fun _ => True) none s.ret

def Term.run {s : Sig} (t : Term s) (x : Env s.args) : s.ret.denote := t.eval x trivial ()

/-- Curried evaluator: `Term.eval gcd_term m n`. -/
def Term.eval {s : Sig} (t : Term s) : FnType s.args s.ret := curryEnv t.run

/-! ## Soundness of `fix` -/

section
variable {params : List Ty} {r : Ty} {R : Env params → Env params → Prop} (wf : WellFounded R)
  (body : Expr params (fun _ => True) (some (Self.top params r R)) r)

/-- The function denoted by a `fix` node. -/
def fixFn : Env params → r.denote := wf.fix (fun x ih => body.eval x trivial ih)

/-- **Soundness (1):** the function run by a `fix` node satisfies its recursive equation. -/
theorem fixFn_eq (x : Env params) :
    fixFn wf body x = body.eval x trivial (fun y _ => fixFn wf body y) :=
  WellFounded.fix_eq _ _ x

/-- **Soundness (2):** it is the only solution of that equation. -/
theorem fixFn_unique (f : Env params → r.denote)
    (hf : ∀ x, f x = body.eval x trivial (fun y _ => f y)) : ∀ x, fixFn wf body x = f x := by
  intro x
  induction x using wf.induction with
  | _ x IH =>
    rw [fixFn_eq, hf x]
    have : (fun y (_ : R y x) => fixFn wf body y) = (fun y _ => f y) := by
      funext y hy; exact IH y hy
    exact congrArg (body.eval x trivial) this

end

theorem eval_fix {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
    (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) (wf : WellFounded R)
    (body : Expr params (fun _ => True) (some (Self.top params r R)) r)
    (args : PExprs Γ params) (k : Expr (r :: Γ) (fun e => G e.2) (sf.map (·.push r)) t)
    (e : Env Γ) (g : G e) (h : Handler sf e) :
    (Expr.fix params r R wf body args k).eval e g h =
      k.eval (fixFn wf body (args.eval e), e) g (Handler.push h) := rfl

/-- Agreement for a program of the shape produced by the capture macro,
`let v := (fix self xs. body) xs in v`: it computes any Lean function `f` that satisfies
the recursive equation of `body`. -/
theorem Term.eval_fix_eq {s : Sig} (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr s.args (fun _ => True) (some (Self.top s.args s.ret R)) s.ret)
    (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x = body.eval x trivial (fun y _ => uncurryEnv f y)) :
    Term.eval (Expr.fix s.args s.ret R wf body (PExprs.ids s.args) (.ret (.var .here)) :
      Term s) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  show (fixFn wf body ((PExprs.ids s.args).eval x), x).1 = _
  rw [PExprs.ids_eval]
  exact fixFn_unique wf body _ hf x

/-! ## Simplification lemmas used by the capture tactics -/

@[simp] theorem eval_ret {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
    (p : PExpr Γ t) (e : Env Γ) (g : G e) (h : Handler sf e) :
    (Expr.ret (G := G) (sf := sf) p).eval e g h = p.eval e := rfl

@[simp] theorem eval_ite {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
    (c : PExpr Γ .bool) (a : Expr Γ (fun e => G e ∧ c.eval e = true) sf t)
    (b : Expr Γ (fun e => G e ∧ c.eval e = false) sf t) (e : Env Γ) (g : G e)
    (h : Handler sf e) :
    (Expr.ite c a b).eval e g h =
      if hc : c.eval e = true then a.eval e ⟨g, hc⟩ h
      else b.eval e ⟨g, Bool.eq_false_iff.mpr hc⟩ h := rfl

@[simp] theorem eval_fixSelfCall {Γ : List Ty} {G : Env Γ → Prop} {sf : Self Γ} {t : Ty}
    (args : PExprs Γ sf.params) (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
    (k : Expr (sf.ret :: Γ) (fun e => G e.2) (some (sf.push sf.ret)) t)
    (e : Env Γ) (g : G e) (h : Handler (some sf) e) :
    (Expr.fixSelfCall args dec k).eval e g h = k.eval (h (args.eval e) (dec e g), e) g h := rfl

end WFLang.PCL
