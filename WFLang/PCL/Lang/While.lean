import RequestProject.WFLang.PCL.Lang.Fix

/-!
# Language `PCL`: well-founded `while` loops

The derived form `Expr.whileLoop` (a `join` for the exit, a `joinrec` for the loop) and its
evaluation lemma `eval_whileLoop`.
-/

namespace WFLang.PCL

/-! ## Well-founded `while` loops: a derived form

`let v := (while c do x := p from x := init) in k` is the statement

```
join K (v) [inv v ∧ ¬ c v] := k in
joinrec L (x) [inv, R] := (if c then jump L p else jump K x) in
jump L init
```

(with the branches swapped when `c` is a negation `!c'`: the test of an `if` is never a
negation).  `whileFn`-style reasoning follows from `joinFn_unique`: the loop computes the Lean
loop `whileWF` (`eval_whileLoop`). -/

/-- The test `c` without its top-level negation. -/
def _root_.WFLang.PExpr.unNot {Γ : List Ty} : PExpr Γ .bool → PExpr Γ .bool
  | .not a => a
  | c => c

theorem _root_.WFLang.PExpr.unNot_isCond {Γ : List Ty} (c : PExpr Γ .bool)
    (hc : c.isLoopCond = true) : c.unNot.isCond = true := by
  cases c <;> simp_all [PExpr.unNot, PExpr.isCond, PExpr.isLoopCond, PExpr.isNF, PExpr.isNot]

theorem _root_.WFLang.PExpr.isCond_of_not_isNot {Γ : List Ty} (c : PExpr Γ .bool)
    (hc : c.isLoopCond = true) (hn : ¬ c.isNot = true) : c.isCond = true := by
  simp_all [PExpr.isCond, PExpr.isLoopCond]

theorem _root_.WFLang.PExpr.unNot_eval {Γ : List Ty} (c : PExpr Γ .bool) (hn : c.isNot = true)
    (e : Env Γ) : c.unNot.eval e = !c.eval e := by
  cases c <;> simp_all [PExpr.unNot, PExpr.isNot, PExpr.eval]

/-- The body of the loop of `Expr.whileLoop`: `if c then jump L p else jump K x`. -/
def Expr.whileBody {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (inv : Env Γ → s.denote → Prop)
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1) :
    Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1) (sf.map (·.push s)) t (fun e r => Q e.2 r)
      (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
        (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
  let loop {G' : Env (s :: Γ) → Prop} (hG : ∀ e, G' e → G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true) :
      Expr GL (s :: Γ) G' (sf.map (·.push s)) t (fun e r => Q e.2 r)
        (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
          (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
    .jump .here p hp (fun e g => step e (hG e g)) (fun _ _ _ h => h)
  let exit {G' : Env (s :: Γ) → Prop} (hG : ∀ e, G' e → G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false) :
      Expr GL (s :: Γ) G' (sf.map (·.push s)) t (fun e r => Q e.2 r)
        (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
          (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
    .jump (.there (.wk .here)) (.var .here) rfl (fun e g => (hG e g).2) (fun _ _ _ h => h)
  if hn : c.isNot = true then
    .ite c.unNot (c.unNot_isCond hc)
      (exit fun e g => ⟨g.1.1, g.1.2, by have := g.2; rw [c.unNot_eval hn] at this; simpa using this⟩)
      (loop fun e g => ⟨g.1.1, g.1.2, by have := g.2; rw [c.unNot_eval hn] at this; simpa using this⟩)
  else
    .ite c (c.isCond_of_not_isNot hc hn) (loop fun _ g => ⟨g.1.1, g.1.2, g.2⟩)
      (exit fun _ g => ⟨g.1.1, g.1.2, g.2⟩)

/-- `let v := (while c do x := p from x := init) in k`: a **well-founded `while` loop** on a
state `x : s`, whose result (the first state on which the test `c` is false) is bound to `v`.
The loop carries a relation `R` on the states (well-founded by `wf`, for each value of the
enclosing variables) and an invariant `inv`: the initial state satisfies the invariant
(`hinit`), and each iteration (`x := p`, run on a state satisfying the invariant and the test)
keeps the invariant and goes down (`step`).  `k` knows that `v` satisfies the invariant and not
the test.  This is a derived form: a `join` (the exit `K`) and a `joinrec` (the loop `L`). -/
def Expr.whileLoop {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (init : PExpr Γ s) (hi : init.isNF = true)
    (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (wf : ∀ e, WellFounded (R e))
    (inv : Env Γ → s.denote → Prop) (hinit : ∀ e, G e → inv e (init.eval e))
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1)
    (k : Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false)
      (sf.map (·.push s)) t (fun e v => Q e.2 v) (.wk js s)) :
    Expr GL Γ G sf t Q js :=
  .join s (fun e v => inv e v ∧ c.eval (v, e) = false) k
    (.joinrec s inv R wf (Expr.whileBody s c hc R inv p hp step)
      (.jump .here init hi hinit (fun _ _ _ h => h)))

/-- **A `while` loop computes the Lean loop `whileWF`** of its test and its body, and runs the
rest of the statement on its result. -/
@[simp] theorem eval_whileLoop {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (init : PExpr Γ s) (hi : init.isNF = true)
    (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (wf : ∀ e, WellFounded (R e))
    (inv : Env Γ → s.denote → Prop) (hinit : ∀ e, G e → inv e (init.eval e))
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1)
    (k : Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false)
      (sf.map (·.push s)) t (fun e v => Q e.2 v) (.wk js s))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.whileLoop s init hi c hc R wf inv hinit p hp step k).eval ge e g h je).1 =
      (k.eval ge (whileWF (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
          (fun y hy hc => step (y, e) ⟨g, hy, hc⟩) (init.eval e) (hinit e g), e)
        ⟨g, whileWF_spec (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
          (fun y hy hc => step (y, e) ⟨g, hy, hc⟩) (init.eval e) (hinit e g)⟩
        (Handler.push h) je).1 := by
  -- the loop's value, followed by the rest `k`
  let W := whileWF (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
    (fun y hy hc => step (y, e) ⟨g, hy, hc⟩)
  have hW := whileWF_spec (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
    (fun y hy hc => step (y, e) ⟨g, hy, hc⟩)
  let K : (v : s.denote) → (inv e v ∧ c.eval (v, e) = false) → {r : t.denote // Q e r} :=
    fun v hv => k.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je
  let F : (x : s.denote) → inv e x → {r : t.denote // Q e r} := fun x hx => K (W x hx) (hW x hx)
  have key := joinFn_unique ge wf (Expr.whileBody (GL := GL) (sf := sf) (Q := Q) (js := js)
    s c hc R inv p hp step) e g h (K, je) F (by
      intro x hx
      have Kc : ∀ v1 v2 (h1 : inv e v1 ∧ c.eval (v1, e) = false)
          (h2 : inv e v2 ∧ c.eval (v2, e) = false), v1 = v2 → (K v1 h1).1 = (K v2 h2).1 := by
        intro v1 v2 h1 h2 hv; subst hv; rfl
      unfold Expr.whileBody
      split
      · rename_i hn
        simp only [Expr.eval, JVar.get]
        split
        · rename_i hc'
          have hcx : c.eval (x, e) = false := by
            rw [c.unNot_eval hn] at hc'; simpa using hc'
          exact Kc _ _ (hW x hx) ⟨hx, by simpa using hcx⟩ (whileWF_of_false (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
        · rename_i hc'
          have hcx : c.eval (x, e) = true := by
            rw [c.unNot_eval hn] at hc'; simpa using hc'
          exact Kc _ _ (hW x hx) (hW _ _) (whileWF_of_true (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
      · simp only [Expr.eval, JVar.get]
        split
        · rename_i hcx
          exact Kc _ _ (hW x hx) (hW _ _) (whileWF_of_true (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
        · rename_i hcx
          exact Kc _ _ (hW x hx) ⟨hx, by simpa using hcx⟩ (whileWF_of_false (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx (by simpa using hcx)))
  exact key (init.eval e) (hinit e g)

end WFLang.PCL
