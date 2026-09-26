import RequestProject.WFLang.PCL.Lang.Syntax

/-!
# Language `PCL`: the evaluator

The evaluator `Expr.eval` (terminating, with no fuel), and the soundness of recursive join
points (`joinFn`): their unfolding equations and uniqueness.  `Expr.eval` is the reference
semantics; compiled code runs it with the jump machine of `Machine.lean`.
-/

namespace WFLang.PCL

/-! ## Handlers of recursive calls -/

/-- What a statement may use to perform a recursive call: a function defined on the
arguments that are `R`-below the current parameters and satisfy the precondition, returning
a result that satisfies the postcondition. -/
@[reducible] def Handler {Γ : List Ty} : Option (Self Γ) → Env Γ → Type
  | none, _ => Unit
  | some sf, e => (y : Env sf.params) → sf.R y (sf.cur e) → sf.pre y →
      {v : sf.ret.denote // sf.post y v}

/-- Moving a handler under a new local variable. -/
def Handler.push {Γ : List Ty} {r : Ty} {v : r.denote} {e : Env Γ} :
    {sf : Option (Self Γ)} → Handler sf e → Handler (sf.map (·.push r)) ((v, e) : Env (r :: Γ))
  | none, h => h
  | some _, h => h

/-! ## The evaluator -/

/-- The evaluator: structural recursion on the syntax; a `joinrec` node is run by
`WellFounded.fix` on its own relation, and a `join` node passes the closure of its body to its
scope.  The values `ge` of the global functions are fixed.  No fuel, no runtime checks: the
proofs (path conditions, pre- and postconditions, normal forms) are erased by code
generation. -/
def Expr.eval {GL : List Fn} (ge : FEnv GL) : {Γ : List Ty} → {G : Env Γ → Prop} →
    {sf : Option (Self Γ)} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G sf t Q js → (e : Env Γ) → G e → Handler sf e → JEnv js e →
    {v : t.denote // Q e v}
  | _, _, _, _, _, _, .ret p _ post, e, g, _, _ => ⟨p.eval e, post e g⟩
  | _, _, _, _, _, _, .ite c _ a b, e, g, h, je =>
      if hc : c.eval e = true then a.eval ge e ⟨g, hc⟩ h je
      else b.eval ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h je
  | _, _, _, _, _, _, .fixSelfCall args _ dec hpre k, e, g, h, je =>
      let v := h (args.eval e) (dec e g) (hpre e g)
      let r := k.eval ge (v.1, e) ⟨g, v.2⟩ h je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .gCall i args _ hpre k, e, g, h, je =>
      let v := i.get ge (args.eval e) (hpre e g)
      let r := k.eval ge (v.1, e) ⟨g, v.2⟩ (Handler.push h) je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .plet _ p _ k, e, g, h, je =>
      let r := k.eval ge (p.eval e, e) ⟨g, rfl⟩ (Handler.push h) je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .map _ _ l _ body k, e, g, h, je =>
      let vs := (l.eval e).attach.map fun x => (body.eval ge (x.1, e) ⟨g, x.2⟩ (Handler.push h) ()).1
      let r := k.eval ge (vs, e) g (Handler.push h) je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .foldl _ _ l _ init _ body k, e, g, h, je =>
      let r := (l.eval e).attach.foldl (fun acc x =>
        (body.eval ge (acc, x.1, e) ⟨g, x.2⟩ (Handler.push (Handler.push h)) ()).1) (init.eval e)
      let r' := k.eval ge (r, e) g (Handler.push h) je
      ⟨r'.1, r'.2⟩
  | _, _, _, _, _, _, .join _ _ body m, e, g, h, je =>
      m.eval ge e g h ((fun v hv => body.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je), je)
  | _, _, _, _, _, _, .joinrec _ P _ wf body m, e, g, h, je =>
      let F := (wf e).fix (C := fun x => P e x → Subtype _)
        (fun x ih hx => body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
          ((fun y hy => ih y hy.2 hy.1), je))
      m.eval ge e g h ((fun v hv => F v hv), je)
  | _, _, _, _, _, _, .jump i p _ hpre hpost, e, g, _, je =>
      let r := i.get je (p.eval e) (hpre e g)
      ⟨r.1, hpost e g r.1 r.2⟩

/-! ## Soundness of recursive join points -/

section
variable {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
  {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
  {s : Ty} {P : Env Γ → s.denote → Prop} {R : Env Γ → s.denote → s.denote → Prop}
  (wf : ∀ e, WellFounded (R e))
  (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
    (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
      (fun e r => Q e.2 r)))
  (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e)

/-- The function denoted by a recursive join point (at the environment `e` of its definition,
with the handler `h` of the enclosing function and the values `je` of the outer join points):
the result of the enclosing statement when the join point is entered with parameter `x`. -/
def joinFn : (x : s.denote) → P e x → {r : t.denote // Q e r} :=
  (wf e).fix (C := fun x => P e x → {r // Q e r})
    (fun x ih hx => body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
      ((fun y hy => ih y hy.2 hy.1), je))

/-- **Soundness (1):** a recursive join point satisfies its equation: entering it runs its
body, in which a back edge re-enters it. -/
theorem joinFn_eq (x : s.denote) (hx : P e x) :
    joinFn ge wf body e g h je x hx =
      body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
        ((fun y hy => joinFn ge wf body e g h je y hy.1), je) := by
  unfold joinFn
  rw [WellFounded.fix_eq]

/-- **Soundness (2):** that equation has only one solution. -/
theorem joinFn_unique (F : (x : s.denote) → P e x → {r : t.denote // Q e r})
    (hF : ∀ x hx, (F x hx).1 = (body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
      ((fun y hy => F y hy.1), je)).1) :
    ∀ x hx, (joinFn ge wf body e g h je x hx).1 = (F x hx).1 := by
  intro x
  induction x using (wf e).induction with
  | _ x IH =>
    intro hx
    rw [joinFn_eq, hF x hx]
    have : (fun y (hy : P e y ∧ R e y x) => joinFn ge wf body e g h je y hy.1) =
        (fun y hy => F y hy.1) := by
      funext y hy; exact Subtype.ext (IH y hy.2 hy.1)
    exact congrArg (fun k => (body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h) (k, je)).1) this

end

@[simp] theorem eval_joinrec {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (P : Env Γ → s.denote → Prop) (R : Env Γ → s.denote → s.denote → Prop)
    (wf : ∀ e, WellFounded (R e))
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
        (fun e r => Q e.2 r)))
    (m : Expr GL Γ G sf t Q (.bind js s P Q))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.joinrec s P R wf body m).eval ge e g h je).1 =
      (m.eval ge e g h ((fun v hv => joinFn ge wf body e g h je v hv), je)).1 := rfl

end WFLang.PCL
