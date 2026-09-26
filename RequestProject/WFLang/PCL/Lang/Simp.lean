import RequestProject.WFLang.PCL.Lang.Program

/-!
# Language `PCL`: simplification lemmas

The `@[simp]` lemmas used by the capture tactics: one evaluation step of each statement, and
the lookup of global functions and join points.
-/

namespace WFLang.PCL

/-! ## Simplification lemmas used by the capture tactics -/

section
variable {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
  {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}

@[simp] theorem eval_ret {sf : Option (Self Γ)} (p : PExpr Γ t) (hp : p.isNF = true)
    (post : ∀ e, G e → Q e (p.eval e))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ret (GL := GL) (sf := sf) (js := js) p hp post).eval ge e g h je).1 =
      p.eval e := rfl

@[simp] theorem eval_ite {sf : Option (Self Γ)}
    (c : PExpr Γ .bool) (hc : c.isCond = true)
    (a : Expr GL Γ (fun e => G e ∧ c.eval e = true) sf t Q js)
    (b : Expr GL Γ (fun e => G e ∧ c.eval e = false) sf t Q js) (e : Env Γ) (g : G e)
    (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ite c hc a b).eval ge e g h je).1 =
      if hc : c.eval e = true then (a.eval ge e ⟨g, hc⟩ h je).1
      else (b.eval ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h je).1 := by
  simp only [Expr.eval]; split <;> rfl

@[simp] theorem eval_fixSelfCall {sf : Self Γ}
    (args : PExprs Γ sf.params) (ha : args.isNF = true)
    (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
    (hpre : ∀ e, G e → sf.pre (args.eval e))
    (k : Expr GL (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1)
      (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret))
    (e : Env Γ) (g : G e) (h : Handler (some sf) e) (je : JEnv js e) :
    ((Expr.fixSelfCall args ha dec hpre k).eval ge e g h je).1 =
      (k.eval ge ((h (args.eval e) (dec e g) (hpre e g)).1, e)
        ⟨g, (h (args.eval e) (dec e g) (hpre e g)).2⟩ h je).1 := rfl

/-- A call of a global function runs the function found in the global context. -/
@[simp] theorem eval_gCall {sf : Option (Self Γ)} {f : Fn}
    (i : FnVar GL f) (args : PExprs Γ f.params) (ha : args.isNF = true)
    (hpre : ∀ e, G e → f.pre (args.eval e))
    (k : Expr GL (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1)
      (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.gCall i args ha hpre k).eval ge e g h je).1 =
      (k.eval ge ((i.get ge (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get ge (args.eval e) (hpre e g)).2⟩ (Handler.push h) je).1 := rfl

/-- A `map` node maps its body over the list (the membership proofs come from `List.attach`,
in the evaluator only), then runs the rest on the result. -/
@[simp] theorem eval_map {sf : Option (Self Γ)}
    (s u : Ty) (l : PExpr Γ (.list s)) (hl : l.isNF = true)
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ e.1 ∈ l.eval e.2) (sf.map (·.push s)) u
      (fun _ _ => True) .nil)
    (k : Expr GL (.list u :: Γ) (fun e => G e.2) (sf.map (·.push (.list u))) t
      (fun e v => Q e.2 v) (.wk js (.list u)))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.map s u l hl body k).eval ge e g h je).1 =
      (k.eval ge ((l.eval e).attach.map fun x =>
          (body.eval ge (x.1, e) ⟨g, x.2⟩ (Handler.push h) ()).1, e) g
        (Handler.push h) je).1 := rfl

/-- A `join` node runs its scope, with the closure of its body as the value of the new join
point. -/
@[simp] theorem eval_join {sf : Option (Self Γ)}
    (s : Ty) (P : Env Γ → s.denote → Prop)
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.wk js s))
    (m : Expr GL Γ G sf t Q (.bind js s P Q))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.join s P body m).eval ge e g h je).1 =
      (m.eval ge e g h
        ((fun v hv => body.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je), je)).1 :=
  rfl

/-- A `jump` runs the join point. -/
@[simp] theorem eval_jump {sf : Option (Self Γ)}
    (i : JVar js) (p : PExpr Γ i.arg) (hp : p.isNF = true)
    (hpre : ∀ e, G e → i.pre e (p.eval e))
    (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r)
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.jump (GL := GL) (sf := sf) i p hp hpre hpost).eval ge e g h je).1 =
      (i.get je (p.eval e) (hpre e g)).1 := rfl

end

@[simp] theorem FnVar.get_here {fs : List Fn} {f : Fn} (fe : FEnv (f :: fs)) :
    (FnVar.here : FnVar (f :: fs) f).get fe = fe.1 := rfl

@[simp] theorem FnVar.get_there {fs : List Fn} {f g : Fn} (i : FnVar fs f)
    (fe : FEnv (g :: fs)) : (FnVar.there i : FnVar (g :: fs) f).get fe = i.get fe.2 := rfl

@[simp] theorem Globals.env_nil : Globals.nil.env = () := rfl

@[simp] theorem Globals.env_defn {GL : List Fn} (gs : Globals GL) (f : Fn)
    (R : Env f.params → Env f.params → Prop) (wf : WellFounded R)
    (body : Expr GL f.params f.pre (some (Self.top f.params f.ret R f.pre f.post)) f.ret
      f.post .nil) :
    (Globals.defn gs f R wf body).env = (fixFn gs.env wf body, gs.env) := rfl

@[simp] theorem JVar.get_here {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty}
    {P : Env Γ → s.denote → Prop} {Q : Env Γ → t.denote → Prop} {e : Env Γ}
    (je : JEnv (.bind js s P Q) e) :
    (JVar.here : JVar (.bind js s P Q)).get je = je.1 := rfl

@[simp] theorem JVar.get_there {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty}
    {P : Env Γ → s.denote → Prop} {Q : Env Γ → t.denote → Prop} {e : Env Γ} (i : JVar js)
    (je : JEnv (.bind js s P Q) e) :
    (JVar.there i : JVar (.bind js s P Q)).get je = i.get (e := e) je.2 := rfl

@[simp] theorem JVar.get_wk {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty}
    {e : Env (s :: Γ)} (i : JVar js) (je : JEnv (.wk js s) e) :
    (JVar.wk i : JVar (.wk js s)).get je = i.get (e := e.2) je := rfl

end WFLang.PCL
