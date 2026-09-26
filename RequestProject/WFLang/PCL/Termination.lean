import RequestProject.WFLang.PCL.Lang
import Mathlib.Logic.Relation

/-!
# Why a `PCL` recursive function always has a base case, and why evaluation always terminates

The evaluator `Expr.eval` never looks for a base case: it is a total Lean function
(structural recursion on the syntax, plus `WellFounded.fix` at recursive join points and in the global functions), so it terminates
for *every* well-typed program, and it returns a plain value (no `Option`, no error, no
default value).

This file shows that the base case nevertheless exists, as a *consequence* of the typing
rules.  `firstCall body x` is the argument tuple of the first recursive call that the body
makes when run on `x`, or `none` if the body returns without calling itself (a base case).

* `firstCall_dec`: the first call always goes `R`-down (this is what the `dec` proof on the
  `fixSelfCall` node says).
* `fix_body_reaches_base`: from any starting argument `x`, following first calls reaches, after
  finitely many `R`-steps, an argument on which the body returns without a recursive call.
* `fix_body_has_base_case`: in particular every recursive function body has a base case.
* `loop_unbuildable`: the non-terminating program `f x = f x` cannot be written, because the
  decrease proof its `fixSelfCall` node needs does not exist for a well-founded `R`.
* `joinrec_loop_unbuildable`: the non-terminating loop `joinrec j (x) := jump j x` cannot be
  written either: its back edge needs a proof that `x` is below itself.
-/

namespace WFLang.PCL

/-- What `firstCall` knows about the join points in scope: for each of them, the first
recursive call made by its body when it is jumped to with a given argument (or `none`).  The
calls go below `c0`, the current parameters of the enclosing function (the same at the
definition of the join point and at each jump to it). -/
@[reducible] def JFirst {params : List Ty} (R : Env params → Env params → Prop) (pre : Env params → Prop)
    (c0 : Env params) : {Γ : List Ty} → {t : Ty} → JScope Γ t → Env Γ → Type
  | _, _, .nil, _ => Unit
  | _, _, .bind js s P _, e =>
      ((v : s.denote) → P e v → Option {y : Env params // R y c0 ∧ pre y}) ×
        JFirst R pre c0 js e
  | _, _, .wk js _, e => JFirst R pre c0 js e.2

/-- Lookup in `JFirst`. -/
def JVar.getFirst {params : List Ty} {R : Env params → Env params → Prop}
    {pre : Env params → Prop} {c0 : Env params} :
    {Γ : List Ty} → {t : Ty} → {js : JScope Γ t} → (i : JVar js) → {e : Env Γ} →
    JFirst R pre c0 js e → (v : i.arg.denote) → i.pre e v →
      Option {y : Env params // R y c0 ∧ pre y}
  | _, _, .bind _ _ _ _, .here, _, jf => jf.1
  | _, _, .bind _ _ _ _, .there i, _, jf => i.getFirst jf.2
  | _, _, .wk _ _, .wk i, _, jf => i.getFirst jf

/-- The arguments of the first recursive call made on input `e` (together with the fact that
they are `R`-below the current parameters and satisfy the precondition), or `none` if a `ret`
is reached first.  A `jump` continues with the body of the join point (`jf`).  Calls of global
functions are complete calls: they are run, and the first recursive call is looked for in the
rest.  A recursive join point (a loop inside the body) is followed by well-founded recursion
on its own relation: each back edge re-enters its body, until the body makes a recursive call
of the enclosing function or leaves the loop.  A `map` node looks for the first recursive call in
its body, element by element; if the body makes none, the map is evaluated with the handler `h`
(the values of the recursive calls already completed, which none of these runs needs) and the
first recursive call is looked for in the rest. -/
def Expr.firstCall {GL : List Fn} (ge : FEnv GL) : {Γ : List Ty} → {G : Env Γ → Prop} →
    {sf : Self Γ} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G (some sf) t Q js → (e : Env Γ) → G e → Handler (some sf) e →
    JFirst sf.R sf.pre (sf.cur e) js e →
    Option {y : Env sf.params // sf.R y (sf.cur e) ∧ sf.pre y}
  | _, _, _, _, _, _, .ret _ _ _, _, _, _, _ => none
  | _, _, _, _, _, _, .ite c _ a b, e, g, h, jf =>
      if hc : c.eval e = true then a.firstCall ge e ⟨g, hc⟩ h jf
      else b.firstCall ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h jf
  | _, _, _, _, _, _, .fixSelfCall args _ dec hpre _, e, g, _, _ =>
      some ⟨args.eval e, dec e g, hpre e g⟩
  | _, _, _, _, _, _, .gCall i args _ hpre k, e, g, h, jf =>
      k.firstCall ge ((i.get ge (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get ge (args.eval e) (hpre e g)).2⟩ (Handler.push h) jf
  | _, _, _, _, _, _, .map _ _ l _ body k, e, g, h, jf =>
      ((l.eval e).attach.findSome? fun x =>
          body.firstCall ge (x.1, e) ⟨g, x.2⟩ (Handler.push h) ()).or
        (k.firstCall ge ((l.eval e).attach.map fun x =>
          (body.eval ge (x.1, e) ⟨g, x.2⟩ (Handler.push h) ()).1, e) g (Handler.push h) jf)
  | _, _, _, _, _, _, .join _ _ body m, e, g, h, jf =>
      m.firstCall ge e g h ((fun v hv => body.firstCall ge (v, e) ⟨g, hv⟩ (Handler.push h) jf), jf)
  | _, _, _, _, _, _, .joinrec _ P _ wf body m, e, g, h, jf =>
      let F := (wf e).fix (C := fun x => P e x → Option _)
        (fun x ih hx => body.firstCall ge (x, e) ⟨g, hx⟩ (Handler.push h)
          ((fun y hy => ih y hy.2 hy.1), jf))
      m.firstCall ge e g h ((fun v hv => F v hv), jf)
  | _, _, _, _, _, _, .jump i p _ hpre _, e, g, _, jf =>
      i.getFirst jf (p.eval e) (hpre e g)

/-- The first recursive call always goes down along `R`. -/
theorem firstCall_dec {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop}
    {pre : Env params → Prop} {post : Env params → r.denote → Prop}
    (body : Expr GL params pre (some (Self.top params r R pre post)) r post .nil)
    (x : Env params) (hx : pre x) (h : Handler (some (Self.top params r R pre post)) x)
    (y : {y : Env params // R y x ∧ pre y})
    (_ : body.firstCall ge x hx h () = some y) :
    R y.1 x :=
  y.2.1

/-- **Every run of the body of a recursive function reaches a base case.**  Starting from any
argument `x` satisfying the precondition and following the first recursive call of each step,
one reaches in finitely many `R`-steps an argument `z` on which the body returns without calling
itself. -/
theorem fix_body_reaches_base {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop}
    {pre : Env params → Prop} {post : Env params → r.denote → Prop}
    (wf : WellFounded R) (body : Expr GL params pre (some (Self.top params r R pre post)) r post .nil)
    (x : Env params) (hx : pre x) :
    ∃ z, Relation.ReflTransGen R z x ∧ ∃ hz : pre z,
      body.firstCall ge z hz (fun y _ hy => fixFn ge wf body y hy) () = none := by
  induction x using wf.induction with
  | _ x IH =>
    cases h : body.firstCall ge x hx (fun y _ hy => fixFn ge wf body y hy) () with
    | none => exact ⟨x, .refl, hx, h⟩
    | some y =>
      obtain ⟨z, hz, hbase⟩ := IH y.1 y.2.1 y.2.2
      exact ⟨z, hz.tail y.2.1, hbase⟩

/-- In particular, every recursive function body has a base case: an input on which it returns
without a recursive call (as soon as some input satisfies the precondition). -/
theorem fix_body_has_base_case {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop} {pre : Env params → Prop}
    {post : Env params → r.denote → Prop} (wf : WellFounded R)
    (body : Expr GL params pre (some (Self.top params r R pre post)) r post .nil)
    (x : Env params) (hx : pre x) :
    ∃ z, ∃ hz : pre z, body.firstCall ge z hz (fun y _ hy => fixFn ge wf body y hy) () = none :=
  (fix_body_reaches_base ge wf body x hx).imp fun _ h => h.2

/-- **The looping program cannot be written.**  `fix self x. let v := self x in v` would need
a decrease proof `dec : ∀ e, R e e`; no well-founded `R` admits one. -/
theorem loop_unbuildable {params : List Ty} (R : Env params → Env params → Prop)
    (wf : WellFounded R) (x : Env params)
    (dec : ∀ e : Env params, True →
      (Self.top params .nat R (fun _ => True) (fun _ _ => True)).R
        ((PExprs.ids params).eval e)
        ((Self.top params .nat R (fun _ => True) (fun _ _ => True)).cur e)) : False := by
  obtain ⟨z, _, hz⟩ := fix_body_has_base_case (GL := []) () wf
    (Expr.fixSelfCall (PExprs.ids params) (PExprs.ids_isNF _) dec
      (fun _ _ => trivial) (.ret (.var .here) rfl (fun _ _ => trivial))) x trivial
  rw [Expr.firstCall] at hz
  cases hz

/-- **The looping join point cannot be written.**  In `joinrec j (x) := jump j x in …`, the back
edge `jump j x` needs the proof `hpre` that its argument `x` is below the current parameter
`x` along the well-founded relation `R e` (whenever the jump is reached, i.e. under the path
condition `G` and the precondition `P` of the join point).  No such proof exists as soon as the
loop can be entered (`G e` and `P e x` for some `e`, `x`). -/
theorem joinrec_loop_unbuildable {Γ : List Ty} {G : Env Γ → Prop} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} {s : Ty}
    (P : Env Γ → s.denote → Prop) (R : Env Γ → s.denote → s.denote → Prop)
    (wf : ∀ e, WellFounded (R e))
    (hpre : ∀ e : Env (s :: Γ), G e.2 ∧ P e.2 e.1 →
      (JVar.here : JVar (JScope.bind (JScope.wk js s) s
        (fun e v => P e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r))).pre e
        ((PExpr.var Var.here : PExpr (s :: Γ) s).eval e))
    (e : Env Γ) (x : s.denote) (g : G e) (hx : P e x) : False :=
  (wf e).induction (C := fun y => ¬ R e y y) x (fun y ih hy => ih y hy hy)
    (hpre (x, e) ⟨g, hx⟩).2

end WFLang.PCL

/-! The evaluator's totality is checked by Lean's kernel.  Its only axiom is `propext`, which
comes from the library definitions of the bitwise operators `&&&`, `|||`, `^^^`, `<<<`, `>>>`
(defined in Lean's library by well-founded recursion), not from `Expr.eval` itself. -/
/-- info: 'WFLang.PCL.Expr.eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms WFLang.PCL.Expr.eval
