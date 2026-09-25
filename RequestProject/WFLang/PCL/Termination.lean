import RequestProject.WFLang.PCL.Lang
import Mathlib.Logic.Relation

/-!
# Why a `PCL` `fix` always has a base case, and why evaluation always terminates

The evaluator `Expr.eval` never looks for a base case: it is a total Lean function
(structural recursion on the syntax, plus `WellFounded.fix` at `fix` nodes), so it terminates
for *every* well-typed program, and it returns a plain value (no `Option`, no error, no
default value).

This file shows that the base case nevertheless exists, as a *consequence* of the typing
rules.  `firstCall body x` is the argument tuple of the first recursive call that the body
makes when run on `x`, or `none` if the body returns without calling itself (a base case).

* `firstCall_dec`: the first call always goes `R`-down (this is what the `dec` proof on the
  `fixSelfCall` node says).
* `fix_body_reaches_base`: from any starting argument `x`, following first calls reaches, after
  finitely many `R`-steps, an argument on which the body returns without a recursive call.
* `fix_body_has_base_case`: in particular every `fix` body has a base case.
* `loop_unbuildable`: the non-terminating program `f x = f x` cannot be written, because the
  decrease proof its `fixSelfCall` node needs does not exist for a well-founded `R`.
-/

namespace WFLang.PCL

/-- What `firstCall` knows about the join points in scope: for each of them, the first
recursive call made by its body when it is jumped to with a given argument (or `none`).  The
calls go below `c0`, the current parameters of the enclosing function (the same at the
definition of the join point and at each jump to it). -/
def JFirst {params : List Ty} (R : Env params → Env params → Prop) (pre : Env params → Prop)
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
is reached first.  A `jump` continues with the body of the join point (`jf`).  Calls of local
and global functions are complete calls: they are run, and the first recursive call is looked
for in the rest. -/
def Expr.firstCall {GL : List Fn} (ge : FEnv GL) : {Γ : List Ty} → {G : Env Γ → Prop} →
    {fns : List Fn} → {sf : Self Γ} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G fns (some sf) t Q js → (e : Env Γ) → G e → FEnv fns →
    JFirst sf.R sf.pre (sf.cur e) js e →
    Option {y : Env sf.params // sf.R y (sf.cur e) ∧ sf.pre y}
  | _, _, _, _, _, _, _, .ret _ _ _, _, _, _, _ => none
  | _, _, _, _, _, _, _, .ite c _ a b, e, g, fe, jf =>
      if hc : c.eval e = true then a.firstCall ge e ⟨g, hc⟩ fe jf
      else b.firstCall ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ fe jf
  | _, _, _, _, _, _, _, .fixSelfCall args _ dec hpre _, e, g, _, _ =>
      some ⟨args.eval e, dec e g, hpre e g⟩
  | _, _, _, _, _, _, _, .fnCall i args _ hpre k, e, g, fe, jf =>
      k.firstCall ge ((i.get fe (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get fe (args.eval e) (hpre e g)).2⟩ fe jf
  | _, _, _, _, _, _, _, .gCall i args _ hpre k, e, g, fe, jf =>
      k.firstCall ge ((i.get ge (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get ge (args.eval e) (hpre e g)).2⟩ fe jf
  | _, _, _, _, _, _, _, .fix _ _ _ wf _ _ body rest, e, g, fe, jf =>
      rest.firstCall ge e g (fixFn ge wf body fe, fe) jf
  | _, _, _, _, _, _, _, .join _ _ body m, e, g, fe, jf =>
      m.firstCall ge e g fe ((fun v hv => body.firstCall ge (v, e) ⟨g, hv⟩ fe jf), jf)
  | _, _, _, _, _, _, _, .jump i p _ hpre _, e, g, _, jf =>
      i.getFirst jf (p.eval e) (hpre e g)

/-- The first recursive call always goes down along `R`. -/
theorem firstCall_dec {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty} {R : Env params → Env params → Prop}
    {pre : Env params → Prop} {post : Env params → r.denote → Prop} {fns : List Fn}
    (body : Expr GL params pre fns (some (Self.top params r R pre post)) r post .nil) (fe : FEnv fns)
    (x : Env params) (hx : pre x) (y : {y : Env params // R y x ∧ pre y})
    (_ : body.firstCall ge x hx fe () = some y) :
    R y.1 x :=
  y.2.1

/-- **Every run of a `fix` body reaches a base case.**  Starting from any argument `x`
satisfying the precondition and following the first recursive call of each step, one
reaches in finitely many `R`-steps an argument `z` on which the body returns without calling
itself. -/
theorem fix_body_reaches_base {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty} {R : Env params → Env params → Prop}
    {pre : Env params → Prop} {post : Env params → r.denote → Prop} {fns : List Fn}
    (wf : WellFounded R) (body : Expr GL params pre fns (some (Self.top params r R pre post)) r post .nil)
    (fe : FEnv fns) (x : Env params) (hx : pre x) :
    ∃ z, Relation.ReflTransGen R z x ∧ ∃ hz : pre z, body.firstCall ge z hz fe () = none := by
  induction x using wf.induction with
  | _ x IH =>
    cases h : body.firstCall ge x hx fe () with
    | none => exact ⟨x, .refl, hx, h⟩
    | some y =>
      obtain ⟨z, hz, hbase⟩ := IH y.1 y.2.1 y.2.2
      exact ⟨z, hz.tail y.2.1, hbase⟩

/-- In particular, every `fix` body has a base case: an input on which it returns without a
recursive call (as soon as some input satisfies the precondition). -/
theorem fix_body_has_base_case {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop} {pre : Env params → Prop}
    {post : Env params → r.denote → Prop} {fns : List Fn} (wf : WellFounded R)
    (body : Expr GL params pre fns (some (Self.top params r R pre post)) r post .nil) (fe : FEnv fns)
    (x : Env params) (hx : pre x) : ∃ z, ∃ hz : pre z, body.firstCall ge z hz fe () = none :=
  (fix_body_reaches_base ge wf body fe x hx).imp fun _ h => h.2

/-- **The looping program cannot be written.**  `fix self x. let v := self x in v` would need
a decrease proof `dec : ∀ e, R e e`; no well-founded `R` admits one. -/
theorem loop_unbuildable {params : List Ty} (R : Env params → Env params → Prop)
    (wf : WellFounded R) (x : Env params)
    (dec : ∀ e : Env params, True →
      (Self.top params .nat R (fun _ => True) (fun _ _ => True)).R
        ((PExprs.ids params).eval e)
        ((Self.top params .nat R (fun _ => True) (fun _ _ => True)).cur e)) : False := by
  obtain ⟨z, _, hz⟩ := fix_body_has_base_case (GL := []) () wf
    (Expr.fixSelfCall (fns := []) (PExprs.ids params) (PExprs.ids_isNF _) dec
      (fun _ _ => trivial) (.ret (.var .here) rfl (fun _ _ => trivial))) () x trivial
  rw [Expr.firstCall] at hz
  cases hz

end WFLang.PCL

/-! The evaluator's totality is checked by Lean's kernel.  Its only axiom is `propext`, which
comes from the library definitions of the bitwise operators `&&&`, `|||`, `^^^`, `<<<`, `>>>`
(defined in Lean's library by well-founded recursion), not from `Expr.eval` itself. -/
/-- info: 'WFLang.PCL.Expr.eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms WFLang.PCL.Expr.eval
