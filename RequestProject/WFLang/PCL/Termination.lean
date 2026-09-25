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
  `call` node says).
* `fix_body_reaches_base`: from any starting argument `x`, following first calls reaches, after
  finitely many `R`-steps, an argument on which the body returns without a recursive call.
* `fix_body_has_base_case`: in particular every `fix` body has a base case.
* `loop_unbuildable`: the non-terminating program `f x = f x` cannot be written, because the
  decrease proof its `call` node needs does not exist for a well-founded `R`.
-/

namespace WFLang.PCL

/-- The arguments of the first recursive call made on input `e` (together with the fact that
they are `R`-below the current parameters), or `none` if a `ret` is reached first. -/
def Expr.firstCall : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Self Γ} → {t : Ty} →
    Expr Γ G (some sf) t → (e : Env Γ) → G e →
    Option {y : Env sf.params // sf.R y (sf.cur e)}
  | _, _, _, _, .ret _, _, _ => none
  | _, _, _, _, .ite c a b, e, g =>
      if hc : c.eval e = true then a.firstCall e ⟨g, hc⟩
      else b.firstCall e ⟨g, Bool.eq_false_iff.mpr hc⟩
  | _, _, _, _, .call args dec _, e, g => some ⟨args.eval e, dec e g⟩
  | _, _, _, _, .fix _ _ _ wf body args k, e, g =>
      k.firstCall (fixFn wf body (args.eval e), e) g

/-- The first recursive call always goes down along `R`. -/
theorem firstCall_dec {params : List Ty} {r : Ty} {R : Env params → Env params → Prop}
    (body : Expr params (fun _ => True) (some (Self.top params r R)) r) (x : Env params)
    (y : {y : Env params // R y x}) (_ : body.firstCall x trivial = some y) : R y.1 x :=
  y.2

/-- **Every run of a `fix` body reaches a base case.**  Starting from any argument `x` and
following the first recursive call of each step, one reaches in finitely many `R`-steps an
argument `z` on which the body returns without calling itself. -/
theorem fix_body_reaches_base {params : List Ty} {r : Ty} {R : Env params → Env params → Prop}
    (wf : WellFounded R) (body : Expr params (fun _ => True) (some (Self.top params r R)) r)
    (x : Env params) :
    ∃ z, Relation.ReflTransGen R z x ∧ body.firstCall z trivial = none := by
  induction x using wf.induction with
  | _ x IH =>
    cases h : body.firstCall x trivial with
    | none => exact ⟨x, .refl, h⟩
    | some y =>
      obtain ⟨z, hz, hbase⟩ := IH y.1 y.2
      exact ⟨z, hz.tail y.2, hbase⟩

/-- In particular, every `fix` body has a base case: an input on which it returns without a
recursive call.  (Every `Env` is inhabited, so this needs no extra hypothesis.) -/
theorem fix_body_has_base_case {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop} (wf : WellFounded R)
    (body : Expr params (fun _ => True) (some (Self.top params r R)) r) (x : Env params) :
    ∃ z, body.firstCall z trivial = none :=
  (fix_body_reaches_base wf body x).imp fun _ h => h.2

/-- **The looping program cannot be written.**  `fix self x. let v := self x in v` would need
a decrease proof `dec : ∀ e, R e e`; no well-founded `R` admits one. -/
theorem loop_unbuildable {params : List Ty} (R : Env params → Env params → Prop)
    (wf : WellFounded R) (x : Env params)
    (dec : ∀ e : Env params, True → (Self.top params .nat R).R
        ((PExprs.ids params).eval e) ((Self.top params .nat R).cur e)) : False := by
  obtain ⟨z, hz⟩ := fix_body_has_base_case wf
    (Expr.call (PExprs.ids params) dec (.ret (.var .here))) x
  rw [Expr.firstCall] at hz
  cases hz

end WFLang.PCL

/-! The evaluator itself uses no axioms at all: its totality is checked by Lean's kernel. -/
/-- info: 'WFLang.PCL.Expr.eval' does not depend on any axioms -/
#guard_msgs in #print axioms WFLang.PCL.Expr.eval
