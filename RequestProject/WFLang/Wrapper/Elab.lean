import RequestProject.WFLang.Wrapper.Guarded
import RequestProject.WFLang.Wrapper.GuardedAcc
import RequestProject.WFLang.Wrapper.FreeCall
import RequestProject.WFLang.Wrapper.Checked
import RequestProject.WFLang.Wrapper.Bridge
import RequestProject.WFLang.Common.Translate

/-!
# `#lean_wf_func_to_term f` for the wrapper designs

Given a Lean function `f : T₁ → … → Tₙ → T` (with `Tᵢ, T ∈ {Nat, Bool}`) defined by
well-founded recursion (`termination_by … decreasing_by …`), the term elaborator

```
def f_term : Guarded.Term ⟨[.nat, .nat], .nat⟩ := #lean_wf_func_to_term f
```

1. reads the unfolding equation `f.eq_def` and translates its right-hand side
   into an object-language body (`if`, `=`/`==`, `<`, `≤`, `+ - * / %`,
   `&&`, `||`, `!`, literals, arguments, recursive calls of `f`);
2. extracts the well-founded relation `r` and its proof `WellFounded r` that
   Lean itself used to define `f` (from `WellFounded.fix` /
   `WellFounded.Nat.fix`), and pulls it back along the packing of the
   arguments — this becomes the `Prop`-level relation of the term;
3. extracts the decreasing proofs of every recursive call site of `f`
   (in particular the ones written by the user in `decreasing_by`) and uses
   them to discharge the certificate of the chosen design (`wf_cert`).

Which design is built is decided by the expected type (`Guarded.Term`,
`GuardedAcc.Term`, `FreeCall.Term` or `Checked.Term`).
-/

namespace WFLang.Wrapper.Capture

open Lean Meta Elab Term
open WFLang.Meta
open WFLang.Translate

/-- The empty relation, used for non-recursive functions. -/
def emptyRel (α : Type) : α → α → Prop := fun _ _ => False

theorem emptyRel_wf (α : Type) : WellFounded (emptyRel α) :=
  ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩

theorem allCalls_ite {A B τ : Type} (P : A → Prop) (c : Prop) [Decidable c]
    (a b : WFLang.FreeCall.Comp A B τ) :
    (if c then a else b).AllCalls P = if c then a.AllCalls P else b.AllCalls P := by
  split <;> rfl

theorem bind_ite {A B σ τ : Type} (c : Prop) [Decidable c] (a b : WFLang.FreeCall.Comp A B σ)
    (f : σ → WFLang.FreeCall.Comp A B τ) :
    (if c then a else b).bind f = if c then a.bind f else b.bind f := by
  split <;> rfl

/-- Tactic used to discharge the certificates: unfold everything, then close
the resulting "recursive call is smaller" goals with the call-site proofs
extracted from the Lean definition (or by `omega`/`decreasing_tactic`). -/
syntax (name := wfCert) "wf_cert" : tactic

macro_rules
  | `(tactic| wf_cert) => `(tactic| first
      | (intro a b
         try dsimp [InvImage, WellFoundedRelation.rel, WFLang.Wrapper.Capture.emptyRel, WFLang.fixedRel]
         try rw [Prod.lex_def]
         try simp only [InvImage, WellFoundedRelation.rel, sizeOf_nat, Nat.lt_wfRel]
         infer_instance)
      | (try apply WFLang.Guarded.dec_of_freeCall
         try apply WFLang.Checked.contracting_of_allCalls
         intro x
         try intro ih
         simp only [WFLang.Guarded.Dec, WFLang.FreeCall.Dec] at *
         simp [WFLang.Guarded.sem, WFLang.Guarded.sems, WFLang.FreeCall.evalC,
           WFLang.FreeCall.evalsC, WFLang.FreeCall.Comp.bind, WFLang.FreeCall.Comp.AllCalls,
           WFLang.Var.get, WFLang.BinOp.eval, WFLang.Ty.beq, InvImage, WFLang.fixedRel,
           WFLang.Wrapper.Capture.allCalls_ite, WFLang.Wrapper.Capture.bind_ite] at *
         all_goals (first
           | done
           | (intros; solve_by_elim)
           | ((repeat' (first | (intro _) | apply And.intro | split)) <;>
              (first
                | done
                | omega
                | ((simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, Nat.lt_wfRel,
                    sizeOf_nat] at *) <;> omega)))
           | (intros; simp_all)
           | (intros; omega)
           | decreasing_tactic)))

/-- The structure behind a program type (unfolding type synonyms). -/
partial def structOf (t : Lean.Expr) : MetaM Name := do
  let t ← whnfCore t
  let .const n _ := t.getAppFn | throwError "#lean_wf_func_to_term: unexpected expected type {t}"
  if isStructure (← getEnv) n then return n
  let some t' ← unfoldDefinition? t | throwError "#lean_wf_func_to_term: {n} is not a program type"
  structOf t'

/-- Is the expected type one of the wrapper program types? -/
def isWrapperType (t : Lean.Expr) : MetaM Bool := do
  try
    let n ← structOf (← instantiateMVars t)
    return n == ``WFLang.Guarded.Term || n == ``WFLang.FreeCall.Term || n == ``WFLang.Checked.Term
  catch _ => return false

/-- `wf_agree` for the wrapper designs: by uniqueness of solutions of the recursive equation
(`Term.eval_eq`) it suffices that `f` satisfies the equation of the body, which follows from
`f.eq_def`. -/
def evalWrapperAgree : Tactic.TacticM Unit := do
  let (t, f, eqDef) ← agreeTarget "wf_agree"
  agreeRec f.getId eqDef
    (← `(tactic| first
        | rw [WFLang.Guarded.Term.eval_eq _ $f]
        | rw [WFLang.GuardedAcc.Term.eval_eq _ $f]
        | rw [WFLang.FreeCall.Term.eval_eq _ $f]
        | rw [WFLang.Checked.Term.eval_eq _ $f]))
    (← `(tactic| simp [$t:ident, WFLang.Expr.evalWith, WFLang.Exprs.evalWith, WFLang.Var.get,
        WFLang.BinOp.eval, WFLang.Ty.beq, WFLang.uncurryEnv]))

/-- Build the program of the wrapper design selected by `expected`. -/
def captureWrapper (fn : Name) (expected : Lean.Expr) : TermElabM Lean.Expr := do
  let expected ← instantiateMVars expected
  let (argTys, retTy) ← signatureOf fn
  let gam := mkTyList argTys
  let sig := mkApp2 (mkConst ``WFLang.Sig.mk) gam retTy
  -- body, from the unfolding equation, in direct style
  let bodyStx ← withEqnRhs fn fun xs rhs => pexpr
    { Ctx.ofParams fn xs with
      ns := `WFLang.Expr, onCall := some (directCall `WFLang.Expr `WFLang.Exprs) } rhs
  let body ← elabTermEnsuringType bodyStx (mkApp (mkConst ``WFLang.Body) sig)
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  -- relation and well-foundedness, pulled back along the argument packing
  let envTy := mkApp (mkConst ``WFLang.Env) gam
  let (R, wf, lemmas) ← match ← closedFixOf fn with
    | some fix => pure fix
    | none =>
      -- a non-recursive function: the empty relation will do
      if body.find? (·.isConstOf ``WFLang.Expr.call) |>.isSome then
        throwError "#lean_wf_func_to_term: {fn} is not defined by well-founded recursion"
      pure (← mkAppOptM ``emptyRel #[envTy], ← mkAppOptM ``emptyRel_wf #[envTy], #[])
  -- build the structure selected by the expected type
  let sName ← structOf expected
  let ctor := getStructureCtor (← getEnv) sName
  let mut val := mkApp (mkConst ctor.name) sig
  let mut ty ← inferType val
  for field in getStructureFields (← getEnv) sName do
    let .forallE _ d _ _ ← whnf ty | throwError "unexpected constructor type"
    let v ← match field.toString with
      | "body" => pure body
      | "R" => pure R
      | "wf" => pure wf
      | _ => do
        let m ← mkFreshExprSyntheticOpaqueMVar d
        let hyps ← lemmas.mapIdxM fun i p => do
          return { userName := Name.mkSimple s!"call_ok_{i}", type := ← inferType p, value := p }
        let (_, g) ← m.mvarId!.assertHypotheses hyps
        let rest ← Tactic.run g (Tactic.evalTactic (← `(tactic| wf_cert)))
        unless rest.isEmpty do
          throwError "#lean_wf_func_to_term: could not discharge field `{field}`"
        instantiateMVars m
    val := mkApp val v
    ty := (← whnf ty).bindingBody!.instantiate1 v
  unless ← isDefEq ty expected do
    throwError "#lean_wf_func_to_term: produced{indentExpr ty}\nbut expected{indentExpr expected}"
  return val

end WFLang.Wrapper.Capture
