import RequestProject.WFLang.Capture.Meta.Mutual

/-!
# Capture metaprogramming: tactics

The tactics `wf_norm_tuples`, `wf_dec`, `wf_solve`, `wf_dec_tag`, `wf_dec_ho`,
`wf_list_cases` and `wf_close`, used by the agreement proofs.
-/

namespace WFLang.Meta

open Lean Meta Elab Term

/-! ## Tactics -/

/-- `wf_norm_tuples` reduces the applications of `WFLang.PCL.tupleTy` to closed lists of types,
and of `WFLang.Ty.denote` to closed object types (`Ty.nat.denote` becomes `Nat`), in the goal and
in the hypotheses (also inside implicit arguments, e.g. the types of the
projections `Prod.fst`, `Prod.snd`).  The same value may otherwise appear with two different
(definitionally equal) types, which `omega` would treat as two different atoms. -/
syntax (name := wfNormTuples) "wf_norm_tuples" : tactic

/-- `e` with the applications of `WFLang.PCL.tupleTy` and `WFLang.Ty.denote` to closed arguments
reduced. -/
def normTuples (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if (x.isAppOfArity `WFLang.PCL.tupleTy 1 || x.isAppOfArity ``WFLang.Ty.denote 1) &&
        !x.hasFVar && !x.hasMVar then
      let r ← whnfR x
      if r != x then return .visit r
    return .done x)

@[tactic wfNormTuples] def evalWfNormTuples : Tactic.Tactic := fun _ =>
  Tactic.withMainContext do
    let mut g ← Tactic.getMainGoal
    let t ← instantiateMVars (← g.getType)
    let t' ← normTuples t
    if t' != t then g ← g.replaceTargetDefEq t'
    for fv in (← g.getDecl).lctx.getFVarIds do
      let d ← g.withContext fv.getDecl
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let ty' ← g.withContext (normTuples ty)
      if ty' != ty then g ← g.replaceLocalDeclDefEq fv ty'
    Tactic.replaceMainGoal [g]

/-- `wf_dec [extra simp lemmas]` proves one obligation `∀ e, G e → P e` of a program from its
path condition `G`: the decrease `R (args e) (cur e)` of a recursive call, the precondition of
the arguments of a call, or the postcondition at a `ret`.  It uses the decreasing proofs of
the Lean definition (offered as hypotheses), `omega`, or `decreasing_tactic`. -/
syntax (name := wfDec) "wf_dec" (" [" ident,* "]")? : tactic

/-- The closing step of `wf_dec`. -/
syntax (name := wfSolve) "wf_solve" : tactic

macro_rules
  | `(tactic| wf_solve) => `(tactic| first
        | done
        | assumption
        | omega
        | ((simp only [WellFoundedRelation.rel, Prod.lex_def, InvImage, Nat.lt_wfRel,
              sizeOf_nat] at *) <;> omega)
        | solve_by_elim
        | (simp_all; done)
        | (simp_all <;> omega)
        | ((simp only [← List.length_pos_iff, ← ne_eq] at *) <;> omega)
        | (((simp only [List.length_pos_iff, ne_eq] at *) <;> simp_all); done)
        | ((simp only [WFLang.Ty.denote, WFLang.PCL.tupleTy] at *) <;> first
            | omega
            | exact Nat.mod_lt _ (by omega)
            | (simp_all; done)
            | (simp_all <;> omega))
        | (simp_all <;> (try simp only [WFLang.Ty.denote] at *) <;> omega)
        | (simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel, sizeOf_nat] at *
           solve_by_elim)
        | (simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel, sizeOf_nat, bne_iff_ne,
              beq_iff_eq, ne_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true'] at *
           solve_by_elim)
        | decreasing_tactic)

macro_rules
  | `(tactic| wf_dec [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec))
  | `(tactic| wf_dec) => `(tactic| (
      intro e g
      try simp [wflang_eval, WFLang.fixedRel, WFLang.fixedAtRel,
        WFLang.preRel, InvImage] at g ⊢
      try casesm* _ ∧ _
      try wf_norm_tuples
      first
        | wf_solve
        | (and_intros <;> wf_solve)))

/-- `wf_dec_tag [extra simp lemmas]`: `wf_dec` for the global function capturing a group
of mutually recursive functions, whose first parameter is a tag: the tag is made a variable and
substituted by its value from the path condition, which selects the member (and its packing into
Lean's domain). -/
syntax (name := wfDecTag) "wf_dec_tag" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| wf_dec_tag [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec_tag))
  | `(tactic| wf_dec_tag) => `(tactic| (
      intro e g
      obtain ⟨t, e⟩ := e
      try simp [wflang_eval, InvImage] at g ⊢
      try casesm* _ ∧ _
      try subst_vars
      try simp only [ite_true, ite_false, reduceIte, WFLang.Ty.denote] at *
      try ((repeat' split) <;> (try contradiction))
      try simp only [WFLang.Ty.denote] at *
      first
        | wf_solve
        | (and_intros <;> wf_solve)))

/-- `wf_dec_ho [extra simp lemmas]`: `wf_dec` for the global function capturing a
function together with a specialised function whose function argument calls it (relation
`WFLang.hoRel`): the tag is substituted by its value, which selects the case of `hoRel`. -/
syntax (name := wfDecHO) "wf_dec_ho" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| wf_dec_ho [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec_ho))
  | `(tactic| wf_dec_ho) => `(tactic| (
      intro e g
      obtain ⟨t, e⟩ := e
      try simp [wflang_eval, InvImage] at g ⊢
      try casesm* _ ∧ _
      try subst_vars
      try simp only [ite_true, ite_false, reduceIte, WFLang.Ty.denote] at *
      try ((repeat' split) <;> (try contradiction))
      all_goals (
        try simp [WFLang.hoRel, WFLang.fixedRel, WFLang.fixedAtRel, InvImage] at *
        try intros
        try casesm* _ ∧ _
        try subst_vars
        try simp only [WFLang.Ty.denote] at *
        first
          | wf_solve
          | (and_intros <;> wf_solve))))

/-- Case analysis, two levels deep (`[]`, `[a]`, `a :: b :: t`), on the list variable `fv`. -/
def casesList2 (g : MVarId) (fv : FVarId) : MetaM (List MVarId) := do
  let mut out := []
  for s in ← g.cases fv do
    if s.ctorName == ``List.cons then
      let some tl := s.fields[1]? | out := out ++ [s.mvarId]; continue
      out := out ++ ((← s.mvarId.cases tl.fvarId!).toList.map (·.mvarId))
    else out := out ++ [s.mvarId]
  return out

/-- `wf_list_cases` closes a goal by a two-level case analysis on one of its list variables
(the patterns of a Lean `match` on lists, e.g. `x :: y :: rest`, split the cases differently
from the tests `l = []`, `l.tail = []` of the program), followed by `simp_all`. -/
syntax (name := wfListCases) "wf_list_cases" : tactic

@[tactic wfListCases] def evalWfListCases : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    unless (← whnfR d.type).isAppOf ``List do continue
    let saved ← saveState
    try
      let gs ← casesList2 g d.fvarId
      for g' in gs do
        let rest ← Tactic.run g' (Tactic.evalTactic (← `(tactic| simp_all)))
        unless rest.isEmpty do throwError "not closed"
      Tactic.replaceMainGoal []
      return
    catch _ => restoreState saved
  throwError "wf_list_cases: failed"

/-- `wf_close` closes the goals left by an agreement proof after unfolding: split every `if`
and `match`, then simplify or use `omega`. -/
syntax (name := wfClose) "wf_close" : tactic

macro_rules
  | `(tactic| wf_close) => `(tactic| (
      all_goals (repeat' split)
      all_goals first
        | (simp_all [Nat.sub_one_add_one]; done)
        | omega
        | (simp_all [Nat.sub_one_add_one] <;> omega)
        | (simp_all [Nat.sub_one_add_one] <;> congr <;> omega)
        | (simp_all [Nat.sub_one_add_one, Bool.beq_eq_decide_eq]; done)
        | (simp_all [Nat.sub_one_add_one, Bool.beq_eq_decide_eq] <;> omega)
        | wf_list_cases))

end WFLang.Meta
