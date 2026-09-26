import RequestProject.WFLang.Capture.Meta.Mutual

/-!
# Capture metaprogramming: tactics

The tactics `wf_norm_tuples`, `wf_subst_lets`, `wf_dec`, `wf_solve`, `wf_dec_tag`, `wf_dec_ho`,
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

/-- Is `e` a variable of the program: a chain of projections `Prod.fst`/`Prod.snd` of a local
variable (the environment)? -/
partial def isEnvProj (e : Lean.Expr) : Bool :=
  if e.isFVar then true
  else if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then isEnvProj e.appArg!
  else false

/-- `wf_subst_lets` substitutes the variables bound by pure `let`s (`PCL.Expr.plet`): each
hypothesis `x = v` of the path condition, where `x` is a variable of the program (a projection
of the environment) that does not occur in the non-literal value `v`, is used to rewrite `x` into
`v` in the goal and in the other hypotheses.  The obligations then mention the values
themselves, as the Lean function does (for instance `m % n < n` rather than `r < n`, with the
hypothesis `r = m % n`). -/
syntax (name := wfSubstLets) "wf_subst_lets" : tactic

/-- A hypothesis `x = v` of `g` that `wf_subst_lets` uses (see there), whose variable `x` is
not in `done`. -/
def letEqHyp? (g : MVarId) (done : List Lean.Expr) : MetaM (Option (FVarId × Lean.Expr)) :=
  g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless isEnvProj lhs && !lhs.isFVar && !done.contains lhs do continue
      if rhs.isFVar || rhs.isRawNatLit || rhs.nat?.isSome || rhs.int?.isSome || rhs.isConst ||
          isEnvProj rhs then continue
      if (rhs.find? (· == lhs)).isSome then continue
      return some (d.fvarId, lhs)
    return none

@[tactic wfSubstLets] def evalWfSubstLets : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let mut g ← Tactic.getMainGoal
  let mut done : List Lean.Expr := []
  for _ in [0:(← getLCtx).numIndices] do
    let some (h, lhs) ← letEqHyp? g done | break
    done := lhs :: done
    g ← g.withContext do
      let mut g := g
      -- the goal
      let tgt ← instantiateMVars (← g.getType)
      if (tgt.find? (· == lhs)).isSome then
        let r ← g.rewrite tgt (mkFVar h)
        g ← g.replaceTargetEq r.eNew r.eqProof
      -- the other hypotheses
      for d in (← g.getDecl).lctx do
        if d.isImplementationDetail || d.fvarId == h then continue
        let ty ← instantiateMVars d.type
        unless (ty.find? (· == lhs)).isSome do continue
        unless ← isProp ty do continue
        try
          let r ← g.rewrite ty (mkFVar h)
          g := (← g.replaceLocalDecl d.fvarId r.eNew r.eqProof).mvarId
        catch _ => pure ()
      return g
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
        | (apply Nat.mod_lt; omega)
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
        -- an `if` in the goal (e.g. from `min`/`max`): split it, then `omega` in each branch
        | (((try simp only [WFLang.Ty.denote, WFLang.PCL.tupleTy] at *); (repeat' split) <;>
            first | omega | (simp_all <;> omega)); done)
        | decreasing_tactic)

macro_rules
  | `(tactic| wf_dec [$extra,*]) => `(tactic| ((try simp only [$[$extra:ident],*]); wf_dec))
  | `(tactic| wf_dec) => `(tactic| (
      intro e g
      try simp [wflang_eval, WFLang.fixedRel, WFLang.fixedAtRel,
        WFLang.preRel, InvImage] at g ⊢
      try casesm* _ ∧ _
      try wf_subst_lets
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
      try wf_subst_lets
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
      try wf_subst_lets
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
        let rest ← Tactic.run g' (Tactic.evalTactic (← `(tactic|
          first | (simp_all; done) | simp_all [Bool.or_assoc, Bool.and_assoc])))
        unless rest.isEmpty do throwError "not closed"
      Tactic.replaceMainGoal []
      return
    catch _ => restoreState saved
  throwError "wf_list_cases: failed on the goal{indentD (← Meta.ppGoal g)}"

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
        | (simp_all [Nat.sub_one_add_one, decide_eq_false, decide_eq_true]; done)
        | (simp_all [Nat.sub_one_add_one, Bool.or_assoc, Bool.and_assoc]; done)
        | wf_list_cases))

end WFLang.Meta
