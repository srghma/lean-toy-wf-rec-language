import RequestProject.WFLang.PCL.Lang.Eval

/-!
# Language `PCL`: the jump machine (the evaluator that is actually run)

`Expr.eval` (in `Eval.lean`) is the reference evaluator: a join point is a closure stored in
the environment `JEnv`, and a `jump` calls it.  Each iteration of a loop (`joinrec`) therefore
nests one more call (the jump calls the closure of the loop body, which runs the body, which
jumps …), so the evaluator uses stack in proportion to the number of iterations.  Likewise a
recursive call is an argument of the rest of the statement, even when that rest is just
`ret v`, so a tail-recursive function uses stack in proportion to its number of calls.

`Expr.evalS` is the same evaluator without join-point closures.  A statement returns a `Step`:
its value, a **pending jump** `jmp i v` to one of the join points `i` in scope, or a **pending
tail call** `call y` of the enclosing function (the statement `let v := self y in ret v`,
recognised by `Expr.retHere?`).  The statement that defines a join point handles the jumps to
it:

* `join j (v) := body in m`: if `m` jumps to `j`, run `body`;
* `joinrec j (x) := body in m`: if `m` jumps to `j`, run the loop `runLoop`: run `body`; while it
  jumps back to `j`, run it again with the new parameter.  `runLoop` is a tail-recursive
  function, compiled to a loop: the iterations of a loop use no stack.

Any other jump, and any tail call, is passed outwards unchanged; tail calls are run by the
function itself (`fixS` in `Fix.lean`, also a loop).  The stack depth of the machine is thus
bounded by the nesting depth of the syntax plus the depth of the *non-tail* recursive calls,
not by the number of loop iterations or tail calls.

`Expr.eval_val_eq_evalS` proves `(x.eval ge e g h je).1 = (x.evalS ge e g h).run h je`, and
`Expr.eval = Expr.evalImpl` is registered as a `@[csimp]` lemma, so compiled code (and `#eval`)
runs `evalS`.  The results of the machine are thus the results of `Expr.eval`, by a proof.
-/

namespace WFLang.PCL

/-! ## Steps -/

/-- A pending **tail call** of the enclosing recursive function `sf` (a statement
`let v := self args in ret v`): its arguments `y`, below the current parameters, satisfying
the precondition, and the fact that the result type `t` of the statement is the result type of
the function.  There is none outside a recursive function. -/
@[reducible] def TailCall {Γ : List Ty} : Option (Self Γ) → Ty → Env Γ → Type
  | none, _, _ => Empty
  | some sf, t, e => {y : Env sf.params // sf.R y (sf.cur e) ∧ sf.pre y ∧ sf.ret = t}

/-- The value of a tail call, computed by the handler of recursive calls. -/
def TailCall.run {Γ : List Ty} {t : Ty} {e : Env Γ} :
    {sf : Option (Self Γ)} → Handler sf e → TailCall sf t e → t.denote
  | none, _, c => Empty.elim c
  | some _, h, c => cast (congrArg Ty.denote c.2.2.2) (h c.1 c.2.1 c.2.2.1).1

/-- A tail call under one more local variable, seen from outside it. -/
def TailCall.unpush {Γ : List Ty} {t s : Ty} {x : s.denote} {e : Env Γ} :
    {sf : Option (Self Γ)} → TailCall (sf.map (·.push s)) t ((x, e) : Env (s :: Γ)) →
      TailCall sf t e
  | none, c => Empty.elim c
  | some _, c => c

@[simp] theorem TailCall.unpush_run {Γ : List Ty} {t s : Ty} {x : s.denote} {e : Env Γ}
    {sf : Option (Self Γ)} (c : TailCall (sf.map (·.push s)) t ((x, e) : Env (s :: Γ)))
    (h : Handler sf e) : c.unpush.run h = c.run (Handler.push h) := by
  cases sf with
  | none => exact Empty.elim c
  | some _ => rfl

/-- The outcome of a statement run by the jump machine at the environment `e`: a value, a
pending jump to a join point `i` in scope, with its argument `v` (which satisfies the
precondition of `i`), or a pending tail call of the enclosing recursive function. -/
inductive Step {Γ : List Ty} {t : Ty} (sf : Option (Self Γ)) (js : JScope Γ t) (e : Env Γ) :
    Type where
  | val (r : t.denote)
  | jmp (i : JVar js) (v : i.arg.denote) (hv : i.pre e v)
  | call (c : TailCall sf t e)

/-- The value of a step, given the handler `h` of recursive calls and the closures `je` of the
join points in scope (only used to relate the machine to `Expr.eval`, and where the value of a
step is needed: at the top level, where there is no join point, and in the body of a `map`). -/
def Step.run {Γ : List Ty} {t : Ty} {sf : Option (Self Γ)} {js : JScope Γ t} {e : Env Γ} :
    Step sf js e → Handler sf e → JEnv js e → t.denote
  | .val r, _, _ => r
  | .jmp i v hv, _, je => (i.get je v hv).1
  | .call c, h, _ => c.run h

/-- A step of a statement under one more local variable, seen from outside it. -/
def Step.unwk {Γ : List Ty} {t s : Ty} {sf : Option (Self Γ)} {js : JScope Γ t} {x : s.denote}
    {e : Env Γ} : Step (sf.map (·.push s)) (.wk js s) ((x, e) : Env (s :: Γ)) → Step sf js e
  | .val r => .val r
  | .jmp (.wk i) v hv => .jmp i v hv
  | .call c => .call c.unpush

@[simp] theorem Step.unwk_run {Γ : List Ty} {t s : Ty} {sf : Option (Self Γ)} {js : JScope Γ t}
    {x : s.denote} {e : Env Γ} (st : Step (sf.map (·.push s)) (.wk js s) ((x, e) : Env (s :: Γ)))
    (h : Handler sf e) (je : JEnv js e) :
    (st.unwk).run h je = st.run (Handler.push h) je := by
  cases st with
  | val r => rfl
  | jmp i v hv => cases i; rfl
  | call c => exact TailCall.unpush_run c h

/-! ## Tail calls -/

/-- Is the call-free expression `p` the variable bound last (`here`)?  If so, its type is the
type of that variable. -/
def pexprHere? {r : Ty} {Γ : List Ty} {t : Ty} : PExpr (r :: Γ) t → Option (PLift (r = t))
  | .var .here => some ⟨rfl⟩
  | _ => none

theorem pexprHere?_eval {r : Ty} {Γ : List Ty} {t : Ty} (p : PExpr (r :: Γ) t) (heq : PLift (r = t))
    (hp : pexprHere? p = some heq) (env : Env (r :: Γ)) :
    p.eval env = cast (congrArg Ty.denote heq.down) env.1 := by
  unfold pexprHere? at hp
  split at hp
  · rfl
  · cases hp

/-- Is the statement `k` (under a new variable `v`) the statement `ret v`?  This is the
continuation of a tail call `let v := self args in ret v`. -/
def Expr.retHere? {GL : List Fn} {r : Ty} {Γ : List Ty} {G : Env (r :: Γ) → Prop}
    {sf : Option (Self (r :: Γ))} {t : Ty} {Q : Env (r :: Γ) → t.denote → Prop}
    {js : JScope (r :: Γ) t} : Expr GL (r :: Γ) G sf t Q js → Option (PLift (r = t))
  | .ret p _ _ => pexprHere? p
  | _ => none

theorem Expr.retHere?_eval {GL : List Fn} (ge : FEnv GL) {r : Ty} {Γ : List Ty}
    {G : Env (r :: Γ) → Prop} {sf : Option (Self (r :: Γ))} {t : Ty}
    {Q : Env (r :: Γ) → t.denote → Prop} {js : JScope (r :: Γ) t}
    (k : Expr GL (r :: Γ) G sf t Q js) (heq : PLift (r = t)) (hk : k.retHere? = some heq)
    (env : Env (r :: Γ)) (g : G env) (h : Handler sf env) (je : JEnv js env) :
    (k.eval ge env g h je).1 = cast (congrArg Ty.denote heq.down) env.1 := by
  unfold Expr.retHere? at hk
  split at hk
  · exact pexprHere?_eval _ heq hk env
  · cases hk

/-! ## Loops -/

/-- A loop: `step x` either ends the loop with a result, or continues with a parameter that is
smaller along the well-founded relation.  Tail-recursive: compiled to a loop. -/
def runLoop {α C : Type} [WellFoundedRelation α] (P : α → Prop)
    (step : (x : α) → P x → C ⊕ {y : α // P y ∧ WellFoundedRelation.rel y x}) (x : α)
    (hx : P x) : C :=
  match step x hx with
  | .inl c => c
  | .inr y => runLoop P step y.1 y.2.1
termination_by x
decreasing_by exact y.2.2

theorem runLoop_eq {α C : Type} [WellFoundedRelation α] (P : α → Prop)
    (step : (x : α) → P x → C ⊕ {y : α // P y ∧ WellFoundedRelation.rel y x}) (x : α)
    (hx : P x) :
    runLoop P step x hx = match step x hx with
      | .inl c => c
      | .inr y => runLoop P step y.1 y.2.1 := by
  rw [runLoop]

/-! ## The jump machine -/

/-- One iteration of a loop `joinrec j (x) := body in m`: classify the step of the body into
a back edge (a jump to `j`), or the end of the loop (a value, or a jump to an outer join
point). -/
def loopStep {Γ : List Ty} {t s : Ty} {sf : Option (Self Γ)} {js : JScope Γ t} {P : Env Γ → s.denote → Prop}
    {R : Env Γ → s.denote → s.denote → Prop} {Q : Env Γ → t.denote → Prop} {e : Env Γ}
    {x : s.denote} :
    Step (sf.map (·.push s))
      (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r))
      ((x, e) : Env (s :: Γ)) → Step sf js e ⊕ {y : s.denote // P e y ∧ R e y x}
  | .val r => .inl (.val r)
  | .jmp .here y hy => .inr ⟨y, hy⟩
  | .jmp (.there (.wk i)) y hy => .inl (.jmp i y hy)
  | .call c => .inl (.call c.unpush)

/-- The jump machine: `Expr.eval` without join-point closures (see the module docstring).
Structural recursion on the syntax; a loop is run by `runLoop`. -/
def Expr.evalS {GL : List Fn} (ge : FEnv GL) : {Γ : List Ty} → {G : Env Γ → Prop} →
    {sf : Option (Self Γ)} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G sf t Q js → (e : Env Γ) → G e → Handler sf e → Step sf js e
  | _, _, _, _, _, _, .ret p _ _, e, _, _ => .val (p.eval e)
  | _, _, _, _, _, _, .ite c _ a b, e, g, h =>
      if hc : c.eval e = true then a.evalS ge e ⟨g, hc⟩ h
      else b.evalS ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h
  | _, _, _, _, _, _, .fixSelfCall args _ dec hpre k, e, g, h =>
      match k.retHere? with
      | some heq => .call ⟨args.eval e, dec e g, hpre e g, heq.down⟩
      | none =>
        let v := h (args.eval e) (dec e g) (hpre e g)
        Step.unwk (sf := some _) (k.evalS ge (v.1, e) ⟨g, v.2⟩ h)
  | _, _, _, _, _, _, .gCall i args _ hpre k, e, g, h =>
      let v := i.get ge (args.eval e) (hpre e g)
      (k.evalS ge (v.1, e) ⟨g, v.2⟩ (Handler.push h)).unwk
  | _, _, _, _, _, _, .map _ _ l _ body k, e, g, h =>
      let vs := (l.eval e).attach.map fun x =>
        (body.evalS ge (x.1, e) ⟨g, x.2⟩ (Handler.push h)).run (Handler.push h) ()
      (k.evalS ge (vs, e) g (Handler.push h)).unwk
  | _, _, _, _, _, _, .foldl _ _ l _ init _ body k, e, g, h =>
      let r := (l.eval e).attach.foldl (fun acc x =>
        (body.evalS ge (acc, x.1, e) ⟨g, x.2⟩ (Handler.push (Handler.push h))).run
          (Handler.push (Handler.push h)) ()) (init.eval e)
      (k.evalS ge (r, e) g (Handler.push h)).unwk
  | _, _, _, _, _, _, .join _ _ body m, e, g, h =>
      match m.evalS ge e g h with
      | .val r => .val r
      | .jmp .here v hv => (body.evalS ge (v, e) ⟨g, hv⟩ (Handler.push h)).unwk
      | .jmp (.there i) v hv => .jmp i v hv
      | .call c => .call c
  | _, _, _, _, _, _, .joinrec _ _ R wf body m, e, g, h =>
      match m.evalS ge e g h with
      | .val r => .val r
      | .jmp .here v hv =>
          @runLoop _ _ ⟨R e, wf e⟩ _
            (fun x hx => loopStep (body.evalS ge (x, e) ⟨g, hx⟩ (Handler.push h))) v hv
      | .jmp (.there i) v hv => .jmp i v hv
      | .call c => .call c
  | _, _, _, _, _, _, .jump i p _ hpre _, e, g, _ => .jmp i (p.eval e) (hpre e g)

/-! ## The jump machine computes `Expr.eval`

`Expr.eval` is replaced by the machine in compiled code (`@[csimp]`). -/

/-- A recursive join point run by the machine: `runLoop` over the steps of its body computes
`joinFn` (given that the machine computes the body). -/
theorem joinFn_eq_runLoop {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    {s : Ty} {P : Env Γ → s.denote → Prop} {R : Env Γ → s.denote → s.denote → Prop}
    (wf : ∀ e, WellFounded (R e))
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
        (fun e r => Q e.2 r)))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e)
    (ihb : ∀ {x : s.denote} {hx : G e ∧ P e x} je',
      (body.eval ge (x, e) hx (Handler.push h) je').1 =
        (body.evalS ge (x, e) hx (Handler.push h)).run (Handler.push h) je')
    (v : s.denote) (hv : P e v) :
    (joinFn ge wf body e g h je v hv).1 =
      (@runLoop _ _ ⟨R e, wf e⟩ (P e)
        (fun x hx => loopStep (body.evalS ge (x, e) ⟨g, hx⟩ (Handler.push h))) v hv).run h je := by
  induction v using (wf e).induction with
  | _ v IH =>
    rw [joinFn_eq, @runLoop_eq _ _ ⟨R e, wf e⟩, ihb]
    generalize body.evalS ge (v, e) ⟨g, hv⟩ (Handler.push h) = st
    cases st with
    | val r => rfl
    | jmp i y hy =>
      cases i with
      | here => exact IH y hy.2 hy.1
      | there i => cases i; rfl
    | call c => exact (TailCall.unpush_run c h).symm

/-- **The jump machine agrees with the evaluator:** the value computed by `Expr.eval` is the
step of `Expr.evalS`, where a pending jump is run by the closure of its join point, and a
pending tail call by the handler of recursive calls. -/
theorem Expr.eval_val_eq_evalS {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (x : Expr GL Γ G sf t Q js) (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    (x.eval ge e g h je).1 = (x.evalS ge e g h).run h je := by
  induction x with
  | ret p hp post => rfl
  | ite c hc a b iha ihb =>
    simp only [Expr.eval, Expr.evalS]
    split
    · exact iha _ _ _ _
    · exact ihb _ _ _ _
  | fixSelfCall args ha dec hpre k ih =>
    simp only [Expr.eval, Expr.evalS]
    split
    · next heq hk => exact Expr.retHere?_eval ge k heq hk _ _ _ _
    · exact (ih _ _ _ _).trans (Step.unwk_run (sf := some _) _ h je).symm
  | gCall i args ha hpre k ih =>
    simp only [Expr.eval, Expr.evalS, Step.unwk_run]
    exact ih _ _ _ _
  | map s u l hl body k ihb ihk =>
    simp only [Expr.eval, Expr.evalS, Step.unwk_run]
    rw [List.map_congr_left (fun x _ => ihb _ _ _ _)]
    exact ihk _ _ _ _
  | foldl s u l hl init hi body k ihb ihk =>
    simp only [Expr.eval, Expr.evalS, Step.unwk_run]
    have hf : (fun acc (x : {x // x ∈ l.eval e}) =>
        (body.eval ge (acc, x.1, e) ⟨g, x.2⟩ (Handler.push (Handler.push h)) ()).1) =
        (fun acc x => (body.evalS ge (acc, x.1, e) ⟨g, x.2⟩ (Handler.push (Handler.push h))).run
          (Handler.push (Handler.push h)) ()) := by
      funext acc x; exact ihb _ _ _ _
    rw [hf]
    exact ihk _ _ _ _
  | join s P body m ihb ihm =>
    simp only [Expr.eval, Expr.evalS]
    rw [ihm]
    generalize evalS ge m e g h = st
    cases st with
    | val r => rfl
    | jmp i v hv =>
      cases i with
      | here => exact (ihb _ _ _ _).trans (Step.unwk_run _ _ _).symm
      | there i => rfl
    | call c => rfl
  | joinrec s P R wf body m ihb ihm =>
    rw [eval_joinrec, ihm]
    simp only [Expr.evalS]
    generalize evalS ge m e g h = st
    cases st with
    | val r => rfl
    | jmp i v hv =>
      cases i with
      | there i => rfl
      | here => exact joinFn_eq_runLoop ge wf body e g h je (fun je' => ihb _ _ _ je') v hv
    | call c => rfl
  | jump i p hp hpre hpost => rfl

/-- `Expr.eval` computed by the jump machine (the proof component is erased at runtime). -/
def Expr.evalImpl {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (x : Expr GL Γ G sf t Q js) (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    {v : t.denote // Q e v} :=
  ⟨(x.evalS ge e g h).run h je, x.eval_val_eq_evalS ge e g h je ▸ (x.eval ge e g h je).2⟩

/-- Compiled code runs `Expr.eval` with the jump machine. -/
@[csimp] theorem Expr.eval_eq_evalImpl : @Expr.eval = @Expr.evalImpl := by
  funext GL ge Γ G sf t Q js x e g h je
  exact Subtype.ext (x.eval_val_eq_evalS ge e g h je)

end WFLang.PCL
