import RequestProject.WFLang.PCL.Lang.Machine

/-!
# Language `PCL`: global functions

The function denoted by the body of a global function (`fixFn`), its unfolding equation and
uniqueness; and `fixS`, which computes it with the jump machine (tail calls run as jumps).
`fixFn = fixFnImpl` is a `@[csimp]` lemma: compiled code runs global functions with `fixS`.
-/

namespace WFLang.PCL

/-! ## Soundness of global functions -/

section
variable {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
  {R : Env params → Env params → Prop} (wf : WellFounded R)
  {pre : Env params → Prop} {post : Env params → r.denote → Prop}
  (body : Expr GL params pre (some (Self.top params r R pre post)) r post .nil)

/-- The function denoted by the body of a global function (given the values `ge` of the global
functions before it). -/
def fixFn : (x : Env params) → pre x → {v : r.denote // post x v} :=
  wf.fix (C := fun x => pre x → {v // post x v})
    (fun x ih hx => body.eval ge x hx (fun y hy hpy => ih y hy hpy) ())

/-- **Soundness (1):** a global function satisfies its recursive equation. -/
theorem fixFn_eq (x : Env params) (hx : pre x) :
    fixFn ge wf body x hx =
      body.eval ge x hx (fun y _ hy => fixFn ge wf body y hy) () := by
  unfold fixFn
  rw [WellFounded.fix_eq]

/-- **Soundness (2):** its values are the only solution of that equation. -/
theorem fixFn_unique (F : (x : Env params) → pre x → {v : r.denote // post x v})
    (hF : ∀ x hx, (F x hx).1 = (body.eval ge x hx (fun y _ hy => F y hy) ()).1) :
    ∀ x hx, (fixFn ge wf body x hx).1 = (F x hx).1 := by
  intro x
  induction x using wf.induction with
  | _ x IH =>
    intro hx
    rw [fixFn_eq, hF x hx]
    have : (fun y (_ : R y x) hy => fixFn ge wf body y hy) = (fun y _ hy => F y hy) := by
      funext y hy hpy; exact Subtype.ext (IH y hy hpy)
    exact congrArg (fun h => (body.eval ge x hx h ()).1) this

end

/-! ## Global functions run by the jump machine

`fixS` computes `fixFn` with the machine: the body is run by `Expr.evalS`; a pending tail call
(`let v := self args in ret v`) is run by a tail call of `fixS` itself, which is compiled to a
jump, so tail-recursive global functions run in constant stack.  Other recursive calls go
through the handler, a closure calling `fixS`.  `fixS` carries its own specification (its value
is the value of `fixFn`), which provides the postconditions the handler needs.  The instance
argument is the well-founded relation of the function (`termination_by` uses it). -/

/-- A global function run by the jump machine (see above). -/
def fixS {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    [I : WellFoundedRelation (Env params)]
    {pre : Env params → Prop} {post : Env params → r.denote → Prop}
    (body : Expr GL params pre (some (Self.top params r I.rel pre post)) r post .nil)
    (x : Env params) (hx : pre x) : {v : r.denote // v = (fixFn ge I.wf body x hx).1} :=
  let H : Handler (some (Self.top params r I.rel pre post)) x := fun y _ hpy =>
    ⟨(fixS ge body y hpy).1, by rw [(fixS ge body y hpy).2]; exact (fixFn ge I.wf body y hpy).2⟩
  have hH : H = fun y _ hpy => fixFn ge I.wf body y hpy := by
    funext y hy hpy; exact Subtype.ext (fixS ge body y hpy).2
  have key : (fixFn ge I.wf body x hx).1 = (body.evalS ge x hx H).run H () := by
    rw [fixFn_eq, Expr.eval_val_eq_evalS, hH]
  match hst : body.evalS ge x hx H with
  | .val v => ⟨v, by rw [key, hst]; rfl⟩
  | .call c => ⟨(fixS ge body c.1 c.2.2.1).1, by
      rw [(fixS ge body c.1 c.2.2.1).2, key, hst, hH]; rfl⟩
termination_by x
decreasing_by
  all_goals first
    | assumption
    | exact (‹TailCall (some (Self.top params r I.rel pre post)) r x›).2.1

/-- `fixFn` computed by the jump machine (the proof component is erased at runtime). -/
def fixFnImpl {GL : List Fn} (ge : FEnv GL) {params : List Ty} {r : Ty}
    {R : Env params → Env params → Prop} (wf : WellFounded R)
    {pre : Env params → Prop} {post : Env params → r.denote → Prop}
    (body : Expr GL params pre (some (Self.top params r R pre post)) r post .nil)
    (x : Env params) (hx : pre x) : {v : r.denote // post x v} :=
  ⟨(@fixS GL ge params r ⟨R, wf⟩ pre post body x hx).1, by
    rw [(@fixS GL ge params r ⟨R, wf⟩ pre post body x hx).2]; exact (fixFn ge wf body x hx).2⟩

/-- Compiled code runs global functions with the jump machine. -/
@[csimp] theorem fixFn_eq_fixFnImpl : @fixFn = @fixFnImpl := by
  funext GL ge params r R wf pre post body x hx
  exact Subtype.ext (@fixS GL ge params r ⟨R, wf⟩ pre post body x hx).2.symm

end WFLang.PCL
