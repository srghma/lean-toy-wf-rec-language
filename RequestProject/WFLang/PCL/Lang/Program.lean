import RequestProject.WFLang.PCL.Lang.While

/-!
# Language `PCL`: programs

The global context (`Globals`), programs (`PTerm`, `Term`, `Term.eval`), programs made of one
recursive function (`PTerm.ofFix`, `Term.ofFix_eval`), and tuples (`tupleTy`, `toEnv`).
-/

namespace WFLang.PCL

/-! ## The global context -/

/-- The **global context** of a program: a list of global function definitions, each of
which may call the ones defined before it.  A global function is a closed well-founded
recursive function (relation `R`, proof `wf`, body `body`); a non-recursive one has the empty
relation `emptyRelation`, well-founded by `emptyWf.wf` (its body makes no recursive call). -/
inductive Globals : List Fn → Type where
  | nil : Globals []
  | defn {GL : List Fn} (gs : Globals GL) (f : Fn) (R : Env f.params → Env f.params → Prop)
      (wf : WellFounded R)
      (body : Expr GL f.params f.pre (some (Self.top f.params f.ret R f.pre f.post)) f.ret
        f.post .nil) : Globals (f :: GL)

/-- The values of the global functions. -/
def Globals.env : {GL : List Fn} → Globals GL → FEnv GL
  | _, .nil => ()
  | _, .defn gs _ _ wf body => (fixFn gs.env wf body, gs.env)

/-- The number of global functions. -/
def Globals.size : {GL : List Fn} → Globals GL → Nat
  | _, .nil => 0
  | _, .defn gs _ _ _ _ => gs.size + 1

/-! ## Programs -/

/-- Closed programs of signature `s` with precondition `pre` and postcondition `post`: a
global context `globals`, and the main statement over the parameters, outside any recursive
function, with no join point in scope. -/
structure PTerm (s : Sig) (pre : Env s.args → Prop) (post : Env s.args → s.ret.denote → Prop)
    where
  /-- the signatures of the global functions -/
  {GL : List Fn}
  /-- the global functions -/
  globals : Globals GL
  /-- the main statement -/
  main : Expr GL s.args pre none s.ret post .nil

/-- Run a program on arguments satisfying its precondition. -/
def PTerm.run {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) (x : Env s.args) (h : pre x) : s.ret.denote :=
  (t.main.eval t.globals.env x h () ()).1

/-- **The result of a program satisfies its postcondition** (for free: it is part of the
typing of the program). -/
theorem PTerm.run_post {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop} (t : PTerm s pre post) (x : Env s.args)
    (h : pre x) : post x (t.run x h) := (t.main.eval t.globals.env x h () ()).2

/-- Closed programs without precondition (the usual case), and by default without
postcondition. -/
abbrev Term (s : Sig) (post : Env s.args → s.ret.denote → Prop := fun _ _ => True) :=
  PTerm s (fun _ => True) post

def Term.run {s : Sig} {post : Env s.args → s.ret.denote → Prop} (t : Term s post)
    (x : Env s.args) : s.ret.denote := PTerm.run t x trivial

/-- Curried evaluator: `Term.eval gcd_term m n`. -/
def Term.eval {s : Sig} {post : Env s.args → s.ret.denote → Prop} (t : Term s post) :
    FnType s.args s.ret := curryEnv t.run

/-! ## Programs made of one recursive function -/

/-- The main statement `let v := f xs in v` calling the last global function `f` on the
parameters. -/
def Expr.callTop {GL : List Fn} {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop} :
    Expr (⟨s.args, s.ret, pre, post⟩ :: GL) s.args pre none s.ret post .nil :=
  .gCall .here (PExprs.ids s.args) (PExprs.ids_isNF _)
    (fun e g => by rw [PExprs.ids_eval]; exact g)
    (.ret (.var .here) rfl (fun e g => by have h := g.2; rw [PExprs.ids_eval] at h; exact h))

/-- The program whose global context is `gs` followed by the recursive function
`fix self xs. body`, and whose main statement calls that function on the parameters. -/
def PTerm.ofFix {GL : List Fn} {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop} (gs : Globals GL)
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr GL s.args pre (some (Self.top s.args s.ret R pre post)) s.ret post .nil) :
    PTerm s pre post :=
  ⟨Globals.defn gs ⟨s.args, s.ret, pre, post⟩ R wf body, Expr.callTop⟩

/-- Agreement for a program `PTerm.ofFix gs R wf body`: it computes any function `F` (defined
on the arguments satisfying the precondition, with results satisfying the postcondition) that
satisfies the recursive equation of `body`. -/
theorem PTerm.ofFix_run {GL : List Fn} {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop} (gs : Globals GL)
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr GL s.args pre (some (Self.top s.args s.ret R pre post)) s.ret post .nil)
    (F : (x : Env s.args) → pre x → {v : s.ret.denote // post x v})
    (hF : ∀ x hx, (F x hx).1 = (body.eval gs.env x hx (fun y _ hy => F y hy) ()).1) :
    ∀ x hx, (PTerm.ofFix gs R wf body).run x hx = (F x hx).1 := by
  intro x hx
  show (fixFn gs.env wf body ((PExprs.ids s.args).eval x) _).1 = _
  have key : ∀ y (hy : pre y), y = x → (fixFn gs.env wf body y hy).1 = (F x hx).1 := by
    intro y hy e; subst e; exact fixFn_unique gs.env wf body F hF y hy
  exact key _ _ (PExprs.ids_eval _ _)

/-- The special case of a program without precondition and postcondition that computes a
curried Lean function `f`. -/
theorem Term.ofFix_eval {GL : List Fn} {s : Sig} (gs : Globals GL)
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr GL s.args (fun _ => True)
      (some (Self.top s.args s.ret R (fun _ => True) (fun _ _ => True))) s.ret (fun _ _ => True)
      .nil)
    (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x =
      (body.eval gs.env x trivial (fun y _ _ => ⟨uncurryEnv f y, trivial⟩) ()).1) :
    Term.eval (PTerm.ofFix gs R wf body : Term s) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  exact PTerm.ofFix_run gs R wf body (fun y _ => ⟨uncurryEnv f y, trivial⟩) (fun y _ => hf y) x
    trivial

/-- The special case of a program without precondition, with a postcondition, that computes
the values of a curried Lean function `f` (e.g. `Subtype.val ∘ g` for a function `g` with a
subtype result), provided `f` satisfies the postcondition. -/
theorem Term.ofFix_eval_post {GL : List Fn} {s : Sig} {post : Env s.args → s.ret.denote → Prop}
    (gs : Globals GL) (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr GL s.args (fun _ => True)
      (some (Self.top s.args s.ret R (fun _ => True) post)) s.ret post .nil)
    (f : FnType s.args s.ret) (hpost : ∀ x, post x (uncurryEnv f x))
    (hf : ∀ x, uncurryEnv f x =
      (body.eval gs.env x trivial (fun y _ _ => ⟨uncurryEnv f y, hpost y⟩) ()).1) :
    Term.eval (PTerm.ofFix gs R wf body : Term s post) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  exact PTerm.ofFix_run gs R wf body (fun y _ => ⟨uncurryEnv f y, hpost y⟩) (fun y _ => hf y)
    x trivial

/-! ## Tuples: the parameter of a recursive join point capturing a function of several
parameters -/

/-- The object type of a tuple of values of types `ts` (right-nested pairs; the type itself
for one value). -/
@[reducible] def tupleTy : List Ty → Ty
  | [] => .bool
  | [t] => t
  | t :: ts => .prod t (tupleTy ts)

/-- A tuple, as an environment. -/
def toEnv : (ts : List Ty) → (tupleTy ts).denote → Env ts
  | [], _ => ()
  | [_], x => (x, ())
  | _ :: _ :: _, x => (x.1, toEnv _ x.2)

@[simp] theorem toEnv_nil (x : (tupleTy []).denote) : toEnv [] x = () := rfl
@[simp] theorem toEnv_one (t : Ty) (x : (tupleTy [t]).denote) : toEnv [t] x = (x, ()) := rfl
@[simp] theorem toEnv_cons (t u : Ty) (ts : List Ty) (x : (tupleTy (t :: u :: ts)).denote) :
    toEnv (t :: u :: ts) x = (x.1, toEnv (u :: ts) x.2) := rfl

end WFLang.PCL
