import RequestProject.WFLang.Core.PExpr

/-!
# Language `PCL`: well-founded recursion as a construct of the grammar (proof-carrying calls)

The grammar has three layers:

```
PExpr   ::= x | lit | op PExpr PExpr | !PExpr | if PExpr then PExpr else PExpr
                                             -- call-free, total values   (Core/PExpr.lean)
Expr    ::= ret PExpr                        -- tail statements           (this file)
          | if PExpr then Expr else Expr
          | let v := self args in Expr       -- fixSelfCall
          | let v := f args in Expr          -- fnCall
          | letrec f := fix self xs. Expr in Expr     -- fix
          | join j (v) := Expr in Expr       -- join
          | jump j PExpr                     -- jump
```

In this language well-founded recursion is a constructor of `Expr` itself:

```
| fix params r R wf pre post body rest  -- letrec f := (fix self params. body) in rest
| fnCall f args hpre k                  -- let v := f args in k    (f a local function in scope)
| fixSelfCall args dec hpre k           -- let v := self args in k (inside a fix body)
```

* `fix` defines a local recursive function and scopes it over the rest of the statement: like
  `ite`, it only occurs in **tail position**.  It carries the relation `R` and
  `wf : WellFounded R` (a `Prop`), a *precondition* `pre` on its parameters and a
  *postcondition* `post` relating its parameters and its result.  Most functions have
  `pre = True` and `post = True`.  A precondition is what a Lean function with a proof parameter
  (`def f (n : Nat) (h : P n)`) needs; a postcondition is what a Lean function with a subtype
  result (`def f (n : Nat) : {r // Q n r}`) provides, and what its termination proofs may use
  about the results of its recursive calls.
* The local functions in scope are the index `fns` of `Expr` (typed de Bruijn indices
  `FnVar`); they are called by `fnCall`, which binds the result (with its postcondition) to a new
  variable.  A local function is complete when it is called, so `fnCall` needs no decrease
  proof, only the precondition of the arguments.  Bodies of `fix` nodes may call the local
  functions defined before them.
* Inside a `fix` body, the function being defined is called by `fixSelfCall`, which carries its
  **own** decrease proof `dec`, stating that the argument tuple is `R`-smaller than the current
  parameters *whenever the call is reached*.  "Whenever the call is reached" is expressed by the
  index `G : Env Γ → Prop` of `Expr`: the path condition, strengthened by each `ite` branch, by
  the precondition of the enclosing function and by the postconditions of the calls already
  made.  Each call also proves the precondition of its arguments (`hpre`).
* Every statement also carries the postcondition `Q : Env Γ → t.denote → Prop` it must
  establish: each `ret` proves it from its path condition.
* **Join points** (`join`/`jump`, the index `js` of `Expr`): `join j (v : s) := k in m` names
  the continuation `k` (the rest of the computation, with a hole `v`), and `m` ends, in each of
  its tail positions, either normally or with `jump j p`, which runs `k` with `v := p`.  A join
  point is not a function: it is not recursive, it is only used in tail position, and it is
  not visible inside the bodies of `fix` nodes (it would escape its function).  Its parameter
  may carry a precondition `P`, which each jump proves and the body `k` may use.
* Expressions are in **strict A-normal form**: arithmetic, comparisons, `bool_eq`, `&&`,
  `||`, `!` are in the call-free `PExpr` layer (`Core/PExpr.lean`); the result of every call
  (`fnCall`, `fixSelfCall`) is bound to a new variable; and the compound statements, `ite`
  (case), `fix` (local recursive functions, i.e. loops and folds) and `join`, occur only in tail
  position: the rest of the computation is inside their branches, resp. their scope.  A Lean
  `if`/`match` containing a call in non-tail position is captured as
  `join j (v) := ⟦rest⟧ in if c then (…; jump j a) else (…; jump j b)`, so the rest of the
  computation is written once (without join points it would have to be copied into both
  branches, which is exponential in the number of such `if`s).  A call of a recursive
  function (or a loop) in non-tail position is captured as `fix f := … in let v := f args in k`.

The path condition and the decrease proofs only mention `PExpr.eval`, which is defined
before `Expr`, so no induction–recursion is needed.  All proofs are `Prop`s and are erased by
code generation: the evaluator never checks anything at runtime and has no fuel.
-/

namespace WFLang.PCL

/-! ## Local functions -/

/-- The signature of a local recursive function: parameters, result type, precondition and
postcondition. -/
structure Fn where
  params : List Ty
  ret : Ty
  pre : Env params → Prop
  post : Env params → ret.denote → Prop

/-- The meaning of a local function: defined on the arguments satisfying its precondition,
with results satisfying its postcondition. -/
abbrev FnVal (f : Fn) : Type := (x : Env f.params) → f.pre x → {v : f.ret.denote // f.post x v}

/-- Typed de Bruijn indices of local functions. -/
inductive FnVar : List Fn → Fn → Type where
  | here {fs : List Fn} {f : Fn} : FnVar (f :: fs) f
  | there {fs : List Fn} {f g : Fn} : FnVar fs f → FnVar (g :: fs) f

/-- Values of the local functions in scope. -/
def FEnv : List Fn → Type
  | [] => Unit
  | f :: fs => FnVal f × FEnv fs

/-- Lookup of a local function. -/
def FnVar.get : {fs : List Fn} → {f : Fn} → FnVar fs f → FEnv fs → FnVal f
  | _ :: _, _, .here, fe => fe.1
  | _ :: _, _, .there i, fe => i.get fe.2

/-! ## Join points -/

/-- The join points in scope in context `Γ`, for statements of result type `t`.  `bind js s P Q`
adds a join point defined in the current context, with a parameter of type `s` satisfying `P`,
that establishes the postcondition `Q`; `wk js s` is the scope `js` seen under one more local
variable of type `s` (weakening is a constructor, so that it costs nothing at runtime and
computes by simplification). -/
inductive JScope : List Ty → Ty → Type where
  | nil {Γ : List Ty} {t : Ty} : JScope Γ t
  | bind {Γ : List Ty} {t : Ty} (js : JScope Γ t) (s : Ty) (P : Env Γ → s.denote → Prop)
      (Q : Env Γ → t.denote → Prop) : JScope Γ t
  | wk {Γ : List Ty} {t : Ty} (js : JScope Γ t) (s : Ty) : JScope (s :: Γ) t

/-- Typed de Bruijn indices of join points. -/
inductive JVar : {Γ : List Ty} → {t : Ty} → JScope Γ t → Type where
  | here {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} {P : Env Γ → s.denote → Prop}
      {Q : Env Γ → t.denote → Prop} : JVar (.bind js s P Q)
  | there {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} {P : Env Γ → s.denote → Prop}
      {Q : Env Γ → t.denote → Prop} : JVar js → JVar (.bind js s P Q)
  | wk {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} : JVar js → JVar (.wk js s)

/-- The parameter type of a join point. -/
def JVar.arg : {Γ : List Ty} → {t : Ty} → {js : JScope Γ t} → JVar js → Ty
  | _, _, .bind _ s _ _, .here => s
  | _, _, .bind _ _ _ _, .there i => i.arg
  | _, _, .wk _ _, .wk i => i.arg

/-- The precondition of a join point, read at the current environment. -/
def JVar.pre : {Γ : List Ty} → {t : Ty} → {js : JScope Γ t} → (i : JVar js) → Env Γ →
    i.arg.denote → Prop
  | _, _, .bind _ _ P _, .here, e => P e
  | _, _, .bind _ _ _ _, .there i, e => i.pre e
  | _, _, .wk _ _, .wk i, e => i.pre e.2

/-- The postcondition established by a join point, read at the current environment. -/
def JVar.post : {Γ : List Ty} → {t : Ty} → {js : JScope Γ t} → (i : JVar js) → Env Γ →
    t.denote → Prop
  | _, _, .bind _ _ _ Q, .here, e => Q e
  | _, _, .bind _ _ _ _, .there i, e => i.post e
  | _, _, .wk _ _, .wk i, e => i.post e.2

/-- Values of the join points in scope at the environment `e`: the closures of their bodies. -/
def JEnv : {Γ : List Ty} → {t : Ty} → JScope Γ t → Env Γ → Type
  | _, _, .nil, _ => Unit
  | _, t, .bind js s P Q, e => ((v : s.denote) → P e v → {r : t.denote // Q e r}) × JEnv js e
  | _, _, .wk js _, e => JEnv js e.2

/-- Lookup of a join point. -/
def JVar.get : {Γ : List Ty} → {t : Ty} → {js : JScope Γ t} → (i : JVar js) → {e : Env Γ} →
    JEnv js e → (v : i.arg.denote) → i.pre e v → {r : t.denote // i.post e r}
  | _, _, .bind _ _ _ _, .here, _, je => je.1
  | _, _, .bind _ _ _ _, .there i, _, je => i.get je.2
  | _, _, .wk _ _, .wk i, _, je => i.get je

/-! ## Statements -/

/-- The innermost enclosing recursive function: its parameters, result type, well-founded
relation, precondition, postcondition, and how to read its current parameters from the
environment. -/
structure Self (Γ : List Ty) where
  params : List Ty
  ret : Ty
  R : Env params → Env params → Prop
  pre : Env params → Prop
  post : Env params → ret.denote → Prop
  cur : Env Γ → Env params

/-- The same function, seen under one more local variable. -/
def Self.push {Γ : List Ty} (sf : Self Γ) (t : Ty) : Self (t :: Γ) :=
  { sf with cur := fun e => sf.cur e.2 }

/-- The function whose body is being defined: its parameters are the whole context. -/
def Self.top (params : List Ty) (r : Ty) (R : Env params → Env params → Prop)
    (pre : Env params → Prop) (post : Env params → r.denote → Prop) : Self params :=
  { params := params, ret := r, R := R, pre := pre, post := post, cur := id }

/-- Statements of result type `t` in context `Γ`, reached under the path condition `G`, with
the local functions `fns` in scope, inside the recursive function `sf` (if any), establishing
the postcondition `Q`, with the join points `js` in scope. -/
inductive Expr : (Γ : List Ty) → (Env Γ → Prop) → List Fn → Option (Self Γ) → (t : Ty) →
    (Env Γ → t.denote → Prop) → JScope Γ t → Type where
  /-- Return a call-free value, which satisfies the postcondition. -/
  | ret {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (p : PExpr Γ t) (post : ∀ e, G e → Q e (p.eval e)) : Expr Γ G fns sf t Q js
  /-- `if c then a else b`, in tail position; each branch knows the outcome of the test. -/
  | ite {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (c : PExpr Γ .bool)
      (a : Expr Γ (fun e => G e ∧ c.eval e = true) fns sf t Q js)
      (b : Expr Γ (fun e => G e ∧ c.eval e = false) fns sf t Q js) : Expr Γ G fns sf t Q js
  /-- `let v := self args in k`, with the proofs that the call goes down and that the
  arguments satisfy the precondition; `k` may use the postcondition of `v`. -/
  | fixSelfCall {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Self Γ} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (args : PExprs Γ sf.params)
      (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
      (hpre : ∀ e, G e → sf.pre (args.eval e))
      (k : Expr (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1) fns
        (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret)) :
      Expr Γ G fns (some sf) t Q js
  /-- `let v := f args in k`, for a local function `f` in scope, with the proof that the
  arguments satisfy its precondition; `k` may use the postcondition of `v`. -/
  | fnCall {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} {f : Fn}
      (i : FnVar fns f) (args : PExprs Γ f.params)
      (hpre : ∀ e, G e → f.pre (args.eval e))
      (k : Expr (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1) fns
        (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret)) :
      Expr Γ G fns sf t Q js
  /-- `letrec f := (fix self params. body) in rest`, in tail position: a local well-founded
  recursive function with relation `R` (proved well-founded by `wf`), precondition `pre` and
  postcondition `post`, in scope in `rest`.  Its body may call the local functions `fns`
  defined before it, but not jump to the join points in scope. -/
  | fix {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) (wf : WellFounded R)
      (pre : Env params → Prop) (post : Env params → r.denote → Prop)
      (body : Expr params pre fns (some (Self.top params r R pre post)) r post .nil)
      (rest : Expr Γ G (⟨params, r, pre, post⟩ :: fns) sf t Q js) : Expr Γ G fns sf t Q js
  /-- `join j (v : s) := body in m`, in tail position: the join point `j` (whose parameter
  satisfies `P`) is in scope in `m`.  Its body runs in the current context extended by `v`,
  under the current path condition and `P`; it may jump to the join points defined before. -/
  | join {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (s : Ty) (P : Env Γ → s.denote → Prop)
      (body : Expr (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) fns (sf.map (·.push s)) t
        (fun e r => Q e.2 r) (.wk js s))
      (m : Expr Γ G fns sf t Q (.bind js s P Q)) : Expr Γ G fns sf t Q js
  /-- `jump j p`, in tail position: run the join point `j` on `p`, with the proof that `p`
  satisfies its precondition; its result satisfies the current postcondition. -/
  | jump {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (i : JVar js) (p : PExpr Γ i.arg)
      (hpre : ∀ e, G e → i.pre e (p.eval e))
      (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r) : Expr Γ G fns sf t Q js

/-! ## The evaluator -/

/-- What a statement may use to perform a recursive call: a function defined on the
arguments that are `R`-below the current parameters and satisfy the precondition, returning
a result that satisfies the postcondition. -/
def Handler {Γ : List Ty} : Option (Self Γ) → Env Γ → Type
  | none, _ => Unit
  | some sf, e => (y : Env sf.params) → sf.R y (sf.cur e) → sf.pre y →
      {v : sf.ret.denote // sf.post y v}

/-- Moving a handler under a new local variable. -/
def Handler.push {Γ : List Ty} {r : Ty} {v : r.denote} {e : Env Γ} :
    {sf : Option (Self Γ)} → Handler sf e → Handler (sf.map (·.push r)) ((v, e) : Env (r :: Γ))
  | none, h => h
  | some _, h => h

/-- The evaluator: structural recursion on the syntax; a `fix` node is run by
`WellFounded.fix` on its own relation, and a `join` node passes the closure of its body to its
scope.  No fuel, no runtime checks: the proofs (path conditions, pre- and postconditions) are
erased by code generation. -/
def Expr.eval : {Γ : List Ty} → {G : Env Γ → Prop} → {fns : List Fn} → {sf : Option (Self Γ)} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr Γ G fns sf t Q js → (e : Env Γ) → G e → FEnv fns → Handler sf e → JEnv js e →
    {v : t.denote // Q e v}
  | _, _, _, _, _, _, _, .ret p post, e, g, _, _, _ => ⟨p.eval e, post e g⟩
  | _, _, _, _, _, _, _, .ite c a b, e, g, fe, h, je =>
      if hc : c.eval e = true then a.eval e ⟨g, hc⟩ fe h je
      else b.eval e ⟨g, Bool.eq_false_iff.mpr hc⟩ fe h je
  | _, _, _, _, _, _, _, .fixSelfCall args dec hpre k, e, g, fe, h, je =>
      let v := h (args.eval e) (dec e g) (hpre e g)
      let r := k.eval (v.1, e) ⟨g, v.2⟩ fe h je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, _, .fnCall i args hpre k, e, g, fe, h, je =>
      let v := i.get fe (args.eval e) (hpre e g)
      let r := k.eval (v.1, e) ⟨g, v.2⟩ fe (Handler.push h) je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, _, .fix _ _ _ wf pre post body rest, e, g, fe, h, je =>
      let F : (x : _) → pre x → {v // post x v} := wf.fix (C := fun x => pre x → {v // post x v})
        (fun x ih hx => body.eval x hx fe (fun y hy hpy => ih y hy hpy) ())
      rest.eval e g (F, fe) h je
  | _, _, _, _, _, _, _, .join _ _ body m, e, g, fe, h, je =>
      m.eval e g fe h
        ((fun v hv => body.eval (v, e) ⟨g, hv⟩ fe (Handler.push h) je), je)
  | _, _, _, _, _, _, _, .jump i p hpre hpost, e, g, _, _, je =>
      let r := i.get je (p.eval e) (hpre e g)
      ⟨r.1, hpost e g r.1 r.2⟩

/-- Closed programs of signature `s` with precondition `pre` and postcondition `post`:
statements over the parameters, outside any recursive function, with no local function and no
join point in scope. -/
abbrev PTerm (s : Sig) (pre : Env s.args → Prop) (post : Env s.args → s.ret.denote → Prop) :=
  Expr s.args pre [] none s.ret post .nil

/-- Run a program on arguments satisfying its precondition. -/
def PTerm.run {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) (x : Env s.args) (h : pre x) : s.ret.denote :=
  (t.eval x h () () ()).1

/-- **The result of a program satisfies its postcondition** (for free: it is part of the
typing of the program). -/
theorem PTerm.run_post {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop} (t : PTerm s pre post) (x : Env s.args)
    (h : pre x) : post x (t.run x h) := (t.eval x h () () ()).2

/-- Closed programs without precondition (the usual case), and by default without
postcondition. -/
abbrev Term (s : Sig) (post : Env s.args → s.ret.denote → Prop := fun _ _ => True) :=
  PTerm s (fun _ => True) post

def Term.run {s : Sig} {post : Env s.args → s.ret.denote → Prop} (t : Term s post)
    (x : Env s.args) : s.ret.denote := PTerm.run t x trivial

/-- Curried evaluator: `Term.eval gcd_term m n`. -/
def Term.eval {s : Sig} {post : Env s.args → s.ret.denote → Prop} (t : Term s post) :
    FnType s.args s.ret := curryEnv t.run

/-! ## Soundness of `fix` -/

section
variable {params : List Ty} {r : Ty} {R : Env params → Env params → Prop} (wf : WellFounded R)
  {pre : Env params → Prop} {post : Env params → r.denote → Prop} {fns : List Fn}
  (body : Expr params pre fns (some (Self.top params r R pre post)) r post .nil) (fe : FEnv fns)

/-- The function denoted by a `fix` node (given the values `fe` of the local functions in
scope). -/
def fixFn : (x : Env params) → pre x → {v : r.denote // post x v} :=
  wf.fix (C := fun x => pre x → {v // post x v})
    (fun x ih hx => body.eval x hx fe (fun y hy hpy => ih y hy hpy) ())

/-- **Soundness (1):** the function defined by a `fix` node satisfies its recursive equation. -/
theorem fixFn_eq (x : Env params) (hx : pre x) :
    fixFn wf body fe x hx = body.eval x hx fe (fun y _ hy => fixFn wf body fe y hy) () := by
  unfold fixFn
  rw [WellFounded.fix_eq]

/-- **Soundness (2):** its values are the only solution of that equation. -/
theorem fixFn_unique (F : (x : Env params) → pre x → {v : r.denote // post x v})
    (hF : ∀ x hx, (F x hx).1 = (body.eval x hx fe (fun y _ hy => F y hy) ()).1) :
    ∀ x hx, (fixFn wf body fe x hx).1 = (F x hx).1 := by
  intro x
  induction x using wf.induction with
  | _ x IH =>
    intro hx
    rw [fixFn_eq, hF x hx]
    have : (fun y (_ : R y x) hy => fixFn wf body fe y hy) = (fun y _ hy => F y hy) := by
      funext y hy hpy; exact Subtype.ext (IH y hy hpy)
    exact congrArg (fun h => (body.eval x hx fe h ()).1) this

end

@[simp] theorem eval_fix {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) (wf : WellFounded R)
    (pre : Env params → Prop) (post : Env params → r.denote → Prop)
    (body : Expr params pre fns (some (Self.top params r R pre post)) r post .nil)
    (rest : Expr Γ G (⟨params, r, pre, post⟩ :: fns) sf t Q js)
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.fix params r R wf pre post body rest).eval e g fe h je).1 =
      (rest.eval e g (fixFn wf body fe, fe) h je).1 := rfl

/-! ## Programs made of one recursive function -/

/-- The program `fix f := (fix self xs. body) in f xs` produced by the capture macro. -/
def PTerm.ofFix {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr s.args pre [] (some (Self.top s.args s.ret R pre post)) s.ret post .nil) :
    PTerm s pre post :=
  Expr.fix s.args s.ret R wf pre post body
    (.fnCall .here (PExprs.ids s.args) (fun e g => by rw [PExprs.ids_eval]; exact g)
      (.ret (.var .here) (fun e g => by have h := g.2; rw [PExprs.ids_eval] at h; exact h)))

/-- Agreement for a program `PTerm.ofFix R wf body`: it computes any function `F` (defined on
the arguments satisfying the precondition, with results satisfying the postcondition) that
satisfies the recursive equation of `body`. -/
theorem PTerm.ofFix_run {s : Sig} {pre : Env s.args → Prop}
    {post : Env s.args → s.ret.denote → Prop}
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr s.args pre [] (some (Self.top s.args s.ret R pre post)) s.ret post .nil)
    (F : (x : Env s.args) → pre x → {v : s.ret.denote // post x v})
    (hF : ∀ x hx, (F x hx).1 = (body.eval x hx () (fun y _ hy => F y hy) ()).1) :
    ∀ x hx, (PTerm.ofFix R wf body).run x hx = (F x hx).1 := by
  intro x hx
  show (fixFn wf body () ((PExprs.ids s.args).eval x) _).1 = _
  have key : ∀ y (hy : pre y), y = x → (fixFn wf body () y hy).1 = (F x hx).1 := by
    intro y hy e; subst e; exact fixFn_unique wf body () F hF y hy
  exact key _ _ (PExprs.ids_eval _ _)

/-- The special case of a program without precondition and postcondition that computes a
curried Lean function `f`. -/
theorem Term.ofFix_eval {s : Sig} (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr s.args (fun _ => True) []
      (some (Self.top s.args s.ret R (fun _ => True) (fun _ _ => True))) s.ret (fun _ _ => True)
      .nil)
    (f : FnType s.args s.ret)
    (hf : ∀ x, uncurryEnv f x =
      (body.eval x trivial () (fun y _ _ => ⟨uncurryEnv f y, trivial⟩) ()).1) :
    Term.eval (PTerm.ofFix R wf body : Term s) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  exact PTerm.ofFix_run R wf body (fun y _ => ⟨uncurryEnv f y, trivial⟩) (fun y _ => hf y) x trivial

/-- The special case of a program without precondition, with a postcondition, that computes
the values of a curried Lean function `f` (e.g. `Subtype.val ∘ g` for a function `g` with a
subtype result), provided `f` satisfies the postcondition. -/
theorem Term.ofFix_eval_post {s : Sig} {post : Env s.args → s.ret.denote → Prop}
    (R : Env s.args → Env s.args → Prop) (wf : WellFounded R)
    (body : Expr s.args (fun _ => True) []
      (some (Self.top s.args s.ret R (fun _ => True) post)) s.ret post .nil)
    (f : FnType s.args s.ret) (hpost : ∀ x, post x (uncurryEnv f x))
    (hf : ∀ x, uncurryEnv f x =
      (body.eval x trivial () (fun y _ _ => ⟨uncurryEnv f y, hpost y⟩) ()).1) :
    Term.eval (PTerm.ofFix R wf body : Term s post) = f := by
  refine curryEnv_eq _ _ fun x => ?_
  exact PTerm.ofFix_run R wf body (fun y _ => ⟨uncurryEnv f y, hpost y⟩) (fun y _ => hf y)
    x trivial

/-! ## Simplification lemmas used by the capture tactics -/

@[simp] theorem eval_ret {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} (p : PExpr Γ t)
    (post : ∀ e, G e → Q e (p.eval e))
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ret (fns := fns) (sf := sf) (js := js) p post).eval e g fe h je).1 = p.eval e := rfl

@[simp] theorem eval_ite {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (c : PExpr Γ .bool) (a : Expr Γ (fun e => G e ∧ c.eval e = true) fns sf t Q js)
    (b : Expr Γ (fun e => G e ∧ c.eval e = false) fns sf t Q js) (e : Env Γ) (g : G e)
    (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ite c a b).eval e g fe h je).1 =
      if hc : c.eval e = true then (a.eval e ⟨g, hc⟩ fe h je).1
      else (b.eval e ⟨g, Bool.eq_false_iff.mpr hc⟩ fe h je).1 := by
  simp only [Expr.eval]; split <;> rfl

@[simp] theorem eval_fixSelfCall {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn} {sf : Self Γ}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (args : PExprs Γ sf.params) (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
    (hpre : ∀ e, G e → sf.pre (args.eval e))
    (k : Expr (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1) fns
      (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret))
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler (some sf) e) (je : JEnv js e) :
    ((Expr.fixSelfCall args dec hpre k).eval e g fe h je).1 =
      (k.eval ((h (args.eval e) (dec e g) (hpre e g)).1, e)
        ⟨g, (h (args.eval e) (dec e g) (hpre e g)).2⟩ fe h je).1 := rfl

theorem eval_fnCall {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} {f : Fn}
    (i : FnVar fns f) (args : PExprs Γ f.params) (hpre : ∀ e, G e → f.pre (args.eval e))
    (k : Expr (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1) fns
      (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret))
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.fnCall i args hpre k).eval e g fe h je).1 =
      (k.eval ((i.get fe (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get fe (args.eval e) (hpre e g)).2⟩ fe (Handler.push h) je).1 := rfl

@[simp] theorem FnVar.get_here {fs : List Fn} {f : Fn} (v : FnVal f) (fe : FEnv fs) :
    (FnVar.here : FnVar (f :: fs) f).get (v, fe) = v := rfl

@[simp] theorem FnVar.get_there {fs : List Fn} {f g : Fn} (i : FnVar fs f) (v : FnVal g)
    (fe : FEnv fs) : (FnVar.there i : FnVar (g :: fs) f).get (v, fe) = i.get fe := rfl

/-- `eval_fnCall` for a call of the innermost local function (the only form produced by the
capture: `fix … (fnCall here …)`). -/
@[simp] theorem eval_fnCall_here {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} {f : Fn}
    (args : PExprs Γ f.params) (hpre : ∀ e, G e → f.pre (args.eval e))
    (k : Expr (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1) (f :: fns)
      (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret))
    (e : Env Γ) (g : G e) (v : FnVal f) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.fnCall FnVar.here args hpre k).eval e g (v, fe) h je).1 =
      (k.eval ((v (args.eval e) (hpre e g)).1, e)
        ⟨g, (v (args.eval e) (hpre e g)).2⟩ (v, fe) (Handler.push h) je).1 := rfl

/-- A `join` node runs its scope, with the closure of its body as the value of the new join
point. -/
@[simp] theorem eval_join {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (P : Env Γ → s.denote → Prop)
    (body : Expr (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) fns (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.wk js s))
    (m : Expr Γ G fns sf t Q (.bind js s P Q))
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.join s P body m).eval e g fe h je).1 =
      (m.eval e g fe h
        ((fun v hv => body.eval (v, e) ⟨g, hv⟩ fe (Handler.push h) je), je)).1 :=
  rfl

/-- A `jump` runs the join point. -/
@[simp] theorem eval_jump {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (i : JVar js) (p : PExpr Γ i.arg)
    (hpre : ∀ e, G e → i.pre e (p.eval e))
    (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r)
    (e : Env Γ) (g : G e) (fe : FEnv fns) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.jump i p hpre hpost).eval e g fe h je).1 = (i.get je (p.eval e) (hpre e g)).1 := rfl

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
