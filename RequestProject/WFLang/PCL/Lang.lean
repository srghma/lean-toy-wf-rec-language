import RequestProject.WFLang.Core.Normal
import RequestProject.WFLang.Core.While

/-!
# Language `PCL`: well-founded recursion as a construct of the grammar (proof-carrying calls)

The grammar has three layers:

```
PExpr   ::= x | lit | op PExpr PExpr | !PExpr | if PExpr then PExpr else PExpr
                                             -- call-free, total values   (Core/PExpr.lean)
Expr    ::= ret PExpr                        -- tail statements           (this file)
          | if PExpr then Expr else Expr
          | let v := self args in Expr       -- fixSelfCall
          | let v := g args in Expr          -- gCall   (g a global function)
          | join j (v) := Expr in Expr       -- join    (a non-recursive join point)
          | joinrec j (v) [R] := Expr in Expr  -- joinrec (a recursive join point: a loop)
          | jump j PExpr                     -- jump
Program ::= global functions (each: fix self xs. Expr) ; main Expr
```

There are exactly two kinds of named computations, and one kind of local recursion:

* **Global functions** (`Globals`, the parameter `GL` of `Expr`): closed well-founded recursive
  functions, each of which may call the global functions defined before it (`gCall`).  Inside
  its body, a global function calls *itself* by `fixSelfCall`, which carries its **own** decrease
  proof `dec`: the argument tuple is `R`-smaller than the current parameters *whenever the call
  is reached*.  "Whenever the call is reached" is the index `G : Env Γ → Prop` of `Expr`: the
  path condition, strengthened by each `ite` branch, by the precondition of the enclosing
  function and by the postconditions of the calls already made.  A global function carries a
  precondition `pre` (what a Lean function with a proof parameter needs) and a postcondition
  `post` (what a Lean function with a subtype result provides).  A call of a global function
  needs no decrease proof (the callee is complete), only the precondition of the arguments.
* **Join points** (`join`/`joinrec`/`jump`, the index `js` of `Expr`): `join j (v : s) := k in
  m` names the continuation `k` (the rest of the computation, with a hole `v`), and `m` ends, in
  each of its tail positions, either normally or with `jump j p`, which runs `k` with `v := p`.
  A join point lives *inside* the statement that defines it: its body sees the variables, the
  path condition, the enclosing recursive function and the outer join points of its definition
  site.  Its parameter may carry a precondition `P`, which each jump proves and the body may
  use.
* **Recursive join points** (`joinrec`): `joinrec j (x : s) [R, wf] := body in m` is a join point
  whose body may jump back to `j` itself.  Such a *back edge* must go down along the
  well-founded relation `R e` (which may depend on the environment `e` of the definition site):
  inside `body`, the precondition of `j` is `P ∧ R · x`, so every back jump carries its decrease
  proof, like a `fixSelfCall`.  From `m` (the entry), a jump only proves `P`.  A recursive join
  point is a **loop inside the enclosing statement**: tail-recursive helpers (`@[inlinable]`
  ones and specialised loops such as `for`) and well-founded `while` loops are captured as
  recursive join points, at their call sites, with the caller's variables in scope.  The
  well-founded `while` loop `Expr.whileLoop` is a derived form (a `join` for the exit, a
  `joinrec` for the loop).

There is no local function context: every local function of the earlier design is either a
global function (general recursion) or a recursive join point (tail recursion).

Expressions are in **strict A-normal form**: arithmetic, comparisons, `bool_eq`, `&&`, `||`, `!`
are in the call-free `PExpr` layer (`Core/PExpr.lean`); the result of every call (`gCall`,
`fixSelfCall`) is bound to a new variable; and the compound statements `ite`, `join`, `joinrec`
occur only in tail position: the rest of the computation is inside their branches, resp. their
scope.  A Lean `if`/`match` containing a call in non-tail position is captured as
`join j (v) := ⟦rest⟧ in if c then (…; jump j a) else (…; jump j b)`.

Every statement also carries the postcondition `Q : Env Γ → t.denote → Prop` it must establish:
each `ret` proves it from its path condition.  The path condition and the decrease proofs only
mention `PExpr.eval`, which is defined before `Expr`, so no induction–recursion is needed.  All
proofs are `Prop`s and are erased by code generation: the evaluator never checks anything at
runtime and has no fuel.

**Optimised normal form.**  Besides being in ANF, programs are in an optimised normal form
enforced by the grammar: every call-free expression in a statement (`ret`, call arguments,
`jump`) carries a proof `isNF = true`, and every `if` test a proof `isCond = true`
(`Core/Normal.lean`).  The capture produces such programs by simplifying while it translates
(`Capture/Optimize.lean`).  These proofs are Booleans checked by `decide`, and are erased at
runtime.
-/

namespace WFLang.PCL

/-! ## Global functions: signatures, values, indices -/

/-- The signature of a (global) recursive function: parameters, result type, precondition and
postcondition. -/
structure Fn where
  params : List Ty
  ret : Ty
  pre : Env params → Prop
  post : Env params → ret.denote → Prop

/-- The meaning of a function: defined on the arguments satisfying its precondition, with
results satisfying its postcondition. -/
abbrev FnVal (f : Fn) : Type := (x : Env f.params) → f.pre x → {v : f.ret.denote // f.post x v}

/-- Typed de Bruijn indices of global functions. -/
inductive FnVar : List Fn → Fn → Type where
  | here {fs : List Fn} {f : Fn} : FnVar (f :: fs) f
  | there {fs : List Fn} {f g : Fn} : FnVar fs f → FnVar (g :: fs) f

/-- Values of the global functions. -/
def FEnv : List Fn → Type
  | [] => Unit
  | f :: fs => FnVal f × FEnv fs

/-- Lookup of a global function. -/
def FnVar.get : {fs : List Fn} → {f : Fn} → FnVar fs f → FEnv fs → FnVal f
  | _ :: _, _, .here, fe => fe.1
  | _ :: _, _, .there i, fe => i.get fe.2

/-! ## Join points -/

/-- The join points in scope in context `Γ`, for statements of result type `t`.  `bind js s P Q`
adds a join point defined in the current context, with a parameter of type `s` satisfying `P`,
that establishes the postcondition `Q`; `wk js s` is the scope `js` seen under one more local
variable of type `s` (weakening is a constructor, so that it costs nothing at runtime and
computes by simplification).

A recursive join point needs no constructor of its own: inside its body it is an ordinary
`bind` entry whose precondition includes the decrease `R e v x` of the back edge
(see `Expr.joinrec`). -/
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
the global functions `GL` in scope (a parameter: the same everywhere in a program), inside the
recursive function `sf` (if any), establishing the postcondition `Q`, with the join points `js`
in scope.

Every call-free expression of a statement is in optimised normal form (`PExpr.isNF`,
`Core/Normal.lean`), and every `if` test is a condition (`PExpr.isCond`): the proofs `hp`,
`hc`, `ha` (checked by `decide`) make the optimisation part of the grammar. -/
inductive Expr (GL : List Fn) : (Γ : List Ty) → (Env Γ → Prop) → Option (Self Γ) →
    (t : Ty) → (Env Γ → t.denote → Prop) → JScope Γ t → Type where
  /-- Return a call-free value, which satisfies the postcondition. -/
  | ret {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (p : PExpr Γ t) (hp : p.isNF = true) (post : ∀ e, G e → Q e (p.eval e)) :
      Expr GL Γ G sf t Q js
  /-- `if c then a else b`, in tail position; each branch knows the outcome of the test. -/
  | ite {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (c : PExpr Γ .bool) (hc : c.isCond = true)
      (a : Expr GL Γ (fun e => G e ∧ c.eval e = true) sf t Q js)
      (b : Expr GL Γ (fun e => G e ∧ c.eval e = false) sf t Q js) : Expr GL Γ G sf t Q js
  /-- `let v := self args in k`, with the proofs that the call goes down and that the
  arguments satisfy the precondition; `k` may use the postcondition of `v`. -/
  | fixSelfCall {Γ : List Ty} {G : Env Γ → Prop} {sf : Self Γ} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (args : PExprs Γ sf.params) (ha : args.isNF = true)
      (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
      (hpre : ∀ e, G e → sf.pre (args.eval e))
      (k : Expr GL (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1)
        (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret)) :
      Expr GL Γ G (some sf) t Q js
  /-- `let v := g args in k`, for a **global** function `g` (an entry of the global context
  `GL`), with the proof that the arguments satisfy its precondition; `k` may use the
  postcondition of `v`. -/
  | gCall {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t} {f : Fn}
      (i : FnVar GL f) (args : PExprs Γ f.params) (ha : args.isNF = true)
      (hpre : ∀ e, G e → f.pre (args.eval e))
      (k : Expr GL (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1)
        (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret)) :
      Expr GL Γ G sf t Q js
  /-- `join j (v : s) := body in m`, in tail position: the join point `j` (whose parameter
  satisfies `P`) is in scope in `m`.  Its body runs in the current context extended by `v`,
  under the current path condition and `P`; it may jump to the join points defined before. -/
  | join {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (s : Ty) (P : Env Γ → s.denote → Prop)
      (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
        (fun e r => Q e.2 r) (.wk js s))
      (m : Expr GL Γ G sf t Q (.bind js s P Q)) : Expr GL Γ G sf t Q js
  /-- `joinrec j (x : s) [R, wf] := body in m`, in tail position: a **recursive join point**
  (a loop).  Like a `join`, its body runs in the current context extended by `x`, under the
  current path condition and the precondition `P`, inside the same enclosing function, and may
  jump to the join points defined before.  In addition it may jump back to `j` itself: inside
  the body, the precondition of `j` is `P e v ∧ R e v x`, so each back edge proves that the new
  parameter `v` is below the current one `x` along the relation `R e` (well-founded by `wf`, for
  each value `e` of the enclosing variables).  From `m`, `j` only needs `P`. -/
  | joinrec {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (s : Ty) (P : Env Γ → s.denote → Prop) (R : Env Γ → s.denote → s.denote → Prop)
      (wf : ∀ e, WellFounded (R e))
      (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
        (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
          (fun e r => Q e.2 r)))
      (m : Expr GL Γ G sf t Q (.bind js s P Q)) : Expr GL Γ G sf t Q js
  /-- `jump j p`, in tail position: run the join point `j` on `p`, with the proof that `p`
  satisfies its precondition (for a back edge of a recursive join point, this includes the
  decrease); its result satisfies the current postcondition. -/
  | jump {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (i : JVar js) (p : PExpr Γ i.arg) (hp : p.isNF = true)
      (hpre : ∀ e, G e → i.pre e (p.eval e))
      (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r) : Expr GL Γ G sf t Q js

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

/-- The evaluator: structural recursion on the syntax; a `joinrec` node is run by
`WellFounded.fix` on its own relation, and a `join` node passes the closure of its body to its
scope.  The values `ge` of the global functions are fixed.  No fuel, no runtime checks: the
proofs (path conditions, pre- and postconditions, normal forms) are erased by code
generation. -/
def Expr.eval {GL : List Fn} (ge : FEnv GL) : {Γ : List Ty} → {G : Env Γ → Prop} →
    {sf : Option (Self Γ)} →
    {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G sf t Q js → (e : Env Γ) → G e → Handler sf e → JEnv js e →
    {v : t.denote // Q e v}
  | _, _, _, _, _, _, .ret p _ post, e, g, _, _ => ⟨p.eval e, post e g⟩
  | _, _, _, _, _, _, .ite c _ a b, e, g, h, je =>
      if hc : c.eval e = true then a.eval ge e ⟨g, hc⟩ h je
      else b.eval ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h je
  | _, _, _, _, _, _, .fixSelfCall args _ dec hpre k, e, g, h, je =>
      let v := h (args.eval e) (dec e g) (hpre e g)
      let r := k.eval ge (v.1, e) ⟨g, v.2⟩ h je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .gCall i args _ hpre k, e, g, h, je =>
      let v := i.get ge (args.eval e) (hpre e g)
      let r := k.eval ge (v.1, e) ⟨g, v.2⟩ (Handler.push h) je
      ⟨r.1, r.2⟩
  | _, _, _, _, _, _, .join _ _ body m, e, g, h, je =>
      m.eval ge e g h ((fun v hv => body.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je), je)
  | _, _, _, _, _, _, .joinrec _ P _ wf body m, e, g, h, je =>
      let F := (wf e).fix (C := fun x => P e x → Subtype _)
        (fun x ih hx => body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
          ((fun y hy => ih y hy.2 hy.1), je))
      m.eval ge e g h ((fun v hv => F v hv), je)
  | _, _, _, _, _, _, .jump i p _ hpre hpost, e, g, _, je =>
      let r := i.get je (p.eval e) (hpre e g)
      ⟨r.1, hpost e g r.1 r.2⟩

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

/-! ## Soundness of recursive join points -/

section
variable {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
  {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
  {s : Ty} {P : Env Γ → s.denote → Prop} {R : Env Γ → s.denote → s.denote → Prop}
  (wf : ∀ e, WellFounded (R e))
  (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
    (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
      (fun e r => Q e.2 r)))
  (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e)

/-- The function denoted by a recursive join point (at the environment `e` of its definition,
with the handler `h` of the enclosing function and the values `je` of the outer join points):
the result of the enclosing statement when the join point is entered with parameter `x`. -/
def joinFn : (x : s.denote) → P e x → {r : t.denote // Q e r} :=
  (wf e).fix (C := fun x => P e x → {r // Q e r})
    (fun x ih hx => body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
      ((fun y hy => ih y hy.2 hy.1), je))

/-- **Soundness (1):** a recursive join point satisfies its equation: entering it runs its
body, in which a back edge re-enters it. -/
theorem joinFn_eq (x : s.denote) (hx : P e x) :
    joinFn ge wf body e g h je x hx =
      body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
        ((fun y hy => joinFn ge wf body e g h je y hy.1), je) := by
  unfold joinFn
  rw [WellFounded.fix_eq]

/-- **Soundness (2):** that equation has only one solution. -/
theorem joinFn_unique (F : (x : s.denote) → P e x → {r : t.denote // Q e r})
    (hF : ∀ x hx, (F x hx).1 = (body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h)
      ((fun y hy => F y hy.1), je)).1) :
    ∀ x hx, (joinFn ge wf body e g h je x hx).1 = (F x hx).1 := by
  intro x
  induction x using (wf e).induction with
  | _ x IH =>
    intro hx
    rw [joinFn_eq, hF x hx]
    have : (fun y (hy : P e y ∧ R e y x) => joinFn ge wf body e g h je y hy.1) =
        (fun y hy => F y hy.1) := by
      funext y hy; exact Subtype.ext (IH y hy.2 hy.1)
    exact congrArg (fun k => (body.eval ge (x, e) ⟨g, hx⟩ (Handler.push h) (k, je)).1) this

end

@[simp] theorem eval_joinrec {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (P : Env Γ → s.denote → Prop) (R : Env Γ → s.denote → s.denote → Prop)
    (wf : ∀ e, WellFounded (R e))
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.bind (.wk js s) s (fun e v => P e.2 v ∧ R e.2 v e.1)
        (fun e r => Q e.2 r)))
    (m : Expr GL Γ G sf t Q (.bind js s P Q))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.joinrec s P R wf body m).eval ge e g h je).1 =
      (m.eval ge e g h ((fun v hv => joinFn ge wf body e g h je v hv), je)).1 := rfl

/-! ## Well-founded `while` loops: a derived form

`let v := (while c do x := p from x := init) in k` is the statement

```
join K (v) [inv v ∧ ¬ c v] := k in
joinrec L (x) [inv, R] := (if c then jump L p else jump K x) in
jump L init
```

(with the branches swapped when `c` is a negation `!c'`: the test of an `if` is never a
negation).  `whileFn`-style reasoning follows from `joinFn_unique`: the loop computes the Lean
loop `whileWF` (`eval_whileLoop`). -/

/-- The test `c` without its top-level negation. -/
def _root_.WFLang.PExpr.unNot {Γ : List Ty} : PExpr Γ .bool → PExpr Γ .bool
  | .not a => a
  | c => c

theorem _root_.WFLang.PExpr.unNot_isCond {Γ : List Ty} (c : PExpr Γ .bool)
    (hc : c.isLoopCond = true) : c.unNot.isCond = true := by
  cases c <;> simp_all [PExpr.unNot, PExpr.isCond, PExpr.isLoopCond, PExpr.isNF, PExpr.isNot]

theorem _root_.WFLang.PExpr.isCond_of_not_isNot {Γ : List Ty} (c : PExpr Γ .bool)
    (hc : c.isLoopCond = true) (hn : ¬ c.isNot = true) : c.isCond = true := by
  simp_all [PExpr.isCond, PExpr.isLoopCond]

theorem _root_.WFLang.PExpr.unNot_eval {Γ : List Ty} (c : PExpr Γ .bool) (hn : c.isNot = true)
    (e : Env Γ) : c.unNot.eval e = !c.eval e := by
  cases c <;> simp_all [PExpr.unNot, PExpr.isNot, PExpr.eval]

/-- The body of the loop of `Expr.whileLoop`: `if c then jump L p else jump K x`. -/
def Expr.whileBody {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (inv : Env Γ → s.denote → Prop)
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1) :
    Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1) (sf.map (·.push s)) t (fun e r => Q e.2 r)
      (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
        (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
  let loop {G' : Env (s :: Γ) → Prop} (hG : ∀ e, G' e → G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true) :
      Expr GL (s :: Γ) G' (sf.map (·.push s)) t (fun e r => Q e.2 r)
        (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
          (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
    .jump .here p hp (fun e g => step e (hG e g)) (fun _ _ _ h => h)
  let exit {G' : Env (s :: Γ) → Prop} (hG : ∀ e, G' e → G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false) :
      Expr GL (s :: Γ) G' (sf.map (·.push s)) t (fun e r => Q e.2 r)
        (.bind (.wk (.bind js s (fun e v => inv e v ∧ c.eval (v, e) = false) Q) s) s
          (fun e v => inv e.2 v ∧ R e.2 v e.1) (fun e r => Q e.2 r)) :=
    .jump (.there (.wk .here)) (.var .here) rfl (fun e g => (hG e g).2) (fun _ _ _ h => h)
  if hn : c.isNot = true then
    .ite c.unNot (c.unNot_isCond hc)
      (exit fun e g => ⟨g.1.1, g.1.2, by have := g.2; rw [c.unNot_eval hn] at this; simpa using this⟩)
      (loop fun e g => ⟨g.1.1, g.1.2, by have := g.2; rw [c.unNot_eval hn] at this; simpa using this⟩)
  else
    .ite c (c.isCond_of_not_isNot hc hn) (loop fun _ g => ⟨g.1.1, g.1.2, g.2⟩)
      (exit fun _ g => ⟨g.1.1, g.1.2, g.2⟩)

/-- `let v := (while c do x := p from x := init) in k`: a **well-founded `while` loop** on a
state `x : s`, whose result (the first state on which the test `c` is false) is bound to `v`.
The loop carries a relation `R` on the states (well-founded by `wf`, for each value of the
enclosing variables) and an invariant `inv`: the initial state satisfies the invariant
(`hinit`), and each iteration (`x := p`, run on a state satisfying the invariant and the test)
keeps the invariant and goes down (`step`).  `k` knows that `v` satisfies the invariant and not
the test.  This is a derived form: a `join` (the exit `K`) and a `joinrec` (the loop `L`). -/
def Expr.whileLoop {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)}
    {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (init : PExpr Γ s) (hi : init.isNF = true)
    (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (wf : ∀ e, WellFounded (R e))
    (inv : Env Γ → s.denote → Prop) (hinit : ∀ e, G e → inv e (init.eval e))
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1)
    (k : Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false)
      (sf.map (·.push s)) t (fun e v => Q e.2 v) (.wk js s)) :
    Expr GL Γ G sf t Q js :=
  .join s (fun e v => inv e v ∧ c.eval (v, e) = false) k
    (.joinrec s inv R wf (Expr.whileBody s c hc R inv p hp step)
      (.jump .here init hi hinit (fun _ _ _ h => h)))

/-- **A `while` loop computes the Lean loop `whileWF`** of its test and its body, and runs the
rest of the statement on its result. -/
@[simp] theorem eval_whileLoop {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
    (s : Ty) (init : PExpr Γ s) (hi : init.isNF = true)
    (c : PExpr (s :: Γ) .bool) (hc : c.isLoopCond = true)
    (R : Env Γ → s.denote → s.denote → Prop) (wf : ∀ e, WellFounded (R e))
    (inv : Env Γ → s.denote → Prop) (hinit : ∀ e, G e → inv e (init.eval e))
    (p : PExpr (s :: Γ) s) (hp : p.isNF = true)
    (step : ∀ e : Env (s :: Γ), G e.2 ∧ inv e.2 e.1 ∧ c.eval e = true →
      inv e.2 (p.eval e) ∧ R e.2 (p.eval e) e.1)
    (k : Expr GL (s :: Γ) (fun e => G e.2 ∧ inv e.2 e.1 ∧ c.eval e = false)
      (sf.map (·.push s)) t (fun e v => Q e.2 v) (.wk js s))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.whileLoop s init hi c hc R wf inv hinit p hp step k).eval ge e g h je).1 =
      (k.eval ge (whileWF (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
          (fun y hy hc => step (y, e) ⟨g, hy, hc⟩) (init.eval e) (hinit e g), e)
        ⟨g, whileWF_spec (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
          (fun y hy hc => step (y, e) ⟨g, hy, hc⟩) (init.eval e) (hinit e g)⟩
        (Handler.push h) je).1 := by
  -- the loop's value, followed by the rest `k`
  let W := whileWF (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
    (fun y hy hc => step (y, e) ⟨g, hy, hc⟩)
  have hW := whileWF_spec (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e))
    (fun y hy hc => step (y, e) ⟨g, hy, hc⟩)
  let K : (v : s.denote) → (inv e v ∧ c.eval (v, e) = false) → {r : t.denote // Q e r} :=
    fun v hv => k.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je
  let F : (x : s.denote) → inv e x → {r : t.denote // Q e r} := fun x hx => K (W x hx) (hW x hx)
  have key := joinFn_unique ge wf (Expr.whileBody (GL := GL) (sf := sf) (Q := Q) (js := js)
    s c hc R inv p hp step) e g h (K, je) F (by
      intro x hx
      have Kc : ∀ v1 v2 (h1 : inv e v1 ∧ c.eval (v1, e) = false)
          (h2 : inv e v2 ∧ c.eval (v2, e) = false), v1 = v2 → (K v1 h1).1 = (K v2 h2).1 := by
        intro v1 v2 h1 h2 hv; subst hv; rfl
      unfold Expr.whileBody
      split
      · rename_i hn
        simp only [Expr.eval, JVar.get]
        split
        · rename_i hc'
          have hcx : c.eval (x, e) = false := by
            rw [c.unNot_eval hn] at hc'; simpa using hc'
          exact Kc _ _ (hW x hx) ⟨hx, by simpa using hcx⟩ (whileWF_of_false (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
        · rename_i hc'
          have hcx : c.eval (x, e) = true := by
            rw [c.unNot_eval hn] at hc'; simpa using hc'
          exact Kc _ _ (hW x hx) (hW _ _) (whileWF_of_true (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
      · simp only [Expr.eval, JVar.get]
        split
        · rename_i hcx
          exact Kc _ _ (hW x hx) (hW _ _) (whileWF_of_true (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx hcx)
        · rename_i hcx
          exact Kc _ _ (hW x hx) ⟨hx, by simpa using hcx⟩ (whileWF_of_false (R e) (wf e) (inv e) (fun y => c.eval (y, e)) (fun y => p.eval (y, e)) _ x hx (by simpa using hcx)))
  exact key (init.eval e) (hinit e g)

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

/-! ## Simplification lemmas used by the capture tactics -/

section
variable {GL : List Fn} (ge : FEnv GL) {Γ : List Ty} {G : Env Γ → Prop}
  {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}

@[simp] theorem eval_ret {sf : Option (Self Γ)} (p : PExpr Γ t) (hp : p.isNF = true)
    (post : ∀ e, G e → Q e (p.eval e))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ret (GL := GL) (sf := sf) (js := js) p hp post).eval ge e g h je).1 =
      p.eval e := rfl

@[simp] theorem eval_ite {sf : Option (Self Γ)}
    (c : PExpr Γ .bool) (hc : c.isCond = true)
    (a : Expr GL Γ (fun e => G e ∧ c.eval e = true) sf t Q js)
    (b : Expr GL Γ (fun e => G e ∧ c.eval e = false) sf t Q js) (e : Env Γ) (g : G e)
    (h : Handler sf e) (je : JEnv js e) :
    ((Expr.ite c hc a b).eval ge e g h je).1 =
      if hc : c.eval e = true then (a.eval ge e ⟨g, hc⟩ h je).1
      else (b.eval ge e ⟨g, Bool.eq_false_iff.mpr hc⟩ h je).1 := by
  simp only [Expr.eval]; split <;> rfl

@[simp] theorem eval_fixSelfCall {sf : Self Γ}
    (args : PExprs Γ sf.params) (ha : args.isNF = true)
    (dec : ∀ e, G e → sf.R (args.eval e) (sf.cur e))
    (hpre : ∀ e, G e → sf.pre (args.eval e))
    (k : Expr GL (sf.ret :: Γ) (fun e => G e.2 ∧ sf.post (args.eval e.2) e.1)
      (some (sf.push sf.ret)) t (fun e v => Q e.2 v) (.wk js sf.ret))
    (e : Env Γ) (g : G e) (h : Handler (some sf) e) (je : JEnv js e) :
    ((Expr.fixSelfCall args ha dec hpre k).eval ge e g h je).1 =
      (k.eval ge ((h (args.eval e) (dec e g) (hpre e g)).1, e)
        ⟨g, (h (args.eval e) (dec e g) (hpre e g)).2⟩ h je).1 := rfl

/-- A call of a global function runs the function found in the global context. -/
@[simp] theorem eval_gCall {sf : Option (Self Γ)} {f : Fn}
    (i : FnVar GL f) (args : PExprs Γ f.params) (ha : args.isNF = true)
    (hpre : ∀ e, G e → f.pre (args.eval e))
    (k : Expr GL (f.ret :: Γ) (fun e => G e.2 ∧ f.post (args.eval e.2) e.1)
      (sf.map (·.push f.ret)) t (fun e v => Q e.2 v) (.wk js f.ret))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.gCall i args ha hpre k).eval ge e g h je).1 =
      (k.eval ge ((i.get ge (args.eval e) (hpre e g)).1, e)
        ⟨g, (i.get ge (args.eval e) (hpre e g)).2⟩ (Handler.push h) je).1 := rfl

/-- A `join` node runs its scope, with the closure of its body as the value of the new join
point. -/
@[simp] theorem eval_join {sf : Option (Self Γ)}
    (s : Ty) (P : Env Γ → s.denote → Prop)
    (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ P e.2 e.1) (sf.map (·.push s)) t
      (fun e r => Q e.2 r) (.wk js s))
    (m : Expr GL Γ G sf t Q (.bind js s P Q))
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.join s P body m).eval ge e g h je).1 =
      (m.eval ge e g h
        ((fun v hv => body.eval ge (v, e) ⟨g, hv⟩ (Handler.push h) je), je)).1 :=
  rfl

/-- A `jump` runs the join point. -/
@[simp] theorem eval_jump {sf : Option (Self Γ)}
    (i : JVar js) (p : PExpr Γ i.arg) (hp : p.isNF = true)
    (hpre : ∀ e, G e → i.pre e (p.eval e))
    (hpost : ∀ e, G e → ∀ r, i.post e r → Q e r)
    (e : Env Γ) (g : G e) (h : Handler sf e) (je : JEnv js e) :
    ((Expr.jump (GL := GL) (sf := sf) i p hp hpre hpost).eval ge e g h je).1 =
      (i.get je (p.eval e) (hpre e g)).1 := rfl

end

@[simp] theorem FnVar.get_here {fs : List Fn} {f : Fn} (fe : FEnv (f :: fs)) :
    (FnVar.here : FnVar (f :: fs) f).get fe = fe.1 := rfl

@[simp] theorem FnVar.get_there {fs : List Fn} {f g : Fn} (i : FnVar fs f)
    (fe : FEnv (g :: fs)) : (FnVar.there i : FnVar (g :: fs) f).get fe = i.get fe.2 := rfl

@[simp] theorem Globals.env_nil : Globals.nil.env = () := rfl

@[simp] theorem Globals.env_defn {GL : List Fn} (gs : Globals GL) (f : Fn)
    (R : Env f.params → Env f.params → Prop) (wf : WellFounded R)
    (body : Expr GL f.params f.pre (some (Self.top f.params f.ret R f.pre f.post)) f.ret
      f.post .nil) :
    (Globals.defn gs f R wf body).env = (fixFn gs.env wf body, gs.env) := rfl

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
