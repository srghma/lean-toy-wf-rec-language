import RequestProject.WFLang.Core.Normal
import RequestProject.WFLang.Core.While

/-!
# Language `PCL`: well-founded recursion as a construct of the grammar (proof-carrying calls)

The grammar has three layers:

```
PExpr   ::= x | lit | op PExpr PExpr | !PExpr | if PExpr then PExpr else PExpr
                                             -- call-free, total values   (Core/PExpr.lean)
Expr    ::= ret PExpr                        -- tail statements           (PCL/Lang)
          | if PExpr then Expr else Expr
          | let v := self args in Expr       -- fixSelfCall
          | let v := g args in Expr          -- gCall   (g a global function)
          | let v := map (fun x => Expr) PExpr in Expr  -- map (the body knows x ∈ list)
          | let v := foldl (fun acc x => Expr) PExpr PExpr in Expr  -- foldl (idem)
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
  deriving DecidableEq, Repr

/-- There is no global function in the empty global context. -/
instance FnVar.instIsEmptyNil {f : Fn} : IsEmpty (FnVar [] f) := ⟨nofun⟩

/-- Values of the global functions. -/
@[reducible] def FEnv : List Fn → Type
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

/-- The empty join-point scope. (`JScope` has no decidable equality: its entries carry
arbitrary predicates.) -/
instance JScope.instInhabited {Γ : List Ty} {t : Ty} : Inhabited (JScope Γ t) := ⟨.nil⟩

/-- Typed de Bruijn indices of join points. -/
inductive JVar : {Γ : List Ty} → {t : Ty} → JScope Γ t → Type where
  | here {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} {P : Env Γ → s.denote → Prop}
      {Q : Env Γ → t.denote → Prop} : JVar (.bind js s P Q)
  | there {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} {P : Env Γ → s.denote → Prop}
      {Q : Env Γ → t.denote → Prop} : JVar js → JVar (.bind js s P Q)
  | wk {Γ : List Ty} {t : Ty} {js : JScope Γ t} {s : Ty} : JVar js → JVar (.wk js s)
  deriving DecidableEq, Repr

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
@[reducible] def JEnv : {Γ : List Ty} → {t : Ty} → JScope Γ t → Env Γ → Type
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
abbrev Self.push {Γ : List Ty} (sf : Self Γ) (t : Ty) : Self (t :: Γ) :=
  { sf with cur := fun e => sf.cur e.2 }

/-- The function whose body is being defined: its parameters are the whole context. -/
abbrev Self.top (params : List Ty) (r : Ty) (R : Env params → Env params → Prop)
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
  /-- `let v := List.map (fun x => body) l in k`: the list `l` mapped by a statement `body`
  over one more variable `x`.  The body may make calls (recursive calls of the enclosing
  function included); it runs under the current path condition and the fact that `x` is an
  element of `l` (`x ∈ l`), which its decrease proofs may use.  The membership is a fact of the
  path condition, not a value: the program holds no proof term for it, so a Lean
  `l.attach.map (fun ⟨x, h⟩ => …)` is captured as `map (fun x => …) l`.  The body has no join
  point in scope and no postcondition. -/
  | map {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (s u : Ty) (l : PExpr Γ (.list s)) (hl : l.isNF = true)
      (body : Expr GL (s :: Γ) (fun e => G e.2 ∧ e.1 ∈ l.eval e.2) (sf.map (·.push s)) u
        (fun _ _ => True) .nil)
      (k : Expr GL (.list u :: Γ) (fun e => G e.2) (sf.map (·.push (.list u))) t
        (fun e v => Q e.2 v) (.wk js (.list u))) :
      Expr GL Γ G sf t Q js
  /-- `let v := List.foldl (fun acc x => body) init l in k`: the list `l` folded from `init` by a
  statement `body` over two more variables, the element `x` and the accumulator `acc`.  Like the
  body of `map`, the body may make calls (recursive calls of the enclosing function included);
  it runs under the current path condition and the fact that `x` is an element of `l`
  (`x ∈ l`), which its decrease proofs may use, and the program holds no proof term for it: a
  Lean `l.attach.foldl (fun acc ⟨x, h⟩ => …) init` is captured as `foldl (fun acc x => …) init l`.
  The body has no join point in scope and no postcondition. -/
  | foldl {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
      {Q : Env Γ → t.denote → Prop} {js : JScope Γ t}
      (s u : Ty) (l : PExpr Γ (.list s)) (hl : l.isNF = true) (init : PExpr Γ u)
      (hi : init.isNF = true)
      (body : Expr GL (u :: s :: Γ) (fun e => G e.2.2 ∧ e.2.1 ∈ l.eval e.2.2)
        ((sf.map (·.push s)).map (·.push u)) u (fun _ _ => True) .nil)
      (k : Expr GL (u :: Γ) (fun e => G e.2) (sf.map (·.push u)) t
        (fun e v => Q e.2 v) (.wk js u)) :
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

end WFLang.PCL
