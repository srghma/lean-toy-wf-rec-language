import RequestProject.WFLang.PCL.Lang

/-!
# Measures of programs

The number of statement nodes (`size`), of `join` nodes (`joins`) and of calls of global
functions (`gcalls`) of a statement, of the bodies of a global context, and of a program
(main statement and global functions).  Used by the tests to pin the shape of the captured
programs.
-/

namespace WFLang.PCL

variable {GL : List Fn}

/-- The number of statement nodes of a statement. -/
def Expr.size : {Γ : List Ty} → {G : Env Γ → Prop} → {fns : List Fn} →
    {sf : Option (Self Γ)} → {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G fns sf t Q js → Nat
  | _, _, _, _, _, _, _, .ret _ _ _ => 1
  | _, _, _, _, _, _, _, .ite _ _ a b => 1 + a.size + b.size
  | _, _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, _, .fnCall _ _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, _, .gCall _ _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, _, .fix _ _ _ _ _ _ body rest => 1 + body.size + rest.size
  | _, _, _, _, _, _, _, .join _ _ body m => 1 + body.size + m.size
  | _, _, _, _, _, _, _, .jump _ _ _ _ _ => 1

/-- The number of `join` nodes of a statement. -/
def Expr.joins : {Γ : List Ty} → {G : Env Γ → Prop} → {fns : List Fn} →
    {sf : Option (Self Γ)} → {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G fns sf t Q js → Nat
  | _, _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, _, .ite _ _ a b => a.joins + b.joins
  | _, _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.joins
  | _, _, _, _, _, _, _, .fnCall _ _ _ _ k => k.joins
  | _, _, _, _, _, _, _, .gCall _ _ _ _ k => k.joins
  | _, _, _, _, _, _, _, .fix _ _ _ _ _ _ body rest => body.joins + rest.joins
  | _, _, _, _, _, _, _, .join _ _ body m => 1 + body.joins + m.joins
  | _, _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of local `fix` nodes of a statement. -/
def Expr.fixes : {Γ : List Ty} → {G : Env Γ → Prop} → {fns : List Fn} →
    {sf : Option (Self Γ)} → {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G fns sf t Q js → Nat
  | _, _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, _, .ite _ _ a b => a.fixes + b.fixes
  | _, _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.fixes
  | _, _, _, _, _, _, _, .fnCall _ _ _ _ k => k.fixes
  | _, _, _, _, _, _, _, .gCall _ _ _ _ k => k.fixes
  | _, _, _, _, _, _, _, .fix _ _ _ _ _ _ body rest => 1 + body.fixes + rest.fixes
  | _, _, _, _, _, _, _, .join _ _ body m => body.fixes + m.fixes
  | _, _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of calls of global functions of a statement. -/
def Expr.gcalls : {Γ : List Ty} → {G : Env Γ → Prop} → {fns : List Fn} →
    {sf : Option (Self Γ)} → {t : Ty} → {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} →
    Expr GL Γ G fns sf t Q js → Nat
  | _, _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, _, .ite _ _ a b => a.gcalls + b.gcalls
  | _, _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.gcalls
  | _, _, _, _, _, _, _, .fnCall _ _ _ _ k => k.gcalls
  | _, _, _, _, _, _, _, .gCall _ _ _ _ k => 1 + k.gcalls
  | _, _, _, _, _, _, _, .fix _ _ _ _ _ _ body rest => body.gcalls + rest.gcalls
  | _, _, _, _, _, _, _, .join _ _ body m => body.gcalls + m.gcalls
  | _, _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- Sum of a measure over the bodies of the global functions. -/
def Globals.sumBodies (m : ∀ {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop} {fns : List Fn}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t},
    Expr GL Γ G fns sf t Q js → Nat) : {GL : List Fn} → Globals GL → Nat
  | _, .nil => 0
  | _, .defn gs _ _ _ body => gs.sumBodies m + m body

/-- The number of statement nodes of a program (main statement and global functions). -/
def PTerm.size {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.size + t.globals.sumBodies Expr.size

/-- The number of `join` nodes of a program. -/
def PTerm.joins {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.joins + t.globals.sumBodies Expr.joins

/-- The number of local `fix` nodes of a program. -/
def PTerm.fixes {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.fixes + t.globals.sumBodies Expr.fixes

/-- The number of calls of global functions of a program. -/
def PTerm.gcalls {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.gcalls + t.globals.sumBodies Expr.gcalls

/-- The number of global functions of a program. -/
def PTerm.nglobals {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.globals.size

end WFLang.PCL
