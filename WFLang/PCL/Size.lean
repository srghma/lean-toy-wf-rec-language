import RequestProject.WFLang.PCL.Lang

/-!
# Measures of programs

The number of statement nodes (`size`), of (non-recursive) `join` nodes (`joins`), of recursive
join points, i.e. loops inside a statement (`loops`), of calls of global functions (`gcalls`),
of `map` nodes (`maps`), of pure `let` nodes (`lets`), and of nodes of call-free expressions
(`exprNodes`) of a statement, of the bodies of a global context, and of a program (main
statement and global functions).  Used by the tests to pin the shape of the captured programs.
-/

namespace WFLang.PCL

variable {GL : List Fn}

/-- The number of statement nodes of a statement. -/
def Expr.size : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 1
  | _, _, _, _, _, _, .ite _ _ a b => 1 + a.size + b.size
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, .gCall _ _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, .plet _ _ _ k => 1 + k.size
  | _, _, _, _, _, _, .map _ _ _ _ body k => 1 + body.size + k.size
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => 1 + body.size + k.size
  | _, _, _, _, _, _, .join _ _ body m => 1 + body.size + m.size
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => 1 + body.size + m.size
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 1

/-- The number of (non-recursive) `join` nodes of a statement. -/
def Expr.joins : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, .ite _ _ a b => a.joins + b.joins
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.joins
  | _, _, _, _, _, _, .gCall _ _ _ _ k => k.joins
  | _, _, _, _, _, _, .plet _ _ _ k => k.joins
  | _, _, _, _, _, _, .map _ _ _ _ body k => body.joins + k.joins
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => body.joins + k.joins
  | _, _, _, _, _, _, .join _ _ body m => 1 + body.joins + m.joins
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => body.joins + m.joins
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of recursive join points (`joinrec` nodes: loops) of a statement. -/
def Expr.loops : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, .ite _ _ a b => a.loops + b.loops
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.loops
  | _, _, _, _, _, _, .gCall _ _ _ _ k => k.loops
  | _, _, _, _, _, _, .plet _ _ _ k => k.loops
  | _, _, _, _, _, _, .map _ _ _ _ body k => body.loops + k.loops
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => body.loops + k.loops
  | _, _, _, _, _, _, .join _ _ body m => body.loops + m.loops
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => 1 + body.loops + m.loops
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of calls of global functions of a statement. -/
def Expr.gcalls : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, .ite _ _ a b => a.gcalls + b.gcalls
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.gcalls
  | _, _, _, _, _, _, .gCall _ _ _ _ k => 1 + k.gcalls
  | _, _, _, _, _, _, .plet _ _ _ k => k.gcalls
  | _, _, _, _, _, _, .map _ _ _ _ body k => body.gcalls + k.gcalls
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => body.gcalls + k.gcalls
  | _, _, _, _, _, _, .join _ _ body m => body.gcalls + m.gcalls
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => body.gcalls + m.gcalls
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of `map` nodes of a statement. -/
def Expr.maps : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, .ite _ _ a b => a.maps + b.maps
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.maps
  | _, _, _, _, _, _, .gCall _ _ _ _ k => k.maps
  | _, _, _, _, _, _, .plet _ _ _ k => k.maps
  | _, _, _, _, _, _, .map _ _ _ _ body k => 1 + body.maps + k.maps
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => body.maps + k.maps
  | _, _, _, _, _, _, .join _ _ body m => body.maps + m.maps
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => body.maps + m.maps
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of pure `let` nodes (`plet`, shared values) of a statement. -/
def Expr.lets : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret _ _ _ => 0
  | _, _, _, _, _, _, .ite _ _ a b => a.lets + b.lets
  | _, _, _, _, _, _, .fixSelfCall _ _ _ _ k => k.lets
  | _, _, _, _, _, _, .gCall _ _ _ _ k => k.lets
  | _, _, _, _, _, _, .plet _ _ _ k => 1 + k.lets
  | _, _, _, _, _, _, .map _ _ _ _ body k => body.lets + k.lets
  | _, _, _, _, _, _, .foldl _ _ _ _ _ _ body k => body.lets + k.lets
  | _, _, _, _, _, _, .join _ _ body m => body.lets + m.lets
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => body.lets + m.lets
  | _, _, _, _, _, _, .jump _ _ _ _ _ => 0

/-- The number of nodes of a call-free expression. -/
def _root_.WFLang.PExpr.nodes {Γ : List Ty} : {t : Ty} → PExpr Γ t → Nat
  | _, .var _ => 1
  | _, .lit _ _ => 1
  | _, .bin _ a b => 1 + a.nodes + b.nodes
  | _, .not a => 1 + a.nodes
  | _, .un _ a => 1 + a.nodes
  | _, .ite c a b => 1 + c.nodes + a.nodes + b.nodes

/-- The number of nodes of an argument tuple. -/
def _root_.WFLang.PExprs.nodes {Γ : List Ty} : {ts : List Ty} → PExprs Γ ts → Nat
  | _, .nil => 0
  | _, .cons a as => a.nodes + as.nodes

/-- The total number of nodes of the call-free expressions of a statement (the work of
evaluating them, counted syntactically).  A value used several times but bound once by a pure
`let` is counted once. -/
def Expr.exprNodes : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    {Q : Env Γ → t.denote → Prop} → {js : JScope Γ t} → Expr GL Γ G sf t Q js → Nat
  | _, _, _, _, _, _, .ret p _ _ => p.nodes
  | _, _, _, _, _, _, .ite c _ a b => c.nodes + a.exprNodes + b.exprNodes
  | _, _, _, _, _, _, .fixSelfCall args _ _ _ k => args.nodes + k.exprNodes
  | _, _, _, _, _, _, .gCall _ args _ _ k => args.nodes + k.exprNodes
  | _, _, _, _, _, _, .plet _ p _ k => p.nodes + k.exprNodes
  | _, _, _, _, _, _, .map _ _ l _ body k => l.nodes + body.exprNodes + k.exprNodes
  | _, _, _, _, _, _, .foldl _ _ l _ init _ body k =>
      l.nodes + init.nodes + body.exprNodes + k.exprNodes
  | _, _, _, _, _, _, .join _ _ body m => body.exprNodes + m.exprNodes
  | _, _, _, _, _, _, .joinrec _ _ _ _ body m => body.exprNodes + m.exprNodes
  | _, _, _, _, _, _, .jump _ p _ _ _ => p.nodes

/-- Sum of a measure over the bodies of the global functions. -/
def Globals.sumBodies (m : ∀ {GL : List Fn} {Γ : List Ty} {G : Env Γ → Prop}
    {sf : Option (Self Γ)} {t : Ty} {Q : Env Γ → t.denote → Prop} {js : JScope Γ t},
    Expr GL Γ G sf t Q js → Nat) : {GL : List Fn} → Globals GL → Nat
  | _, .nil => 0
  | _, .defn gs _ _ _ body => gs.sumBodies m + m body

/-- The number of statement nodes of a program (main statement and global functions). -/
def PTerm.size {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.size + t.globals.sumBodies Expr.size

/-- The number of (non-recursive) `join` nodes of a program. -/
def PTerm.joins {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.joins + t.globals.sumBodies Expr.joins

/-- The number of recursive join points (loops) of a program. -/
def PTerm.loops {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.loops + t.globals.sumBodies Expr.loops

/-- The number of calls of global functions of a program. -/
def PTerm.gcalls {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.gcalls + t.globals.sumBodies Expr.gcalls

/-- The number of `map` nodes of a program. -/
def PTerm.maps {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.maps + t.globals.sumBodies Expr.maps

/-- The number of pure `let` nodes (shared values) of a program. -/
def PTerm.lets {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.lets + t.globals.sumBodies Expr.lets

/-- The total number of nodes of the call-free expressions of a program. -/
def PTerm.exprNodes {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.main.exprNodes + t.globals.sumBodies Expr.exprNodes

/-- The number of global functions of a program. -/
def PTerm.nglobals {s : Sig} {pre : Env s.args → Prop} {post : Env s.args → s.ret.denote → Prop}
    (t : PTerm s pre post) : Nat :=
  t.globals.size

end WFLang.PCL
