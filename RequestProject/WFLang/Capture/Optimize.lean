import RequestProject.WFLang.Capture.Meta

/-!
# The optimiser of the capture: call-free expressions in optimised normal form

The translation of a Lean term into a call-free `PExpr` goes through a small meta-level
representation `PE`, built only by the *smart constructors* `PE.mkBin`, `PE.mkNot`, `PE.mkUn`,
`PE.mkIte`.  They perform, while the expression is built:

* **constant folding**: an operator applied to literals is evaluated (`2 + 3` becomes `5`,
  `(1, [2]).2 ++ [3]` becomes `[2, 3]`, `decide (3 < 5)` becomes `true`);
* **algebraic identities**: `x + 0`, `x * 1`, `x * 0`, `x - 0`, `0 - x`, `x / 1`, `x % 1`,
  `x ^ 0`, `x ^ 1`, `1 ^ x`, `b && true`, `b && false`, `b || true`, `b || false`,
  `xor b true`, `l ++ []`, … (both orders where they hold, and on `Int`);
* **unary simplifications**: `!!b = b`, `- - i = i`, `(a, b).1 = a`, `(a, b).2 = b`;
* **branches**: `if true`/`if false` keep one branch, `if !c then a else b` becomes
  `if c then b else a`, `if c then true else false` becomes `c` (and `!c` for the swapped
  literals), and `if c then v else v` becomes `v`.

Every expression they build is in the normal form `PExpr.isNF` of `Core/Normal.lean`, so the
proofs `(by decide)` that the statements of `PCL.Expr` require always succeed.  All these
rewrites are equations of Lean's `Nat`/`Int`/`Bool`/`List` operations (the same ones `simp`
knows), so the agreement proofs are unaffected.
-/

namespace WFLang.Translate

open Lean Meta Elab Term

/-- Literal values of the object types. -/
inductive LitVal where
  | nat (n : Nat)
  | int (i : Int)
  | bool (b : Bool)
  /-- a list literal, with the object type (`WFLang.Ty` expression) of its elements -/
  | list (elemTy : Lean.Expr) (xs : List LitVal)
  | pair (a b : LitVal)
  deriving Inhabited

namespace LitVal

/-- The object type of a literal (a `WFLang.Ty` expression). -/
partial def ty : LitVal → Lean.Expr
  | .nat _ => mkConst ``WFLang.Ty.nat
  | .int _ => mkConst ``WFLang.Ty.int
  | .bool _ => mkConst ``WFLang.Ty.bool
  | .list t _ => mkApp (mkConst ``WFLang.Ty.list) t
  | .pair a b => mkApp2 (mkConst ``WFLang.Ty.prod) a.ty b.ty

/-- Equality of literal values. -/
partial def eqv : LitVal → LitVal → Bool
  | .nat a, .nat b => a == b
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .list _ xs, .list _ ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => eqv x y
  | .pair a b, .pair c d => eqv a c && eqv b d
  | _, _ => false

/-- The default value (`WFLang.Ty.default`) of an object type. -/
partial def default (t : Lean.Expr) : Option LitVal :=
  if t.isConstOf ``WFLang.Ty.nat then some (.nat 0)
  else if t.isConstOf ``WFLang.Ty.int then some (.int 0)
  else if t.isConstOf ``WFLang.Ty.bool then some (.bool false)
  else if t.isAppOfArity ``WFLang.Ty.list 1 then some (.list (t.getArg! 0) [])
  else if t.isAppOfArity ``WFLang.Ty.prod 2 then
    return .pair (← default (t.getArg! 0)) (← default (t.getArg! 1))
  else none

end LitVal

/-- A binary operator: its `WFLang.BinOp` constructor and its syntax. -/
structure BOp where
  name : Name
  stx : TSyntax `term

/-- A unary operator: its `WFLang.UnOp` constructor and its syntax. -/
structure UOp where
  name : Name
  stx : TSyntax `term

/-- Meta-level call-free expressions, as the translation builds them. -/
inductive PE where
  /-- the de Bruijn variable `i` -/
  | var (i : Nat)
  | lit (v : LitVal)
  | bin (op : BOp) (a b : PE)
  | not (a : PE)
  | un (op : UOp) (a : PE)
  | ite (c a b : PE)
  /-- an expression given by its syntax (padding with default values), never simplified -/
  | raw (stx : TSyntax `term)
  deriving Inhabited

namespace PE

def natLit (n : Nat) : PE := .lit (.nat n)
def boolLit (b : Bool) : PE := .lit (.bool b)

/-- Is it the literal `v`? -/
def isLitOf (e : PE) (v : LitVal) : Bool :=
  match e with
  | .lit w => w.eqv v
  | _ => false

def isNatLit (e : PE) (n : Nat) : Bool := e.isLitOf (.nat n)
def isIntLit (e : PE) (i : Int) : Bool := e.isLitOf (.int i)
def isNil (e : PE) : Bool :=
  match e with
  | .lit (.list _ []) => true
  | _ => false

/-- The value of a binary operator on literals. -/
def evalBin (op : Name) (a b : LitVal) : Option LitVal :=
  match op, a, b with
  | ``WFLang.BinOp.add, .nat x, .nat y => some (.nat (x + y))
  | ``WFLang.BinOp.sub, .nat x, .nat y => some (.nat (x - y))
  | ``WFLang.BinOp.mul, .nat x, .nat y => some (.nat (x * y))
  | ``WFLang.BinOp.div, .nat x, .nat y => some (.nat (x / y))
  | ``WFLang.BinOp.mod, .nat x, .nat y => some (.nat (x % y))
  | ``WFLang.BinOp.lt, .nat x, .nat y => some (.bool (decide (x < y)))
  | ``WFLang.BinOp.le, .nat x, .nat y => some (.bool (decide (x ≤ y)))
  | ``WFLang.BinOp.beq, x, y => some (.bool (x.eqv y))
  | ``WFLang.BinOp.and, .bool x, .bool y => some (.bool (x && y))
  | ``WFLang.BinOp.or, .bool x, .bool y => some (.bool (x || y))
  | ``WFLang.BinOp.bxor, .bool x, .bool y => some (.bool (Bool.xor x y))
  | ``WFLang.BinOp.pow, .nat x, .nat y => if y ≤ 256 then some (.nat (x ^ y)) else none
  | ``WFLang.BinOp.shiftLeft, .nat x, .nat y => if y ≤ 256 then some (.nat (x <<< y)) else none
  | ``WFLang.BinOp.shiftRight, .nat x, .nat y => some (.nat (x >>> y))
  | ``WFLang.BinOp.land, .nat x, .nat y => some (.nat (x &&& y))
  | ``WFLang.BinOp.lor, .nat x, .nat y => some (.nat (x ||| y))
  | ``WFLang.BinOp.xor, .nat x, .nat y => some (.nat (x ^^^ y))
  | ``WFLang.BinOp.gcd, .nat x, .nat y => some (.nat (Nat.gcd x y))
  | ``WFLang.BinOp.lcm, .nat x, .nat y => some (.nat (Nat.lcm x y))
  | ``WFLang.BinOp.iadd, .int x, .int y => some (.int (x + y))
  | ``WFLang.BinOp.isub, .int x, .int y => some (.int (x - y))
  | ``WFLang.BinOp.imul, .int x, .int y => some (.int (x * y))
  | ``WFLang.BinOp.idiv, .int x, .int y => some (.int (x / y))
  | ``WFLang.BinOp.imod, .int x, .int y => some (.int (x % y))
  | ``WFLang.BinOp.ilt, .int x, .int y => some (.bool (decide (x < y)))
  | ``WFLang.BinOp.ile, .int x, .int y => some (.bool (decide (x ≤ y)))
  | ``WFLang.BinOp.pair, x, y => some (.pair x y)
  | ``WFLang.BinOp.cons, x, .list t xs => some (.list t (x :: xs))
  | ``WFLang.BinOp.append, .list t xs, .list _ ys => some (.list t (xs ++ ys))
  | _, _, _ => none

/-- The value of a unary operator on a literal. -/
def evalUn (op : Name) (a : LitVal) : Option LitVal :=
  match op, a with
  | ``WFLang.UnOp.log2, .nat x => some (.nat (Nat.log2 x))
  | ``WFLang.UnOp.ineg, .int x => some (.int (-x))
  | ``WFLang.UnOp.toNat, .int x => some (.nat x.toNat)
  | ``WFLang.UnOp.natAbs, .int x => some (.nat x.natAbs)
  | ``WFLang.UnOp.ofNat, .nat x => some (.int x)
  | ``WFLang.UnOp.fst, .pair x _ => some x
  | ``WFLang.UnOp.snd, .pair _ y => some y
  | ``WFLang.UnOp.head, .list t [] => LitVal.default t
  | ``WFLang.UnOp.head, .list _ (x :: _) => some x
  | ``WFLang.UnOp.tail, .list t xs => some (.list t xs.tail)
  | ``WFLang.UnOp.isNil, .list _ xs => some (.bool xs.isEmpty)
  | ``WFLang.UnOp.length, .list _ xs => some (.nat xs.length)
  | _, _ => none

/-- `!a`, simplified. -/
def mkNot (a : PE) : PE :=
  match a with
  | .lit (.bool b) => .lit (.bool !b)
  | .not x => x
  | _ => .not a

/-- `op a b`, simplified (constant folding and algebraic identities). -/
def mkBin (op : BOp) (a b : PE) : PE := Id.run do
  if let (.lit x, .lit y) := (a, b) then
    if let some v := evalBin op.name x y then return .lit v
  match op.name with
  | ``WFLang.BinOp.add =>
    if a.isNatLit 0 then return b
    if b.isNatLit 0 then return a
  | ``WFLang.BinOp.sub =>
    if b.isNatLit 0 then return a
    if a.isNatLit 0 then return natLit 0
  | ``WFLang.BinOp.mul =>
    if a.isNatLit 0 || b.isNatLit 0 then return natLit 0
    if a.isNatLit 1 then return b
    if b.isNatLit 1 then return a
  | ``WFLang.BinOp.div =>
    if b.isNatLit 1 then return a
    if a.isNatLit 0 || b.isNatLit 0 then return natLit 0
  | ``WFLang.BinOp.mod =>
    if b.isNatLit 0 then return a
    if a.isNatLit 0 || b.isNatLit 1 then return natLit 0
  | ``WFLang.BinOp.pow =>
    if b.isNatLit 1 then return a
    if a.isNatLit 1 || b.isNatLit 0 then return natLit 1
  | ``WFLang.BinOp.and =>
    if a.isLitOf (.bool true) then return b
    if b.isLitOf (.bool true) then return a
    if a.isLitOf (.bool false) || b.isLitOf (.bool false) then return boolLit false
  | ``WFLang.BinOp.or =>
    if a.isLitOf (.bool false) then return b
    if b.isLitOf (.bool false) then return a
    if a.isLitOf (.bool true) || b.isLitOf (.bool true) then return boolLit true
  | ``WFLang.BinOp.bxor =>
    if a.isLitOf (.bool false) then return b
    if b.isLitOf (.bool false) then return a
    if a.isLitOf (.bool true) then return mkNot b
    if b.isLitOf (.bool true) then return mkNot a
  | ``WFLang.BinOp.iadd =>
    if a.isIntLit 0 then return b
    if b.isIntLit 0 then return a
  | ``WFLang.BinOp.isub => if b.isIntLit 0 then return a
  | ``WFLang.BinOp.imul =>
    if a.isIntLit 0 || b.isIntLit 0 then return .lit (.int 0)
    if a.isIntLit 1 then return b
    if b.isIntLit 1 then return a
  | ``WFLang.BinOp.append =>
    if a.isNil then return b
    if b.isNil then return a
  | _ => pure ()
  return .bin op a b

/-- `op a`, simplified. -/
def mkUn (op : UOp) (a : PE) : PE := Id.run do
  if let .lit x := a then
    if let some v := evalUn op.name x then return .lit v
  match op.name, a with
  | ``WFLang.UnOp.fst, .bin p x _ => if p.name == ``WFLang.BinOp.pair then return x
  | ``WFLang.UnOp.snd, .bin p _ y => if p.name == ``WFLang.BinOp.pair then return y
  | ``WFLang.UnOp.ineg, .un o x => if o.name == ``WFLang.UnOp.ineg then return x
  | _, _ => pure ()
  return .un op a

/-- `if c then a else b`, simplified. -/
partial def mkIte (c a b : PE) : PE := Id.run do
  match c with
  | .lit (.bool true) => return a
  | .lit (.bool false) => return b
  | .not c' => return mkIte c' b a
  | _ => pure ()
  if let (.lit x, .lit y) := (a, b) then
    if x.eqv y then return a
    if let (.bool true, .bool false) := (x, y) then return c
    if let (.bool false, .bool true) := (x, y) then return mkNot c
  return .ite c a b

/-- An object type (a `WFLang.Ty` expression) as syntax. -/
partial def tyExprStx (t : Lean.Expr) : MetaM (TSyntax `term) := do
  if t.isConstOf ``WFLang.Ty.nat then return ← `(WFLang.Ty.nat)
  if t.isConstOf ``WFLang.Ty.bool then return ← `(WFLang.Ty.bool)
  if t.isConstOf ``WFLang.Ty.int then return ← `(WFLang.Ty.int)
  if t.isAppOfArity ``WFLang.Ty.prod 2 then
    return ← `(WFLang.Ty.prod $(← tyExprStx (t.getArg! 0)) $(← tyExprStx (t.getArg! 1)))
  if t.isAppOfArity ``WFLang.Ty.list 1 then
    return ← `(WFLang.Ty.list $(← tyExprStx (t.getArg! 0)))
  throwError "#lean_wf_func_to_term: unexpected object type {t}"

/-- The Lean value of a literal, as syntax. -/
partial def _root_.WFLang.Translate.LitVal.valStx : LitVal → MetaM (TSyntax `term)
  | .nat n => `(($(quote n) : Nat))
  | .int i => if i < 0 then `((-($(quote i.natAbs) : Int))) else `(($(quote i.natAbs) : Int))
  | .bool true => `(true)
  | .bool false => `(false)
  | .list t xs => do
    let mut acc ← `(@List.nil (WFLang.Ty.denote $(← tyExprStx t)))
    for x in xs.reverse do
      acc ← `(List.cons $(← x.valStx) $acc)
    return acc
  | .pair a b => do `(Prod.mk $(← a.valStx) $(← b.valStx))

/-- Syntax of a de Bruijn variable. -/
def varStx : Nat → MetaM (TSyntax `term)
  | 0 => `(WFLang.Var.here)
  | i + 1 => do `(WFLang.Var.there $(← varStx i))

/-- The `PExpr` syntax of an expression. -/
partial def render : PE → MetaM (TSyntax `term)
  | .var i => do `(WFLang.PExpr.var $(← varStx i))
  | .lit (.nat n) => `(WFLang.PExpr.lit WFLang.Ty.nat $(quote n))
  | .lit (.bool true) => `(WFLang.PExpr.lit WFLang.Ty.bool true)
  | .lit (.bool false) => `(WFLang.PExpr.lit WFLang.Ty.bool false)
  | .lit v => do `(WFLang.PExpr.lit $(← tyExprStx v.ty) $(← v.valStx))
  | .bin op a b => do `(WFLang.PExpr.bin $(op.stx) $(← render a) $(← render b))
  | .not a => do `(WFLang.PExpr.not $(← render a))
  | .un op a => do `(WFLang.PExpr.un $(op.stx) $(← render a))
  | .ite c a b => do `(WFLang.PExpr.ite $(← render c) $(← render a) $(← render b))
  | .raw s => pure s

end PE

end WFLang.Translate
