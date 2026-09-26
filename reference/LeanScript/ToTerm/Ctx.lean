module

public meta import LeanScript.ToTerm.TyView

@[expose] public section

meta section

/-!
# Where a translation stands

The context of a translation — the signature it runs against, the binders it has entered
and the de Bruijn index each of them reads as — and the reader of a signature.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The context a translation runs in -/

/-- One declaration of the signature: the name it is bound to, its tree, and the
    reference that names it. -/
structure GlobalEntry where
  /-- The identifier the declaration is bound to. -/
  name : String
  /-- Its tree. -/
  ty : Expr
  /-- The `LeanScript.GlobalRef` that points at it. -/
  ref : Expr
  deriving BEq, Repr

/-- Where a translation stands: the signature, the context it started in, and the
    binders it has entered since. -/
structure TCtx where
  /-- The signature, as an expression. -/
  sg : Expr
  /-- The declarations of the signature. -/
  globals : Array GlobalEntry
  /-- The context the translation started in, as an expression. -/
  base : Expr
  /-- The binders entered since, **outermost first**, each with its tree. -/
  binders : Array (FVarId × Expr) := #[]
  /-- The inductives whose fold the translation is inside the branches of.  A `match` on
      a value of one of them is the fold's own look further down, never a `…_casesOn`
      (`LeanScript.ToTerm.TransRecCases`), so that the depth of a fold is how far its
      branches read and does not change with how Lean happened to compile them. -/
  foldInds : Array Name := #[]
  deriving BEq, Repr

/-- The context of the translation, as an expression: the binders entered, innermost
    first, in front of the context it started in. -/
def TCtx.gamma (c : TCtx) : Expr :=
  c.binders.foldl (init := c.base) fun acc (_, t) => consCtxE t acc

/-- Enter a binder of this tree. -/
def TCtx.push (c : TCtx) (f : FVarId) (t : Expr) : TCtx :=
  { c with binders := c.binders.push (f, t) }

/-- Enter the binders of a branch: `ts` are the trees of the fields it binds, in
    declaration order, so the first field is de Bruijn index `0`. -/
def TCtx.pushFields (c : TCtx) (fs : Array (FVarId × Expr)) : TCtx :=
  { c with binders := c.binders ++ fs.reverse }

/-- The trees of the binders entered, innermost first. -/
def TCtx.binderTys (c : TCtx) : List Expr :=
  (c.binders.map (·.2)).toList.reverse

/-! ## The variables -/

/-- The de Bruijn index `k` of the context `ts ++ base`. -/
partial def mkIndexE (ts : List Expr) (base : Expr) (k : Nat) : MetaM Expr := do
  match ts, k with
  | t :: rest, 0 =>
      return mkAppN (mkConst ``LeanScript.DeBruijnProj.head)
        #[tyE, tyE, idTyE, t, mkCtxE rest base]
  | t :: rest, k + 1 =>
      let some b := rest[k]? | throwError "`#leanscript_to_term`: variable out of range"
      let v ← mkIndexE rest base k
      return mkAppN (mkConst ``LeanScript.DeBruijnProj.tail)
        #[tyE, tyE, idTyE, t, mkCtxE rest base, b, v]
  | [], _ => throwError "`#leanscript_to_term`: variable out of range"

/-- The term that reads the variable `f` of the context. -/
def TCtx.var (c : TCtx) (f : FVarId) : MetaM Expr := do
  let some i := c.binders.findIdx? (fun (g, _) => g == f)
    | throwError "`#leanscript_to_term`: {Expr.fvar f} is not a variable of the \
        translated definition"
  let k := c.binders.size - 1 - i
  let τ := c.binders[i]!.2
  let idx ← mkIndexE c.binderTys c.base k
  return mkAppN (mkConst `LeanScript.Term.var) #[c.sg, c.gamma, τ, idx]

/-! ## The signature -/

/-- Read the declarations of a signature: their names, their trees and the references
    that point at them. -/
def parseSig (sg : Expr) : MetaM (Array GlobalEntry) := do
  let declsE ← whnf (mkApp (mkConst ``LeanScript.Sig.decls) sg)
  -- the cons cells of the list, outermost first
  let mut cells : Array (Expr × Expr) := #[]   -- (head, tail)
  let mut cur := declsE
  repeat
    match (← whnf cur).getAppFnArgs with
    | (``List.cons, #[_, d, ds]) => cells := cells.push (d, ds); cur := ds
    | (``List.nil, _) => break
    | _ => throwError "`#leanscript_to_term`: the signature's declarations are not a \
        list written out: {declsE}"
  let mut out : Array GlobalEntry := #[]
  for i in [0:cells.size] do
    let (d, ds) := cells[i]!
    let dv ← whnf d
    let some (name, ty) ← pure (match dv.getAppFnArgs with
      | (``LeanScript.GlobalDecl.mk, #[n, t]) => some (n, t)
      | _ => none)
      | throwError "`#leanscript_to_term`: a declaration of the signature is not \
          written out: {d}"
    let some nameStr := (match ← whnf name with | .lit (.strVal s) => some s | _ => none)
      | throwError "`#leanscript_to_term`: the name of a declaration is not a string \
          literal: {name}"
    -- the reference: `i` tails around a head
    let mut ref := mkAppN (mkConst ``LeanScript.DeBruijnProj.head)
      #[mkConst ``LeanScript.GlobalDecl, tyE, mkConst ``LeanScript.GlobalDecl.ty, d, ds]
    let tyR ← reduceTy ty
    for j in [0:i] do
      let (d', ds') := cells[i - 1 - j]!
      ref := mkAppN (mkConst ``LeanScript.DeBruijnProj.tail)
        #[mkConst ``LeanScript.GlobalDecl, tyE, mkConst ``LeanScript.GlobalDecl.ty,
          d', ds', tyR, ref]
    out := out.push { name := nameStr, ty := tyR, ref := ref }
  return out

/-- The declaration of the signature a Lean constant stands for, if it declares one: the
    name is matched in full (`Foo.bar`) and by its last component (`bar`). -/
def TCtx.global? (c : TCtx) (n : Name) : Option GlobalEntry :=
  let full := n.toString
  let short := n.getString!
  (c.globals.find? (·.name == full)).orElse fun _ => c.globals.find? (·.name == short)

end LeanScript.ToTerm

end

end
