module
public import LeanScript.Ty.TyWfIn
public import LeanScript.DeBruijn
@[expose] public section

namespace LeanScript

/-!
# Contexts, variables and the signature of a module

What a term is written against: its context `Ctx` (the types in scope, each a `TyWf`), the
typed de Bruijn variables `Var Γ τ` into it (with the notation `Γ ∋ τ` and the sugar
`v♯n`), and the module's top-level declarations — `GlobalDecl`, the signature `Sig` and
the references `GlobalRef` to them.
-/

/-! ## Variables -/

/-- The types of the values in scope, innermost first.  A context holds **types of
    the language**: a tree together with the proof that it is one. -/
abbrev Ctx := List TyWf

/-- A variable: a de Bruijn index into the context, carrying the type it is bound at. -/
abbrev Var (Γ : Ctx) (τ : TyWf) : Type := DeBruijn Γ τ

/-- The variable just bound. -/
abbrev Var.head {Γ : Ctx} {τ : TyWf} : Var (τ :: Γ) τ := DeBruijn.head

/-- A variable bound further out. -/
abbrev Var.tail {Γ : Ctx} {τ1 τ2 : TyWf} (v : Var Γ τ1) : Var (τ2 :: Γ) τ1 :=
  DeBruijn.tail v

/-- Membership notation: `Γ ∋ τ`. -/
infix:40 " ∋ " => Var

/-- Expand a natural number literal into nested `Var.tail` / `Var.head`. -/
syntax "var_get_elem" (ppSpace term) : term
macro_rules | `(term| var_get_elem $n) => match n.1.toNat with
| 0     => `(term| DeBruijn.head)
| n + 1 => `(term| DeBruijn.tail (var_get_elem $(Lean.quote n)))

/-- Sugar: `v♯0` is `Var.head`, `v♯1` is `Var.tail Var.head`, … -/
macro "v♯" n:term:90 : term => `(var_get_elem $n)

/-- The de Bruijn index of a variable: how many binders out it is. -/
abbrev Var.index {Γ : Ctx} {τ : TyWf} (v : Var Γ τ) : Nat := DeBruijn.index v

/-! ## The signature of a module

A `Term` is written against a fixed list of top-level declarations — the ones the
compiled module binds, plus the ones it imports from the runtime.  A reference to one of
them is a `GlobalRef`, an index into that list, so the *name* and the *type* of a global
are read off the signature rather than written at the use site.
-/

/-- One top-level declaration a term may refer to: the name it is bound to, and its
    type.

    There is deliberately **no** `isInlined` field: whether a declaration is inlined is a
    property of the *translation* into this language, not of the language, and an
    inlined declaration simply does not reach a signature. -/
structure GlobalDecl where
  /-- The identifier the declaration is bound to. -/
  name : String
  /-- Its type. -/
  ty : TyWf
  -- `LeanScript.Ty.beq` is the equality of trees (`LeanScript.Ty.TyBEq`), so a
  -- declaration has a decidable equality and its `==` is that equality.
  deriving BEq, DecidableEq, ReflBEq, LawfulBEq, Repr

/-- The signature of the module being compiled: every top-level name a `Term` of it may
    mention, **each of them declared once**.  The proof is a field, so a signature that
    declares a name twice cannot be built.  "Declared once" is the library's `List.Nodup`
    of the names, which is decidable, so `by decide` discharges it for a signature written
    out. -/
structure Sig where
  /-- The declarations, in order. -/
  decls : List GlobalDecl
  /-- No name is declared twice. -/
  h_names_unique : (decls.map GlobalDecl.name).Nodup := by decide
  deriving BEq, DecidableEq, ReflBEq, LawfulBEq, Repr

/-- A reference to a declaration of the signature — a de Bruijn index into it, whose
    type is the one the signature gives it.  There is no other way to name a global, so
    a `Term` cannot call a name that is not declared, nor call a declared one at a type
    it does not have. -/
abbrev GlobalRef (ds : List GlobalDecl) (τ : TyWf) : Type :=
  DeBruijnProj GlobalDecl.ty ds τ

/-- The declaration just bound. -/
@[match_pattern] abbrev GlobalRef.here {g : GlobalDecl} {ds : List GlobalDecl} :
    GlobalRef (g :: ds) g.ty := DeBruijnProj.head

/-- A declaration bound further out. -/
@[match_pattern] abbrev GlobalRef.there {g : GlobalDecl} {ds : List GlobalDecl} {τ : TyWf}
    (r : GlobalRef ds τ) : GlobalRef (g :: ds) τ := DeBruijnProj.tail r

/-- The name a reference resolves to: the name of the declaration it points at. -/
def GlobalRef.name {ds : List GlobalDecl} {τ : TyWf} (r : GlobalRef ds τ) : String :=
  r.entry.name

@[simp] theorem GlobalRef.name_here {g : GlobalDecl} {ds : List GlobalDecl} :
    (GlobalRef.here (g := g) (ds := ds)).name = g.name := rfl

@[simp] theorem GlobalRef.name_there {g : GlobalDecl} {ds : List GlobalDecl} {τ : TyWf}
    (r : GlobalRef ds τ) : (GlobalRef.there (g := g) r).name = r.name := rfl
