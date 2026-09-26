import RequestProject.WFLang.Core.PExpr
import Mathlib.Control.Traversable.Lemmas

/-!
# Functorial and traversable structure of the grammar

None of the grammar datatypes is a type constructor `Type u → Type v`: they are families
indexed by object types (`Ty`) and contexts (`List Ty`), and their only "contents" are the
variables of the context.  So Lean's `Functor` / `Traversable` classes (which need a type
constructor) cannot be instantiated; this file gives the corresponding structure over the
variables instead:

* `PExpr.rename` / `PExprs.rename` : map a renaming `∀ {t}, Var Γ t → Var Δ t` over an
  expression (the `Functor.map` analogue), with the functor laws `rename_id` and
  `rename_rename` (the `LawfulFunctor` analogue), `wk_eq_rename` (weakening is a renaming),
  and the semantic law `eval_rename`;
* `PExpr.traverseVars` / `PExprs.traverseVars` : effectful renaming in any applicative functor
  (the `Traversable.traverse` analogue), with the `LawfulTraversable` laws:
  `traverseVars_id` (identity), `traverseVars_comp` (composition), `traverseVars_pure`
  (`traverse` of pure functions is `map`) and `traverseVars_naturality` (naturality in the
  applicative functor).

The decidable-equality and printing instances (`DecidableEq`, hence `BEq`, `ReflBEq`,
`LawfulBEq`; `Repr`, `Hashable`, hence `LawfulHashable`) are derived at the definitions of the
datatypes; `Inhabited` / `IsEmpty` instances are given here.
-/

namespace WFLang

universe u

/-! ## Inhabitedness -/

/-- Every expression type is inhabited, by the literal `default`. -/
instance PExpr.instInhabited {Γ : List Ty} {t : Ty} : Inhabited (PExpr Γ t) :=
  ⟨.lit t t.default⟩

/-- The argument tuple made of the literals `default`. -/
def PExprs.defaults {Γ : List Ty} : (ts : List Ty) → PExprs Γ ts
  | [] => .nil
  | t :: ts => .cons (.lit t t.default) (PExprs.defaults ts)

/-- Every argument-tuple type is inhabited, by literals. -/
instance PExprs.instInhabited {Γ : List Ty} {ts : List Ty} : Inhabited (PExprs Γ ts) :=
  ⟨PExprs.defaults ts⟩

/-- There is no variable in the empty context. -/
instance Var.instIsEmptyNil {t : Ty} : IsEmpty (Var [] t) := ⟨nofun⟩

/-! ## Renaming (the functor structure) -/

/-- Rename the variables of an expression. -/
def PExpr.rename {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) :
    {t : Ty} → PExpr Γ t → PExpr Δ t
  | _, .var v => .var (f v)
  | _, .lit t v => .lit t v
  | _, .bin op a b => .bin op (a.rename f) (b.rename f)
  | _, .not a => .not (a.rename f)
  | _, .un op a => .un op (a.rename f)
  | _, .ite c a b => .ite (c.rename f) (a.rename f) (b.rename f)

/-- Rename the variables of an argument tuple. -/
def PExprs.rename {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) :
    {ts : List Ty} → PExprs Γ ts → PExprs Δ ts
  | _, .nil => .nil
  | _, .cons a as => .cons (a.rename f) (as.rename f)

/-- Functor law: renaming by the identity. -/
@[simp] theorem PExpr.rename_id {Γ : List Ty} :
    ∀ {t : Ty} (e : PExpr Γ t), e.rename (fun v => v) = e
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, .bin _ a b => by simp only [rename, rename_id a, rename_id b]
  | _, .not a => by simp only [rename, rename_id a]
  | _, .un _ a => by simp only [rename, rename_id a]
  | _, .ite c a b => by simp only [rename, rename_id c, rename_id a, rename_id b]

/-- Functor law: renaming twice is renaming by the composite. -/
@[simp] theorem PExpr.rename_rename {Γ Δ Θ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t)
    (g : ∀ {t : Ty}, Var Δ t → Var Θ t) :
    ∀ {t : Ty} (e : PExpr Γ t), (e.rename f).rename g = e.rename (fun v => g (f v))
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, .bin _ a b => by simp only [rename, rename_rename f g a, rename_rename f g b]
  | _, .not a => by simp only [rename, rename_rename f g a]
  | _, .un _ a => by simp only [rename, rename_rename f g a]
  | _, .ite c a b => by
    simp only [rename, rename_rename f g c, rename_rename f g a, rename_rename f g b]

@[simp] theorem PExprs.rename_id {Γ : List Ty} :
    ∀ {ts : List Ty} (e : PExprs Γ ts), e.rename (fun v => v) = e
  | _, .nil => rfl
  | _, .cons a as => by simp only [rename, PExpr.rename_id, rename_id as]

@[simp] theorem PExprs.rename_rename {Γ Δ Θ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t)
    (g : ∀ {t : Ty}, Var Δ t → Var Θ t) :
    ∀ {ts : List Ty} (e : PExprs Γ ts), (e.rename f).rename g = e.rename (fun v => g (f v))
  | _, .nil => rfl
  | _, .cons a as => by simp only [rename, PExpr.rename_rename, rename_rename f g as]

/-- Weakening is the renaming by `Var.there`. -/
theorem PExpr.wk_eq_rename {s : Ty} {Γ : List Ty} :
    ∀ {t : Ty} (e : PExpr Γ t), e.wk (s := s) = e.rename Var.there
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, .bin _ a b => by simp only [wk, rename, wk_eq_rename a, wk_eq_rename b]
  | _, .not a => by simp only [wk, rename, wk_eq_rename a]
  | _, .un _ a => by simp only [wk, rename, wk_eq_rename a]
  | _, .ite c a b => by simp only [wk, rename, wk_eq_rename c, wk_eq_rename a, wk_eq_rename b]

theorem PExprs.wk_eq_rename {s : Ty} {Γ : List Ty} :
    ∀ {ts : List Ty} (e : PExprs Γ ts), e.wk (s := s) = e.rename Var.there
  | _, .nil => rfl
  | _, .cons a as => by simp only [wk, rename, PExpr.wk_eq_rename, wk_eq_rename as]

/-- Semantics of renaming: evaluating a renamed expression in `ρ` is evaluating the original
in any environment `σ` that agrees with `ρ` along the renaming. -/
theorem PExpr.eval_rename {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) (ρ : Env Δ)
    (σ : Env Γ) (h : ∀ {t : Ty} (v : Var Γ t), (f v).get ρ = v.get σ) :
    ∀ {t : Ty} (e : PExpr Γ t), (e.rename f).eval ρ = e.eval σ
  | _, .var v => h v
  | _, .lit _ _ => rfl
  | _, .bin _ a b => by simp only [rename, eval, eval_rename f ρ σ h a, eval_rename f ρ σ h b]
  | _, .not a => by simp only [rename, eval, eval_rename f ρ σ h a]
  | _, .un _ a => by simp only [rename, eval, eval_rename f ρ σ h a]
  | _, .ite c a b => by
    simp only [rename, eval, eval_rename f ρ σ h c, eval_rename f ρ σ h a,
      eval_rename f ρ σ h b]

theorem PExprs.eval_rename {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) (ρ : Env Δ)
    (σ : Env Γ) (h : ∀ {t : Ty} (v : Var Γ t), (f v).get ρ = v.get σ) :
    ∀ {ts : List Ty} (e : PExprs Γ ts), (e.rename f).eval ρ = e.eval σ
  | _, .nil => rfl
  | _, .cons a as => by
    simp only [rename, eval, PExpr.eval_rename f ρ σ h a, eval_rename f ρ σ h as]

/-! ## Traversal (the traversable structure) -/

/-- Effectful renaming: traverse the variables of an expression, left to right, in an
applicative functor. -/
def PExpr.traverseVars {m : Type → Type u} [Applicative m] {Γ Δ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) : {t : Ty} → PExpr Γ t → m (PExpr Δ t)
  | _, .var v => PExpr.var <$> f v
  | _, .lit t v => pure (.lit t v)
  | _, .bin op a b => PExpr.bin op <$> a.traverseVars f <*> b.traverseVars f
  | _, .not a => PExpr.not <$> a.traverseVars f
  | _, .un op a => PExpr.un op <$> a.traverseVars f
  | _, .ite c a b => PExpr.ite <$> c.traverseVars f <*> a.traverseVars f <*> b.traverseVars f

/-- Effectful renaming of an argument tuple. -/
def PExprs.traverseVars {m : Type → Type u} [Applicative m] {Γ Δ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) : {ts : List Ty} → PExprs Γ ts → m (PExprs Δ ts)
  | _, .nil => pure .nil
  | _, .cons a as => PExprs.cons <$> a.traverseVars f <*> as.traverseVars f

section Laws

variable {m : Type → Type u} [Applicative m] [LawfulApplicative m]

/-- Traversing with pure functions is renaming. -/
theorem PExpr.traverseVars_pure {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) :
    ∀ {t : Ty} (e : PExpr Γ t),
      e.traverseVars (m := m) (fun v => pure (f v)) = pure (e.rename f)
  | _, .var _ => by simp [traverseVars, rename]
  | _, .lit _ _ => rfl
  | _, .bin _ a b => by
    simp [traverseVars, rename, traverseVars_pure f a, traverseVars_pure f b]
  | _, .not a => by simp [traverseVars, rename, traverseVars_pure f a]
  | _, .un _ a => by simp [traverseVars, rename, traverseVars_pure f a]
  | _, .ite c a b => by
    simp [traverseVars, rename, traverseVars_pure f c, traverseVars_pure f a,
      traverseVars_pure f b]

theorem PExprs.traverseVars_pure {Γ Δ : List Ty} (f : ∀ {t : Ty}, Var Γ t → Var Δ t) :
    ∀ {ts : List Ty} (e : PExprs Γ ts),
      e.traverseVars (m := m) (fun v => pure (f v)) = pure (e.rename f)
  | _, .nil => rfl
  | _, .cons a as => by
    simp [traverseVars, rename, PExpr.traverseVars_pure f a, traverseVars_pure f as]

/-- Identity law. -/
theorem PExpr.traverseVars_id {Γ : List Ty} {t : Ty} (e : PExpr Γ t) :
    e.traverseVars (m := Id) (fun v => pure v) = pure e := by
  rw [traverseVars_pure (fun v => v), rename_id]

theorem PExprs.traverseVars_id {Γ : List Ty} {ts : List Ty} (e : PExprs Γ ts) :
    e.traverseVars (m := Id) (fun v => pure v) = pure e := by
  rw [traverseVars_pure (fun v => v), rename_id]

/-- Naturality law: an applicative transformation commutes with traversal. -/
theorem PExpr.traverseVars_naturality {n : Type → Type u} [Applicative n] [LawfulApplicative n]
    (η : ApplicativeTransformation m n) {Γ Δ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) :
    ∀ {t : Ty} (e : PExpr Γ t),
      η (e.traverseVars f) = e.traverseVars (fun v => η (f v))
  | _, .var _ => by simp [traverseVars, functor_norm]
  | _, .lit _ _ => by simp [traverseVars, functor_norm]
  | _, .bin _ a b => by
    simp [traverseVars, functor_norm, traverseVars_naturality η f a,
      traverseVars_naturality η f b]
  | _, .not a => by simp [traverseVars, functor_norm, traverseVars_naturality η f a]
  | _, .un _ a => by simp [traverseVars, functor_norm, traverseVars_naturality η f a]
  | _, .ite c a b => by
    simp [traverseVars, functor_norm, traverseVars_naturality η f c,
      traverseVars_naturality η f a, traverseVars_naturality η f b]

theorem PExprs.traverseVars_naturality {n : Type → Type u} [Applicative n]
    [LawfulApplicative n] (η : ApplicativeTransformation m n) {Γ Δ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) :
    ∀ {ts : List Ty} (e : PExprs Γ ts),
      η (e.traverseVars f) = e.traverseVars (fun v => η (f v))
  | _, .nil => by simp [traverseVars, functor_norm]
  | _, .cons a as => by
    simp [traverseVars, functor_norm, PExpr.traverseVars_naturality η f a,
      traverseVars_naturality η f as]

/-- Composition law: traversing with `f` and then with `g` is a single traversal in the
composite applicative functor `Functor.Comp m n`. -/
theorem PExpr.traverseVars_comp {n : Type → Type} [Applicative n] [LawfulApplicative n]
    {m : Type → Type} [Applicative m] [LawfulApplicative m] {Γ Δ Θ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) (g : ∀ {t : Ty}, Var Δ t → n (Var Θ t)) :
    ∀ {t : Ty} (e : PExpr Γ t),
      e.traverseVars (m := Functor.Comp m n) (fun v => Functor.Comp.mk (g <$> f v)) =
        Functor.Comp.mk (PExpr.traverseVars g <$> e.traverseVars f)
  | _, .var _ => by simp [traverseVars, functor_norm]
  | _, .lit _ _ => by simp [traverseVars, functor_norm]; rfl
  | _, .bin _ a b => by
    simp [traverseVars, functor_norm, traverseVars_comp f g a, traverseVars_comp f g b]; rfl
  | _, .not a => by simp [traverseVars, functor_norm, traverseVars_comp f g a]
  | _, .un _ a => by simp [traverseVars, functor_norm, traverseVars_comp f g a]
  | _, .ite c a b => by
    simp [traverseVars, functor_norm, traverseVars_comp f g c, traverseVars_comp f g a,
      traverseVars_comp f g b]; rfl

theorem PExprs.traverseVars_comp {n : Type → Type} [Applicative n] [LawfulApplicative n]
    {m : Type → Type} [Applicative m] [LawfulApplicative m] {Γ Δ Θ : List Ty}
    (f : ∀ {t : Ty}, Var Γ t → m (Var Δ t)) (g : ∀ {t : Ty}, Var Δ t → n (Var Θ t)) :
    ∀ {ts : List Ty} (e : PExprs Γ ts),
      e.traverseVars (m := Functor.Comp m n) (fun v => Functor.Comp.mk (g <$> f v)) =
        Functor.Comp.mk (PExprs.traverseVars g <$> e.traverseVars f)
  | _, .nil => by simp [traverseVars, functor_norm]; rfl
  | _, .cons a as => by
    simp [traverseVars, functor_norm, PExpr.traverseVars_comp f g a,
      traverseVars_comp f g as]; rfl

end Laws

end WFLang
