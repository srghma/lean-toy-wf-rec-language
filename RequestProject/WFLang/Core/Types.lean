import Mathlib.Order.RelClasses

/-!
# Core of `PCL`: types, environments, variables, operators

* object types `Ty` (`nat`, `bool`, `int`, pairs `prod s t`, lists `list t`) and their
  denotation,
* environments `Env Γ` (right-nested tuples) and typed de Bruijn variables `Var Γ t`,
* signatures `Sig` of recursive functions, curried function types `FnType` and
  (un)currying,
* the primitive binary operators `BinOp` (`+ - * / %`, `<`, `≤`, `bool_eq`, `&&`, `||`, and
  more: `^`, shifts, bitwise operators, `gcd`, `lcm`, the same arithmetic on `Int`, pairing,
  `cons`, `++`) and unary operators `UnOp` (`log2`, `Int` negation and conversions,
  projections, `head`, `tail`, `isNil`, `length`, `List.range`, `List.sum`).
-/

namespace WFLang

/-- Object-language types. -/
inductive Ty where
  | nat
  | bool
  | int
  | prod (s t : Ty)
  | list (t : Ty)
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- Denotation of object types. -/
@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .int => Int
  | .prod s t => s.denote × t.denote
  | .list t => List t.denote

/-- Decidable equality of the denotations. -/
instance Ty.decEq : (t : Ty) → DecidableEq t.denote
  | .nat => inferInstanceAs (DecidableEq Nat)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .int => inferInstanceAs (DecidableEq Int)
  | .prod s t => @instDecidableEqProd _ _ (Ty.decEq s) (Ty.decEq t)
  | .list t => @instDecidableEqList _ (Ty.decEq t)

/-- `Repr` of the denotations (used by the derived `Repr` of expressions with literals). -/
instance Ty.instRepr : (t : Ty) → Repr t.denote
  | .nat => inferInstanceAs (Repr Nat)
  | .bool => inferInstanceAs (Repr Bool)
  | .int => inferInstanceAs (Repr Int)
  | .prod s t =>
    letI := Ty.instRepr s; letI := Ty.instRepr t; inferInstanceAs (Repr (s.denote × t.denote))
  | .list t => letI := Ty.instRepr t; inferInstanceAs (Repr (List t.denote))

/-- `Hashable` of the denotations (used by the derived `Hashable` of expressions). -/
instance Ty.instHashable : (t : Ty) → Hashable t.denote
  | .nat => inferInstanceAs (Hashable Nat)
  | .bool => inferInstanceAs (Hashable Bool)
  | .int => inferInstanceAs (Hashable Int)
  | .prod s t =>
    letI := Ty.instHashable s; letI := Ty.instHashable t
    inferInstanceAs (Hashable (s.denote × t.denote))
  | .list t => letI := Ty.instHashable t; inferInstanceAs (Hashable (List t.denote))

/-- `bool_eq` at every object type. -/
def Ty.beq : (t : Ty) → t.denote → t.denote → Bool
  | .nat, a, b => @BEq.beq Nat _ a b
  | .bool, a, b => @BEq.beq Bool _ a b
  | .int, a, b => @BEq.beq Int _ a b
  | .prod s t, a, b => s.beq a.1 b.1 && t.beq a.2 b.2
  | .list t, a, b => @decide (a = b) (Ty.decEq (.list t) a b)

/-- A default value of every type (the value of `head []`). -/
def Ty.default : (t : Ty) → t.denote
  | .nat => (0 : Nat)
  | .bool => false
  | .int => (0 : Int)
  | .prod s t => (s.default, t.default)
  | .list _ => ([] : List _)

/-- Environments: right-nested tuples `(v₁, (v₂, … , ()))`. -/
@[reducible] def Env : List Ty → Type
  | [] => Unit
  | t :: ts => t.denote × Env ts

/-- Typed de Bruijn variables. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {t : Ty} : Var (t :: Γ) t
  | there {Γ : List Ty} {s t : Ty} : Var Γ t → Var (s :: Γ) t
  deriving DecidableEq, Repr, Hashable

/-- Variable lookup. -/
def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.denote
  | _ :: _, _, .here, env => env.1
  | _ :: _, _, .there v, env => v.get env.2

/-- Signature of a recursive function. -/
structure Sig where
  args : List Ty
  ret : Ty
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Curried Lean function type `a₁ → … → aₙ → r`. -/
@[reducible] def FnType : List Ty → Ty → Type
  | [], r => r.denote
  | t :: ts, r => t.denote → FnType ts r

/-- Curry a function on environments. -/
def curryEnv : {ts : List Ty} → {r : Ty} → (Env ts → r.denote) → FnType ts r
  | [], _, f => f ()
  | _ :: _, _, f => fun a => curryEnv (fun e => f (a, e))

/-- Uncurry. -/
def uncurryEnv : {ts : List Ty} → {r : Ty} → FnType ts r → Env ts → r.denote
  | [], _, f, _ => f
  | _ :: _, _, f, e => uncurryEnv (f e.1) e.2

theorem curryEnv_congr : ∀ {ts : List Ty} {r : Ty} (f g : Env ts → r.denote),
    (∀ x, f x = g x) → curryEnv f = curryEnv g
  | [], _, _, _, h => h ()
  | _ :: _, _, _, _, h => by
    funext a
    exact curryEnv_congr _ _ (fun e => h (a, e))

theorem curryEnv_uncurryEnv : ∀ {ts : List Ty} {r : Ty} (f : FnType ts r),
    curryEnv (uncurryEnv f) = f
  | [], _, _ => rfl
  | _ :: _, _, f => by
    funext a
    exact curryEnv_uncurryEnv (f a)

/-- A function on environments that agrees pointwise with `uncurryEnv f` curries to `f`.
Every agreement theorem ends with this step. -/
theorem curryEnv_eq {ts : List Ty} {r : Ty} (g : Env ts → r.denote) (f : FnType ts r)
    (h : ∀ x, g x = uncurryEnv f x) : curryEnv g = f := by
  rw [← curryEnv_uncurryEnv f]
  exact curryEnv_congr _ _ h

/-- Primitive binary operators, typed. -/
inductive BinOp : Ty → Ty → Ty → Type where
  | add : BinOp .nat .nat .nat
  | sub : BinOp .nat .nat .nat
  | mul : BinOp .nat .nat .nat
  | div : BinOp .nat .nat .nat
  | mod : BinOp .nat .nat .nat
  | lt : BinOp .nat .nat .bool
  | le : BinOp .nat .nat .bool
  | beq (t : Ty) : BinOp t t .bool
  | and : BinOp .bool .bool .bool
  | or : BinOp .bool .bool .bool
  /-- `xor` on booleans. -/
  | bxor : BinOp .bool .bool .bool
  | pow : BinOp .nat .nat .nat
  | shiftLeft : BinOp .nat .nat .nat
  | shiftRight : BinOp .nat .nat .nat
  /-- bitwise `&&&`, `|||`, `^^^` on `Nat`. -/
  | land : BinOp .nat .nat .nat
  | lor : BinOp .nat .nat .nat
  | xor : BinOp .nat .nat .nat
  | gcd : BinOp .nat .nat .nat
  | lcm : BinOp .nat .nat .nat
  /-- `Int` arithmetic and comparisons. -/
  | iadd : BinOp .int .int .int
  | isub : BinOp .int .int .int
  | imul : BinOp .int .int .int
  | idiv : BinOp .int .int .int
  | imod : BinOp .int .int .int
  | ilt : BinOp .int .int .bool
  | ile : BinOp .int .int .bool
  /-- `(a, b)` -/
  | pair (s t : Ty) : BinOp s t (.prod s t)
  /-- `a :: l` -/
  | cons (t : Ty) : BinOp t (.list t) (.list t)
  /-- `l₁ ++ l₂` -/
  | append (t : Ty) : BinOp (.list t) (.list t) (.list t)
  deriving DecidableEq, Repr, Hashable

/-- Meaning of the primitive operators. -/
def BinOp.eval : {a b c : Ty} → BinOp a b c → a.denote → b.denote → c.denote
  | _, _, _, .add, x, y => @HAdd.hAdd Nat Nat Nat _ x y
  | _, _, _, .sub, x, y => @HSub.hSub Nat Nat Nat _ x y
  | _, _, _, .mul, x, y => @HMul.hMul Nat Nat Nat _ x y
  | _, _, _, .div, x, y => @HDiv.hDiv Nat Nat Nat _ x y
  | _, _, _, .mod, x, y => @HMod.hMod Nat Nat Nat _ x y
  | _, _, _, .lt, x, y => decide (@LT.lt Nat _ x y)
  | _, _, _, .le, x, y => decide (@LE.le Nat _ x y)
  | _, _, _, .beq t, x, y => t.beq x y
  | _, _, _, .and, x, y => (x && y : Bool)
  | _, _, _, .or, x, y => (x || y : Bool)
  | _, _, _, .bxor, x, y => Bool.xor x y
  | _, _, _, .pow, x, y => @HPow.hPow Nat Nat Nat _ x y
  | _, _, _, .shiftLeft, x, y => @HShiftLeft.hShiftLeft Nat Nat Nat _ x y
  | _, _, _, .shiftRight, x, y => @HShiftRight.hShiftRight Nat Nat Nat _ x y
  | _, _, _, .land, x, y => @HAnd.hAnd Nat Nat Nat _ x y
  | _, _, _, .lor, x, y => @HOr.hOr Nat Nat Nat _ x y
  | _, _, _, .xor, x, y => @HXor.hXor Nat Nat Nat _ x y
  | _, _, _, .gcd, x, y => Nat.gcd x y
  | _, _, _, .lcm, x, y => Nat.lcm x y
  | _, _, _, .iadd, x, y => @HAdd.hAdd Int Int Int _ x y
  | _, _, _, .isub, x, y => @HSub.hSub Int Int Int _ x y
  | _, _, _, .imul, x, y => @HMul.hMul Int Int Int _ x y
  | _, _, _, .idiv, x, y => @HDiv.hDiv Int Int Int _ x y
  | _, _, _, .imod, x, y => @HMod.hMod Int Int Int _ x y
  | _, _, _, .ilt, x, y => decide (@LT.lt Int _ x y)
  | _, _, _, .ile, x, y => decide (@LE.le Int _ x y)
  | _, _, _, .pair _ _, x, y => (x, y)
  | _, _, _, .cons _, x, y => x :: y
  | _, _, _, .append _, x, y => x ++ y

/-- Primitive unary operators, typed (`!` is the separate constructor `PExpr.not`). -/
inductive UnOp : Ty → Ty → Type where
  | log2 : UnOp .nat .nat
  /-- `-x` on `Int` -/
  | ineg : UnOp .int .int
  /-- `Int.toNat` -/
  | toNat : UnOp .int .nat
  /-- `Int.natAbs` -/
  | natAbs : UnOp .int .nat
  /-- the cast `Nat → Int` -/
  | ofNat : UnOp .nat .int
  | fst (s t : Ty) : UnOp (.prod s t) s
  | snd (s t : Ty) : UnOp (.prod s t) t
  /-- `l.headD default` (only used where `l` is known to be non-empty) -/
  | head (t : Ty) : UnOp (.list t) t
  | tail (t : Ty) : UnOp (.list t) (.list t)
  | isNil (t : Ty) : UnOp (.list t) .bool
  | length (t : Ty) : UnOp (.list t) .nat
  /-- `List.range n = [0, 1, …, n - 1]` -/
  | range : UnOp .nat (.list .nat)
  /-- `List.sum` of a list of `Nat` -/
  | sum : UnOp (.list .nat) .nat
  deriving DecidableEq, Repr, Hashable

/-- Meaning of the unary operators. -/
def UnOp.eval : {a b : Ty} → UnOp a b → a.denote → b.denote
  | _, _, .log2, x => Nat.log2 x
  | _, _, .ineg, x => @Neg.neg Int _ x
  | _, _, .toNat, x => Int.toNat x
  | _, _, .natAbs, x => Int.natAbs x
  | _, _, .ofNat, x => ((x : Nat) : Int)
  | _, _, .fst _ _, x => x.1
  | _, _, .snd _ _, x => x.2
  | _, _, .head t, x => x.headD t.default
  | _, _, .tail _, x => x.tail
  | _, _, .isNil _, x => x.isEmpty
  | _, _, .length _, x => x.length
  | _, _, .range, x => List.range x
  | _, _, .sum, x => @List.sum Nat _ _ x

/-! ## Relations with fixed parameters -/

/-- The relation "same `f`-value `k`, and `g`-values related by `r k`" on any type `α` is
well-founded if every `r k` is.  It is a subrelation of the inverse image along
`x ↦ ⟨f x, g x⟩` of the lexicographic order `PSigma.Lex` of the empty relation (on the values of
`f`) and the `r k` (on the values of `g`), which is well-founded by Mathlib's
`WellFounded.psigma_lex`. -/
theorem fibreRel_wf {α K : Sort _} {D : Sort _} {f : α → K} {g : α → D}
    {r : K → D → D → Prop} (h : ∀ k, WellFounded (r k)) :
    WellFounded (fun x y => f x = f y ∧ r (f y) (g x) (g y)) :=
  Subrelation.wf
    (r := InvImage (PSigma.Lex (β := fun _ => D) emptyRelation r) fun x => ⟨f x, g x⟩)
    (fun {x y} ⟨hf, hr⟩ => by
      change PSigma.Lex (β := fun _ => D) emptyRelation r ⟨f x, g x⟩ ⟨f y, g y⟩
      rw [hf]; exact .right _ hr)
    (InvImage.wf _ (WellFounded.psigma_lex emptyWf.wf h))

/-- A relation on `Env Γ` whose *fixed parameters* may sit at any positions: `f` reads the
fixed components, `g` packs the others.  Related environments agree on the fixed components,
and their packed other components are related by `r k`, where `k` are the fixed values.  The
capture elaborator uses it when Lean moved fixed parameters that are not a prefix of the
parameter list (e.g. `def f (n k : Nat)` with `k` fixed) outside the `WellFounded.fix`. -/
def fixedAtRel {Γ : List Ty} {K : Type} {D : Sort _} (f : Env Γ → K) (g : Env Γ → D)
    (r : K → D → D → Prop) : Env Γ → Env Γ → Prop :=
  fun x y => f x = f y ∧ r (f y) (g x) (g y)

theorem fixedAtRel_wf {Γ : List Ty} {K : Type} {D : Sort _} {f : Env Γ → K} {g : Env Γ → D}
    {r : K → D → D → Prop} (h : ∀ k, WellFounded (r k)) : WellFounded (fixedAtRel f g r) :=
  fibreRel_wf h

/-- A relation on `Env (t :: ts)` whose first component is a *fixed parameter*: related
environments agree on it, and their tails are related by `R a`, where `a` is that fixed value.
The capture elaborator uses it for functions such as `def f (k : Nat) : Nat → Nat`, where `k`
is passed unchanged to every recursive call (Lean keeps such parameters outside the
`WellFounded.fix`). -/
def fixedRel {t : Ty} {ts : List Ty} (R : t.denote → Env ts → Env ts → Prop) :
    Env (t :: ts) → Env (t :: ts) → Prop :=
  fun x y => x.1 = y.1 ∧ R y.1 x.2 y.2

theorem fixedRel_wf {t : Ty} {ts : List Ty} {R : t.denote → Env ts → Env ts → Prop}
    (h : ∀ a, WellFounded (R a)) : WellFounded (fixedRel R) :=
  fixedAtRel_wf (f := fun x : Env (t :: ts) => x.1) (g := fun x => x.2) h

/-- A relation on `Env Γ` for a function with a *precondition* `pre` (proof parameters):
related environments satisfy `pre`, agree on their fixed components (read by `f`), and their
packings `g x hx` (which may contain the proofs) are related by `r k`, where `k` are the fixed
values.  The capture elaborator uses it for functions such as `def f (n : Nat) (h : P n)`,
whose Lean fixpoint runs on the dependent pairs `⟨n, h⟩`. -/
def preRel {Γ : List Ty} {K : Type} {D : Sort _} (pre : Env Γ → Prop) (f : Env Γ → K)
    (g : (x : Env Γ) → pre x → D) (r : K → D → D → Prop) : Env Γ → Env Γ → Prop :=
  fun x y => ∃ (hx : pre x) (hy : pre y), f x = f y ∧ r (f y) (g x hx) (g y hy)

/-- Well-foundedness of `preRel`: on the environments satisfying `pre` (the only ones it
relates) it is an instance of `fibreRel_wf`. -/
theorem preRel_wf {Γ : List Ty} {K : Type} {D : Sort _} {pre : Env Γ → Prop} {f : Env Γ → K}
    {g : (x : Env Γ) → pre x → D} {r : K → D → D → Prop} (h : ∀ k, WellFounded (r k)) :
    WellFounded (preRel pre f g r) := by
  have hS : ∀ s : Subtype pre, Acc (preRel pre f g r) s.1 := fun s =>
    (fibreRel_wf (f := fun s : Subtype pre => f s.1) (g := fun s => g s.1 s.2) h).induction
      (C := fun s => Acc (preRel pre f g r) s.1) s
      fun s IH => Acc.intro _ fun y ⟨hy, _, hf, hr⟩ => IH ⟨y, hy⟩ ⟨hf, hr⟩
  exact ⟨fun x => Acc.intro _ fun y ⟨hy, _⟩ => hS ⟨y, hy⟩⟩

/-! ## Relations for recursion through a function argument -/

/-- The relation of the global function that captures a Lean function `f` together
with the copy of a function `g` specialised to a function argument which itself calls `f`
(e.g. `f (n+1) = g (fun r => f n r) …`, as in `for` loops whose body calls `f`).  States are
`Sum.inl x` (a call `f x`) and `Sum.inr y` (a call of the specialised `g`, whose lifted
variables, the free variables of the function argument, are `lam y`).  `Call x k` says that
the function argument with lifted variables `k` may call `f x`:

* `f x' < f x` if `Rf x' x` (the recursion of `f`);
* `g y < f x` (entering `g` from `f x`) if every call `f x'` the function argument may make is
  `Rf`-below `x`;
* `g y' < g y` if they have the same lifted variables and `Rg y' y` (the recursion of `g`);
* `f x' < g y` if the function argument of `g y` may call `f x'`. -/
def hoRel {X Y K : Type} (Rf : X → X → Prop) (Rg : Y → Y → Prop) (lam : Y → K)
    (Call : X → K → Prop) : X ⊕ Y → X ⊕ Y → Prop
  | .inl x', .inl x => Rf x' x
  | .inr y, .inl x => ∀ x', Call x' (lam y) → Rf x' x
  | .inr y', .inr y => lam y' = lam y ∧ Rg y' y
  | .inl x', .inr y => Call x' (lam y)

theorem hoRel_wf {X Y K : Type} {Rf : X → X → Prop} {Rg : Y → Y → Prop} {lam : Y → K}
    {Call : X → K → Prop} (hf : WellFounded Rf) (hg : WellFounded Rg) :
    WellFounded (hoRel Rf Rg lam Call) := by
  -- every `f x` is accessible, by induction on `x`; on the way, every `g y` entered from
  -- `f x`, by induction on `y`
  have accF : ∀ x, Acc (hoRel Rf Rg lam Call) (.inl x) := by
    intro x
    induction x using hf.induction with
    | _ x IHx =>
      have accG : ∀ y, (∀ x', Call x' (lam y) → Rf x' x) →
          Acc (hoRel Rf Rg lam Call) (.inr y) := by
        intro y
        induction y using hg.induction with
        | _ y IHy =>
          intro hy
          refine Acc.intro _ fun z hz => ?_
          match z, hz with
          | .inl x', hz => exact IHx x' (hy x' hz)
          | .inr y', ⟨hl, hr⟩ => exact IHy y' hr (fun x' h => hy x' (hl ▸ h))
      refine Acc.intro _ fun z hz => ?_
      match z, hz with
      | .inl x', hz => exact IHx x' hz
      | .inr y, hz => exact accG y hz
  -- then every `g y`, by induction on `y`: below it are `g y'` with `Rg y' y`, and calls of `f`
  have accG : ∀ y, Acc (hoRel Rf Rg lam Call) (.inr y) := by
    intro y
    induction y using hg.induction with
    | _ y IH =>
      refine Acc.intro _ fun z hz => ?_
      match z, hz with
      | .inl x', _ => exact accF x'
      | .inr y', ⟨_, hr⟩ => exact IH y' hr
  refine ⟨fun z => ?_⟩
  match z with
  | .inl x => exact accF x
  | .inr y => exact accG y

end WFLang
