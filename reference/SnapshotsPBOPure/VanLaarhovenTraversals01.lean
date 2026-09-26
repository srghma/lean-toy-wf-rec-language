
import LeanScript.Term.Elab
import LeanScript.Term.Compile
inductive Fun where
  | Abs : String → Fun → Fun
  | App : Fun → Fun → Fun
  deriving Repr, DecidableEq

/-- One-layer applicative traversal of the immediate children of a node. -/
def traverseFun1 {f : Type → Type} [Applicative f] (k : Fun → f Fun) : Fun → f Fun
  | Fun.Abs id a => Fun.Abs id <$> k a
  | Fun.App a b => Fun.App <$> k a <*> k b

/-- Number of nodes of a term; used as the termination measure. -/
def Fun.size : Fun → Nat
  | Fun.Abs _ a => a.size + 1
  | Fun.App a b => a.size + b.size + 1

/-- Dependent version of `traverseFun1`: the callback is only ever applied to
immediate children, and it is handed a proof that its argument is strictly
smaller than `t`. -/
def traverseFun1D {f : Type → Type} [Applicative f] (t : Fun)
    (k : (a : Fun) → a.size < t.size → f Fun) : f Fun :=
  match t, k with
  | Fun.Abs id a, k => Fun.Abs id <$> k a (by simp [Fun.size])
  | Fun.App a b, k =>
      Fun.App <$> k a (by simp [Fun.size]; omega) <*> k b (by simp [Fun.size]; omega)

/-- Forgetting the size proofs turns `traverseFun1D` back into `traverseFun1`. -/
theorem traverseFun1D_eq {f : Type → Type} [Applicative f] (k : Fun → f Fun) (t : Fun) :
    traverseFun1D t (fun a _ => k a) = traverseFun1 k t := by
  cases t <;> rfl

/-- Bottom-up monadic rewriting: rewrite the children first, then the node. -/
def rewriteBottomUpM {m : Type → Type} [Monad m] (k : Fun → m Fun) (t : Fun) : m Fun := do
  let t' ← traverseFun1D t (fun a _ => rewriteBottomUpM k a)
  k t'
termination_by t.size
decreasing_by exact ‹_›

/-- `rewriteBottomUpM` satisfies the intended recursive equation, phrased with
the original (non-dependent) `traverseFun1`. -/
theorem rewriteBottomUpM_eq {m : Type → Type} [Monad m] (k : Fun → m Fun) (t : Fun) :
    rewriteBottomUpM k t = (do let t' ← traverseFun1 (rewriteBottomUpM k) t; k t') := by
  rw [rewriteBottomUpM, traverseFun1D_eq]

/-- Pure bottom-up rewriting. -/
def rewriteBottomUp (k : Fun → Fun) : Fun → Fun := fun a =>
  Id.run (rewriteBottomUpM (m := Id) (fun f => pure (k f)) a)

/-- The pure version's recursive equation. -/
theorem rewriteBottomUp_eq (k : Fun → Fun) (t : Fun) :
    rewriteBottomUp k t = k (traverseFun1 (f := Id) (rewriteBottomUp k) t) := by
  show Id.run (rewriteBottomUpM (m := Id) (fun f => pure (k f)) t) = _
  rw [rewriteBottomUpM_eq]
  rfl

/-- Unfolding at an `Abs` node. -/
theorem rewriteBottomUp_Abs (k : Fun → Fun) (id : String) (a : Fun) :
    rewriteBottomUp k (Fun.Abs id a) = k (Fun.Abs id (rewriteBottomUp k a)) := by
  rw [rewriteBottomUp_eq]; rfl

/-- Unfolding at an `App` node. -/
theorem rewriteBottomUp_App (k : Fun → Fun) (a b : Fun) :
    rewriteBottomUp k (Fun.App a b) =
      k (Fun.App (rewriteBottomUp k a) (rewriteBottomUp k b)) := by
  rw [rewriteBottomUp_eq]; rfl

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction Fun.size
  signature   : Fun → Nat
  argTy       : -
  resTy       : -
  recursion   : structural         (encoded with the recursor of the datatype)
  status      : rejected           (`Fun` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all))
  primitives  :
    Nat.add
  context     : -
---
info: LeanFunction rewriteBottomUp
  signature   : (Fun → Fun) → Fun → Fun
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (`Fun` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all))
  primitives  :
    Nat.add
  context     :
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  Unit.unit  [Init.Prelude]
    ok  rewriteBottomUpM  [_current]
---
info: LeanFunction rewriteBottomUpM
  signature   : {m : Type → Type} → [Monad m] → (Fun → m Fun) → Fun → m Fun
  argTy       : -
  resTy       : -
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Nat.add
  context     :
    ok  Fun.size  [_current]
    ok  traverseFun1D  [_current]
---
info: LeanFunction traverseFun1
  signature   : {f : Type → Type} → [Applicative f] → (Fun → f Fun) → Fun → f Fun
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     : -
---
info: LeanFunction traverseFun1D
  signature   : {f : Type → Type} → [Applicative f] → (t : Fun) → ((a : Fun) → a.size < t.size → f Fun) → f Fun
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Nat.add
  context     :
    ok  Fun.size  [_current]
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for_all

/-! ## The compiled terms

`#leanjs_compile_term_for_all` compiles every public function of this file into a
`LeanScript.Expr.Term`, bound to `<f>.leanTerm`, and `<f>.leanFn` is that term run by
`LeanScript.Term.evalClosed`.  The report says which functions were compiled and, for
the ones that were refused, why. -/

/--
info: LeanTerms of this module
  refused   Fun.size: the type `Fun` has no `Ty`: `Fun` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all)
  refused   rewriteBottomUp: the type `Fun →   Fun` has no `Ty`: `Fun` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all)
  refused   rewriteBottomUpM: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  refused   traverseFun1: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
  refused   traverseFun1D: the type `Type → Type` has no `Ty`: a type or a proposition, which carries no value
-/
#guard_msgs in
#leanjs_compile_term_for_all
