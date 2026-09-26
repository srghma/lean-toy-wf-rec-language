module
public import LeanScript.ExprCtx

@[expose] public section

set_option autoImplicit false

/-!
# `natRecCtx`: the context a block of previous answers is written in

Split out of the grammar (`LeanScript.Expr.Term`) because it is an ordinary list
operation: `k` copies of a type in front of a context, with the two facts about it the
evaluator and its proofs need.
-/

namespace LeanScript

/-- The context a block of `k` previous answers is written in: `k` copies of `τ` in front
    of `Γ`.

    Written as a recursion rather than as `List.replicate k τ ++ Γ` — the two are equal
    (`natRecCtx_eq_replicate`), and this one reduces on a `k + 1` that is not a literal,
    which is what the evaluator's clause for `Term.nat_rec` needs.  At a literal depth it
    is the context one would have written by hand: `natRecCtx τ 2 Γ` is `τ :: τ :: Γ`. -/
def natRecCtx (τ : TyWf) : Nat → Ctx → Ctx
  | 0, Γ => Γ
  | k + 1, Γ => τ :: natRecCtx τ k Γ

@[simp] theorem natRecCtx_zero (τ : TyWf) (Γ : Ctx) : natRecCtx τ 0 Γ = Γ := rfl

@[simp] theorem natRecCtx_succ (τ : TyWf) (k : Nat) (Γ : Ctx) :
    natRecCtx τ (k + 1) Γ = τ :: natRecCtx τ k Γ := rfl

theorem natRecCtx_eq_replicate (τ : TyWf) (Γ : Ctx) :
    (k : Nat) → natRecCtx τ k Γ = List.replicate k τ ++ Γ
  | 0 => rfl
  | k + 1 => by
      show τ :: natRecCtx τ k Γ = _
      rw [natRecCtx_eq_replicate τ Γ k]
      rfl

theorem natRecCtx_length (τ : TyWf) (Γ : Ctx) :
    (k : Nat) → (natRecCtx τ k Γ).length = k + Γ.length
  | 0 => (Nat.zero_add _).symm
  | k + 1 => by
      show (natRecCtx τ k Γ).length + 1 = _
      rw [natRecCtx_length τ Γ k]
      omega

end LeanScript

end
