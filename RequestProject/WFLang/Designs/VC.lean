import RequestProject.WFLang.PCL.Lang

/-!
# Design `PCL-VC`: proof-free syntax, one verification condition per program

This is a variant of `PCL` (`PCL/Lang.lean`).  The difference is **where the termination proofs
live**:

* in `PCL`, every `call` node carries its own decrease proof `dec`, and `Expr` is indexed by the
  path condition `G` so that `dec` can use the enclosing `if` tests;
* in `PCL-VC`, the syntax contains **no proofs at all** except `wf : WellFounded R` on `fix`.
  A `call` is just `let v := self args in k`.  The decrease obligations of the whole program are
  collected by a function `Expr.VC` (a *verification-condition generator*) into a single `Prop`,
  and the evaluator takes one proof of it.

The termination argument (the relation `R`, e.g. a measure) is still chosen by whoever writes
the `fix` node; `VC` is what makes sure it is *correct*.  A program whose relation is wrong
simply has a false `VC`, so it cannot be evaluated at all — there is no "measure exhausted" case
at runtime and no default value.

`erase` turns a `PCL` program into a `PCL-VC` program (forgets the proofs), and
`erase_vc` / `erase_eval` show that the `VC` of the result holds and that it computes the same
value.  So every function captured by `#lean_wf_func_to_term` into `PCL` is also available here
(`Certified.ofPCL`).
-/

namespace WFLang.VC

open PCL (Self Handler Handler.push)

/-- `PCL-VC` statements: `PCL` without the path-condition index and without `dec`. -/
inductive Expr : (Γ : List Ty) → Option (Self Γ) → Ty → Type where
  /-- Return a call-free value. -/
  | ret {Γ : List Ty} {sf : Option (Self Γ)} {t : Ty} (p : PExpr Γ t) : Expr Γ sf t
  /-- `if c then a else b`. -/
  | ite {Γ : List Ty} {sf : Option (Self Γ)} {t : Ty}
      (c : PExpr Γ .bool) (a b : Expr Γ sf t) : Expr Γ sf t
  /-- `let v := self args in k` — no proof attached. -/
  | call {Γ : List Ty} {sf : Self Γ} {t : Ty} (args : PExprs Γ sf.params)
      (k : Expr (sf.ret :: Γ) (some (sf.push sf.ret)) t) : Expr Γ (some sf) t
  /-- `let v := (fix self params. body) args in k`, recursion along `R`. -/
  | fix {Γ : List Ty} {sf : Option (Self Γ)} {t : Ty}
      (params : List Ty) (r : Ty) (R : Env params → Env params → Prop) (wf : WellFounded R)
      (body : Expr params (some (Self.top params r R)) r)
      (args : PExprs Γ params)
      (k : Expr (r :: Γ) (sf.map (·.push r)) t) : Expr Γ sf t

/-- The verification condition of a statement at environment `e`: every call that is reached
goes down in the relation of its enclosing `fix` (for any results of earlier calls). -/
def Expr.VC : {Γ : List Ty} → {sf : Option (Self Γ)} → {t : Ty} → Expr Γ sf t → Env Γ → Prop
  | _, _, _, .ret _, _ => True
  | _, _, _, .ite c a b, e => (c.eval e = true → a.VC e) ∧ (c.eval e = false → b.VC e)
  | _, some sf, _, .call args k, e => sf.R (args.eval e) (sf.cur e) ∧ ∀ v, k.VC (v, e)
  | _, _, _, .fix _ _ _ _ body _ k, e => (∀ x, body.VC x) ∧ ∀ v, k.VC (v, e)

/-- The evaluator.  It takes a proof of the `VC`; that proof is used (only) to justify the
recursive calls, and is erased by code generation.  No runtime checks, no fuel, no default. -/
def Expr.eval : {Γ : List Ty} → {sf : Option (Self Γ)} → {t : Ty} →
    (p : Expr Γ sf t) → (e : Env Γ) → p.VC e → Handler sf e → t.denote
  | _, _, _, .ret p, e, _, _ => p.eval e
  | _, _, _, .ite c a b, e, hv, h =>
      if hc : c.eval e = true then a.eval e (hv.1 hc) h
      else b.eval e (hv.2 (Bool.eq_false_iff.mpr hc)) h
  | _, some _, _, .call args k, e, hv, h => k.eval (h (args.eval e) hv.1, e) (hv.2 _) h
  | _, _, _, .fix _ _ _ wf body args k, e, hv, h =>
      k.eval (wf.fix (fun x ih => body.eval x (hv.1 x) ih) (args.eval e), e) (hv.2 _)
        (Handler.push h)

/-! ## Soundness of `fix` -/

section
variable {params : List Ty} {r : Ty} {R : Env params → Env params → Prop} (wf : WellFounded R)
  (body : Expr params (some (Self.top params r R)) r) (hb : ∀ x, body.VC x)

/-- The function denoted by a `fix` node whose body satisfies its `VC`. -/
def fixFn : Env params → r.denote := wf.fix (fun x ih => body.eval x (hb x) ih)

/-- **Soundness (1):** the fixpoint equation. -/
theorem fixFn_eq (x : Env params) :
    fixFn wf body hb x = body.eval x (hb x) (fun y _ => fixFn wf body hb y) :=
  WellFounded.fix_eq _ _ x

/-- **Soundness (2):** uniqueness of the solution. -/
theorem fixFn_unique (f : Env params → r.denote)
    (hf : ∀ x, f x = body.eval x (hb x) (fun y _ => f y)) : ∀ x, fixFn wf body hb x = f x := by
  intro x
  induction x using wf.induction with
  | _ x IH =>
    rw [fixFn_eq, hf x]
    have : (fun y (_ : R y x) => fixFn wf body hb y) = (fun y _ => f y) := by
      funext y hy; exact IH y hy
    exact congrArg (body.eval x (hb x)) this

end

/-! ## Closed programs -/

/-- Closed programs of signature `s` (syntax only). -/
abbrev Term (s : Sig) := Expr s.args none s.ret

/-- A program together with the proof that all its recursive calls decrease. -/
structure Certified (s : Sig) where
  term : Term s
  vc : ∀ x, term.VC x

/-- Curried evaluator of a certified program. -/
def Certified.eval {s : Sig} (c : Certified s) : FnType s.args s.ret :=
  curryEnv fun x => c.term.eval x (c.vc x) ()

/-! ## From `PCL` to `PCL-VC`: forgetting the per-call proofs -/

/-- Erase the path conditions and the per-call proofs of a `PCL` program. -/
def erase : {Γ : List Ty} → {G : Env Γ → Prop} → {sf : Option (Self Γ)} → {t : Ty} →
    PCL.Expr Γ G sf t → Expr Γ sf t
  | _, _, _, _, .ret p => .ret p
  | _, _, _, _, .ite c a b => .ite c (erase a) (erase b)
  | _, _, _, _, .call args _ k => .call args (erase k)
  | _, _, _, _, .fix params r R wf body args k => .fix params r R wf (erase body) args (erase k)

/-- The per-call proofs of a `PCL` program establish the `VC` of its erasure. -/
theorem erase_vc : ∀ {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
    (p : PCL.Expr Γ G sf t) (e : Env Γ), G e → (erase p).VC e
  | _, _, _, _, .ret _, _, _ => trivial
  | _, _, _, _, .ite _ a b, e, g =>
      ⟨fun hc => erase_vc a e ⟨g, hc⟩, fun hc => erase_vc b e ⟨g, hc⟩⟩
  | _, _, _, _, .call _ dec k, e, g => ⟨dec e g, fun v => erase_vc k (v, e) g⟩
  | _, _, _, _, .fix _ _ _ _ body _ k, e, g =>
      ⟨fun x => erase_vc body x trivial, fun v => erase_vc k (v, e) g⟩

/-- Erasure preserves the result. -/
theorem erase_eval : ∀ {Γ : List Ty} {G : Env Γ → Prop} {sf : Option (Self Γ)} {t : Ty}
    (p : PCL.Expr Γ G sf t) (e : Env Γ) (g : G e) (h : Handler sf e),
    p.eval e g h = (erase p).eval e (erase_vc p e g) h
  | _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, .ite c a b, e, g, h => by
      simp only [PCL.Expr.eval, erase, Expr.eval]
      split
      · exact erase_eval a e _ h
      · exact erase_eval b e _ h
  | _, _, _, _, .call args dec k, e, g, h => by
      simp only [PCL.Expr.eval, erase, Expr.eval]
      exact erase_eval k (h (args.eval e) (dec e g), e) g h
  | _, _, _, _, .fix params r R wf body args k, e, g, h => by
      simp only [PCL.Expr.eval, erase, Expr.eval]
      have hfix : (wf.fix (fun x ih => body.eval x trivial ih) : Env params → r.denote) =
          wf.fix (fun x ih => (erase body).eval x (erase_vc body x trivial) ih) := by
        funext x
        induction x using wf.induction with
        | _ x IH =>
          rw [WellFounded.fix_eq, WellFounded.fix_eq, erase_eval body x trivial]
          congr 1
          funext y hy
          exact IH y hy
      rw [hfix]
      exact erase_eval k _ g _

/-- Every `PCL` program (in particular every function captured by `#lean_wf_func_to_term`)
gives a certified `PCL-VC` program. -/
def Certified.ofPCL {s : Sig} (t : PCL.Term s) : Certified s :=
  ⟨erase t, fun x => erase_vc t x trivial⟩

theorem Certified.ofPCL_eval {s : Sig} (t : PCL.Term s) :
    (Certified.ofPCL t).eval = PCL.Term.eval t := by
  refine curryEnv_congr _ _ fun x => ?_
  exact (erase_eval t x trivial ()).symm

end WFLang.VC
