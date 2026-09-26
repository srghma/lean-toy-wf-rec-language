
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
Two mutually tail-recursive functions whose parameters **disagree** on their types:
`walkStr` takes a `Nat` and a `String`, `walkNat` a `Nat` and a `Nat`.

The merged loop gives them one slot vector, and a slot is shared only where the members
agree on its type (`LakeJs.Compile`, `groupSlotAlloc`), so the loop here has three slots
— `Nat`, `String`, `Nat` — rather than two slots one of which holds values of two types.
Every loop variable therefore has a single type, which is what lets a JavaScript engine
keep it unboxed.
-/

mutual

def walkStr : Nat → String → Nat
  | 0, s => s.length
  | n + 1, s => walkNat n (s.length + 1)

def walkNat : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => walkStr n (if k == 0 then "" else "xy")

end

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction walkNat
  signature   : Nat → Nat → Nat
  argTy       : nat
  resTy       : (fn nat nat)
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decEq
    String.length
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
---
info: LeanFunction walkStr
  signature   : Nat → String → Nat
  argTy       : nat
  resTy       : (fn string nat)
  recursion   : mutual structural  (encoded with the recursors of the block)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decEq
    String.length
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
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
  compiled  walkNat
  compiled  walkStr
-/
#guard_msgs in
#leanjs_compile_term_for_all

/-! ## The compiled terms, run

Each line below says that the compiled term and the Lean function answer with the same
thing, and is settled by `decide +kernel`: the **kernel** reduces
`LeanScript.Term.evalClosed` applied to the generated term, so each line checks the
whole pipeline — the type translation, the compiler and the evaluator of
`LeanScript.Eval` — against Lean's own answer.  The arguments are small on purpose: the
kernel reduces the evaluator by unfolding it, which is far slower than compiled code. -/

example : walkStr.leanFn 5 "abc" = walkStr 5 "abc" := by decide +kernel
example : walkNat.leanFn 6 3 = walkNat 6 3 := by decide +kernel
