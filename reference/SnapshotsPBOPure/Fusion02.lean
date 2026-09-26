
import LeanScript.Term.Elab
import LeanScript.Term.Compile
-- 1. Stream Representation
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

-- 2. Conversions: fromArray
@[inline]
def fromArray (arr : Array α) : Unfold α where
  State := Nat
  seed  := 0
  step ix :=
    if h : ix < arr.size then
      some (ix + 1, arr[ix])
    else
      none
  measure ix := arr.size - ix
  decreasing := by
    intro x x' a hx
    split at hx
    · injection hx with h1
      simp_all only [Prod.mk.injEq]
      obtain ⟨left, right⟩ := h1
      subst left right
      grind only
    · contradiction

-- 3. Conversions: toArray
@[inline]
def toArrayLoop (u : Unfold α) (s : u.State) (acc : Array α) : Array α :=
  match _h : u.step s with
  | none => acc
  | some (s', a) => toArrayLoop u s' (acc.push a)
termination_by u.measure s
decreasing_by exact u.decreasing s s' a _h

@[inline]
def toArray (u : Unfold α) : Array α :=
  toArrayLoop u u.seed #[]

-- 4. Stream combinators: mapU
@[inline]
def mapU (f : α → β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step s :=
    match u.step s with
    | none => none
    | some (s', a) => some (s', f a)
  measure := u.measure
  decreasing := by
    intro x x' b hx
    cases hstep : u.step x with
    | none =>
      rw [hstep] at hx
      contradiction
    | some pair =>
      obtain ⟨s_next, a⟩ := pair
      rw [hstep] at hx
      injection hx with h1
      simp_all only [Prod.mk.injEq]
      obtain ⟨left, right⟩ := h1
      subst left right
      grind only [Nat.le_antisymm, Nat.le_of_lt, Unfold.decreasing]

-- 5. Stream combinators: filterMapU
@[inline]
def filterMapStep (u : Unfold α) (f : α → Option β) (s : u.State) : Option (u.State × β) :=
  match _h : u.step s with
  | none => none
  | some (s', a) =>
    match f a with
    | some b => some (s', b)
    | none   => filterMapStep u f s'
termination_by u.measure s
decreasing_by exact u.decreasing s s' a _h

theorem filterMapStep_decreasing_aux (u : Unfold α) (f : α → Option β) (n : Nat) :
    ∀ s, u.measure s ≤ n → ∀ s' b, filterMapStep u f s = some (s', b) → u.measure s' < u.measure s := by
  induction n with
  | zero =>
    intro s hs s' b h
    have hdec_all := u.decreasing s
    rw [filterMapStep] at h
    split at h
    · contradiction
    · have := hdec_all _ _ (by assumption)
      omega
  | succ n ih =>
    intro s hs s' b h
    have hdec_all := u.decreasing s
    rw [filterMapStep] at h
    split at h
    · contradiction
    · split at h
      · injection h with h1
        simp_all only [Option.some.injEq, Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff,
          forall_eq', gt_iff_lt]
      · have hdec := hdec_all _ _ (by assumption)
        have := ih _ (by omega) s' b h
        omega

theorem filterMapStep_decreasing (u : Unfold α) (f : α → Option β) (s s' : u.State) (b : β)
    (h : filterMapStep u f s = some (s', b)) : u.measure s' < u.measure s :=
  filterMapStep_decreasing_aux u f (u.measure s) s (Nat.le_refl _) s' b h

@[inline]
def filterMapU (f : α → Option β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step  := filterMapStep u f
  measure := u.measure
  decreasing := fun x x' b h => filterMapStep_decreasing u f x x' b h

@[inline]
def filterU (p : α → Bool) (u : Unfold α) : Unfold α :=
  filterMapU (fun a => if p a then some a else none) u

-- 6. Helper combinators
@[inline]
def overArray (f : Unfold α → Unfold β) (arr : Array α) : Array β :=
  toArray (f (fromArray arr))

@[inline]
def dropPrefix1 (s : String) : Option String :=
  if s.startsWith "1" then some (s.drop 1).toString else none

-- 7. Test pipeline
def test (arr : Array Int) : Array String :=
  flip overArray arr fun u =>
    u
      |> mapU (· + 1)
      |> mapU toString
      |> filterMapU dropPrefix1
      |> mapU ("2" ++ ·)
      |> filterU (· != "wat")
      |> mapU (· ++ "1")

-- #eval test #[0, 9, 10, 1]
-- Output: #["21", "201", "211"]

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction dropPrefix1
  signature   : String → Option String
  argTy       : string
  resTy       : (taggedUnion [] [string])
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Char.ofNatAux
    Nat.add
    Nat.decEq
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mod
    Nat.pow
    Nat.sub
    String.Internal.append
    String.Slice.Pattern.Internal.memcmpStr
    String.extract
    String.getUTF8Byte
    String.ofList
    String.utf8ByteSize
    UInt32.ofBitVec
    UInt8.decEq
    UInt8.land
    UInt8.ofNat
    panicCore
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?  [Init.Data.String.Pattern.String]
    ok  String.Slice.Pattern.ForwardSliceSearcher.startsWith  [Init.Data.String.Pattern.String]
    ok  String.Slice.isEmpty  [Init.Data.String.Defs]
    ok  String.Slice.toString  [Init.Data.String.Slice]
    ok  String.drop  [Init.Data.String.TakeDrop]
    ok  String.startsWith  [Init.Data.String.TakeDrop]
    ok  String.toSlice  [Init.Data.String.Defs]
---
info: LeanFunction filterMapStep
  signature   : {α : Type} → {β : Type u_1} → (u : Unfold α) → (α → Option β) → u.State → Option (u.State × β)
  argTy       : -
  resTy       : -
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction filterMapU
  signature   : {α β : Type} → (α → Option β) → Unfold α → Unfold β
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     :
    ok  filterMapStep  [_current]
---
info: LeanFunction filterU
  signature   : {α : Type} → (α → Bool) → Unfold α → Unfold α
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  filterMapU  [_current]
---
info: LeanFunction fromArray
  signature   : {α : Type} → Array α → Unfold α
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Array.getInternal
    Array.size
    Nat.add
    Nat.decLt
    Nat.sub
  context     : -
---
info: LeanFunction mapU
  signature   : {α β : Type} → (α → β) → Unfold α → Unfold β
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  : -
  context     :
    ok  Unit.unit  [Init.Prelude]
---
info: LeanFunction overArray
  signature   : {α β : Type} → (Unfold α → Unfold β) → Array α → Array β
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Array.getInternal
    Array.mk
    Array.push
    Array.size
    Nat.add
    Nat.decLt
    Nat.sub
  context     :
    ok  fromArray  [_current]
    ok  toArray  [_current]
---
info: LeanFunction test
  signature   : Array Int → Array String
  argTy       : (array int)
  resTy       : (array string)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.mk
    Array.push
    Array.size
    Char.ofNatAux
    Int.add
    Int.negSucc
    Int.ofNat
    Nat.add
    Nat.decEq
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mod
    Nat.pow
    Nat.sub
    String.Internal.append
    String.Slice.Pattern.Internal.memcmpStr
    String.append
    String.decEq
    String.extract
    String.getUTF8Byte
    String.ofList
    String.utf8ByteSize
    UInt32.ofBitVec
    UInt8.decEq
    UInt8.land
    UInt8.ofNat
    panicCore
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Int.repr  [Init.Data.Int.Repr]
    ok  bne  [Init.Core]
    ok  dropPrefix1  [_current]
    ok  filterMapU  [_current]
    ok  filterU  [_current]
    ok  flip  [Init.Core]
    ok  mapU  [_current]
    ok  overArray  [_current]
---
info: LeanFunction toArray
  signature   : {α : Type} → Unfold α → Array α
  argTy       : -
  resTy       : -
  recursion   : none               (no recursion to encode)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Array.mk
    Array.push
  context     :
    ok  List.toArray  [Init.Prelude]
    ok  toArrayLoop  [_current]
---
info: LeanFunction toArrayLoop
  signature   : {α : Type} → (u : Unfold α) → u.State → Array α → Array α
  argTy       : -
  resTy       : -
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : rejected           (a type or a proposition, which carries no value)
  primitives  :
    Array.push
  context     : -
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
  compiled  dropPrefix1  (no leanFn: its Lean type is not the denotation of its Ty)
  refused   filterMapU: the type `α → Option β` has no `Ty`: not a constant type
  refused   filterU: the type `α → Bool` has no `Ty`: not a constant type
  refused   fromArray: the type `Array α` has no `Ty`: not a constant type
  refused   mapU: the type `α → β` has no `Ty`: not a constant type
  refused   overArray: the type `Unfold α → Unfold β` has no `Ty`: a type or a proposition, which carries no value
  refused   test: the type `Unfold α` has no `Ty`: a type or a proposition, which carries no value
  refused   toArray: the type `Unfold α` has no `Ty`: a type or a proposition, which carries no value
  refused   toArrayLoop: the type `Unfold α` has no `Ty`: a type or a proposition, which carries no value
-/
#guard_msgs in
#leanjs_compile_term_for_all
