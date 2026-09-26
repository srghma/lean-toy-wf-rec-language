
import LeanScript.Term.Elab
import LeanScript.Term.Compile
/-!
Walking a string one position at a time. A Lean string position is a byte offset into
the UTF-8 encoding of the string, so every primitive that takes one is written in
terms of `_utf8(s)`, the encoding the runtime remembers for the last two strings. The
loops below asked for that view at every step; `LakeJs/LoopHoist.lean` now takes it
once, in front of the loop, since a string is immutable and the loop never assigns it.
-/

/-- Counting the occurrences of a character: the standard byte-position walk. -/
def test1 (s : String) (c : Char) : Nat :=
  let rec go (p : String.Pos.Raw) (n : Nat) : Nat :=
    if String.Pos.Raw.atEnd s p then n
    else go (String.Pos.Raw.next s p) (if String.Pos.Raw.get s p == c then n + 1 else n)
  termination_by s.utf8ByteSize - p.byteIdx
  decreasing_by
    simp_wf
    have h1 : p.byteIdx < (String.Pos.Raw.next s p).byteIdx := by
      simp [String.Pos.Raw.next, String.Pos.Raw.byteIdx_add_char, Char.utf8Size_pos]
    have h2 : p.byteIdx < s.utf8ByteSize := by
      simpa [String.Pos.Raw.atEnd, String.Pos.Raw.lt_iff] using
        (by assumption : ¬ String.Pos.Raw.atEnd s p)
    omega
  go 0 0

/-- The same walk, answering with the position of the first occurrence. -/
def test2 (s : String) (c : Char) : String.Pos.Raw :=
  let rec go (p : String.Pos.Raw) : String.Pos.Raw :=
    if String.Pos.Raw.atEnd s p then p
    else if String.Pos.Raw.get s p == c then p
    else go (String.Pos.Raw.next s p)
  termination_by s.utf8ByteSize - p.byteIdx
  decreasing_by
    simp_wf
    have h1 : p.byteIdx < (String.Pos.Raw.next s p).byteIdx := by
      simp [String.Pos.Raw.next, String.Pos.Raw.byteIdx_add_char, Char.utf8Size_pos]
    have h2 : p.byteIdx < s.utf8ByteSize := by
      simpa [String.Pos.Raw.atEnd, String.Pos.Raw.lt_iff] using
        (by assumption : ¬ String.Pos.Raw.atEnd s p)
    omega
  go 0

/-- `String.length` counts the characters of the string, so asking for it at every
    step of a loop is quadratic; the string is invariant, so it is asked once. -/
def test4 (s : String) : Nat :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    if i < s.length then go (i + 1) (acc + i) else acc
  go 0 0

/-- The loop assigns the string it measures, so its encoding is not the same at every
    step and nothing is hoisted. -/
def test3 (s : String) (n : Nat) : Nat := Id.run do
  let mut s := s
  let mut acc := 0
  for _ in [0:n] do
    acc := acc + s.utf8ByteSize
    s := s.push 'x'
  return acc

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : String → Char → Nat
  argTy       : string
  resTy       : (fn char nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.sub
    String.Pos.Raw.atEnd
    String.Pos.Raw.get
    String.Pos.Raw.next
    String.utf8ByteSize
    UInt32.decEq
  context     :
    ok  test1.go  [_current]
---
info: LeanFunction test1.go
  signature   : String → Char → String.Pos.Raw → Nat → Nat
  argTy       : string
  resTy       : (fn char (fn stringPosRaw (fn nat nat)))
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.sub
    String.Pos.Raw.atEnd
    String.Pos.Raw.get
    String.Pos.Raw.next
    String.utf8ByteSize
    UInt32.decEq
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  decEq  [Init.Prelude]
---
info: LeanFunction test2
  signature   : String → Char → String.Pos.Raw
  argTy       : string
  resTy       : (fn char stringPosRaw)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.sub
    String.Pos.Raw.atEnd
    String.Pos.Raw.get
    String.Pos.Raw.next
    String.utf8ByteSize
    UInt32.decEq
  context     :
    ok  test2.go  [_current]
---
info: LeanFunction test2.go
  signature   : String → Char → String.Pos.Raw → String.Pos.Raw
  argTy       : string
  resTy       : (fn char (fn stringPosRaw stringPosRaw))
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.sub
    String.Pos.Raw.atEnd
    String.Pos.Raw.get
    String.Pos.Raw.next
    String.utf8ByteSize
    UInt32.decEq
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  decEq  [Init.Prelude]
---
info: LeanFunction test3
  signature   : String → Nat → Nat
  argTy       : string
  resTy       : (fn nat nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.emptyWithCapacity
    Array.push
    Char.ofNatAux
    Nat.add
    Nat.decLt
    Nat.mod
    Nat.pow
    Nat.sub
    String.push
    String.utf8ByteSize
    UInt32.ofBitVec
  context     :
    ok  Char.ofNat  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  Std.Legacy.Range.forIn'  [Init.Data.Range.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test4
  signature   : String → Nat
  argTy       : string
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.sub
    String.length
  context     :
    ok  test4.go  [_current]
---
info: LeanFunction test4.go
  signature   : String → Nat → Nat → Nat
  argTy       : string
  resTy       : (fn nat (fn nat nat))
  recursion   : well-founded       (encoded as Term.fixAcc: the Acc proof is a field)
  status      : representable in Term
  primitives  :
    Nat.add
    Nat.decLt
    Nat.sub
    String.length
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
  compiled  test1
  compiled  test1.go
  compiled  test2
  compiled  test2.go
  refused   test3: the type `Type u_1 → Type u_2` has no `Ty`: a type or a proposition, which carries no value
  compiled  test4
  compiled  test4.go
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

example : test1.leanFn "banana" 'a' = test1 "banana" 'a' := by decide +kernel
example : test2.leanFn "banana" 'n' = test2 "banana" 'n' := by decide +kernel
example : test4.leanFn "hello" = test4 "hello" := by decide +kernel
