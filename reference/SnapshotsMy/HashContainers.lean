import Std.Data.HashMap
import Std.Data.HashSet
import LeanScript.Term.Elab
import LeanScript.Term.Compile

/-!
The three representations `LakeJs/Backend/HashRepr.lean` gives a hash container, and
the copy it makes of one that is looked at after an operation that answers with a new
container.
-/

/-- String keys: the entries are the properties of a prototype-less object. -/
def test1 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x (m.getD x 0 + 1)
  return m.size

/-- Number keys: a `Map`. -/
def test2 (xs : List Nat) : Option Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for x in xs do
    m := m.insert x (x * x)
  return m[3]?

/-- Nothing is stored: a `Set`. -/
def test3 (xs : List String) : Nat := Id.run do
  let mut s : Std.HashSet String := {}
  for x in xs do
    s := s.insert x
  return s.size + (if s.contains "a" then 1 else 0)

/-- A map and a set in one function: they start from empty containers of their own. -/
def test4 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  let mut s : Std.HashSet String := {}
  for x in xs do
    s := s.insert (x ++ "!")
  return m.size + s.size

/-- Two containers erased out of one: each works on a copy. -/
def test5 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  let a := m.erase "a"
  let b := m.erase "b"
  return a.size * 100 + b.size

/-- String keys, and the size is never asked for: a plain object, with no number of
    entries to keep up to date. -/
def test7 (xs : List String) (k : String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x x.length
  return m.getD k 0

/-- The order the entries come out in is Lean's, which no JavaScript container has:
    this keeps Lean's own implementation. -/
def test6 (xs : List String) : List String := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  return m.toList.map (·.1)

/-! ## Generated `LeanFunction` reports

One report per **public function** of this file, produced by
`#leanjs_generate_term_and_ctx_for_all` (see `LeanScript.Term.Elab`).  Each says what
`Ty` the function has, which kind of recursion Lean used to elaborate it — and so which
constructor of `LeanScript.Expr.Term` would hold it — which `@[extern]` primitives it
needs, and which other declarations would have to be translated with it. -/

/--
info: LeanFunction test1
  signature   : List String → Nat
  argTy       : (recTaggedUnion [] [string self])
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.decEq
    String.hash
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.getD  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.size  [Std.Data.HashMap.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test2
  signature   : List Nat → Option Nat
  argTy       : (recTaggedUnion [] [nat self])
  resTy       : (taggedUnion [] [nat])
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Char.ofNatAux
    Nat.add
    Nat.decEq
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mod
    Nat.mul
    Nat.pow
    Nat.sub
    String.Internal.append
    String.ofList
    UInt32.ofBitVec
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
    panicCore
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.DHashMap.contains  [Std.Data.DHashMap.Basic]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.get  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.get!  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.get?  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test3
  signature   : List String → Nat
  argTy       : (recTaggedUnion [] [string self])
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.decEq
    String.hash
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Bool.decEq  [Init.Prelude]
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.HashSet.contains  [Std.Data.HashSet.Basic]
    ok  Std.HashSet.emptyWithCapacity  [Std.Data.HashSet.Basic]
    ok  Std.HashSet.insert  [Std.Data.HashSet.Basic]
    ok  Std.HashSet.size  [Std.Data.HashSet.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test4
  signature   : List String → Nat
  argTy       : (recTaggedUnion [] [string self])
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.append
    String.decEq
    String.hash
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.size  [Std.Data.HashMap.Basic]
    ok  Std.HashSet.emptyWithCapacity  [Std.Data.HashSet.Basic]
    ok  Std.HashSet.insert  [Std.Data.HashSet.Basic]
    ok  Std.HashSet.size  [Std.Data.HashSet.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test5
  signature   : List String → Nat
  argTy       : (recTaggedUnion [] [string self])
  resTy       : nat
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.decEq
    String.hash
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.erase  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.size  [Std.Data.HashMap.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test6
  signature   : List String → List String
  argTy       : (recTaggedUnion [] [string self])
  resTy       : (recTaggedUnion [] [string self])
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decEq
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.decEq
    String.hash
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  List.map  [Init.Prelude]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.toList  [Std.Data.HashMap.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
---
info: LeanFunction test7
  signature   : List String → String → Nat
  argTy       : (recTaggedUnion [] [string self])
  resTy       : (fn string nat)
  recursion   : none               (no recursion to encode)
  status      : representable in Term
  primitives  :
    Array.getInternal
    Array.replicate
    Array.set
    Array.size
    Array.uget
    Array.uset
    Nat.add
    Nat.decLe
    Nat.decLt
    Nat.div
    Nat.mul
    Nat.sub
    String.decEq
    String.hash
    String.length
    UInt64.ofNat
    UInt64.shiftRight
    UInt64.toUSize
    UInt64.xor
    USize.land
    USize.ofNat
    USize.sub
    USize.toNat
  context     :
    ok  Decidable.decide  [Init.Prelude]
    ok  Function.comp  [Init.Prelude]
    ok  Function.const  [Init.Prelude]
    ok  Id.run  [Init.Control.Id]
    ok  List.forIn'  [Init.Data.List.Control]
    ok  Std.HashMap.emptyWithCapacity  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.getD  [Std.Data.HashMap.Basic]
    ok  Std.HashMap.insert  [Std.Data.HashMap.Basic]
    ok  Unit.unit  [Init.Prelude]
    ok  inferInstance  [Init.Prelude]
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
  refused   test1: the type `Std.DHashMap.Raw String fun x =>   Nat` has no `Ty`: `Std.DHashMap.Internal.AssocList` is a recursive declaration with parameters, which the recursive ...
  refused   test2: the type `α` has no `Ty`: not a constant type
  refused   test3: the type `Std.DHashMap.Raw String fun x =>   Unit` has no `Ty`: `Std.DHashMap.Internal.AssocList` is a recursive declaration with parameters, which the recursiv ...
  refused   test4: the type `Std.DHashMap.Raw String fun x =>   Nat` has no `Ty`: `Std.DHashMap.Internal.AssocList` is a recursive declaration with parameters, which the recursive ...
  refused   test5: the type `Std.DHashMap.Raw String fun x =>   Nat` has no `Ty`: `Std.DHashMap.Internal.AssocList` is a recursive declaration with parameters, which the recursive ...
  refused   test6: the type `α → β` has no `Ty`: not a constant type
  refused   test7: the type `α` has no `Ty`: not a constant type
-/
#guard_msgs in
#leanjs_compile_term_for_all
