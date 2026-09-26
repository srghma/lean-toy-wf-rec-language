module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
public import LeanScript.LeanInitPureExterns.Core
public import LeanScript.LeanInitPureExterns.FixedWidth
public import LeanScript.LeanInitPureExterns.String
public import LeanScript.LeanInitPureExterns.Float
-- public import Init.Data.FloatArray.Basic
-- public import Init.System.IO
-- public import Init.System.Promise
-- public import Init.ShareCommon
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

-- `usize`/`isize` are `uint64`/`int64` in this grammar, so every entry that speaks about
-- one is already covered by the `UInt64`/`Int64` entries and is commented out below.
-- protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64
-- protected abbrev LeanPrimTy.isize : LeanPrimTy := int64
-- protected abbrev USize_size : Nat := UInt64.size
-- protected abbrev LeanPrimTy.byteArray : LeanPrimTyCovariant LeanPrimTy := Array UInt8 -- Though array doesnt have analogues to lean_byte_array_copy_slice, lean_byte_array_hash, lean_sarray_dec_eq, lean_string_validate_utf8, lean_string_from_utf8_unchecked, lean_string_to_utf8, lean_string_utf8_get_fast - we will support them differently
-- protected abbrev LeanPrimTy.floatArray : LeanPrimTyCovariant LeanPrimTy := Array Float

variable {MyTy : Type}
  (denote : MyTy → Type)
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (list : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  -- the run-time handles are not values, so nothing that speaks about one is listed
  -- (`IO.Promise`, `IO.Process.Child`, `ShareCommon.Object`, `ShareCommon.State`)
  -- (io_promise : MyTy → MyTy)
  -- (io_process_child : IO.Process.StdioConfig → MyTy)
  -- (shareCommon_object : MyTy)
  -- (shareCommon_stateFactory : Type)
  -- (shareCommon_state : shareCommon_stateFactory -> MyTy)
  -- `Lean.Name` is an ordinary inductive of the language (its `LeanScriptTyWf` instance is
  -- in `LeanScript.Ty.Instances`); no entry of the catalogue answers with one
  (leanName : MyTy)
  (ordering : MyTy)
  -- A byte array is `Array UInt8` and a float array is `Array Float`, so neither is a
  -- type former of its own here; the entries that speak about one are commented out
  -- below, and will be supported either through the ordinary array entries or through a
  -- separate API.
  -- (byteArray : MyTy)
  -- (floatArray : MyTy)

/-!
## The catalogue, in two levels

The families are in four modules, by theme: `LeanScript.LeanInitPureExterns.Core`
(`Prelude`, `Core`, `Nat`, `Int`, `Array`, …), `.FixedWidth` (`UInt8` … `Int64`),
`.String` and `.Float`.  This module holds the sections of `Init` whose entries are all
commented out, and `LeanInitPureExtern` itself.

Each `-- Init/…` section of the catalogue is an inductive of its own (a *family*,
`PreludeExtern`, `StringBasicExtern`, …; the long `UInt`/`SInt` sections are split by
width), and `LeanInitPureExtern` has one constructor per family, holding an entry of it.
The constructors of the entries are the families' (`PreludeExtern.lean_nat_add`); the
module `LeanScript.LeanInitPureExternShorthands` derives for each one a shorthand
in `LeanInitPureExtern`'s own namespace (`LeanInitPureExtern.lean_nat_add a b` is
`.preludeExtern (.lean_nat_add a b)`), usable in patterns as well, so an entry is still written
`.lean_nat_add a b` wherever a `LeanInitPureExtern` is expected.

Two reasons for the split:
* the compiled runtime keeps a constructor's number in 8 bits, and only the numbers
  `0 … 243` are for ordinary constructors, so compiled code cannot build a constructor
  (with fields) numbered past `243`: with one inductive of 460 entries, a definition
  building one of the later ones did not compile ("tag too big");
* a `match` on an inductive is reduced through its recursor, which takes one minor
  premise per constructor, so every call of a 460-way `Extern.eval` instantiated 460
  alternatives; the two-level `Extern.eval` instantiates the families plus one family.

Every family is written against the same parameters as `LeanInitPureExtern`, but only
the ones its entries use are its own parameters (as for any inductive in a `variable`
context), so the constructor of `LeanInitPureExtern` applies each family to those:
when an entry that uses another parameter (`option`, say) is added to a family, add it
there too.  After editing the catalogue, rerun `python3 scripts/gen_externs.py`.
-/

----------------------
-- Init/Data/Repr.lean: every entry is commented out, so it has no family
----------------------
-- | lean_string_of_usize : denote LeanPrimTy.usize → LeanInitPureExtern string -- USize.repr

-------------------------
-- Init/Data/Nat/Gcd.lean: every entry is commented out, so it has no family
-------------------------
-- `Nat.gcd` is translated as an ordinary function (from its definition, as if it had no
-- `@[extern]`), and `#leanscript_to_term` reads `Nat.gcd._unary` as `Nat.gcd`
-- | lean_nat_gcd__Nat_gcd__unary : (_ : Nat) ×' Nat → LeanInitPureExtern nat -- Nat.gcd._unary
-- | lean_nat_gcd__Nat_gcd : Nat → Nat → LeanInitPureExtern nat -- Nat.gcd

---------------------------------
-- Init/Data/ByteArray/Basic.lean: every entry is commented out, so it has no family
---------------------------------
-- | lean_byte_array_copy_slice : ByteArray → Nat → ByteArray → Nat → Nat → (exact : Bool := true) → LeanInitPureExtern byteArray -- ByteArray.copySlice -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_hash : ByteArray → LeanInitPureExtern uint64 -- ByteArray.hash -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_size__ByteArray_usize : ByteArray → LeanInitPureExtern LeanPrimTy.usize -- ByteArray.usize
-- | lean_sarray_dec_eq__ByteArray_beq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.beq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_dec_eq__ByteArray_decEq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.decEq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_set : ByteArray → Nat → UInt8 → LeanInitPureExtern byteArray -- ByteArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_fget : (a : ByteArray) → (i : Nat) → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_fset : (a : ByteArray) → (i : Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_uget : (a : ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_get : ByteArray → Nat → LeanInitPureExtern uint8 -- ByteArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)

----------------------------------
-- Init/Data/FloatArray/Basic.lean: every entry is commented out, so it has no family
----------------------------------
-- | lean_mk_empty_float_array : Nat → LeanInitPureExtern floatArray -- FloatArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_get : FloatArray → Nat → LeanInitPureExtern float -- FloatArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_uget : (a : FloatArray) → (i : USize) → (h : i.toNat < a.size) → LeanInitPureExtern float -- FloatArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_fset : (ds : FloatArray) → (i : Nat) → Float → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_uset : (a : FloatArray) → (i : USize) → Float → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_fget : (ds : FloatArray) → (i : Nat) → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern float -- FloatArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_set : FloatArray → Nat → Float → LeanInitPureExtern floatArray -- FloatArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_data : FloatArray → LeanInitPureExtern (array float) -- FloatArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_size__FloatArray_usize : FloatArray → LeanInitPureExtern LeanPrimTy.usize -- FloatArray.usize
-- | lean_float_array_mk : Array Float → LeanInitPureExtern floatArray -- FloatArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_size : FloatArray → LeanInitPureExtern nat -- FloatArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_push : FloatArray → Float → LeanInitPureExtern floatArray -- FloatArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)

----------------------
-- Init/System/IO.lean: every entry is commented out, so it has no family
----------------------
-- | lean_io_process_child_pid : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitPureExtern uint32 -- IO.Process.Child.pid

---------------------------
-- Init/System/Promise.lean: every entry is commented out, so it has no family
---------------------------
-- | lean_io_promise_result_opt : (αt : MyTy) → denote (io_promise αt) → LeanInitPureExtern (task (option αt)) -- IO.Promise.result?
-- | lean_option_get_or_block : (αt : MyTy) → Option (denote αt) → LeanInitPureExtern αt -- _private.Init.System.Promise.0.IO.Option.getOrBlock!

------------------------
-- Init/ShareCommon.lean: every entry is commented out, so it has no family
------------------------
-- | lean_sharecommon_quick : (αt : MyTy) → denote αt → LeanInitPureExtern αt -- ShareCommon.shareCommon'
-- | lean_state_sharecommon : (αt : MyTy) → {σ : shareCommon_stateFactory} → denote (shareCommon_state σ) → denote αt → LeanInitPureExtern (prod αt (shareCommon_state σ)) -- ShareCommon.State.shareCommon
-- | lean_sharecommon_eq : denote shareCommon_object → denote shareCommon_object → LeanInitPureExtern LeanPrimTy.bool -- ShareCommon.Object.eq
-- | lean_sharecommon_hash : denote shareCommon_object → LeanInitPureExtern uint64 -- ShareCommon.Object.hash

/-- A pure extern of `Init`, applied to all of its arguments (and to the proofs it takes):
    an entry of one of the families above.

    **No `DecidableEq`/`BEq`.**  `Float`, `Float32` and their models have `DecidableEq`
    (structural equality of the bits), so the `Float` fields are not what prevents it.
    What does:
    * some entries hold **functions** — `lean_string_foldl` holds a
      `String → Char → String`, and `lean_string_any`, `lean_string_nextwhile`,
      `lean_substring_all` and `lean_substring_takewhile` a `Char → Bool` — and equality
      of functions like `String → Char → String` cannot be decided;
    * other fields are values `denote αt` of an arbitrary type of the language, which can
      itself be a function type;
    * and the index of an entry is computed through the abstract coercions and type
      formers above, so `deriving DecidableEq` cannot unify the indices of two entries. -/
inductive LeanInitPureExtern : MyTy → Type where
  /-- An entry of `PreludeExtern` (`Init/Prelude.lean`). -/
  | preludeExtern {τ : MyTy} : PreludeExtern denote list leanName τ → LeanInitPureExtern τ
  /-- An entry of `CoreExtern` (`Init/Core.lean`). -/
  | coreExtern {τ : MyTy} : CoreExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `IntBasicExtern` (`Init/Data/Int/Basic.lean`). -/
  | intBasicExtern {τ : MyTy} : IntBasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatDivExtern` (`Init/Data/Nat/Div/Basic.lean`). -/
  | natDivExtern {τ : MyTy} : NatDivExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatBitwiseExtern` (`Init/Data/Nat/Bitwise/Basic.lean`). -/
  | natBitwiseExtern {τ : MyTy} : NatBitwiseExtern τ → LeanInitPureExtern τ
  /-- An entry of `UIntBasicAuxExtern` (`Init/Data/UInt/BasicAux.lean`). -/
  | uintBasicAuxExtern {τ : MyTy} : UIntBasicAuxExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringBootstrapExtern` (`Init/Data/String/Bootstrap.lean`). -/
  | stringBootstrapExtern {τ : MyTy} : StringBootstrapExtern τ → LeanInitPureExtern τ
  /-- An entry of `UtilExtern` (`Init/Util.lean`). -/
  | utilExtern {τ : MyTy} : UtilExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `ArraySetExtern` (`Init/Data/Array/Set.lean`). -/
  | arraySetExtern {τ : MyTy} : ArraySetExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `ArrayBasicExtern` (`Init/Data/Array/Basic.lean`). -/
  | arrayBasicExtern {τ : MyTy} : ArrayBasicExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `MetaDefsExtern` (`Init/Meta/Defs.lean`). -/
  | metaDefsExtern {τ : MyTy} : MetaDefsExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatLog2Extern` (`Init/Data/Nat/Log2.lean`). -/
  | natLog2Extern {τ : MyTy} : NatLog2Extern τ → LeanInitPureExtern τ
  /-- An entry of `IntDivModExtern` (`Init/Data/Int/DivMod/Basic.lean`). -/
  | intDivModExtern {τ : MyTy} : IntDivModExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt8BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt8` entries). -/
  | uint8BasicExtern {τ : MyTy} : UInt8BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt16BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt16` entries). -/
  | uint16BasicExtern {τ : MyTy} : UInt16BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt32BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt32` entries). -/
  | uint32BasicExtern {τ : MyTy} : UInt32BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt64BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt64` entries). -/
  | uint64BasicExtern {τ : MyTy} : UInt64BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringPosRawExtern` (`Init/Data/String/PosRaw.lean`). -/
  | stringPosRawExtern {τ : MyTy} : StringPosRawExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringDefsExtern` (`Init/Data/String/Defs.lean`). -/
  | stringDefsExtern {τ : MyTy} : StringDefsExtern τ → LeanInitPureExtern τ
  /-- An entry of `PlatformExtern` (`Init/System/Platform.lean`). -/
  | platformExtern {τ : MyTy} : PlatformExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringBasicExtern` (`Init/Data/String/Basic.lean`). -/
  | stringBasicExtern {τ : MyTy} : StringBasicExtern option list τ → LeanInitPureExtern τ
  /-- An entry of `StringLengthExtern` (`Init/Data/String/Length.lean`). -/
  | stringLengthExtern {τ : MyTy} : StringLengthExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int8BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int8` entries). -/
  | int8BasicExtern {τ : MyTy} : Int8BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int16BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int16` entries). -/
  | int16BasicExtern {τ : MyTy} : Int16BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int32BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int32` entries). -/
  | int32BasicExtern {τ : MyTy} : Int32BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int64BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int64` entries). -/
  | int64BasicExtern {τ : MyTy} : Int64BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringPatternExtern` (`Init/Data/String/Pattern/Basic.lean`). -/
  | stringPatternExtern {τ : MyTy} : StringPatternExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringSliceExtern` (`Init/Data/String/Slice.lean`). -/
  | stringSliceExtern {τ : MyTy} : StringSliceExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringModifyExtern` (`Init/Data/String/Modify.lean`). -/
  | stringModifyExtern {τ : MyTy} : StringModifyExtern τ → LeanInitPureExtern τ
  /-- An entry of `FloatExtern` (`Init/Data/Float/Float.lean`). -/
  | floatExtern {τ : MyTy} : FloatExtern prod τ → LeanInitPureExtern τ
  /-- An entry of `UIntLog2Extern` (`Init/Data/UInt/Log2.lean`). -/
  | uintLog2Extern {τ : MyTy} : UIntLog2Extern τ → LeanInitPureExtern τ
  /-- An entry of `SIntFloatExtern` (`Init/Data/SInt/Float.lean`). -/
  | sIntFloatExtern {τ : MyTy} : SIntFloatExtern τ → LeanInitPureExtern τ
  /-- An entry of `Float32Extern` (`Init/Data/Float/Float32.lean`). -/
  | float32Extern {τ : MyTy} : Float32Extern prod τ → LeanInitPureExtern τ
  /-- An entry of `SIntFloat32Extern` (`Init/Data/SInt/Float32.lean`). -/
  | sIntFloat32Extern {τ : MyTy} : SIntFloat32Extern τ → LeanInitPureExtern τ
  /-- An entry of `OrdStringExtern` (`Init/Data/Ord/String.lean`). -/
  | ordStringExtern {τ : MyTy} : OrdStringExtern ordering τ → LeanInitPureExtern τ

end LeanScript

end
