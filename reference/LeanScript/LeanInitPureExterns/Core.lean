module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: the core of `Init` (`Prelude`, `Core`, `Nat`, `Int`, `Array`, `Util`, `Meta`, `Platform`)

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised).  Every family is written against
the same parameters as `LeanInitPureExtern`; only the ones its entries use become its own.
After editing the catalogue, rerun `python3 scripts/gen_externs.py`.
-/

open LeanPrimTy
open LeanPrimTyCovariant

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
  (leanName : MyTy)
  (ordering : MyTy)

--------------------
-- Init/Prelude.lean
--------------------
/-- The pure externs of `Init/Prelude.lean`. -/
inductive PreludeExtern : MyTy → Type where
  | lean_uint32_of_nat_mk : BitVec 32 → PreludeExtern uint32 -- UInt32.ofBitVec
  | lean_uint32_dec_eq : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decEq
  -- | lean_byte_array_size : ByteArray → PreludeExtern nat -- ByteArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_string_to_utf8__String_toByteArray : String → PreludeExtern byteArray -- String.toByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint32_dec_lt : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decLt
  | lean_nat_div : Nat → Nat → PreludeExtern nat -- Nat.div
  -- | lean_sorry : (αt : MyTy) → Bool → PreludeExtern αt -- sorryAx -- XXX: DONT IMPLEMENT
  | lean_uint32_of_nat__UInt32_ofNatLT : (n : Nat) → (h : n < UInt32.size) → PreludeExtern uint32 -- UInt32.ofNatLT
  | lean_uint32_of_nat__Char_ofNatAux : (n : Nat) → (h : n.isValidChar) → PreludeExtern char -- Char.ofNatAux
  | lean_array_get_borrowed : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → PreludeExtern αt -- Array.get!InternalBorrowed
  | lean_uint8_to_nat__UInt8_toBitVec : UInt8 → PreludeExtern (bitvec 8) -- UInt8.toBitVec
  | lean_nat_dec_lt : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decLt
  -- | lean_string_from_utf8_unchecked : (toByteArray : ByteArray) → toByteArray.IsValidUTF8 → PreludeExtern string -- String.ofByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_mod__Nat_modCore : Nat → Nat → PreludeExtern nat -- Nat.modCore
  | lean_nat_mod__Nat_mod : Nat → Nat → PreludeExtern nat -- Nat.mod
  | lean_array_push : (αt : MyTy) → Array (denote αt) → denote αt → PreludeExtern (array αt) -- Array.push
  -- | lean_byte_array_mk : Array UInt8 → PreludeExtern byteArray -- ByteArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_sub : Nat → Nat → PreludeExtern nat -- Nat.sub
  | lean_uint8_dec_lt : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decLt
  -- | lean_byte_array_data : ByteArray → PreludeExtern (array uint8) -- ByteArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_system_platform_nbits : PreludeExtern (lazy nat) -- System.Platform.getNumBits
  | lean_uint32_dec_le : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decLe
  | lean_array_get_size : (αt : MyTy) → Array (denote αt) → PreludeExtern nat -- Array.size
  | lean_array_to_list : (αt : MyTy) → Array (denote αt) → PreludeExtern (list αt) -- Array.toList
  | lean_nat_dec_eq__Nat_decEq : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decEq
  | lean_nat_dec_eq__Nat_beq : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.beq
  | lean_array_fget_borrowed : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → PreludeExtern αt -- Array.getInternalBorrowed
  | lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (αt : MyTy) → Nat → PreludeExtern (array αt) -- Array.emptyWithCapacity
  | lean_mk_empty_array_with_capacity__Array_mkEmpty : (αt : MyTy) → Nat → PreludeExtern (array αt) -- Array.mkEmpty
  | lean_uint8_of_nat__UInt8_ofNat : Nat → PreludeExtern uint8 -- UInt8.ofNat
  | lean_uint8_of_nat__UInt8_ofNatLT : (n : Nat) → (h : n < UInt8.size) → PreludeExtern uint8 -- UInt8.ofNatLT
  -- | lean_is_scalar : (αt : MyTy) → denote αt → PreludeExtern LeanPrimTy.bool -- isScalarObj
  | lean_uint8_dec_le : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decLe
  | lean_nat_dec_le__Nat_ble : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.ble
  | lean_nat_dec_le__Nat_decLe : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decLe
  | lean_array_get : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → PreludeExtern αt -- Array.get!Internal
  | lean_nat_add : Nat → Nat → PreludeExtern nat -- Nat.add
  -- | lean_panic_fn_borrowed : (αt : MyTy) → String → PreludeExtern αt -- panicCore
  | lean_uint16_to_nat__UInt16_toBitVec : UInt16 → PreludeExtern (bitvec 16) -- UInt16.toBitVec
  | lean_uint16_of_nat_mk : BitVec 16 → PreludeExtern uint16 -- UInt16.ofBitVec
  | lean_uint16_dec_eq : UInt16 → UInt16 → PreludeExtern LeanPrimTy.bool -- UInt16.decEq
  | lean_string_dec_eq : String → String → PreludeExtern LeanPrimTy.bool -- String.decEq
  | lean_nat_pred : Nat → PreludeExtern nat -- Nat.pred
  -- | lean_usize_of_nat__USize_ofNatLT : (n : Nat) → (h : n < LeanScript.USize_size) → PreludeExtern LeanPrimTy.usize -- USize.ofNatLT
  | lean_string_mk__String_ofList : List Char → PreludeExtern string -- String.ofList
  | lean_string_hash : String → PreludeExtern uint64 -- String.hash
  | lean_uint64_to_nat__UInt64_toBitVec : UInt64 → PreludeExtern (bitvec 64) -- UInt64.toBitVec
  | lean_uint64_of_nat_mk : BitVec 64 → PreludeExtern uint64 -- UInt64.ofBitVec
  | lean_uint32_to_nat__UInt32_toNat : UInt32 → PreludeExtern nat -- UInt32.toNat
  | lean_uint32_to_nat__UInt32_toBitVec : UInt32 → PreludeExtern (bitvec 32) -- UInt32.toBitVec
  | lean_uint64_dec_eq : UInt64 → UInt64 → PreludeExtern LeanPrimTy.bool -- UInt64.decEq
  | lean_uint16_of_nat__UInt16_ofNatLT : (n : Nat) → (h : n < UInt16.size) → PreludeExtern uint16 -- UInt16.ofNatLT
  | lean_name_eq : denote leanName → denote leanName → PreludeExtern LeanPrimTy.bool -- Lean.Name.beq
  | lean_uint8_of_nat_mk : BitVec 8 → PreludeExtern uint8 -- UInt8.ofBitVec
  -- | lean_mk_empty_byte_array : Nat → PreludeExtern byteArray -- ByteArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint8_dec_eq : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decEq
  | lean_nat_pow : Nat → Nat → PreludeExtern nat -- Nat.pow
  -- | lean_usize_dec_eq : denote LeanPrimTy.usize → denote LeanPrimTy.usize → PreludeExtern LeanPrimTy.bool -- USize.decEq
  -- | lean_usize_of_nat_mk : BitVec 64 → PreludeExtern LeanPrimTy.usize -- USize.ofBitVec
  | lean_array_fget : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → PreludeExtern αt -- Array.getInternal
  | lean_nat_mul : Nat → Nat → PreludeExtern nat -- Nat.mul
  -- | lean_usize_to_nat__USize_toBitVec : denote LeanPrimTy.usize → PreludeExtern (bitvec 64) -- USize.toBitVec
  | lean_string_utf8_byte_size : String → PreludeExtern nat -- String.utf8ByteSize
  -- | lean_byte_array_push : ByteArray → UInt8 → PreludeExtern byteArray -- ByteArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_array_mk : (αt : MyTy) → List (denote αt) → PreludeExtern (array αt) -- Array.mk
  | lean_uint64_mix_hash : UInt64 → UInt64 → PreludeExtern uint64 -- mixHash
  | lean_uint64_of_nat__UInt64_ofNatLT : (n : Nat) → (h : n < UInt64.size) → PreludeExtern uint64 -- UInt64.ofNatLT

-----------------
-- Init/Core.lean
-----------------
/-- The pure externs of `Init/Core.lean`. -/
inductive CoreExtern : MyTy → Type where
  -- | lean_task_map : (αt : MyTy) → (βt : MyTy) → (denote αt → denote βt) → denote (task αt) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → CoreExtern (task βt) -- Task.map
  -- | lean_task_spawn : (αt : MyTy) → (denote (lazy αt)) → (prio : Task.Priority := Task.Priority.default) → CoreExtern (task αt) -- Task.spawn
  | lean_strict_or : Bool → Bool → CoreExtern LeanPrimTy.bool -- strictOr
  | lean_thunk_pure : (αt : MyTy) → denote αt → CoreExtern (thunk αt) -- Thunk.pure
  | lean_mk_thunk : (αt : MyTy) → (denote (lazy αt)) → CoreExtern (thunk αt) -- Thunk.mk
  -- | lean_task_get_own : (αt : MyTy) → denote (task αt) → CoreExtern αt -- Task.get
  -- | lean_task_pure : (αt : MyTy) → denote αt → CoreExtern (task αt) -- Task.pure
  | lean_thunk_get_own : (αt : MyTy) → Thunk (denote αt) → CoreExtern αt -- Thunk.get
  | lean_strict_and : Bool → Bool → CoreExtern LeanPrimTy.bool -- strictAnd
  -- | lean_task_bind : (αt : MyTy) → (βt : MyTy) → denote (task αt) → (denote αt → denote (task βt)) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → CoreExtern (task βt) -- Task.bind

---------------------------
-- Init/Data/Int/Basic.lean
---------------------------
/-- The pure externs of `Init/Data/Int/Basic.lean`. -/
inductive IntBasicExtern : MyTy → Type where
  | lean_nat_to_int : Nat → IntBasicExtern int -- Int.ofNat
  | lean_int_dec_le : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decLe
  | lean_int_dec_lt : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decLt
  | lean_int_dec_eq : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decEq
  | lean_int_mul : Int → Int → IntBasicExtern int -- Int.mul
  | lean_int_dec_nonneg : Int → IntBasicExtern LeanPrimTy.bool -- Int.decNonneg
  | lean_int_neg_succ_of_nat : Nat → IntBasicExtern int -- Int.negSucc
  | lean_int_add : Int → Int → IntBasicExtern int -- Int.add
  | lean_int_neg : Int → IntBasicExtern int -- Int.neg
  | lean_int_sub : Int → Int → IntBasicExtern int -- Int.sub
  | lean_nat_abs : Int → IntBasicExtern nat -- Int.natAbs

-------------------------------
-- Init/Data/Nat/Div/Basic.lean
-------------------------------
/-- The pure externs of `Init/Data/Nat/Div/Basic.lean`. -/
inductive NatDivExtern : MyTy → Type where
  | lean_nat_div_exact : (x : Nat) → (y : Nat) → (h : y ∣ x) → NatDivExtern nat -- Nat.divExact

-----------------------------------
-- Init/Data/Nat/Bitwise/Basic.lean
-----------------------------------
/-- The pure externs of `Init/Data/Nat/Bitwise/Basic.lean`. -/
inductive NatBitwiseExtern : MyTy → Type where
  | lean_nat_lxor : Nat → Nat → NatBitwiseExtern nat -- Nat.xor
  | lean_nat_shiftl : Nat → Nat → NatBitwiseExtern nat -- Nat.shiftLeft
  | lean_nat_shiftr : Nat → Nat → NatBitwiseExtern nat -- Nat.shiftRight
  | lean_nat_land : Nat → Nat → NatBitwiseExtern nat -- Nat.land
  | lean_nat_lor : Nat → Nat → NatBitwiseExtern nat -- Nat.lor

-----------------
-- Init/Util.lean
-----------------
/-- The pure externs of `Init/Util.lean`. -/
inductive UtilExtern : MyTy → Type where
  -- | lean_dbg_sleep : (αt : MyTy) → UInt32 → (denote (lazy αt)) → UtilExtern αt -- dbgSleep
  -- | lean_ptr_addr : (αt : MyTy) → denote αt → UtilExtern LeanPrimTy.usize -- ptrAddrUnsafe
  -- | lean_dbg_trace : (αt : MyTy) → String → (denote (lazy αt)) → UtilExtern αt -- dbgTrace
  | lean_dbg_trace_if_shared : (αt : MyTy) → String → denote αt → UtilExtern αt -- dbgTraceIfShared
  -- | lean_dbg_stack_trace : (αt : MyTy) → (denote (lazy αt)) → UtilExtern αt -- dbgStackTrace
  -- | lean_is_exclusive_obj : (αt : MyTy) → denote αt → UtilExtern LeanPrimTy.bool -- isExclusiveUnsafe

---------------------------
-- Init/Data/Array/Set.lean
---------------------------
/-- The pure externs of `Init/Data/Array/Set.lean`. -/
inductive ArraySetExtern : MyTy → Type where
  | lean_array_set : (αt : MyTy) → Array (denote αt) → Nat → denote αt → ArraySetExtern (array αt) -- Array.set!
  | lean_array_fset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size := by get_elem_tactic) → ArraySetExtern (array αt) -- Array.set

-----------------------------
-- Init/Data/Array/Basic.lean
-----------------------------
/-- The pure externs of `Init/Data/Array/Basic.lean`. -/
inductive ArrayBasicExtern : MyTy → Type where
  | lean_array_fswap : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (j : Nat) → (h : i < xs.size := by get_elem_tactic) → (h : j < xs.size := by get_elem_tactic) → ArrayBasicExtern (array αt) -- Array.swap
  -- `USize` is `Nat` here, so this is `lean_array_fget`; `#leanscript_to_term` translates a call of `Array.uget` to that entry
  -- | lean_array_uget : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (h : i < xs.size) → ArrayBasicExtern αt -- Array.uget
  | lean_mk_array : (αt : MyTy) → Nat → denote αt → ArrayBasicExtern (array αt) -- Array.replicate
  | lean_array_swap : (αt : MyTy) → Array (denote αt) → Nat → Nat → ArrayBasicExtern (array αt) -- Array.swapIfInBounds
  -- | lean_array_uget_borrowed : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (h : i < xs.size) → ArrayBasicExtern αt -- Array.ugetBorrowed
  | lean_array_pop : (αt : MyTy) → Array (denote αt) → ArrayBasicExtern (array αt) -- Array.pop
  -- `USize` is `Nat` here, so this is `lean_array_fset`; `#leanscript_to_term` translates a call of `Array.uset` to that entry
  -- | lean_array_uset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size) → ArrayBasicExtern (array αt) -- Array.uset
  -- | lean_array_size : (αt : MyTy) → Array (denote αt) → ArrayBasicExtern LeanPrimTy.usize -- Array.usize

----------------------
-- Init/Meta/Defs.lean
----------------------
/-- The pure externs of `Init/Meta/Defs.lean`. -/
inductive MetaDefsExtern : MyTy → Type where
  | lean_version_get_special_desc : MetaDefsExtern (lazy string) -- Lean.version.getSpecialDesc
  | lean_version_get_is_release : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.version.getIsRelease
  | lean_version_get_major : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMajor
  | lean_version_get_patch : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getPatch
  | lean_internal_is_stage0 : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.Internal.isStage0
  | lean_version_get_minor : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMinor
  | lean_get_githash : MetaDefsExtern (lazy string) -- Lean.getGithash
  | lean_internal_has_llvm_backend : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.Internal.hasLLVMBackend

--------------------------
-- Init/Data/Nat/Log2.lean
--------------------------
/-- The pure externs of `Init/Data/Nat/Log2.lean`. -/
inductive NatLog2Extern : MyTy → Type where
  | lean_nat_log2 : Nat → NatLog2Extern nat -- Nat.log2

----------------------------------
-- Init/Data/Int/DivMod/Basic.lean
----------------------------------
/-- The pure externs of `Init/Data/Int/DivMod/Basic.lean`. -/
inductive IntDivModExtern : MyTy → Type where
  | lean_int_emod : Int → Int → IntDivModExtern int -- Int.emod
  | lean_int_div_exact : (x : Int) → (y : Int) → (h : y ∣ x) → IntDivModExtern int -- Int.divExact
  | lean_int_mod : Int → Int → IntDivModExtern int -- Int.tmod
  | lean_int_ediv : Int → Int → IntDivModExtern int -- Int.ediv
  | lean_int_div : Int → Int → IntDivModExtern int -- Int.tdiv

----------------------------
-- Init/System/Platform.lean
----------------------------
/-- The pure externs of `Init/System/Platform.lean`. -/
inductive PlatformExtern : MyTy → Type where
  -- | lean_internal_get_hardware_concurrency : PlatformExtern (lazy uint32) -- System.Platform.Internal.getHardwareConcurrency
  -- | lean_system_platform_linux : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsLinux
  | lean_system_platform_emscripten : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsEmscripten
  | lean_system_platform_target : PlatformExtern (lazy string) -- System.Platform.getTarget
  -- | lean_system_platform_windows : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsWindows
  -- | lean_system_platform_osx : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsOSX

end LeanScript

end
