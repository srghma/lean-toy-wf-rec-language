module

public import LeanScript.Expr.Extern

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The value of an extern call: the core of `Init`

The `eval` of each family of `LeanScript.LeanInitPureExterns.Core` (see
`LeanScript.Eval.Extern` for the dispatch `Extern.eval` and how the cases are written).
-/

/-- The value of an entry of `PreludeExtern` (`Init/Prelude.lean`). -/
def PreludeExtern.eval : {τ : TyWf} → PreludeExtern TyWf.Den TyWf.list TyWf.leanName τ → TyWf.Den τ
  | _, .lean_uint32_of_nat_mk x1 => UInt32.ofBitVec x1
  | _, .lean_uint32_dec_eq x1 x2 => @Decidable.decide _ (UInt32.decEq x1 x2)
  -- a byte or float array: | _, .lean_byte_array_size x1 => ByteArray.size x1
  -- a byte or float array: | _, .lean_string_to_utf8__String_toByteArray x1 => String.toByteArray x1
  | _, .lean_uint32_dec_lt x1 x2 => @Decidable.decide _ (UInt32.decLt x1 x2)
  | _, .lean_nat_div x1 x2 => Nat.div x1 x2
  -- NO sorryAx: _, .lean_sorry x1 x2 => some (sorryAx x2)
  | _, .lean_uint32_of_nat__UInt32_ofNatLT x1 x2 => UInt32.ofNatLT x1 x2
  | _, .lean_uint32_of_nat__Char_ofNatAux x1 x2 => Char.ofNatAux x1 x2
  | _, .lean_array_get_borrowed _ x2 x3 x4 => @Array.get!Internal _ ⟨x2⟩ x3 x4  -- the entry carries the `Inhabited` default itself; borrowing is a representation detail a pure semantics does not see
  | _, .lean_uint8_to_nat__UInt8_toBitVec x1 => UInt8.toBitVec x1
  | _, .lean_nat_dec_lt x1 x2 => @Decidable.decide _ (Nat.decLt x1 x2)
  -- a byte or float array: | _, .lean_string_from_utf8_unchecked x1 x2 => String.ofByteArray x1 x2
  | _, .lean_nat_mod__Nat_modCore x1 x2 => x1 % x2  -- `Nat.modCore_eq_mod`: `Nat.modCore` is `%`, and is `@[irreducible]` with no compiled form
  | _, .lean_nat_mod__Nat_mod x1 x2 => Nat.mod x1 x2
  | _, .lean_array_push _ x2 x3 => Array.push x2 x3
  -- a byte or float array: | _, .lean_byte_array_mk x1 => ByteArray.mk x1
  | _, .lean_nat_sub x1 x2 => Nat.sub x1 x2
  | _, .lean_uint8_dec_lt x1 x2 => @Decidable.decide _ (UInt8.decLt x1 x2)
  -- a byte or float array: | _, .lean_byte_array_data x1 => ByteArray.data x1
  -- NO handle: | _, .lean_system_platform_nbits => some (@Decidable.decide _ (System.Platform.getNumBits))
  | _, .lean_uint32_dec_le x1 x2 => @Decidable.decide _ (UInt32.decLe x1 x2)
  | _, .lean_array_get_size _ x2 => Array.size x2
  | _, .lean_array_to_list _ x2 => TyWf.Den.ofList (Array.toList x2)
  | _, .lean_nat_dec_eq__Nat_decEq x1 x2 => @Decidable.decide _ (Nat.decEq x1 x2)
  | _, .lean_nat_dec_eq__Nat_beq x1 x2 => Nat.beq x1 x2
  | _, .lean_array_fget_borrowed _ x2 x3 x4 => Array.getInternal x2 x3 x4  -- borrowing is a representation detail a pure semantics does not see
  | _, .lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ x2 => Array.emptyWithCapacity x2
  | _, .lean_mk_empty_array_with_capacity__Array_mkEmpty _ x2 => Array.mkEmpty x2
  | _, .lean_uint8_of_nat__UInt8_ofNat x1 => UInt8.ofNat x1
  | _, .lean_uint8_of_nat__UInt8_ofNatLT x1 x2 => UInt8.ofNatLT x1 x2
  -- NO unsafe:| _, .lean_is_scalar x1 x2 => some (isScalarObj x2)
  | _, .lean_uint8_dec_le x1 x2 => @Decidable.decide _ (UInt8.decLe x1 x2)
  | _, .lean_nat_dec_le__Nat_ble x1 x2 => Nat.ble x1 x2
  | _, .lean_nat_dec_le__Nat_decLe x1 x2 => @Decidable.decide _ (Nat.decLe x1 x2)
  | _, .lean_array_get _ x2 x3 x4 => @Array.get!Internal _ ⟨x2⟩ x3 x4
  | _, .lean_nat_add x1 x2 => Nat.add x1 x2
  -- NO inhabited: | _, .lean_panic_fn_borrowed αt msg => some (panicCore msg)  -- `panicCore` needs an `Inhabited` default, which this entry does not carry
  | _, .lean_uint16_to_nat__UInt16_toBitVec x1 => UInt16.toBitVec x1
  | _, .lean_uint16_of_nat_mk x1 => UInt16.ofBitVec x1
  | _, .lean_uint16_dec_eq x1 x2 => @Decidable.decide _ (UInt16.decEq x1 x2)
  | _, .lean_string_dec_eq x1 x2 => @Decidable.decide _ (String.decEq x1 x2)
  | _, .lean_nat_pred x1 => Nat.pred x1
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNatLT x1 x2 => some (@Decidable.decide _ (USize.ofNatLT x1 x2))
  | _, .lean_string_mk__String_ofList x1 => String.ofList x1
  | _, .lean_string_hash x1 => String.hash x1
  | _, .lean_uint64_to_nat__UInt64_toBitVec x1 => UInt64.toBitVec x1
  | _, .lean_uint64_of_nat_mk x1 => UInt64.ofBitVec x1
  | _, .lean_uint32_to_nat__UInt32_toNat x1 => UInt32.toNat x1
  | _, .lean_uint32_to_nat__UInt32_toBitVec x1 => UInt32.toBitVec x1
  | _, .lean_uint64_dec_eq x1 x2 => @Decidable.decide _ (UInt64.decEq x1 x2)
  | _, .lean_uint16_of_nat__UInt16_ofNatLT x1 x2 => UInt16.ofNatLT x1 x2
  | _, .lean_name_eq x1 x2 => Lean.Name.beq (TyWf.Den.toName x1) (TyWf.Den.toName x2)
  | _, .lean_uint8_of_nat_mk x1 => UInt8.ofBitVec x1
  -- a byte or float array: | _, .lean_mk_empty_byte_array x1 => ByteArray.emptyWithCapacity x1
  | _, .lean_uint8_dec_eq x1 x2 => @Decidable.decide _ (UInt8.decEq x1 x2)
  | _, .lean_nat_pow x1 x2 => Nat.pow x1 x2
  -- NO usize: | _, .lean_usize_dec_eq x1 x2 => some (@Decidable.decide _ (USize.decEq x1 x2))
  -- NO usize: | _, .lean_usize_of_nat_mk x1 => some (@Decidable.decide _ (USize.ofBitVec x1))
  | _, .lean_array_fget _ x2 x3 x4 => Array.getInternal x2 x3 x4
  | _, .lean_nat_mul x1 x2 => Nat.mul x1 x2
  -- NO usize: | _, .lean_usize_to_nat__USize_toBitVec x1 => some (@Decidable.decide _ (USize.toBitVec x1))
  | _, .lean_string_utf8_byte_size x1 => String.utf8ByteSize x1
  -- a byte or float array: | _, .lean_byte_array_push x1 x2 => ByteArray.push x1 x2
  | _, .lean_array_mk _ x2 => Array.mk x2
  | _, .lean_uint64_mix_hash x1 x2 => mixHash x1 x2
  | _, .lean_uint64_of_nat__UInt64_ofNatLT x1 x2 => UInt64.ofNatLT x1 x2

/-- The value of an entry of `CoreExtern` (`Init/Core.lean`). -/
def CoreExtern.eval : {τ : TyWf} → CoreExtern TyWf.Den τ → TyWf.Den τ
  -- NO handle: | _, .lean_task_map _ _ x3 x4 x5 x6 => some (@Decidable.decide _ (Task.map x3 x4 x5 x6))
  -- NO handle: | _, .lean_task_spawn _ x2 x3 => some (@Decidable.decide _ (Task.spawn x2 x3))
  | _, .lean_strict_or x1 x2 => strictOr x1 x2
  | _, .lean_thunk_pure _ x2 => x2  -- a thunk denotes the value it will answer with
  | _, .lean_mk_thunk _ x2 => x2  -- a thunk denotes the value its body answers with
  -- NO handle: | _, .lean_task_get_own _ x2 => some (@Decidable.decide _ (Task.get x2))
  -- NO handle: | _, .lean_task_pure _ x2 => some (@Decidable.decide _ (Task.pure x2))
  | _, .lean_thunk_get_own _ x2 => Thunk.get x2
  | _, .lean_strict_and x1 x2 => strictAnd x1 x2
  -- NO handle: | _, .lean_task_bind _ _ x3 x4 x5 x6 => some (@Decidable.decide _ (Task.bind x3 x4 x5 x6))

/-- The value of an entry of `IntBasicExtern` (`Init/Data/Int/Basic.lean`). -/
def IntBasicExtern.eval : {τ : TyWf} → IntBasicExtern τ → TyWf.Den τ
  | _, .lean_nat_to_int x1 => Int.ofNat x1
  | _, .lean_int_dec_le x1 x2 => @Decidable.decide _ (Int.decLe x1 x2)
  | _, .lean_int_dec_lt x1 x2 => @Decidable.decide _ (Int.decLt x1 x2)
  | _, .lean_int_dec_eq x1 x2 => @Decidable.decide _ (Int.decEq x1 x2)
  | _, .lean_int_mul x1 x2 => Int.mul x1 x2
  | _, .lean_int_dec_nonneg x1 => @Decidable.decide _ (Int.decNonneg x1)
  | _, .lean_int_neg_succ_of_nat x1 => Int.negSucc x1
  | _, .lean_int_add x1 x2 => Int.add x1 x2
  | _, .lean_int_neg x1 => Int.neg x1
  | _, .lean_int_sub x1 x2 => Int.sub x1 x2
  | _, .lean_nat_abs x1 => Int.natAbs x1

/-- The value of an entry of `NatDivExtern` (`Init/Data/Nat/Div/Basic.lean`). -/
def NatDivExtern.eval : {τ : TyWf} → NatDivExtern τ → TyWf.Den τ
  | _, .lean_nat_div_exact x1 x2 x3 => Nat.divExact x1 x2 x3

/-- The value of an entry of `NatBitwiseExtern` (`Init/Data/Nat/Bitwise/Basic.lean`). -/
def NatBitwiseExtern.eval : {τ : TyWf} → NatBitwiseExtern τ → TyWf.Den τ
  | _, .lean_nat_lxor x1 x2 => Nat.xor x1 x2
  | _, .lean_nat_shiftl x1 x2 => Nat.shiftLeft x1 x2
  | _, .lean_nat_shiftr x1 x2 => Nat.shiftRight x1 x2
  | _, .lean_nat_land x1 x2 => Nat.land x1 x2
  | _, .lean_nat_lor x1 x2 => Nat.lor x1 x2

/-- The value of an entry of `UtilExtern` (`Init/Util.lean`). -/
def UtilExtern.eval : {τ : TyWf} → UtilExtern TyWf.Den τ → TyWf.Den τ
  -- NO handle: | _, .lean_dbg_sleep _ x2 x3 => some (@Decidable.decide _ (dbgSleep x2 x3))
  -- NO usize: | _, .lean_ptr_addr _ x2 => some (@Decidable.decide _ (ptrAddrUnsafe x2))
  -- NO handle: | _, .lean_dbg_trace _ x2 x3 => some (@Decidable.decide _ (dbgTrace x2 x3))
  | _, .lean_dbg_trace_if_shared _ x2 x3 => dbgTraceIfShared x2 x3
  -- NO handle: | _, .lean_dbg_stack_trace _ x2 => some (@Decidable.decide _ (dbgStackTrace x2))
  -- NO unsafe:| _, .lean_is_exclusive_obj x1 x2 => some (isExclusiveUnsafe x2)

/-- The value of an entry of `ArraySetExtern` (`Init/Data/Array/Set.lean`). -/
def ArraySetExtern.eval : {τ : TyWf} → ArraySetExtern TyWf.Den τ → TyWf.Den τ
  | _, .lean_array_set _ x2 x3 x4 => Array.set! x2 x3 x4
  | _, .lean_array_fset _ x2 x3 x4 x5 => Array.set x2 x3 x4 x5

/-- The value of an entry of `ArrayBasicExtern` (`Init/Data/Array/Basic.lean`). -/
def ArrayBasicExtern.eval : {τ : TyWf} → ArrayBasicExtern TyWf.Den τ → TyWf.Den τ
  | _, .lean_array_fswap _ x2 x3 x4 x5 x6 => Array.swap x2 x3 x4 x5 x6
  -- `USize` is `Nat` here (`lean_array_fget`): | _, .lean_array_uget _ x2 x3 x4 => Array.uget x2 x3 x4
  | _, .lean_mk_array _ x2 x3 => Array.replicate x2 x3
  | _, .lean_array_swap _ x2 x3 x4 => Array.swapIfInBounds x2 x3 x4
  -- NO unsafe:| _, .lean_array_uget_borrowed x1 x2 x3 x4 => some (Array.ugetBorrowed x2 x3 x4)
  | _, .lean_array_pop _ x2 => Array.pop x2
  -- `USize` is `Nat` here (`lean_array_fset`): | _, .lean_array_uset _ x2 x3 x4 x5 => Array.uset x2 x3 x4 x5
  -- NO usize: | _, .lean_array_size _ x2 => some (@Decidable.decide _ (Array.usize x2))

/-- The value of an entry of `MetaDefsExtern` (`Init/Meta/Defs.lean`). -/
def MetaDefsExtern.eval : {τ : TyWf} → MetaDefsExtern τ → TyWf.Den τ
  | _, .lean_version_get_special_desc => ("leanscript" : String)
  | _, .lean_version_get_is_release => false
  | _, .lean_version_get_major => (0 : Nat)
  | _, .lean_version_get_patch => (0 : Nat)
  | _, .lean_internal_is_stage0 => false
  | _, .lean_version_get_minor => (0 : Nat)
  | _, .lean_get_githash => ("leanscript" : String)
  | _, .lean_internal_has_llvm_backend => false

/-- The value of an entry of `NatLog2Extern` (`Init/Data/Nat/Log2.lean`). -/
def NatLog2Extern.eval : {τ : TyWf} → NatLog2Extern τ → TyWf.Den τ
  | _, .lean_nat_log2 x1 => Nat.log2 x1

/-- The value of an entry of `IntDivModExtern` (`Init/Data/Int/DivMod/Basic.lean`). -/
def IntDivModExtern.eval : {τ : TyWf} → IntDivModExtern τ → TyWf.Den τ
  | _, .lean_int_emod x1 x2 => Int.emod x1 x2
  | _, .lean_int_div_exact x1 x2 x3 => Int.divExact x1 x2 x3
  | _, .lean_int_mod x1 x2 => Int.tmod x1 x2
  | _, .lean_int_ediv x1 x2 => Int.ediv x1 x2
  | _, .lean_int_div x1 x2 => Int.tdiv x1 x2

/-- The value of an entry of `PlatformExtern` (`Init/System/Platform.lean`). -/
def PlatformExtern.eval : {τ : TyWf} → PlatformExtern τ → TyWf.Den τ
  -- NO handle: | _, .lean_internal_get_hardware_concurrency => some (@Decidable.decide _ (System.Platform.Internal.getHardwareConcurrency))
  -- NO handle: | _, .lean_system_platform_linux => some (@Decidable.decide _ (System.Platform.getIsLinux))
  | _, .lean_system_platform_emscripten => false
  | _, .lean_system_platform_target => ("nodeorbrowser" : String)
  -- NO handle: | _, .lean_system_platform_windows => some (@Decidable.decide _ (System.Platform.getIsWindows))
  -- NO handle: | _, .lean_system_platform_osx => some (@Decidable.decide _ (System.Platform.getIsOSX))

end LeanScript

end
