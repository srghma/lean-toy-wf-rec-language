module

public import LeanScript.Expr.Extern

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The value of an extern call: the fixed-width integers

The `eval` of each family of `LeanScript.LeanInitPureExterns.FixedWidth` (see
`LeanScript.Eval.Extern` for the dispatch `Extern.eval` and how the cases are written).
-/

/-- The value of an entry of `UIntBasicAuxExtern` (`Init/Data/UInt/BasicAux.lean`). -/
def UIntBasicAuxExtern.eval : {τ : TyWf} → UIntBasicAuxExtern τ → TyWf.Den τ
  | _, .lean_uint64_to_nat__UInt64_toNat x1 => UInt64.toNat x1
  | _, .lean_uint32_to_uint8 x1 => UInt32.toUInt8 x1
  -- NO usize: | _, .lean_usize_to_nat__USize_toNat x1 => some (@Decidable.decide _ (USize.toNat x1))
  | _, .lean_uint64_to_uint32 x1 => UInt64.toUInt32 x1
  | _, .lean_uint32_to_uint16 x1 => UInt32.toUInt16 x1
  | _, .lean_uint16_to_uint32 x1 => UInt16.toUInt32 x1
  | _, .lean_uint32_to_uint64 x1 => UInt32.toUInt64 x1
  | _, .lean_uint32_of_nat__UInt32_ofNat x1 => UInt32.ofNat x1
  -- NO usize: | _, .lean_usize_add x1 x2 => some (@Decidable.decide _ (USize.add x1 x2))
  | _, .lean_uint32_sub x1 x2 => UInt32.sub x1 x2
  | _, .lean_uint16_to_nat__UInt16_toNat x1 => UInt16.toNat x1
  | _, .lean_uint16_to_uint8 x1 => UInt16.toUInt8 x1
  -- NO usize: | _, .lean_usize_sub x1 x2 => some (@Decidable.decide _ (USize.sub x1 x2))
  | _, .lean_uint32_add x1 x2 => UInt32.add x1 x2
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNat x1 => some (@Decidable.decide _ (USize.ofNat x1))
  -- NO usize: | _, .lean_usize_dec_le x1 x2 => some (@Decidable.decide _ (USize.decLe x1 x2))
  | _, .lean_uint8_to_uint64 x1 => UInt8.toUInt64 x1
  | _, .lean_uint8_to_nat__UInt8_toNat x1 => UInt8.toNat x1
  | _, .lean_uint64_of_nat__UInt64_ofNat x1 => UInt64.ofNat x1
  | _, .lean_uint8_to_uint32 x1 => UInt8.toUInt32 x1
  | _, .lean_uint16_of_nat__UInt16_ofNat x1 => UInt16.ofNat x1
  | _, .lean_uint16_to_uint64 x1 => UInt16.toUInt64 x1
  -- NO usize: | _, .lean_usize_dec_lt x1 x2 => some (@Decidable.decide _ (USize.decLt x1 x2))
  | _, .lean_uint64_to_uint8 x1 => UInt64.toUInt8 x1
  | _, .lean_uint64_to_uint16 x1 => UInt64.toUInt16 x1
  | _, .lean_uint8_to_uint16 x1 => UInt8.toUInt16 x1

/-- The value of an entry of `UInt8BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt8` entries). -/
def UInt8BasicExtern.eval : {τ : TyWf} → UInt8BasicExtern τ → TyWf.Den τ
  | _, .lean_uint8_sub x1 x2 => UInt8.sub x1 x2
  | _, .lean_uint8_neg x1 => UInt8.neg x1
  | _, .lean_uint8_lor x1 x2 => UInt8.lor x1 x2
  | _, .lean_uint8_div x1 x2 => UInt8.div x1 x2
  | _, .lean_uint8_shift_right x1 x2 => UInt8.shiftRight x1 x2
  | _, .lean_uint8_shift_left x1 x2 => UInt8.shiftLeft x1 x2
  | _, .lean_uint8_land x1 x2 => UInt8.land x1 x2
  | _, .lean_uint8_mul x1 x2 => UInt8.mul x1 x2
  | _, .lean_uint8_add x1 x2 => UInt8.add x1 x2
  | _, .lean_uint8_complement x1 => UInt8.complement x1
  | _, .lean_uint8_mod x1 x2 => UInt8.mod x1 x2
  | _, .lean_bool_to_uint8 x1 => Bool.toUInt8 x1
  | _, .lean_uint8_xor x1 x2 => UInt8.xor x1 x2

/-- The value of an entry of `UInt16BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt16` entries). -/
def UInt16BasicExtern.eval : {τ : TyWf} → UInt16BasicExtern τ → TyWf.Den τ
  | _, .lean_uint16_neg x1 => UInt16.neg x1
  | _, .lean_uint16_add x1 x2 => UInt16.add x1 x2
  | _, .lean_uint16_lor x1 x2 => UInt16.lor x1 x2
  | _, .lean_uint16_mul x1 x2 => UInt16.mul x1 x2
  | _, .lean_uint16_land x1 x2 => UInt16.land x1 x2
  | _, .lean_uint16_complement x1 => UInt16.complement x1
  | _, .lean_uint16_xor x1 x2 => UInt16.xor x1 x2
  | _, .lean_uint16_shift_left x1 x2 => UInt16.shiftLeft x1 x2
  | _, .lean_uint16_mod x1 x2 => UInt16.mod x1 x2
  | _, .lean_uint16_dec_lt x1 x2 => @Decidable.decide _ (UInt16.decLt x1 x2)
  | _, .lean_uint16_div x1 x2 => UInt16.div x1 x2
  | _, .lean_uint16_dec_le x1 x2 => @Decidable.decide _ (UInt16.decLe x1 x2)
  | _, .lean_uint16_sub x1 x2 => UInt16.sub x1 x2
  | _, .lean_bool_to_uint16 x1 => Bool.toUInt16 x1
  | _, .lean_uint16_shift_right x1 x2 => UInt16.shiftRight x1 x2

/-- The value of an entry of `UInt32BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt32` entries). -/
def UInt32BasicExtern.eval : {τ : TyWf} → UInt32BasicExtern τ → TyWf.Den τ
  | _, .lean_uint32_mod x1 x2 => UInt32.mod x1 x2
  | _, .lean_bool_to_uint32 x1 => Bool.toUInt32 x1
  | _, .lean_uint32_div x1 x2 => UInt32.div x1 x2
  | _, .lean_uint32_shift_right x1 x2 => UInt32.shiftRight x1 x2
  | _, .lean_uint32_neg x1 => UInt32.neg x1
  | _, .lean_uint32_lor x1 x2 => UInt32.lor x1 x2
  | _, .lean_uint32_xor x1 x2 => UInt32.xor x1 x2
  | _, .lean_uint32_shift_left x1 x2 => UInt32.shiftLeft x1 x2
  | _, .lean_uint32_mul x1 x2 => UInt32.mul x1 x2
  | _, .lean_uint32_land x1 x2 => UInt32.land x1 x2
  | _, .lean_uint32_complement x1 => UInt32.complement x1

/-- The value of an entry of `UInt64BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt64` entries). -/
def UInt64BasicExtern.eval : {τ : TyWf} → UInt64BasicExtern τ → TyWf.Den τ
  | _, .lean_uint64_shift_left x1 x2 => UInt64.shiftLeft x1 x2
  -- NO usize: | _, .lean_usize_land x1 x2 => some (@Decidable.decide _ (USize.land x1 x2))
  -- NO usize: | _, .lean_usize_mul x1 x2 => some (@Decidable.decide _ (USize.mul x1 x2))
  -- NO usize: | _, .lean_uint16_to_usize x1 => some (@Decidable.decide _ (UInt16.toUSize x1))
  | _, .lean_uint64_shift_right x1 x2 => UInt64.shiftRight x1 x2
  -- NO usize: | _, .lean_usize_shift_left x1 x2 => some (@Decidable.decide _ (USize.shiftLeft x1 x2))
  -- NO usize: | _, .lean_usize_xor x1 x2 => some (@Decidable.decide _ (USize.xor x1 x2))
  | _, .lean_uint64_complement x1 => UInt64.complement x1
  | _, .lean_uint64_add x1 x2 => UInt64.add x1 x2
  | _, .lean_uint64_lor x1 x2 => UInt64.lor x1 x2
  | _, .lean_uint64_mod x1 x2 => UInt64.mod x1 x2
  -- NO usize: | _, .lean_usize_lor x1 x2 => some (@Decidable.decide _ (USize.lor x1 x2))
  -- NO usize: | _, .lean_usize_neg x1 => some (@Decidable.decide _ (USize.neg x1))
  | _, .lean_uint64_div x1 x2 => UInt64.div x1 x2
  -- NO usize: | _, .lean_usize_to_uint64 x1 => some (@Decidable.decide _ (USize.toUInt64 x1))
  | _, .lean_uint64_mul x1 x2 => UInt64.mul x1 x2
  -- NO usize: | _, .lean_usize_shift_right x1 x2 => some (@Decidable.decide _ (USize.shiftRight x1 x2))
  | _, .lean_uint64_land x1 x2 => UInt64.land x1 x2
  | _, .lean_bool_to_uint64 x1 => Bool.toUInt64 x1
  | _, .lean_uint64_dec_le x1 x2 => @Decidable.decide _ (UInt64.decLe x1 x2)
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNat32 x1 x2 => some (@Decidable.decide _ (USize.ofNat32 x1 x2))
  | _, .lean_uint64_sub x1 x2 => UInt64.sub x1 x2
  | _, .lean_uint64_neg x1 => UInt64.neg x1
  -- NO usize: | _, .lean_usize_div x1 x2 => some (@Decidable.decide _ (USize.div x1 x2))
  -- NO usize: | _, .lean_uint32_to_usize x1 => some (@Decidable.decide _ (UInt32.toUSize x1))
  -- NO usize: | _, .lean_usize_to_uint16 x1 => some (@Decidable.decide _ (USize.toUInt16 x1))
  -- NO usize: | _, .lean_usize_to_uint8 x1 => some (@Decidable.decide _ (USize.toUInt8 x1))
  -- NO usize: | _, .lean_usize_mod x1 x2 => some (@Decidable.decide _ (USize.mod x1 x2))
  | _, .lean_uint64_dec_lt x1 x2 => @Decidable.decide _ (UInt64.decLt x1 x2)
  -- NO usize: | _, .lean_uint8_to_usize x1 => some (@Decidable.decide _ (UInt8.toUSize x1))
  -- NO usize: | _, .lean_bool_to_usize x1 => some (@Decidable.decide _ (Bool.toUSize x1))
  -- NO usize: | _, .lean_uint64_to_usize x1 => some (@Decidable.decide _ (UInt64.toUSize x1))
  -- NO usize: | _, .lean_usize_to_uint32 x1 => some (@Decidable.decide _ (USize.toUInt32 x1))
  -- NO usize: | _, .lean_usize_complement x1 => some (@Decidable.decide _ (USize.complement x1))
  | _, .lean_uint64_xor x1 x2 => UInt64.xor x1 x2

/-- The value of an entry of `Int8BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int8` entries). -/
def Int8BasicExtern.eval : {τ : TyWf} → Int8BasicExtern τ → TyWf.Den τ
  | _, .lean_int8_add x1 x2 => Int8.add x1 x2
  | _, .lean_int8_div x1 x2 => Int8.div x1 x2
  | _, .lean_int8_to_int16 x1 => Int8.toInt16 x1
  | _, .lean_int8_shift_right x1 x2 => Int8.shiftRight x1 x2
  | _, .lean_int8_mod x1 x2 => Int8.mod x1 x2
  | _, .lean_bool_to_int8 x1 => Bool.toInt8 x1
  | _, .lean_int8_shift_left x1 x2 => Int8.shiftLeft x1 x2
  | _, .lean_int8_xor x1 x2 => Int8.xor x1 x2
  | _, .lean_int8_complement x1 => Int8.complement x1
  | _, .lean_int8_dec_eq x1 x2 => @Decidable.decide _ (Int8.decEq x1 x2)
  | _, .lean_int8_neg x1 => Int8.neg x1
  | _, .lean_int8_dec_lt x1 x2 => @Decidable.decide _ (Int8.decLt x1 x2)
  | _, .lean_int8_abs x1 => Int8.abs x1
  | _, .lean_int8_to_int32 x1 => Int8.toInt32 x1
  | _, .lean_int8_sub x1 x2 => Int8.sub x1 x2
  | _, .lean_int8_to_int64 x1 => Int8.toInt64 x1
  | _, .lean_int8_of_nat x1 => Int8.ofNat x1
  | _, .lean_int8_dec_le x1 x2 => @Decidable.decide _ (Int8.decLe x1 x2)
  | _, .lean_int8_to_int x1 => Int8.toInt x1
  | _, .lean_int8_mul x1 x2 => Int8.mul x1 x2
  | _, .lean_int8_land x1 x2 => Int8.land x1 x2
  | _, .lean_int8_of_int x1 => Int8.ofInt x1
  | _, .lean_int8_lor x1 x2 => Int8.lor x1 x2

/-- The value of an entry of `Int16BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int16` entries). -/
def Int16BasicExtern.eval : {τ : TyWf} → Int16BasicExtern τ → TyWf.Den τ
  | _, .lean_int16_of_nat x1 => Int16.ofNat x1
  | _, .lean_int16_dec_le x1 x2 => @Decidable.decide _ (Int16.decLe x1 x2)
  | _, .lean_int16_shift_right x1 x2 => Int16.shiftRight x1 x2
  | _, .lean_int16_div x1 x2 => Int16.div x1 x2
  | _, .lean_int16_dec_lt x1 x2 => @Decidable.decide _ (Int16.decLt x1 x2)
  | _, .lean_int16_to_int x1 => Int16.toInt x1
  | _, .lean_int16_mod x1 x2 => Int16.mod x1 x2
  | _, .lean_int16_dec_eq x1 x2 => @Decidable.decide _ (Int16.decEq x1 x2)
  | _, .lean_bool_to_int16 x1 => Bool.toInt16 x1
  | _, .lean_int16_abs x1 => Int16.abs x1
  | _, .lean_int16_to_int32 x1 => Int16.toInt32 x1
  | _, .lean_int16_complement x1 => Int16.complement x1
  | _, .lean_int16_land x1 x2 => Int16.land x1 x2
  | _, .lean_int16_of_int x1 => Int16.ofInt x1
  | _, .lean_int16_mul x1 x2 => Int16.mul x1 x2
  | _, .lean_int16_shift_left x1 x2 => Int16.shiftLeft x1 x2
  | _, .lean_int16_xor x1 x2 => Int16.xor x1 x2
  | _, .lean_int16_lor x1 x2 => Int16.lor x1 x2
  | _, .lean_int16_add x1 x2 => Int16.add x1 x2
  | _, .lean_int16_to_int8 x1 => Int16.toInt8 x1
  | _, .lean_int16_neg x1 => Int16.neg x1
  | _, .lean_int16_sub x1 x2 => Int16.sub x1 x2
  | _, .lean_int16_to_int64 x1 => Int16.toInt64 x1

/-- The value of an entry of `Int32BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int32` entries). -/
def Int32BasicExtern.eval : {τ : TyWf} → Int32BasicExtern τ → TyWf.Den τ
  | _, .lean_int32_of_int x1 => Int32.ofInt x1
  | _, .lean_int32_land x1 x2 => Int32.land x1 x2
  | _, .lean_int32_mul x1 x2 => Int32.mul x1 x2
  | _, .lean_int32_dec_le x1 x2 => @Decidable.decide _ (Int32.decLe x1 x2)
  | _, .lean_int32_of_nat x1 => Int32.ofNat x1
  | _, .lean_int32_to_int64 x1 => Int32.toInt64 x1
  | _, .lean_int32_sub x1 x2 => Int32.sub x1 x2
  | _, .lean_int32_neg x1 => Int32.neg x1
  | _, .lean_int32_abs x1 => Int32.abs x1
  | _, .lean_int32_dec_eq x1 x2 => @Decidable.decide _ (Int32.decEq x1 x2)
  | _, .lean_int32_dec_lt x1 x2 => @Decidable.decide _ (Int32.decLt x1 x2)
  | _, .lean_int32_xor x1 x2 => Int32.xor x1 x2
  | _, .lean_int32_shift_left x1 x2 => Int32.shiftLeft x1 x2
  | _, .lean_int32_shift_right x1 x2 => Int32.shiftRight x1 x2
  | _, .lean_int32_complement x1 => Int32.complement x1
  | _, .lean_bool_to_int32 x1 => Bool.toInt32 x1
  | _, .lean_int32_to_int8 x1 => Int32.toInt8 x1
  | _, .lean_int32_add x1 x2 => Int32.add x1 x2
  | _, .lean_int32_lor x1 x2 => Int32.lor x1 x2
  | _, .lean_int32_mod x1 x2 => Int32.mod x1 x2
  | _, .lean_int32_to_int x1 => Int32.toInt x1
  | _, .lean_int32_to_int16 x1 => Int32.toInt16 x1
  | _, .lean_int32_div x1 x2 => Int32.div x1 x2

/-- The value of an entry of `Int64BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int64` entries). -/
def Int64BasicExtern.eval : {τ : TyWf} → Int64BasicExtern τ → TyWf.Den τ
  -- NO usize: | _, .lean_isize_complement x1 => some (@Decidable.decide _ (ISize.complement x1))
  -- NO usize: | _, .lean_int64_to_isize x1 => some (@Decidable.decide _ (Int64.toISize x1))
  | _, .lean_int64_sub x1 x2 => Int64.sub x1 x2
  -- NO usize: | _, .lean_isize_to_int8 x1 => some (@Decidable.decide _ (ISize.toInt8 x1))
  | _, .lean_int64_xor x1 x2 => Int64.xor x1 x2
  -- NO usize: | _, .lean_isize_xor x1 x2 => some (@Decidable.decide _ (ISize.xor x1 x2))
  | _, .lean_int64_to_int8 x1 => Int64.toInt8 x1
  -- NO usize: | _, .lean_isize_shift_left x1 x2 => some (@Decidable.decide _ (ISize.shiftLeft x1 x2))
  | _, .lean_int64_mul x1 x2 => Int64.mul x1 x2
  | _, .lean_int64_of_int x1 => Int64.ofInt x1
  -- NO usize: | _, .lean_int32_to_isize x1 => some (@Decidable.decide _ (Int32.toISize x1))
  | _, .lean_int64_land x1 x2 => Int64.land x1 x2
  | _, .lean_int64_lor x1 x2 => Int64.lor x1 x2
  -- NO usize: | _, .lean_isize_mod x1 x2 => some (@Decidable.decide _ (ISize.mod x1 x2))
  -- NO usize: | _, .lean_isize_shift_right x1 x2 => some (@Decidable.decide _ (ISize.shiftRight x1 x2))
  -- NO usize: | _, .lean_isize_to_int16 x1 => some (@Decidable.decide _ (ISize.toInt16 x1))
  -- NO usize: | _, .lean_isize_div x1 x2 => some (@Decidable.decide _ (ISize.div x1 x2))
  -- NO usize: | _, .lean_isize_add x1 x2 => some (@Decidable.decide _ (ISize.add x1 x2))
  -- NO usize: | _, .lean_isize_lor x1 x2 => some (@Decidable.decide _ (ISize.lor x1 x2))
  | _, .lean_int64_mod x1 x2 => Int64.mod x1 x2
  -- NO usize: | _, .lean_isize_of_int x1 => some (@Decidable.decide _ (ISize.ofInt x1))
  | _, .lean_int64_shift_left x1 x2 => Int64.shiftLeft x1 x2
  -- NO usize: | _, .lean_isize_land x1 x2 => some (@Decidable.decide _ (ISize.land x1 x2))
  -- NO usize: | _, .lean_isize_mul x1 x2 => some (@Decidable.decide _ (ISize.mul x1 x2))
  -- NO usize: | _, .lean_isize_to_int x1 => some (@Decidable.decide _ (ISize.toInt x1))
  | _, .lean_int64_dec_lt x1 x2 => @Decidable.decide _ (Int64.decLt x1 x2)
  -- NO usize: | _, .lean_isize_dec_le x1 x2 => some (@Decidable.decide _ (ISize.decLe x1 x2))
  -- NO usize: | _, .lean_isize_of_nat x1 => some (@Decidable.decide _ (ISize.ofNat x1))
  -- NO usize: | _, .lean_isize_to_int64 x1 => some (@Decidable.decide _ (ISize.toInt64 x1))
  -- NO usize: | _, .lean_isize_sub x1 x2 => some (@Decidable.decide _ (ISize.sub x1 x2))
  | _, .lean_int64_complement x1 => Int64.complement x1
  -- NO usize: | _, .lean_isize_abs x1 => some (@Decidable.decide _ (ISize.abs x1))
  -- NO usize: | _, .lean_isize_to_int32 x1 => some (@Decidable.decide _ (ISize.toInt32 x1))
  | _, .lean_int64_to_int32 x1 => Int64.toInt32 x1
  | _, .lean_int64_abs x1 => Int64.abs x1
  | _, .lean_bool_to_int64 x1 => Bool.toInt64 x1
  -- NO usize: | _, .lean_bool_to_isize x1 => some (@Decidable.decide _ (Bool.toISize x1))
  | _, .lean_int64_dec_eq x1 x2 => @Decidable.decide _ (Int64.decEq x1 x2)
  | _, .lean_int64_dec_le x1 x2 => @Decidable.decide _ (Int64.decLe x1 x2)
  | _, .lean_int64_of_nat x1 => Int64.ofNat x1
  | _, .lean_int64_to_int_sint x1 => Int64.toInt x1
  -- NO usize: | _, .lean_isize_dec_lt x1 x2 => some (@Decidable.decide _ (ISize.decLt x1 x2))
  | _, .lean_int64_neg x1 => Int64.neg x1
  -- NO usize: | _, .lean_isize_neg x1 => some (@Decidable.decide _ (ISize.neg x1))
  | _, .lean_int64_add x1 x2 => Int64.add x1 x2
  | _, .lean_int64_div x1 x2 => Int64.div x1 x2
  -- NO usize: | _, .lean_int8_to_isize x1 => some (@Decidable.decide _ (Int8.toISize x1))
  -- NO usize: | _, .lean_isize_dec_eq x1 x2 => some (@Decidable.decide _ (ISize.decEq x1 x2))
  | _, .lean_int64_to_int16 x1 => Int64.toInt16 x1
  -- NO usize: | _, .lean_int16_to_isize x1 => some (@Decidable.decide _ (Int16.toISize x1))
  | _, .lean_int64_shift_right x1 x2 => Int64.shiftRight x1 x2

/-- The value of an entry of `UIntLog2Extern` (`Init/Data/UInt/Log2.lean`). -/
def UIntLog2Extern.eval : {τ : TyWf} → UIntLog2Extern τ → TyWf.Den τ
  -- NO usize: | _, .lean_usize_log2 x1 => some (@Decidable.decide _ (USize.log2 x1))
  | _, .lean_uint16_log2 x1 => UInt16.log2 x1
  | _, .lean_uint64_log2 x1 => UInt64.log2 x1
  | _, .lean_uint8_log2 x1 => UInt8.log2 x1
  | _, .lean_uint32_log2 x1 => UInt32.log2 x1

end LeanScript

end
