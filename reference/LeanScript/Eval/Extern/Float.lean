module

public import LeanScript.Expr.Extern

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The value of an extern call: floating-point numbers

The `eval` of each family of `LeanScript.LeanInitPureExterns.Float` (see
`LeanScript.Eval.Extern` for the dispatch `Extern.eval` and how the cases are written).
-/

/-- The value of an entry of `FloatExtern` (`Init/Data/Float/Float.lean`). -/
def FloatExtern.eval : {τ : TyWf} → FloatExtern TyWf.prod τ → TyWf.Den τ
  | _, .lean_float_frexp x1 => TyWf.Den.ofProd (Float.frExp x1)
  | _, .lean_uint8_to_float x1 => UInt8.toFloat x1
  | _, .lean_float_to_bits__Float_toModel x1 => Float.toModel x1
  | _, .lean_float_to_bits__Float_toBits x1 => Float.toBits x1
  | _, .lean_float_of_bits__Float_ofBits x1 => Float.ofBits x1
  | _, .lean_float_of_bits__Float_ofModel x1 => Float.ofModel x1
  | _, .lean_float_isnan x1 => Float.isNaN x1
  | _, .log10 x1 => Float.log10 x1
  | _, .cbrt x1 => Float.cbrt x1
  | _, .log x1 => Float.log x1
  | _, .lean_float_div x1 x2 => Float.div x1 x2
  | _, .lean_float_beq x1 x2 => Float.beq x1 x2
  | _, .tan x1 => Float.tan x1
  | _, .tanh x1 => Float.tanh x1
  | _, .exp2 x1 => Float.exp2 x1
  | _, .lean_float_to_uint16 x1 => Float.toUInt16 x1
  | _, .lean_uint32_to_float x1 => UInt32.toFloat x1
  | _, .lean_float_decLe__Float_decLe x1 x2 => @Decidable.decide _ (Float.decLe x1 x2)
  | _, .lean_float_decLe__Float_le x1 x2 => Float.le x1 x2
  | _, .lean_float_to_uint64 x1 => Float.toUInt64 x1
  | _, .sqrt x1 => Float.sqrt x1
  | _, .acos x1 => Float.acos x1
  | _, .atan x1 => Float.atan x1
  | _, .acosh x1 => Float.acosh x1
  | _, .floor x1 => Float.floor x1
  | _, .fabs x1 => Float.abs x1
  | _, .lean_float_to_uint32 x1 => Float.toUInt32 x1
  | _, .lean_float_to_string x1 => Float.toString x1
  | _, .lean_uint64_to_float x1 => UInt64.toFloat x1
  | _, .lean_float_decLt__Float_decLt x1 x2 => @Decidable.decide _ (Float.decLt x1 x2)
  | _, .lean_float_decLt__Float_lt x1 x2 => Float.lt x1 x2
  | _, .lean_float_to_uint8 x1 => Float.toUInt8 x1
  | _, .sin x1 => Float.sin x1
  -- NO usize: | _, .lean_usize_to_float x1 => some (@Decidable.decide _ (USize.toFloat x1))
  | _, .cosh x1 => Float.cosh x1
  | _, .exp x1 => Float.exp x1
  | _, .ceil x1 => Float.ceil x1
  -- NO usize: | _, .lean_float_to_usize x1 => some (@Decidable.decide _ (Float.toUSize x1))
  | _, .lean_float_isfinite x1 => Float.isFinite x1
  | _, .round x1 => Float.round x1
  | _, .cos x1 => Float.cos x1
  | _, .log2 x1 => Float.log2 x1
  | _, .atanh x1 => Float.atanh x1
  | _, .atan2 x1 x2 => Float.atan2 x1 x2
  | _, .sinh x1 => Float.sinh x1
  | _, .asinh x1 => Float.asinh x1
  | _, .lean_float_mul x1 x2 => Float.mul x1 x2
  | _, .lean_uint16_to_float x1 => UInt16.toFloat x1
  | _, .asin x1 => Float.asin x1
  | _, .pow x1 x2 => Float.pow x1 x2
  | _, .lean_float_scaleb x1 x2 => Float.scaleB x1 x2
  | _, .lean_float_add x1 x2 => Float.add x1 x2
  | _, .lean_float_sub x1 x2 => Float.sub x1 x2
  | _, .lean_float_negate x1 => Float.neg x1
  | _, .lean_float_isinf x1 => Float.isInf x1

/-- The value of an entry of `SIntFloatExtern` (`Init/Data/SInt/Float.lean`). -/
def SIntFloatExtern.eval : {τ : TyWf} → SIntFloatExtern τ → TyWf.Den τ
  | _, .lean_int32_to_float x1 => Int32.toFloat x1
  | _, .lean_float_to_int16 x1 => Float.toInt16 x1
  | _, .lean_int16_to_float x1 => Int16.toFloat x1
  | _, .lean_float_to_int32 x1 => Float.toInt32 x1
  -- NO usize: | _, .lean_isize_to_float x1 => some (@Decidable.decide _ (ISize.toFloat x1))
  | _, .lean_int8_to_float x1 => Int8.toFloat x1
  | _, .lean_float_to_int8 x1 => Float.toInt8 x1
  | _, .lean_int64_to_float x1 => Int64.toFloat x1
  | _, .lean_float_to_int64 x1 => Float.toInt64 x1
  -- NO usize: | _, .lean_float_to_isize x1 => some (@Decidable.decide _ (Float.toISize x1))

/-- The value of an entry of `Float32Extern` (`Init/Data/Float/Float32.lean`). -/
def Float32Extern.eval : {τ : TyWf} → Float32Extern TyWf.prod τ → TyWf.Den τ
  | _, .tanhf x1 => Float32.tanh x1
  | _, .exp2f x1 => Float32.exp2 x1
  | _, .lean_float32_div x1 x2 => Float32.div x1 x2
  | _, .logf x1 => Float32.log x1
  | _, .lean_float32_decLe__Float32_le x1 x2 => Float32.le x1 x2
  | _, .lean_float32_decLe__Float32_decLe x1 x2 => @Decidable.decide _ (Float32.decLe x1 x2)
  | _, .lean_float_to_float32 x1 => Float.toFloat32 x1
  | _, .lean_float32_to_bits__Float32_toModel x1 => Float32.toModel x1
  | _, .lean_float32_to_bits__Float32_toBits x1 => Float32.toBits x1
  | _, .lean_float32_of_bits__Float32_ofBits x1 => Float32.ofBits x1
  | _, .lean_float32_of_bits__Float32_ofModel x1 => Float32.ofModel x1
  | _, .atanf x1 => Float32.atan x1
  | _, .acoshf x1 => Float32.acosh x1
  | _, .lean_float32_frexp x1 => TyWf.Den.ofProd (Float32.frExp x1)
  | _, .lean_float32_to_uint64 x1 => Float32.toUInt64 x1
  | _, .lean_float32_sub x1 x2 => Float32.sub x1 x2
  | _, .lean_float32_to_uint16 x1 => Float32.toUInt16 x1
  -- NO usize: | _, .lean_usize_to_float32 x1 => some (@Decidable.decide _ (USize.toFloat32 x1))
  | _, .asinf x1 => Float32.asin x1
  | _, .powf x1 x2 => Float32.pow x1 x2
  | _, .lean_float32_beq x1 x2 => Float32.beq x1 x2
  | _, .lean_uint8_to_float32 x1 => UInt8.toFloat32 x1
  | _, .tanf x1 => Float32.tan x1
  | _, .lean_float32_to_float x1 => Float32.toFloat x1
  | _, .lean_float32_isnan x1 => Float32.isNaN x1
  | _, .log10f x1 => Float32.log10 x1
  | _, .cbrtf x1 => Float32.cbrt x1
  | _, .atan2f x1 x2 => Float32.atan2 x1 x2
  | _, .sinhf x1 => Float32.sinh x1
  | _, .cosf x1 => Float32.cos x1
  | _, .lean_uint32_to_float32 x1 => UInt32.toFloat32 x1
  | _, .lean_float32_isinf x1 => Float32.isInf x1
  | _, .lean_float32_negate x1 => Float32.neg x1
  -- NO usize: | _, .lean_float32_to_usize x1 => some (@Decidable.decide _ (Float32.toUSize x1))
  | _, .ceilf x1 => Float32.ceil x1
  | _, .lean_float32_isfinite x1 => Float32.isFinite x1
  | _, .lean_float32_add x1 x2 => Float32.add x1 x2
  | _, .lean_float32_scaleb x1 x2 => Float32.scaleB x1 x2
  | _, .sinf x1 => Float32.sin x1
  | _, .lean_float32_mul x1 x2 => Float32.mul x1 x2
  | _, .lean_float32_to_string x1 => Float32.toString x1
  | _, .asinhf x1 => Float32.asinh x1
  | _, .lean_float32_to_uint32 x1 => Float32.toUInt32 x1
  | _, .log2f x1 => Float32.log2 x1
  | _, .lean_uint64_to_float32 x1 => UInt64.toFloat32 x1
  | _, .atanhf x1 => Float32.atanh x1
  | _, .floorf x1 => Float32.floor x1
  | _, .fabsf x1 => Float32.abs x1
  | _, .roundf x1 => Float32.round x1
  | _, .lean_float32_decLt__Float32_lt x1 x2 => Float32.lt x1 x2
  | _, .lean_float32_decLt__Float32_decLt x1 x2 => @Decidable.decide _ (Float32.decLt x1 x2)
  | _, .acosf x1 => Float32.acos x1
  | _, .sqrtf x1 => Float32.sqrt x1
  | _, .lean_uint16_to_float32 x1 => UInt16.toFloat32 x1
  | _, .coshf x1 => Float32.cosh x1
  | _, .expf x1 => Float32.exp x1
  | _, .lean_float32_to_uint8 x1 => Float32.toUInt8 x1

/-- The value of an entry of `SIntFloat32Extern` (`Init/Data/SInt/Float32.lean`). -/
def SIntFloat32Extern.eval : {τ : TyWf} → SIntFloat32Extern τ → TyWf.Den τ
  | _, .lean_float32_to_int64 x1 => Float32.toInt64 x1
  -- NO usize: | _, .lean_float32_to_isize x1 => some (@Decidable.decide _ (Float32.toISize x1))
  | _, .lean_int32_to_float32 x1 => Int32.toFloat32 x1
  | _, .lean_float32_to_int8 x1 => Float32.toInt8 x1
  | _, .lean_float32_to_int16 x1 => Float32.toInt16 x1
  -- NO usize: | _, .lean_isize_to_float32 x1 => some (@Decidable.decide _ (ISize.toFloat32 x1))
  | _, .lean_int8_to_float32 x1 => Int8.toFloat32 x1
  | _, .lean_float32_to_int32 x1 => Float32.toInt32 x1
  | _, .lean_int16_to_float32 x1 => Int16.toFloat32 x1
  | _, .lean_int64_to_float32 x1 => Int64.toFloat32 x1

end LeanScript

end
