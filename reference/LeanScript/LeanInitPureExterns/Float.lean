module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: floating-point numbers (`Float`, `Float32` and their conversions to signed integers)

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

-----------------------------
-- Init/Data/Float/Float.lean
-----------------------------
/-- The pure externs of `Init/Data/Float/Float.lean`. -/
inductive FloatExtern : MyTy → Type where
  | lean_float_frexp : Float → FloatExtern (prod float int) -- Float.frExp
  | lean_uint8_to_float : UInt8 → FloatExtern float -- UInt8.toFloat
  | lean_float_to_bits__Float_toModel : Float → FloatExtern floatModel -- Float.toModel
  | lean_float_to_bits__Float_toBits : Float → FloatExtern uint64 -- Float.toBits
  | lean_float_of_bits__Float_ofBits : UInt64 → FloatExtern float -- Float.ofBits
  | lean_float_of_bits__Float_ofModel : Float.Model → FloatExtern float -- Float.ofModel
  | lean_float_isnan : Float → FloatExtern LeanPrimTy.bool -- Float.isNaN
  | log10 : Float → FloatExtern float -- Float.log10
  | cbrt : Float → FloatExtern float -- Float.cbrt
  | log : Float → FloatExtern float -- Float.log
  | lean_float_div : Float → Float → FloatExtern float -- Float.div
  | lean_float_beq : Float → Float → FloatExtern LeanPrimTy.bool -- Float.beq
  | tan : Float → FloatExtern float -- Float.tan
  | tanh : Float → FloatExtern float -- Float.tanh
  | exp2 : Float → FloatExtern float -- Float.exp2
  | lean_float_to_uint16 : Float → FloatExtern uint16 -- Float.toUInt16
  | lean_uint32_to_float : UInt32 → FloatExtern float -- UInt32.toFloat
  | lean_float_decLe__Float_decLe : Float → Float → FloatExtern LeanPrimTy.bool -- Float.decLe
  | lean_float_decLe__Float_le : Float → Float → FloatExtern LeanPrimTy.bool -- Float.le
  | lean_float_to_uint64 : Float → FloatExtern uint64 -- Float.toUInt64
  | sqrt : Float → FloatExtern float -- Float.sqrt
  | acos : Float → FloatExtern float -- Float.acos
  | atan : Float → FloatExtern float -- Float.atan
  | acosh : Float → FloatExtern float -- Float.acosh
  | floor : Float → FloatExtern float -- Float.floor
  | fabs : Float → FloatExtern float -- Float.abs
  | lean_float_to_uint32 : Float → FloatExtern uint32 -- Float.toUInt32
  | lean_float_to_string : Float → FloatExtern string -- Float.toString
  | lean_uint64_to_float : UInt64 → FloatExtern float -- UInt64.toFloat
  | lean_float_decLt__Float_decLt : Float → Float → FloatExtern LeanPrimTy.bool -- Float.decLt
  | lean_float_decLt__Float_lt : Float → Float → FloatExtern LeanPrimTy.bool -- Float.lt
  | lean_float_to_uint8 : Float → FloatExtern uint8 -- Float.toUInt8
  | sin : Float → FloatExtern float -- Float.sin
  -- | lean_usize_to_float : denote LeanPrimTy.usize → FloatExtern float -- USize.toFloat
  | cosh : Float → FloatExtern float -- Float.cosh
  | exp : Float → FloatExtern float -- Float.exp
  | ceil : Float → FloatExtern float -- Float.ceil
  -- | lean_float_to_usize : Float → FloatExtern LeanPrimTy.usize -- Float.toUSize
  | lean_float_isfinite : Float → FloatExtern LeanPrimTy.bool -- Float.isFinite
  | round : Float → FloatExtern float -- Float.round
  | cos : Float → FloatExtern float -- Float.cos
  | log2 : Float → FloatExtern float -- Float.log2
  | atanh : Float → FloatExtern float -- Float.atanh
  | atan2 : Float → Float → FloatExtern float -- Float.atan2
  | sinh : Float → FloatExtern float -- Float.sinh
  | asinh : Float → FloatExtern float -- Float.asinh
  | lean_float_mul : Float → Float → FloatExtern float -- Float.mul
  | lean_uint16_to_float : UInt16 → FloatExtern float -- UInt16.toFloat
  | asin : Float → FloatExtern float -- Float.asin
  | pow : Float → Float → FloatExtern float -- Float.pow
  | lean_float_scaleb : Float → Int → FloatExtern float -- Float.scaleB
  | lean_float_add : Float → Float → FloatExtern float -- Float.add
  | lean_float_sub : Float → Float → FloatExtern float -- Float.sub
  | lean_float_negate : Float → FloatExtern float -- Float.neg
  | lean_float_isinf : Float → FloatExtern LeanPrimTy.bool -- Float.isInf

----------------------------
-- Init/Data/SInt/Float.lean
----------------------------
/-- The pure externs of `Init/Data/SInt/Float.lean`. -/
inductive SIntFloatExtern : MyTy → Type where
  | lean_int32_to_float : Int32 → SIntFloatExtern float -- Int32.toFloat
  | lean_float_to_int16 : Float → SIntFloatExtern int16 -- Float.toInt16
  | lean_int16_to_float : Int16 → SIntFloatExtern float -- Int16.toFloat
  | lean_float_to_int32 : Float → SIntFloatExtern int32 -- Float.toInt32
  -- | lean_isize_to_float : denote LeanPrimTy.isize → SIntFloatExtern float -- ISize.toFloat
  | lean_int8_to_float : Int8 → SIntFloatExtern float -- Int8.toFloat
  | lean_float_to_int8 : Float → SIntFloatExtern int8 -- Float.toInt8
  | lean_int64_to_float : Int64 → SIntFloatExtern float -- Int64.toFloat
  | lean_float_to_int64 : Float → SIntFloatExtern int64 -- Float.toInt64
  -- | lean_float_to_isize : Float → SIntFloatExtern LeanPrimTy.isize -- Float.toISize

-------------------------------
-- Init/Data/Float/Float32.lean
-------------------------------
/-- The pure externs of `Init/Data/Float/Float32.lean`. -/
inductive Float32Extern : MyTy → Type where
  | tanhf : Float32 → Float32Extern float32 -- Float32.tanh
  | exp2f : Float32 → Float32Extern float32 -- Float32.exp2
  | lean_float32_div : Float32 → Float32 → Float32Extern float32 -- Float32.div
  | logf : Float32 → Float32Extern float32 -- Float32.log
  | lean_float32_decLe__Float32_le : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.le
  | lean_float32_decLe__Float32_decLe : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.decLe
  | lean_float_to_float32 : Float → Float32Extern float32 -- Float.toFloat32
  | lean_float32_to_bits__Float32_toModel : Float32 → Float32Extern float32Model -- Float32.toModel
  | lean_float32_to_bits__Float32_toBits : Float32 → Float32Extern uint32 -- Float32.toBits
  | lean_float32_of_bits__Float32_ofBits : UInt32 → Float32Extern float32 -- Float32.ofBits
  | lean_float32_of_bits__Float32_ofModel : Float32.Model → Float32Extern float32 -- Float32.ofModel
  | atanf : Float32 → Float32Extern float32 -- Float32.atan
  | acoshf : Float32 → Float32Extern float32 -- Float32.acosh
  | lean_float32_frexp : Float32 → Float32Extern (prod float32 int) -- Float32.frExp
  | lean_float32_to_uint64 : Float32 → Float32Extern uint64 -- Float32.toUInt64
  | lean_float32_sub : Float32 → Float32 → Float32Extern float32 -- Float32.sub
  | lean_float32_to_uint16 : Float32 → Float32Extern uint16 -- Float32.toUInt16
  -- | lean_usize_to_float32 : denote LeanPrimTy.usize → Float32Extern float32 -- USize.toFloat32
  | asinf : Float32 → Float32Extern float32 -- Float32.asin
  | powf : Float32 → Float32 → Float32Extern float32 -- Float32.pow
  | lean_float32_beq : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.beq
  | lean_uint8_to_float32 : UInt8 → Float32Extern float32 -- UInt8.toFloat32
  | tanf : Float32 → Float32Extern float32 -- Float32.tan
  | lean_float32_to_float : Float32 → Float32Extern float -- Float32.toFloat
  | lean_float32_isnan : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isNaN
  | log10f : Float32 → Float32Extern float32 -- Float32.log10
  | cbrtf : Float32 → Float32Extern float32 -- Float32.cbrt
  | atan2f : Float32 → Float32 → Float32Extern float32 -- Float32.atan2
  | sinhf : Float32 → Float32Extern float32 -- Float32.sinh
  | cosf : Float32 → Float32Extern float32 -- Float32.cos
  | lean_uint32_to_float32 : UInt32 → Float32Extern float32 -- UInt32.toFloat32
  | lean_float32_isinf : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isInf
  | lean_float32_negate : Float32 → Float32Extern float32 -- Float32.neg
  -- | lean_float32_to_usize : Float32 → Float32Extern LeanPrimTy.usize -- Float32.toUSize
  | ceilf : Float32 → Float32Extern float32 -- Float32.ceil
  | lean_float32_isfinite : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isFinite
  | lean_float32_add : Float32 → Float32 → Float32Extern float32 -- Float32.add
  | lean_float32_scaleb : Float32 → Int → Float32Extern float32 -- Float32.scaleB
  | sinf : Float32 → Float32Extern float32 -- Float32.sin
  | lean_float32_mul : Float32 → Float32 → Float32Extern float32 -- Float32.mul
  | lean_float32_to_string : Float32 → Float32Extern string -- Float32.toString
  | asinhf : Float32 → Float32Extern float32 -- Float32.asinh
  | lean_float32_to_uint32 : Float32 → Float32Extern uint32 -- Float32.toUInt32
  | log2f : Float32 → Float32Extern float32 -- Float32.log2
  | lean_uint64_to_float32 : UInt64 → Float32Extern float32 -- UInt64.toFloat32
  | atanhf : Float32 → Float32Extern float32 -- Float32.atanh
  | floorf : Float32 → Float32Extern float32 -- Float32.floor
  | fabsf : Float32 → Float32Extern float32 -- Float32.abs
  | roundf : Float32 → Float32Extern float32 -- Float32.round
  | lean_float32_decLt__Float32_lt : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.lt
  | lean_float32_decLt__Float32_decLt : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.decLt
  | acosf : Float32 → Float32Extern float32 -- Float32.acos
  | sqrtf : Float32 → Float32Extern float32 -- Float32.sqrt
  | lean_uint16_to_float32 : UInt16 → Float32Extern float32 -- UInt16.toFloat32
  | coshf : Float32 → Float32Extern float32 -- Float32.cosh
  | expf : Float32 → Float32Extern float32 -- Float32.exp
  | lean_float32_to_uint8 : Float32 → Float32Extern uint8 -- Float32.toUInt8

------------------------------
-- Init/Data/SInt/Float32.lean
------------------------------
/-- The pure externs of `Init/Data/SInt/Float32.lean`. -/
inductive SIntFloat32Extern : MyTy → Type where
  | lean_float32_to_int64 : Float32 → SIntFloat32Extern int64 -- Float32.toInt64
  -- | lean_float32_to_isize : Float32 → SIntFloat32Extern LeanPrimTy.isize -- Float32.toISize
  | lean_int32_to_float32 : Int32 → SIntFloat32Extern float32 -- Int32.toFloat32
  | lean_float32_to_int8 : Float32 → SIntFloat32Extern int8 -- Float32.toInt8
  | lean_float32_to_int16 : Float32 → SIntFloat32Extern int16 -- Float32.toInt16
  -- | lean_isize_to_float32 : denote LeanPrimTy.isize → SIntFloat32Extern float32 -- ISize.toFloat32
  | lean_int8_to_float32 : Int8 → SIntFloat32Extern float32 -- Int8.toFloat32
  | lean_float32_to_int32 : Float32 → SIntFloat32Extern int32 -- Float32.toInt32
  | lean_int16_to_float32 : Int16 → SIntFloat32Extern float32 -- Int16.toFloat32
  | lean_int64_to_float32 : Int64 → SIntFloat32Extern float32 -- Int64.toFloat32

end LeanScript

end
