module

public import LeanScript.Eval.Extern.Core
public import LeanScript.Eval.Extern.FixedWidth
public import LeanScript.Eval.Extern.String
public import LeanScript.Eval.Extern.Float

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The value of an extern call

`Extern.eval` gives every pure extern of `Init`, applied to values, the value the Lean function it implements
answers with.  The catalogue is in two levels (`LeanScript.LeanInitPureExterns`), and so is
`Extern.eval`: a short dispatch on the family of the entry, to the `eval` of that family
(`PreludeExtern.eval`, `StringBasicExtern.eval`, …).  Reducing a call thus goes through a
split over the 35 families and one over the entries of one family (at most 55), not
through one split over all 460 entries.  An extern holds its arguments as values, so each
family's `eval` is a plain case analysis: each case applies the Lean function to the arguments — the native function itself, so a
term runs what the compiled program runs.  An entry that takes a proof (`Array.getInternal`,
`String.Pos.Raw.next'`, `String.Pos.next`, ...) holds it, and the case hands it to the Lean
function.  `Lean.Name.beq` reads its arguments back as `Lean.Name`s (`TyWf.Den.toName`).
The entries the catalogue comments
out (the `USize`/`ISize` entries, the byte and float arrays, the run-time handles, and the
entries whose meaning is not a value) are commented out here too.

Where the result has one of the derived type formers of `LeanScript.Expr.Extern`, the Lean value
is converted into the value of that shape: a `List`, an `Option`, a pair and an
`Ordering` become a value of `TyWf.list`, `TyWf.option`, `TyWf.prod` and `TyWf.ordering`.
(An *array* result needs no conversion: an array of the language denotes a Lean
`Array`.)

The `eval`s of the families are in `LeanScript.Eval.Extern.Core`, `.FixedWidth`,
`.String` and `.Float`, one module per module of the catalogue.
-/

-- the entries of the sections of the catalogue whose entries are all commented out (so
-- they have no family)
-- NO usize: | _, .lean_string_of_usize x1 => some (@Decidable.decide _ (USize.repr x1))
-- `Nat.gcd` is an ordinary function: | _, .lean_nat_gcd__Nat_gcd__unary x1 => Nat.gcd x1.1 x1.2
-- `Nat.gcd` is an ordinary function: | _, .lean_nat_gcd__Nat_gcd x1 x2 => Nat.gcd x1 x2
-- a byte or float array: | _, .lean_byte_array_copy_slice x1 x2 x3 x4 x5 x6 => ByteArray.copySlice x1 x2 x3 x4 x5 x6
-- a byte or float array: | _, .lean_byte_array_hash x1 => ByteArray.hash x1
-- NO usize: | _, .lean_sarray_size__ByteArray_usize x1 => some (@Decidable.decide _ (ByteArray.usize x1))
-- a byte or float array: | _, .lean_sarray_dec_eq__ByteArray_beq x1 x2 => ByteArray.beq x1 x2
-- a byte or float array: | _, .lean_sarray_dec_eq__ByteArray_decEq x1 x2 => @Decidable.decide _ (ByteArray.decEq x1 x2)
-- a byte or float array: | _, .lean_byte_array_set x1 x2 x3 => ByteArray.set! x1 x2 x3
-- a byte or float array: | _, .lean_byte_array_fget x1 x2 x3 => ByteArray.get x1 x2 x3
-- a byte or float array: | _, .lean_byte_array_uset x1 x2 x3 x4 => ByteArray.uset x1 x2 x3 x4
-- a byte or float array: | _, .lean_byte_array_fset x1 x2 x3 x4 => ByteArray.set x1 x2 x3 x4
-- a byte or float array: | _, .lean_byte_array_uget x1 x2 x3 => ByteArray.uget x1 x2 x3
-- a byte or float array: | _, .lean_byte_array_get x1 x2 => ByteArray.get! x1 x2
-- a byte or float array: | _, .lean_mk_empty_float_array x1 => FloatArray.emptyWithCapacity x1
-- a byte or float array: | _, .lean_float_array_get x1 x2 => FloatArray.get! x1 x2
-- a byte or float array: | _, .lean_float_array_uget x1 x2 x3 => FloatArray.uget x1 x2 x3
-- a byte or float array: | _, .lean_float_array_fset x1 x2 x3 x4 => FloatArray.set x1 x2 x3 x4
-- a byte or float array: | _, .lean_float_array_uset x1 x2 x3 x4 => FloatArray.uset x1 x2 x3 x4
-- a byte or float array: | _, .lean_float_array_fget x1 x2 x3 => FloatArray.get x1 x2 x3
-- a byte or float array: | _, .lean_float_array_set x1 x2 x3 => FloatArray.set! x1 x2 x3
-- a byte or float array: | _, .lean_float_array_data x1 => FloatArray.data x1
-- NO usize: | _, .lean_sarray_size__FloatArray_usize x1 => some (@Decidable.decide _ (FloatArray.usize x1))
-- a byte or float array: | _, .lean_float_array_mk x1 => FloatArray.mk x1
-- a byte or float array: | _, .lean_float_array_size x1 => FloatArray.size x1
-- a byte or float array: | _, .lean_float_array_push x1 x2 => FloatArray.push x1 x2
-- NO handle: | _, .lean_io_process_child_pid x1 => IO.Process.Child.pid x1
-- NO handle: | _, .lean_io_promise_result_opt _ x2 => some (@Decidable.decide _ (IO.Promise.result? x2))
-- NO private: _, .lean_option_get_or_block x1 x2 => some (_private.Init.System.Promise.0.IO.Option.getOrBlock! x2)
-- NO handle: | _, .lean_sharecommon_quick _ x2 => ShareCommon.shareCommon' x2
-- NO handle: | _, .lean_state_sharecommon _ x2 x3 => ShareCommon.State.shareCommon x2 x3
-- NO unsafe:| _, .lean_sharecommon_eq x1 x2 => some (ShareCommon.Object.eq x1 x2)
-- NO unsafe:| _, .lean_sharecommon_hash x1 => some (ShareCommon.Object.hash x1)

/-- The value of a pure extern of `Init`: the Lean function it implements, applied to its
    arguments.  A short dispatch to the `eval` of the entry's family. -/
def Extern.eval : {τ : TyWf} → Extern τ → TyWf.Den τ
  | _, .preludeExtern e => PreludeExtern.eval e
  | _, .coreExtern e => CoreExtern.eval e
  | _, .intBasicExtern e => IntBasicExtern.eval e
  | _, .natDivExtern e => NatDivExtern.eval e
  | _, .natBitwiseExtern e => NatBitwiseExtern.eval e
  | _, .uintBasicAuxExtern e => UIntBasicAuxExtern.eval e
  | _, .stringBootstrapExtern e => StringBootstrapExtern.eval e
  | _, .utilExtern e => UtilExtern.eval e
  | _, .arraySetExtern e => ArraySetExtern.eval e
  | _, .arrayBasicExtern e => ArrayBasicExtern.eval e
  | _, .metaDefsExtern e => MetaDefsExtern.eval e
  | _, .natLog2Extern e => NatLog2Extern.eval e
  | _, .intDivModExtern e => IntDivModExtern.eval e
  | _, .uint8BasicExtern e => UInt8BasicExtern.eval e
  | _, .uint16BasicExtern e => UInt16BasicExtern.eval e
  | _, .uint32BasicExtern e => UInt32BasicExtern.eval e
  | _, .uint64BasicExtern e => UInt64BasicExtern.eval e
  | _, .stringPosRawExtern e => StringPosRawExtern.eval e
  | _, .stringDefsExtern e => StringDefsExtern.eval e
  | _, .platformExtern e => PlatformExtern.eval e
  | _, .stringBasicExtern e => StringBasicExtern.eval e
  | _, .stringLengthExtern e => StringLengthExtern.eval e
  | _, .int8BasicExtern e => Int8BasicExtern.eval e
  | _, .int16BasicExtern e => Int16BasicExtern.eval e
  | _, .int32BasicExtern e => Int32BasicExtern.eval e
  | _, .int64BasicExtern e => Int64BasicExtern.eval e
  | _, .stringPatternExtern e => StringPatternExtern.eval e
  | _, .stringSliceExtern e => StringSliceExtern.eval e
  | _, .stringModifyExtern e => StringModifyExtern.eval e
  | _, .floatExtern e => FloatExtern.eval e
  | _, .uintLog2Extern e => UIntLog2Extern.eval e
  | _, .sIntFloatExtern e => SIntFloatExtern.eval e
  | _, .float32Extern e => Float32Extern.eval e
  | _, .sIntFloat32Extern e => SIntFloat32Extern.eval e
  | _, .ordStringExtern e => OrdStringExtern.eval e

end LeanScript

end
