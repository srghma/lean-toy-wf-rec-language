module

public import LeanScript.Expr.Extern

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# The value of an extern call: strings

The `eval` of each family of `LeanScript.LeanInitPureExterns.String` (see
`LeanScript.Eval.Extern` for the dispatch `Extern.eval` and how the cases are written).
-/

/-- The value of an entry of `StringBootstrapExtern` (`Init/Data/String/Bootstrap.lean`). -/
def StringBootstrapExtern.eval : {τ : TyWf} → StringBootstrapExtern τ → TyWf.Den τ
  | _, .lean_string_utf8_get__String_Internal_get x1 x2 => String.Internal.get x1 x2
  | _, .lean_string_trim x1 => String.Internal.trim x1
  | _, .lean_substring_drop x1 x2 => Substring.Raw.Internal.drop x1 x2
  | _, .lean_substring_prev x1 x2 => Substring.Raw.Internal.prev x1 x2
  | _, .lean_substring_extract x1 x2 x3 => Substring.Raw.Internal.extract x1 x2 x3
  | _, .lean_string_foldl x1 x2 x3 => String.Internal.foldl x1 x2 x3
  | _, .lean_substring_tostring x1 => Substring.Raw.Internal.toString x1
  | _, .lean_string_append__String_Internal_append x1 x2 => String.Internal.append x1 x2
  | _, .lean_string_get_byte_fast__String_Internal_getUTF8Byte x1 x2 x3 => String.Internal.getUTF8Byte x1 x2 x3
  | _, .lean_string_isempty x1 => String.Internal.isEmpty x1
  | _, .lean_string_push x1 x2 => String.push x1 x2
  | _, .lean_string_isprefixof x1 x2 => String.Internal.isPrefixOf x1 x2
  | _, .lean_string_dropright x1 x2 => String.Internal.dropRight x1 x2
  | _, .lean_substring_takewhile x1 x2 => Substring.Raw.Internal.takeWhile x1 x2
  | _, .lean_substring_get x1 x2 => Substring.Raw.Internal.get x1 x2
  -- `USize` is `Nat` here (`lean_string_get_byte_fast__String_Internal_getUTF8Byte`): | _, .lean_string_uget_byte_fast x1 x2 x3 => String.Internal.ugetUTF8Byte x1 x2 x3
  | _, .lean_string_contains x1 x2 => String.Internal.contains x1 x2
  | _, .lean_string_front x1 => String.Internal.front x1
  | _, .lean_string_posof x1 x2 => String.Internal.posOf x1 x2
  | _, .lean_substring_all x1 x2 => Substring.Raw.Internal.all x1 x2
  | _, .lean_string_intercalate x1 x2 => String.Internal.intercalate x1 x2
  | _, .lean_string_drop x1 x2 => String.Internal.drop x1 x2
  | _, .lean_string_length__String_Internal_length x1 => String.Internal.length x1
  | _, .lean_string_utf8_at_end__String_Internal_atEnd x1 x2 => String.Internal.atEnd x1 x2
  | _, .lean_substring_beq x1 x2 => Substring.Raw.Internal.beq x1 x2
  | _, .lean_string_nextwhile x1 x2 x3 => String.Internal.nextWhile x1 x2 x3
  | _, .lean_string_utf8_next__String_Internal_next x1 x2 => String.Internal.next x1 x2
  | _, .lean_string_mk__String_mk x1 => String.ofList x1  -- `String.mk` is a deprecated alias of `String.ofList`
  | _, .lean_string_any x1 x2 => String.Internal.any x1 x2
  | _, .lean_string_pushn x1 x2 x3 => String.Internal.pushn x1 x2 x3
  | _, .lean_string_capitalize x1 => String.Internal.capitalize x1
  | _, .lean_string_utf8_extract__String_Internal_extract x1 x2 x3 => String.Internal.extract x1 x2 x3
  | _, .lean_string_pos_min x1 x2 => String.Pos.Raw.Internal.min x1 x2
  | _, .lean_substring_front x1 => Substring.Raw.Internal.front x1
  | _, .lean_string_pos_sub x1 x2 => String.Pos.Raw.Internal.sub x1 x2
  | _, .lean_substring_isempty x1 => Substring.Raw.Internal.isEmpty x1
  | _, .lean_string_offsetofpos x1 x2 => String.Internal.offsetOfPos x1 x2

/-- The value of an entry of `StringPosRawExtern` (`Init/Data/String/PosRaw.lean`). -/
def StringPosRawExtern.eval : {τ : TyWf} → StringPosRawExtern τ → TyWf.Den τ
  | _, .lean_string_get_byte_fast__String_getUtf8Byte x1 x2 x3 => String.getUTF8Byte x1 x2 x3  -- `String.getUtf8Byte` is a deprecated alias of `String.getUTF8Byte`
  | _, .lean_string_get_byte_fast__String_getUTF8Byte x1 x2 x3 => String.getUTF8Byte x1 x2 x3

/-- The value of an entry of `StringDefsExtern` (`Init/Data/String/Defs.lean`). -/
def StringDefsExtern.eval : {τ : TyWf} → StringDefsExtern τ → TyWf.Den τ
  -- a byte or float array: | _, .lean_string_to_utf8__String_toUTF8 x1 => String.toUTF8 x1
  | _, .lean_string_append__String_append x1 x2 => String.append x1 x2

/-- The value of an entry of `StringBasicExtern` (`Init/Data/String/Basic.lean`). -/
def StringBasicExtern.eval : {τ : TyWf} → StringBasicExtern TyWf.option TyWf.list τ → TyWf.Den τ
  | _, .lean_string_utf8_next__String_next x1 x2 => String.Pos.Raw.next x1 x2  -- `String.next` is a deprecated alias of `String.Pos.Raw.next`
  | _, .lean_string_utf8_next__String_Pos_Raw_next x1 x2 => String.Pos.Raw.next x1 x2
  | _, .lean_string_utf8_get__String_Pos_Raw_get x1 x2 => String.Pos.Raw.get x1 x2
  | _, .lean_string_utf8_get__String_get x1 x2 => String.Pos.Raw.get x1 x2  -- `String.get` is a deprecated alias of `String.Pos.Raw.get`
  | _, .lean_string_utf8_get_opt__String_Pos_Raw_get? x1 x2 => TyWf.Den.ofOption (String.Pos.Raw.get? x1 x2)
  | _, .lean_string_utf8_get_opt__String_get? x1 x2 => TyWf.Den.ofOption (String.Pos.Raw.get? x1 x2)  -- `String.get?` is a deprecated alias of `String.Pos.Raw.get?`
  | _, .lean_string_utf8_prev__String_Pos_Raw_prev x1 x2 => String.Pos.Raw.prev x1 x2
  | _, .lean_string_utf8_prev__String_prev x1 x2 => String.Pos.Raw.prev x1 x2  -- `String.prev` is a deprecated alias of `String.Pos.Raw.prev`
  | _, .lean_string_utf8_next_fast__String_next' x1 x2 x3 => String.Pos.Raw.next' x1 x2 x3  -- `String.next'` is a deprecated alias of `String.Pos.Raw.next'`
  -- the same as `lean_string_utf8_next_fast__String_next'`: | _, .lean_string_utf8_next_fast__String_Pos_Raw_next' x1 x2 x3 => String.Pos.Raw.next' x1 x2 x3
  | _, .lean_string_utf8_next_fast__String_Pos_next x1 x2 => String.Pos.next x1 x2
  | _, .lean_string_data__String_data x1 => TyWf.Den.ofList (α := .prim .char) (String.toList x1)  -- `String.data` is a deprecated alias of `String.toList`
  | _, .lean_string_data__String_toList x1 => TyWf.Den.ofList (α := .prim .char) (String.toList x1)
  | _, .lean_string_utf8_extract_fast x1 x2 => String.extract x1 x2
  | _, .lean_string_utf8_at_end__String_atEnd x1 x2 => String.Pos.Raw.atEnd x1 x2  -- `String.atEnd` is a deprecated alias of `String.Pos.Raw.atEnd`
  | _, .lean_string_utf8_at_end__String_Pos_Raw_atEnd x1 x2 => String.Pos.Raw.atEnd x1 x2
  | _, .lean_string_utf8_get_bang__String_Pos_Raw_get! x1 x2 => String.Pos.Raw.get! x1 x2
  | _, .lean_string_utf8_get_bang__String_get! x1 x2 => String.Pos.Raw.get! x1 x2  -- `String.get!` is a deprecated alias of `String.Pos.Raw.get!`
  -- a byte or float array: | _, .lean_string_utf8_get_fast__String_decodeChar x1 x2 x3 => String.decodeChar x1 x2 x3
  | _, .lean_string_utf8_get_fast__String_get' x1 x2 x3 => String.Pos.Raw.get' x1 x2 x3  -- `String.get'` is a deprecated alias of `String.Pos.Raw.get'`
  | _, .lean_string_utf8_get_fast__String_Pos_Raw_get' x1 x2 x3 => String.Pos.Raw.get' x1 x2 x3
  | _, .lean_string_is_valid_pos x1 x2 => String.Pos.Raw.isValid x1 x2
  | _, .lean_string_dec_lt x1 x2 => @Decidable.decide _ (String.decidableLT x1 x2)
  -- a byte or float array: | _, .lean_string_validate_utf8 x1 => ByteArray.validateUTF8 x1
  | _, .lean_string_utf8_extract__String_Pos_Raw_extract x1 x2 x3 => String.Pos.Raw.extract x1 x2 x3

/-- The value of an entry of `StringLengthExtern` (`Init/Data/String/Length.lean`). -/
def StringLengthExtern.eval : {τ : TyWf} → StringLengthExtern τ → TyWf.Den τ
  | _, .lean_string_length__String_length x1 => String.length x1

/-- The value of an entry of `StringPatternExtern` (`Init/Data/String/Pattern/Basic.lean`). -/
def StringPatternExtern.eval : {τ : TyWf} → StringPatternExtern τ → TyWf.Den τ
  | _, .lean_string_memcmp x1 x2 x3 x4 x5 x6 x7 => String.Slice.Pattern.Internal.memcmpStr x1 x2 x3 x4 x5 x6 x7

/-- The value of an entry of `StringSliceExtern` (`Init/Data/String/Slice.lean`). -/
def StringSliceExtern.eval : {τ : TyWf} → StringSliceExtern τ → TyWf.Den τ
  | _, .lean_slice_dec_lt x1 x2 => @Decidable.decide _ (String.Slice.instDecidableLt x1 x2)
  | _, .lean_slice_hash x1 => String.Slice.hash x1

/-- The value of an entry of `StringModifyExtern` (`Init/Data/String/Modify.lean`). -/
def StringModifyExtern.eval : {τ : TyWf} → StringModifyExtern τ → TyWf.Den τ
  | _, .lean_string_utf8_set__String_Pos_Raw_set x1 x2 x3 => String.Pos.Raw.set x1 x2 x3
  | _, .lean_string_utf8_set__String_Pos_set x1 x2 x3 => String.Pos.set x1 x2 x3
  | _, .lean_string_utf8_set__String_set x1 x2 x3 => String.Pos.Raw.set x1 x2 x3  -- `String.set` is a deprecated alias of `String.Pos.Raw.set`

/-- The value of an entry of `OrdStringExtern` (`Init/Data/Ord/String.lean`). -/
def OrdStringExtern.eval : {τ : TyWf} → OrdStringExtern TyWf.ordering τ → TyWf.Den τ
  | _, .lean_string_compare x1 x2 => TyWf.Den.ofOrdering (String.compare x1 x2)

end LeanScript

end
