module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: strings (`String`, `String.Pos`, `Substring`, slices, patterns, `Ord String`)

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

----------------------------------
-- Init/Data/String/Bootstrap.lean
----------------------------------
/-- The pure externs of `Init/Data/String/Bootstrap.lean`. -/
inductive StringBootstrapExtern : MyTy → Type where
  | lean_string_utf8_get__String_Internal_get : String → String.Pos.Raw → StringBootstrapExtern char -- String.Internal.get
  | lean_string_trim : String → StringBootstrapExtern string -- String.Internal.trim
  | lean_substring_drop : Substring.Raw → Nat → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.drop
  | lean_substring_prev : Substring.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- Substring.Raw.Internal.prev
  | lean_substring_extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.extract
  | lean_string_foldl : (String → Char → String) → String → String → StringBootstrapExtern string -- String.Internal.foldl
  | lean_substring_tostring : Substring.Raw → StringBootstrapExtern string -- Substring.Raw.Internal.toString
  | lean_string_append__String_Internal_append : String → String → StringBootstrapExtern string -- String.Internal.append
  | lean_string_get_byte_fast__String_Internal_getUTF8Byte : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → StringBootstrapExtern uint8 -- String.Internal.getUTF8Byte
  | lean_string_isempty : String → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.isEmpty
  | lean_string_push : String → Char → StringBootstrapExtern string -- String.push
  | lean_string_isprefixof : String → String → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.isPrefixOf
  | lean_string_dropright : String → Nat → StringBootstrapExtern string -- String.Internal.dropRight
  | lean_substring_takewhile : Substring.Raw → (Char → Bool) → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.takeWhile
  | lean_substring_get : Substring.Raw → String.Pos.Raw → StringBootstrapExtern char -- Substring.Raw.Internal.get
  -- `USize` is `Nat` here, so this is `lean_string_get_byte_fast__String_Internal_getUTF8Byte`; `#leanscript_to_term` translates a call of `String.Internal.ugetUTF8Byte` to that entry
  -- | lean_string_uget_byte_fast : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → StringBootstrapExtern uint8 -- String.Internal.ugetUTF8Byte
  | lean_string_contains : String → Char → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.contains
  | lean_string_front : String → StringBootstrapExtern char -- String.Internal.front
  | lean_string_posof : String → Char → StringBootstrapExtern stringPosRaw -- String.Internal.posOf
  | lean_substring_all : Substring.Raw → (Char → Bool) → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.all
  | lean_string_intercalate : String → List String → StringBootstrapExtern string -- String.Internal.intercalate
  | lean_string_drop : String → Nat → StringBootstrapExtern string -- String.Internal.drop
  | lean_string_length__String_Internal_length : String → StringBootstrapExtern nat -- String.Internal.length
  | lean_string_utf8_at_end__String_Internal_atEnd : String → String.Pos.Raw → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.atEnd
  | lean_substring_beq : Substring.Raw → Substring.Raw → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.beq
  | lean_string_nextwhile : String → (Char → Bool) → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Internal.nextWhile
  | lean_string_utf8_next__String_Internal_next : String → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Internal.next
  | lean_string_mk__String_mk : List Char → StringBootstrapExtern string -- String.mk
  | lean_string_any : String → (Char → Bool) → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.any
  | lean_string_pushn : String → Char → Nat → StringBootstrapExtern string -- String.Internal.pushn
  | lean_string_capitalize : String → StringBootstrapExtern string -- String.Internal.capitalize
  | lean_string_utf8_extract__String_Internal_extract : String → String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern string -- String.Internal.extract
  | lean_string_pos_min : String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Pos.Raw.Internal.min
  | lean_substring_front : Substring.Raw → StringBootstrapExtern char -- Substring.Raw.Internal.front
  | lean_string_pos_sub : String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Pos.Raw.Internal.sub
  | lean_substring_isempty : Substring.Raw → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.isEmpty
  | lean_string_offsetofpos : String → String.Pos.Raw → StringBootstrapExtern nat -- String.Internal.offsetOfPos

-------------------------------
-- Init/Data/String/PosRaw.lean
-------------------------------
/-- The pure externs of `Init/Data/String/PosRaw.lean`. -/
inductive StringPosRawExtern : MyTy → Type where
  | lean_string_get_byte_fast__String_getUtf8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → StringPosRawExtern uint8 -- String.getUtf8Byte
  | lean_string_get_byte_fast__String_getUTF8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → StringPosRawExtern uint8 -- String.getUTF8Byte

-----------------------------
-- Init/Data/String/Defs.lean
-----------------------------
/-- The pure externs of `Init/Data/String/Defs.lean`. -/
inductive StringDefsExtern : MyTy → Type where
  -- | lean_string_to_utf8__String_toUTF8 : String → StringDefsExtern byteArray -- String.toUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_append__String_append : String → String → StringDefsExtern string -- String.append

------------------------------
-- Init/Data/String/Basic.lean
------------------------------
/-- The pure externs of `Init/Data/String/Basic.lean`. -/
inductive StringBasicExtern : MyTy → Type where
  | lean_string_utf8_next__String_next : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.next
  | lean_string_utf8_next__String_Pos_Raw_next : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.Pos.Raw.next
  | lean_string_utf8_get__String_Pos_Raw_get : String → String.Pos.Raw → StringBasicExtern char -- String.Pos.Raw.get
  | lean_string_utf8_get__String_get : String → String.Pos.Raw → StringBasicExtern char -- String.get
  | lean_string_utf8_get_opt__String_Pos_Raw_get? : String → String.Pos.Raw → StringBasicExtern (option char) -- String.Pos.Raw.get?
  | lean_string_utf8_get_opt__String_get? : String → String.Pos.Raw → StringBasicExtern (option char) -- String.get?
  | lean_string_utf8_prev__String_Pos_Raw_prev : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.Pos.Raw.prev
  | lean_string_utf8_prev__String_prev : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.prev
  | lean_string_utf8_next_fast__String_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern stringPosRaw -- String.next'
  -- the same function as `lean_string_utf8_next_fast__String_next'`; `#leanscript_to_term` translates a call of `String.Pos.Raw.next'` to that entry
  -- | lean_string_utf8_next_fast__String_Pos_Raw_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern stringPosRaw -- String.Pos.Raw.next'
  | lean_string_utf8_next_fast__String_Pos_next : {s : String} → (pos : s.Pos) → (h : pos ≠ s.endPos) → StringBasicExtern (LeanPrimTy.stringPos s) -- String.Pos.next
  | lean_string_data__String_data : String → StringBasicExtern (list char) -- String.data
  | lean_string_data__String_toList : String → StringBasicExtern (list char) -- String.toList
  | lean_string_utf8_extract_fast : {s : String} → s.Pos → s.Pos → StringBasicExtern string -- String.extract
  | lean_string_utf8_at_end__String_atEnd : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.atEnd
  | lean_string_utf8_at_end__String_Pos_Raw_atEnd : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.Pos.Raw.atEnd
  | lean_string_utf8_get_bang__String_Pos_Raw_get! : String → String.Pos.Raw → StringBasicExtern char -- String.Pos.Raw.get!
  | lean_string_utf8_get_bang__String_get! : String → String.Pos.Raw → StringBasicExtern char -- String.get!
  -- | lean_string_utf8_get_fast__String_decodeChar : (s : String) → (byteIdx : Nat) → (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome = Bool.true) → StringBasicExtern char -- String.decodeChar -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_get_fast__String_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern char -- String.get'
  | lean_string_utf8_get_fast__String_Pos_Raw_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern char -- String.Pos.Raw.get'
  | lean_string_is_valid_pos : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.Pos.Raw.isValid
  | lean_string_dec_lt : String → String → StringBasicExtern LeanPrimTy.bool -- String.decidableLT
  -- | lean_string_validate_utf8 : ByteArray → StringBasicExtern LeanPrimTy.bool -- ByteArray.validateUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_extract__String_Pos_Raw_extract : String → String.Pos.Raw → String.Pos.Raw → StringBasicExtern string -- String.Pos.Raw.extract

-------------------------------
-- Init/Data/String/Length.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Length.lean`. -/
inductive StringLengthExtern : MyTy → Type where
  | lean_string_length__String_length : String → StringLengthExtern nat -- String.length

--------------------------------------
-- Init/Data/String/Pattern/Basic.lean
--------------------------------------
/-- The pure externs of `Init/Data/String/Pattern/Basic.lean`. -/
inductive StringPatternExtern : MyTy → Type where
  | lean_string_memcmp : (lhs : String) → (rhs : String) → (lstart : String.Pos.Raw) → (rstart : String.Pos.Raw) → (len : String.Pos.Raw) → len.offsetBy lstart ≤ lhs.rawEndPos → len.offsetBy rstart ≤ rhs.rawEndPos → StringPatternExtern LeanPrimTy.bool -- String.Slice.Pattern.Internal.memcmpStr

------------------------------
-- Init/Data/String/Slice.lean
------------------------------
/-- The pure externs of `Init/Data/String/Slice.lean`. -/
inductive StringSliceExtern : MyTy → Type where
  | lean_slice_dec_lt : String.Slice → String.Slice → StringSliceExtern LeanPrimTy.bool -- String.Slice.instDecidableLt
  | lean_slice_hash : String.Slice → StringSliceExtern uint64 -- String.Slice.hash

-------------------------------
-- Init/Data/String/Modify.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Modify.lean`. -/
inductive StringModifyExtern : MyTy → Type where
  | lean_string_utf8_set__String_Pos_Raw_set : String → String.Pos.Raw → Char → StringModifyExtern string -- String.Pos.Raw.set
  | lean_string_utf8_set__String_Pos_set : {s : String} → (p : s.Pos) → Char → p ≠ s.endPos → StringModifyExtern string -- String.Pos.set
  | lean_string_utf8_set__String_set : String → String.Pos.Raw → Char → StringModifyExtern string -- String.set

----------------------------
-- Init/Data/Ord/String.lean
----------------------------
/-- The pure externs of `Init/Data/Ord/String.lean`. -/
inductive OrdStringExtern : MyTy → Type where
  | lean_string_compare : String → String → OrdStringExtern ordering -- String.compare

end LeanScript

end
