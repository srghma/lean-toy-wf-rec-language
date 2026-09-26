module

prelude
public import Init.Prelude
public import Init.Data.Float
public import Init.Data.Format.Basic
public import Init.Data.Format.Instances
public import Init.Data.ToString.Basic
public import Init.Data.String.Basic
public import Init.ShareCommon
public import Init.LawfulBEqTactics

@[expose] public section

namespace LeanScript

open Std (Format ToFormat)

/-!
# `LeanPrimTy`: the terminal (leaf) types

These are exactly the types of the compiler's type language that

* contain **no** other type — they are leaves of a `Ty`, and
* are **built in** — the backend knows their JavaScript representation directly,
  without consulting a user-written schema.

They used to be constructors of `Ty` itself.  Splitting them off means

* a backend that only has to decide "how is a scalar represented?" pattern-matches on
  `LeanPrimTy`, a small type with no recursion and no indexed families, and can `deriving
  DecidableEq`/`Repr` freely;
* `Ty` is left with just the six *compound* shapes plus the handful of type
  constructors (`fn`, `array`, `list`, `task`, `promise`, `thunk`) and one
  `Ty.prim` leaf, so a traversal over the tree structure of a type has a dozen cases
  instead of forty;
* the "how is this rendered in JS?" configuration (`number` vs `bigint`, …) is a
  function `LeanPrimTy → …` — see `LeanScript.Config` — rather than a function on `Ty` with
  unreachable cases.

`Ty` re-exports every one of them as an abbreviation (`Ty.nat` is `Ty.prim .nat`), so
existing code that writes `.nat`, `.uint32`, `.bitvec 32`, … is unaffected.

Note that there is **no** `unit` and **no** `void`: a type with one value carries no
information and is erased before it reaches `LeanPrimTy`, and a type with no values has no
runtime representation at all.  This is also why `bitvec n` requires `0 < n`:
`BitVec 0` is a unit type.
-/

/-- A terminal type: a leaf of a `Ty`, with a built-in LEAN TYPE!!! representation

(not javascript!
The term deals only with lean type model,
then lean type model is optimized,
AND ONLY THEN (maybe optimized again and) printed into javascript). -/
inductive LeanPrimTy where
  /-- In JS: `boolean`. -/
  | bool      : LeanPrimTy
  /-- In JS: configurable:
    - if `number` then in `MoreJsTy` will be modeled by `UInt53` (if overflow already happened during `LeanTy` phase - throw and dont attempt to convert to `MoreJsTy`)
      a. `+,-,*,** : UInt53 -> UInt53 -> UInt53` are throwing if overflow during optimization
      b. `/,% : UInt53 -> UInt53 -> UInt53` are throwing if the divisor is 0 during optimization (TODO: unless required by algorithm? should there be optimization at `MoreJsTy` stage at all?)
      then printed as js `number`
    - if `bigint` then in `MoreJsTy` will be modeled by `Nat` then printed as js `bigint`.
  -/
  | nat       : LeanPrimTy
  /-- In JS: configurable:
    - if `number` then in `MoreJsTy` will be modeled by `Int53` then printed as js `number`.
    - if `bigint` then in `MoreJsTy` will be modeled by `Int` then printed as js `bigint`.
  -/
  | int       : LeanPrimTy
  /-- IF `n ≤ 53` then nonconfigurable then in `MoreJsTy` modeled by
    `bitvec_small : (n : Nat) → (h_le_53 : n ≤ 53 := by decide) → (h_positive : 0 < n := by decide) → MoreJsTy`
    then printed as js number

      ELSE IF `n > 53` then configurable:
        if `number` then (unless already overflown during `LeanTy` optimization phase) in `MoreJsTy` modeled by `UInt53` then printed as js `number`.
        if `bigint` then in `MoreJsTy` modeled by `bitvec_big : (n : Nat) → (h_g_53 : 53 < n := by decide)` then printed as js `bigint`.
  -/
  | bitvec    : (n : Nat) → (h_positive : 0 < n := by decide /- bc Unit-like types should be erased -/) → LeanPrimTy
  /-- In JS: `number`. -/
  | uint8     : LeanPrimTy
  /-- In JS: `number`. -/
  | uint16    : LeanPrimTy
  /-- In JS: `number`. -/
  | uint32    : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | uint64    : LeanPrimTy
  /-- In JS: `number`. -/
  | int8      : LeanPrimTy
  /-- In JS: `number`. -/
  | int16     : LeanPrimTy
  /-- In JS: `number`. -/
  | int32     : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | int64     : LeanPrimTy
  /-- In JS: `string`. -/
  | char      : LeanPrimTy
  /-- In JS: `string`. -/
  | string    : LeanPrimTy
  -- /-- In JS: `Uint8Array` / `ArrayBuffer`. -/
  -- | byteArray : LeanPrimTy -- in this `LeanPrimTy` mapped to `Array UInt8`. Then in `MoreJsTy` as `Uint8Array`
  /-- A position in a string — like `.uint32`, but strictly non-negative. -/
  | stringPosRaw : LeanPrimTy
  | stringPos (s : String) : LeanPrimTy -- for `structure Pos (s : String) where`
  /-- In JS: `{ str: string, startPos: number, stopPos: number }`. -/
  | substringRaw : LeanPrimTy
  /-- `.substringRaw` or `.string`? -/
  | stringSlice : LeanPrimTy
  /-- In JS: `number` (IEEE 754 64-bit). -/
  | float     : LeanPrimTy
  /-- In JS: `number` (IEEE 754 32-bit, `Math.fround`). -/
  | float32   : LeanPrimTy
  | floatModel   : LeanPrimTy
  | float32Model   : LeanPrimTy
  -- /-- In JS: `Float64Array`. -/
  -- | floatArray : LeanPrimTy -- in this `LeanPrimTy` mapped to `Array Float`. Then in `MoreJsTy` as `Float64Array`
  -- /-- In JS (node only): a `ChildProcess` handle. -/
  -- | childProcess : LeanPrimTy
  -- Commented out: a `ChildProcess` is a live operating-system process, so it has no
  -- pure meaning and no literal, and a `Term` mentioning it could never be evaluated.
  -- At this stage `Term` is meant to be completely evaluatable.
  -- /-- In JS: `object`? / `any`?. -/
  -- | shareCommonObject : LeanPrimTy
  -- /-- In JS: a `Map`? / cache object?. -/
  -- | shareCommonState  : LeanPrimTy
  -- Commented out: the two `ShareCommon` handles denote a *memory layout*, not a value,
  -- so they have no literal and a `Term` mentioning one could never be evaluated.  Of
  -- the four externs that speak about them, `lean_sharecommon_quick` is kept — it is the
  -- identity on values, which is what `Expr.Step.quick` runs — and the three that read a
  -- handle are commented out with the handles: the interning table is erased.
  deriving Inhabited, Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace LeanPrimTy

-- TODO: name should be constructed as recTaggedUnion

/-- A rendering for debugging and error messages, as a plain `String` (a `Format` does
    not reduce in the kernel, so an `example` settled by `decide` needs a `String`). -/
def pretty : LeanPrimTy → String
  | .bitvec n _ => "(bitvec " ++ toString n ++ ")"
  | .bool => "bool" | .nat => "nat" | .int => "int"
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32" | .uint64 => "uint64"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32" | .int64 => "int64"
  | .char => "char" | .string => "string"
  | .stringPos _s => "stringPos"
  | .stringPosRaw => "stringPosRaw" | .substringRaw => "substringRaw" | .stringSlice => "stringSlice"
  | .float => "float" | .float32 => "float32"
  | .floatModel => "floatModel"
  | .float32Model => "float32Model"
  -- | .shareCommonObject => "shareCommonObject"
  -- | .shareCommonState _ => "shareCommonState"

/-- `LeanScript.LeanPrimTy.pretty`, as a `Format`. -/
def format (t : LeanPrimTy) : Format := t.pretty

instance : ToFormat LeanPrimTy where
  format := format

instance : ToString LeanPrimTy where
  toString := pretty

/-- Is the JavaScript representation of this type configurable (`number` vs
    `bigint`)?  A bit vector of fewer than 32 bits always fits in a `number`. -/
def isNumberConfigurable : LeanPrimTy → Bool
  | .nat | .int | .uint64 | .int64 => true
  | .bitvec n _ => 32 ≤ n
  | _ => false

/-- The Lean type a terminal type describes: the type of the values its literals hold.
    Every terminal type has literals: the three run-time handles, which had none, are
    commented out of `LeanPrimTy`. -/
@[reducible] def denote : LeanPrimTy → Type
  | .bool => Bool
  | .nat => Nat
  | .int => Int
  | .bitvec n _ => BitVec n
  | .uint8 => UInt8
  | .uint16 => UInt16
  | .uint32 => UInt32
  | .uint64 => UInt64
  | .int8 => Int8
  | .int16 => Int16
  | .int32 => Int32
  | .int64 => Int64
  | .char => Char
  | .string => String
  | .stringPos s => String.Pos s
  | .stringPosRaw => String.Pos.Raw
  | .substringRaw => Substring.Raw
  | .stringSlice => String.Slice
  | .float => Float
  | .float32 => Float32
  | .floatModel => Float.Model
  | .float32Model => Float32.Model
  -- | .shareCommonObject => ShareCommon.Object
  -- | .shareCommonState σ => ShareCommon.State σ
  -- `.childProcess`, `.shareCommonObject` and `.shareCommonState` are commented out of
  -- `LeanPrimTy`.

end LeanPrimTy

end LeanScript

end

/-
In JavaScript (❌ means will not be emitted by `lean-to-js` backend (but maybe support will be added anyway for custom functions))

### 1. Typed Arrays (Binary Data Arrays)
Typed Arrays represent fixed-length arrays where every element is of a specific numerical data type. They are backed by an underlying memory buffer (`ArrayBuffer`).

#### **Signed Integers (Two’s complement)**
* **`Int8Array`**: 8-bit signed integers (`-128` to `127`).
* **`Int16Array`**: 16-bit signed integers (`-32,768` to `32,767`).
* **`Int32Array`**: 32-bit signed integers (`-2,147,483,648` to `2,147,483,647`).

#### **Unsigned Integers**
* **`Uint8Array`**: 8-bit unsigned integers (`0` to `255`). Widely used for binary file processing, cryptographic tasks, and networking.
* **`Uint16Array`**: 16-bit unsigned integers (`0` to `65,535`).
* **`Uint32Array`**: 32-bit unsigned integers (`0` to `4,294,967,295`).

#### **Specialized Clamped Integer Array**
* ❌ **`Uint8ClampedArray`**: 8-bit unsigned integers (`0` to `255`).
  * **What makes it specialized:** Standard `Uint8Array` handles overflow/underflow using modulo arithmetic (e.g., `256` wraps around to `0`). `Uint8ClampedArray` instead **clamps** the value (e.g., `300` becomes `255`, `-10` becomes `0`). It was designed specifically for canvas pixel manipulation (`ImageData.data`).

#### **Floating-Point Numbers**
* ❌ **`Float16Array`**: 16-bit half-precision floating-point numbers (introduced in modern ECMAScript for machine learning, graphics, and reduced-memory workloads).
* **`Float32Array`**: 32-bit single-precision IEEE 754 floats. Common in WebGL and 3D graphics.
* **`Float64Array`**: 64-bit double-precision IEEE 754 floats (the format used by standard JavaScript `Number`).

#### **64-bit BigInt Arrays**
* **`BigInt64Array`**: 64-bit signed integers (`-2^63` to `2^63 - 1`). Reads/writes native JavaScript `BigInt` values.
* **`BigUint64Array`**: 64-bit unsigned integers (`0` to `2^64 - 1`).

---

### 2. Closely Related Binary Memory Structures
While not technically array subclasses, these are companion structures for working with array-like binary memory:

* ❌ **`ArrayBuffer` / `SharedArrayBuffer`**: The underlying raw byte buffer holding the actual memory that Typed Arrays view and manipulate.
* ❌ **`DataView`**: A low-level view over an `ArrayBuffer` that allows arbitrary reading/writing of different data types at specified byte offsets and explicit endianness (big-endian or little-endian).
-/
