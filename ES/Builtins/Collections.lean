import ES.Builtins.TypedArrays

/-!
# Array, TypedArrays, ArrayBuffer, SharedArrayBuffer, DataView, Atomics

spec: https://tc39.es/ecma262/

The parts: `Builtins/Array.lean` (Array's functions and prototype methods), `Builtins/Buffers.lean`
(ArrayBuffer, SharedArrayBuffer, DataView), `Builtins/TypedArrays.lean` (%TypedArray%, the typed
array constructors, Atomics).
-/

namespace ES.Builtins.Collections

open ES (F64)

/-- This module's built-in behaviours. -/
def defs : Array BuiltinDef := arrayDefs ++ bufferDefs ++ typedArrayDefs

/-- Creates this module's intrinsics in the realm being created (runs after `coreSetup`). -/
def setup : M Unit := do
  arraySetup
  bufferSetup
  typedArraySetup

end ES.Builtins.Collections
