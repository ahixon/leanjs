import ES.Builtins.Buffers

/-!
# TypedArray objects and Atomics

spec: https://tc39.es/ecma262/#sec-typedarray-objects, https://tc39.es/ecma262/#sec-atomics-object

A typed array is `Kind.typedArray kind buffer byteOffset length` (`length = none`: a
length-tracking view of a resizable buffer); its exotic internal methods are in
`ES/Object.lean`, which also has the TypedArray With Buffer Witness Records (`TARecord`).
-/

namespace ES.Builtins.Collections

open ES (F64)

/-! ## Abstract operations -/

@[inline] def taGet (o : ObjId) (k : Nat) : M Value := typedArrayGetElement o (Conv.ofNat k)
@[inline] def taSet (o : ObjId) (k : Nat) (v : Value) : M Unit := typedArraySetElement o (Conv.ofNat k) v

/-- RequireInternalSlot(O, [[TypedArrayName]]) with the record of its buffer. -/
def thisTA (v : Value) (what : String) : M TARecord := do
  let .obj o := v | throwType s!"{what}: this is not a typed array"
  match ← taRecord? o with
  | some r => pure r
  | none => throwType s!"{what}: this is not a typed array"

/-- ValidateTypedArray spec: https://tc39.es/ecma262/#sec-validatetypedarray -/
def validateTypedArray (v : Value) (what : String) : M TARecord := do
  -- 1-3.
  let r ← thisTA v what
  -- 4.
  if r.isOutOfBounds then throwType s!"{what}: the typed array is detached or out of bounds"
  pure r

/-- The record of a typed array again (after user code may have changed its buffer). -/
def reread (r : TARecord) : M TARecord := do
  match ← taRecord? r.obj with
  | some r => pure r
  | none => pure r

def taCtorName (k : TAKind) : String := s!"%{k.name}%"

/-- TypedArrayCreateFromConstructor spec: https://tc39.es/ecma262/#sec-typedarraycreatefromconstructor -/
def typedArrayCreateFromCtor (ctor : Value) (args : Array Value) : M TARecord := do
  -- 1.
  let nv ← construct ctor args
  -- 2.
  let r ← validateTypedArray nv "TypedArray species constructor"
  -- 3.
  if args.size == 1 then
    if let .num n := args[0]! then
      if r.isOutOfBounds then throwType "TypedArray species constructor: out of bounds"
      if F64.lt (Conv.ofNat r.length) n then throwType "TypedArray species constructor created a too short array"
  pure r

/-- TypedArraySpeciesCreate spec: https://tc39.es/ecma262/#sec-typedarray-species-create -/
def typedArraySpeciesCreate (exemplar : TARecord) (args : Array Value) : M TARecord := do
  -- 1.
  let dflt ← intrinsicV (taCtorName exemplar.kind)
  -- 2.
  let c ← speciesConstructor exemplar.obj dflt
  -- 3.
  let r ← typedArrayCreateFromCtor c args
  -- 4.
  if r.kind.isBigInt != exemplar.kind.isBigInt then throwType "TypedArray species constructor: content type mismatch"
  pure r

/-- TypedArrayCreateSameType spec: https://tc39.es/ecma262/#sec-typedarray-create-same-type -/
def typedArrayCreateSameType (exemplar : TARecord) (len : Nat) : M TARecord := do
  typedArrayCreateFromCtor (← intrinsicV (taCtorName exemplar.kind)) #[numV len]

/-- Converts a value to the element type's numeric type (ToBigInt or ToNumber). -/
def toElementNumeric (k : TAKind) (v : Value) : M Value := do
  if k.isBigInt then pure (.bigint (← toBigInt v)) else pure (.num (← toNum v))

/-- A new typed array object with its slots. -/
def makeTA (proto : ObjId) (k : TAKind) (buf : ObjId) (off : Nat) (len : Option Nat) : M ObjId :=
  alloc { proto := .obj proto, kind := .typedArray k buf off len }

/-- AllocateTypedArray (with a length: AllocateTypedArrayBuffer)
spec: https://tc39.es/ecma262/#sec-allocatetypedarray -/
def allocateTypedArray (k : TAKind) (nt : Value) (len : Nat) : M ObjId := do
  -- 1.
  let proto ← getPrototypeFromConstructor nt s!"%{k.name}.prototype%"
  -- 6. AllocateTypedArrayBuffer
  let buf ← newArrayBuffer (k.elementSize * len)
  makeTA proto k buf 0 (some len)

/-- InitializeTypedArrayFromTypedArray spec: https://tc39.es/ecma262/#sec-initializetypedarrayfromtypedarray -/
def initFromTypedArray (k : TAKind) (proto : ObjId) (src : ObjId) : M ObjId := do
  let some sr ← taRecord? src | throwType "not a typed array"
  -- 8.
  if sr.isOutOfBounds then throwType "source typed array is detached or out of bounds"
  -- 9-10.
  let elementLength := sr.length
  let byteLength := k.elementSize * elementLength
  -- 11-12.
  let data ← if k == sr.kind then cloneArrayBuffer sr.buf sr.byteOffset byteLength else do
    let data ← newArrayBuffer byteLength
    if sr.kind.isBigInt != k.isBigInt then throwType "Content types of source and target typed arrays differ"
    forIdx_ 0 elementLength fun i => do
      let v ← getValueFromBuffer sr.buf (sr.byteOffset + i * sr.kind.elementSize) sr.kind
      setValueInBuffer data (i * k.elementSize) k v
    pure data
  makeTA proto k data 0 (some elementLength)

/-- InitializeTypedArrayFromArrayBuffer spec: https://tc39.es/ecma262/#sec-initializetypedarrayfromarraybuffer -/
def initFromArrayBuffer (k : TAKind) (proto : ObjId) (buffer : ObjId) (byteOffset length : Value) : M ObjId := do
  -- 1.
  let elementSize := k.elementSize
  -- 2-3.
  let offset ← toIndex byteOffset
  if offset % elementSize != 0 then throwRange s!"start offset of {k.name} should be a multiple of {elementSize}"
  -- 5.
  let newLength ← if length.isUndefined then pure none else some <$> toIndex length
  -- 6.
  let some bi ← bufInfo? buffer | throwType "not a buffer"
  if bi.detached then throwType "Cannot construct a typed array on a detached ArrayBuffer"
  -- 4, 7.
  let fixed := bi.maxLen.isNone
  let bufferByteLength := bi.byteLength
  -- 8.
  if newLength.isNone && !fixed then
    if offset > bufferByteLength then throwRange s!"Start offset {offset} is outside the bounds of the buffer"
    return ← makeTA proto k buffer offset none
  -- 9.
  let newByteLength ← match newLength with
    | none => do
      if bufferByteLength % elementSize != 0 then throwRange s!"byte length of {k.name} should be a multiple of {elementSize}"
      if offset > bufferByteLength then throwRange s!"Start offset {offset} is outside the bounds of the buffer"
      pure (bufferByteLength - offset)
    | some nl => do
      if offset + nl * elementSize > bufferByteLength then throwRange s!"Invalid typed array length: {nl}"
      pure (nl * elementSize)
  makeTA proto k buffer offset (some (newByteLength / elementSize))

/-- InitializeTypedArrayFromList spec: https://tc39.es/ecma262/#sec-initializetypedarrayfromlist -/
def initFromList (k : TAKind) (proto : ObjId) (values : Array Value) : M ObjId := do
  let len := values.size
  let buf ← newArrayBuffer (k.elementSize * len)
  let o ← makeTA proto k buf 0 (some len)
  forIdx_ 0 len fun i => taSet o i values[i]!
  pure o

/-- InitializeTypedArrayFromArrayLike spec: https://tc39.es/ecma262/#sec-initializetypedarrayfromarraylike -/
def initFromArrayLike (k : TAKind) (proto : ObjId) (arrayLike : ObjId) : M ObjId := do
  let len ← lengthOf arrayLike
  let buf ← newArrayBuffer (k.elementSize * len)
  let o ← makeTA proto k buf 0 (some len)
  forIdx_ 0 len fun i => do taSet o i (← getIdx arrayLike i)
  pure o

/-- TypedArray(...args) spec: https://tc39.es/ecma262/#sec-typedarray -/
def typedArrayCtor (k : TAKind) : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then throwType s!"Constructor {k.name} requires 'new'"
  -- 5.
  if args.size == 0 then return .obj (← allocateTypedArray k nt 0)
  -- 6.
  let first := args[0]!
  match first with
  | .obj fo =>
    let proto ← getPrototypeFromConstructor nt s!"%{k.name}.prototype%"
    match ← objKind fo with
    | .typedArray .. => pure (.obj (← initFromTypedArray k proto fo))
    | .buffer .. => pure (.obj (← initFromArrayBuffer k proto fo (arg args 1) (arg args 2)))
    | _ =>
      match ← getMethodOf first (.sym WK.iterator) with
      | some m =>
        let values ← iteratorToList (← getIteratorFromMethod first m)
        pure (.obj (← initFromList k proto values))
      | none => pure (.obj (← initFromArrayLike k proto fo))
  | _ =>
    let elementLength ← toIndex first
    pure (.obj (← allocateTypedArray k nt elementLength))

/-- %TypedArray%() spec: https://tc39.es/ecma262/#sec-%typedarray% -/
def typedArrayAbstractCtor : BuiltinFn := fun _ _ _ _ =>
  throwType "Abstract class TypedArray not directly constructable"

/-- %TypedArray%.from spec: https://tc39.es/ecma262/#sec-%typedarray%.from -/
def typedArrayFrom : BuiltinFn := fun _ thisV args _ => do
  let source := arg args 0
  let mapfn := arg args 1
  let thisArg := arg args 2
  -- 1-2.
  let c := thisV
  if !(← isConstructor c) then throwType "TypedArray.from: this is not a constructor"
  -- 3-4.
  let mapping := !mapfn.isUndefined
  if mapping then requireCallable mapfn "TypedArray.from"
  -- 5.
  let usingIterator ← getMethodOf source (.sym WK.iterator)
  -- 6.
  if let some m := usingIterator then
    let values ← iteratorToList (← getIteratorFromMethod source m)
    let len := values.size
    let t ← typedArrayCreateFromCtor c #[numV len]
    forIdx_ 0 len fun k => do
      let kv := values[k]!
      let mv ← if mapping then call mapfn thisArg #[kv, numV k] else pure kv
      setIdx t.obj k mv
    return .obj t.obj
  -- 8-10.
  let arrayLike ← toObj source
  let len ← lengthOf arrayLike
  let t ← typedArrayCreateFromCtor c #[numV len]
  -- 11-12.
  forIdx_ 0 len fun k => do
    let kv ← getIdx arrayLike k
    let mv ← if mapping then call mapfn thisArg #[kv, numV k] else pure kv
    setIdx t.obj k mv
  pure (.obj t.obj)

/-- %TypedArray%.of spec: https://tc39.es/ecma262/#sec-%typedarray%.of -/
def typedArrayOf : BuiltinFn := fun _ thisV args _ => do
  let len := args.size
  let c := thisV
  if !(← isConstructor c) then throwType "TypedArray.of: this is not a constructor"
  let t ← typedArrayCreateFromCtor c #[numV len]
  forIdx_ 0 len fun k => setIdx t.obj k args[k]!
  pure (.obj t.obj)

/-! ## %TypedArray%.prototype -/

/-- get %TypedArray%.prototype.buffer spec: https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.buffer -/
def taBuffer : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisTA thisV "get TypedArray.prototype.buffer"
  pure (.obj r.buf)

/-- get %TypedArray%.prototype.byteLength spec: https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.bytelength -/
def taByteLength : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisTA thisV "get TypedArray.prototype.byteLength"
  pure (numV r.byteLength)

/-- get %TypedArray%.prototype.byteOffset spec: https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.byteoffset -/
def taByteOffset : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisTA thisV "get TypedArray.prototype.byteOffset"
  pure (numV (if r.isOutOfBounds then 0 else r.byteOffset))

/-- get %TypedArray%.prototype.length spec: https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.length -/
def taLength : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisTA thisV "get TypedArray.prototype.length"
  pure (numV r.lengthOr0)

/-- get %TypedArray%.prototype[@@toStringTag] spec: https://tc39.es/ecma262/#sec-get-%typedarray%.prototype-%symbol.tostringtag% -/
def taToStringTag : BuiltinFn := fun _ thisV _ _ => do
  let .obj o := thisV | return .undefined
  match ← objKind o with
  | .typedArray k .. => pure (.str (JSStr.ofString k.name))
  | _ => pure .undefined

/-- %TypedArray%.prototype.at spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.at -/
def taAt : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.at"
  let len := r.length
  let k : Int ← match ← toIntegerOrInfinity (arg args 0) with
    | .inl _ => pure (-1)
    | .inr i => pure (if i ≥ 0 then i else len + i)
  if k < 0 || k ≥ len then return .undefined
  taGet r.obj k.toNat

/-- Moves bytes within a block as %TypedArray%.prototype.copyWithin's step 14 does (direction,
stopping at the limit). -/
def copyWithinBytes (d : ByteArray) (fromIdx toIdx count limit : Nat) (backwards : Bool) : ByteArray :=
  (List.range count).foldl (fun (st : ByteArray × Bool) i =>
    let (d, stopped) := st
    if stopped then (d, true) else
    let (f, t) := if backwards then (fromIdx + count - 1 - i, toIdx + count - 1 - i) else (fromIdx + i, toIdx + i)
    if f < limit && t < limit then (d.set! t (d.get! f), false) else (d, true)) (d, false) |>.1

/-- %TypedArray%.prototype.copyWithin spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.copywithin -/
def taCopyWithin : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let r ← validateTypedArray thisV "TypedArray.prototype.copyWithin"
  let len := r.length
  -- 4-12.
  let targetIndex ← relIndex (arg args 0) len
  let startIndex ← relIndex (arg args 1) len
  let endIndex ← relEnd (arg args 2) len
  -- 13.
  let count := min (endIndex - startIndex) (len - targetIndex)
  -- 14.
  if count > 0 then
    let r ← reread r
    if r.isOutOfBounds then throwType "TypedArray.prototype.copyWithin: the typed array is detached or out of bounds"
    let len := r.length
    let es := r.kind.elementSize
    let limit := len * es + r.byteOffset
    let toB := targetIndex * es + r.byteOffset
    let fromB := startIndex * es + r.byteOffset
    -- DEVIATION (docs/es.md D20): the bytes that still fit below the limit after a shrink,
    -- moved as by memmove (browsers' behaviour and test262's)
    let countBytes := min (count * es) (min (limit - fromB) (limit - toB))
    let backwards := fromB < toB && toB < fromB + countBytes
    modifyObj r.buf fun o => o.withKind fun kd => match kd with
      | .buffer d det ml sh => .buffer (copyWithinBytes d fromB toB countBytes limit backwards) det ml sh
      | kd => kd
  pure (.obj r.obj)

/-- entries/keys/values spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.values -/
def taIter (kind : Nat) : BuiltinFn := fun _ thisV _ _ => do
  let r ← validateTypedArray thisV "TypedArray iterator"
  createArrayIterator (.obj r.obj) kind

/-- every/some spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.every -/
def taEverySome (isSome : Bool) : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV (if isSome then "TypedArray.prototype.some" else "TypedArray.prototype.every")
  let len := r.length
  let cb := arg args 0
  requireCallable cb "TypedArray.prototype.every"
  let res ← forIdx 0 len fun k => do
    let kv ← taGet r.obj k
    if toBoolean (← call cb (arg args 1) #[kv, numV k, .obj r.obj]) == isSome then return some ()
    pure none
  pure (.bool (if res.isSome then isSome else !isSome))

/-- %TypedArray%.prototype.fill spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.fill -/
def taFill : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let r ← validateTypedArray thisV "TypedArray.prototype.fill"
  let len := r.length
  -- 4-5.
  let v ← toElementNumeric r.kind (arg args 0)
  -- 6-11.
  let k ← relIndex (arg args 1) len
  let final ← relEnd (arg args 2) len
  -- 12-15.
  let r ← reread r
  if r.isOutOfBounds then throwType "TypedArray.prototype.fill: the typed array is detached or out of bounds"
  let final := min final r.length
  -- 16-17.
  let es := r.kind.elementSize
  let bits := r.kind.toRaw v
  if k < final then
    modifyObj r.buf fun o => o.withKind fun kd => match kd with
      | .buffer d det ml sh =>
        .buffer ((List.range (final - k)).foldl (fun d i =>
          bytesSet d (r.byteOffset + (k + i) * es) es bits true) d) det ml sh
      | kd => kd
  pure (.obj r.obj)

/-- %TypedArray%.prototype.filter spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.filter -/
def taFilter : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.filter"
  let len := r.length
  let cb := arg args 0
  requireCallable cb "TypedArray.prototype.filter"
  let kept ← M.repeatFrom (0, (#[] : Array Value)) fun (k, kept) => do
    if k ≥ len then return .inr kept
    M.tick
    let kv ← taGet r.obj k
    if toBoolean (← call cb (arg args 1) #[kv, numV k, .obj r.obj]) then return .inl (k + 1, kept.push kv)
    return .inl (k + 1, kept)
  let a ← typedArraySpeciesCreate r #[numV kept.size]
  forIdx_ 0 kept.size fun n => setIdx a.obj n kept[n]!
  pure (.obj a.obj)

/-- find/findIndex/findLast/findLastIndex spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.find -/
def taFind (ascending wantIndex : Bool) : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.find"
  let len := r.length
  let pred := arg args 0
  requireCallable pred "TypedArray.prototype.find"
  let body (k : Nat) : M (Option (Int × Value)) := do
    let kv ← taGet r.obj k
    if toBoolean (← call pred (arg args 1) #[kv, numV k, .obj r.obj]) then return some ((k : Int), kv)
    pure none
  let res ← if ascending then forIdx 0 len body else forIdxDown (if len == 0 then none else some (len - 1)) body
  let (i, v) := res.getD (-1, .undefined)
  pure (if wantIndex then intV i else v)

/-- %TypedArray%.prototype.forEach spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.foreach -/
def taForEach : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.forEach"
  let len := r.length
  let cb := arg args 0
  requireCallable cb "TypedArray.prototype.forEach"
  forIdx_ 0 len fun k => do
    let kv ← taGet r.obj k
    let _ ← call cb (arg args 1) #[kv, numV k, .obj r.obj]
  pure .undefined

/-- %TypedArray%.prototype.includes spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.includes -/
def taIncludes : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.includes"
  let len := r.length
  if len == 0 then return .bool false
  let some k ← searchStart (arg args 1) len | return .bool false
  let res ← forIdx k len fun k => do
    if sameValueZero (← taGet r.obj k) (arg args 0) then return some () else pure none
  pure (.bool res.isSome)

/-- %TypedArray%.prototype.indexOf spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.indexof -/
def taIndexOf : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.indexOf"
  let len := r.length
  if len == 0 then return intV (-1)
  let some k ← searchStart (arg args 1) len | return intV (-1)
  let res ← forIdx k len fun k => do
    if ← hasIdx r.obj k then
      if isStrictlyEqual (← taGet r.obj k) (arg args 0) then return some k
    pure none
  pure (match res with | some k => numV k | none => intV (-1))

/-- %TypedArray%.prototype.lastIndexOf spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.lastindexof -/
def taLastIndexOf : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.lastIndexOf"
  let len := r.length
  if len == 0 then return intV (-1)
  let n ← if args.size > 1 then toIntegerOrInfinity (arg args 1) else pure (.inr ((len : Int) - 1))
  let start : Option Nat := match n with
    | .inl true => none
    | .inl false => some (len - 1)
    | .inr n => if n ≥ 0 then some (min n.toNat (len - 1))
      else if (len : Int) + n < 0 then none else some ((len : Int) + n).toNat
  let res ← forIdxDown start fun k => do
    if ← hasIdx r.obj k then
      if isStrictlyEqual (← taGet r.obj k) (arg args 0) then return some k
    pure none
  pure (match res with | some k => numV k | none => intV (-1))

/-- %TypedArray%.prototype.join spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.join -/
def taJoin : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.join"
  let len := r.length
  let sep ← if (arg args 0).isUndefined then pure (JSStr.ofString ",") else toStr (arg args 0)
  M.repeatFrom (0, JSStr.empty) fun (k, acc) => do
    if k ≥ len then return .inr (Value.str acc)
    M.tick
    let acc := if k > 0 then acc ++ sep else acc
    let e ← taGet r.obj k
    if e.isUndefined then return .inl (k + 1, acc)
    return .inl (k + 1, acc ++ (← toStr e))

/-- %TypedArray%.prototype.map spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.map -/
def taMap : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.map"
  let len := r.length
  let cb := arg args 0
  requireCallable cb "TypedArray.prototype.map"
  let a ← typedArraySpeciesCreate r #[numV len]
  forIdx_ 0 len fun k => do
    let kv ← taGet r.obj k
    let mv ← call cb (arg args 1) #[kv, numV k, .obj r.obj]
    setIdx a.obj k mv
  pure (.obj a.obj)

/-- reduce/reduceRight spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.reduce -/
def taReduce (right : Bool) : BuiltinFn := fun _ thisV args _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.reduce"
  let len := r.length
  let cb := arg args 0
  requireCallable cb "TypedArray.prototype.reduce"
  if len == 0 && args.size < 2 then throwType "Reduce of empty array with no initial value"
  let idx (i : Nat) : Nat := if right then len - 1 - i else i
  let (start, acc) ← if args.size ≥ 2 then pure (0, args[1]!) else do pure (1, ← taGet r.obj (idx 0))
  M.repeatFrom (start, acc) fun (i, acc) => do
    if i ≥ len then return .inr acc
    M.tick
    let kv ← taGet r.obj (idx i)
    return .inl (i + 1, ← call cb .undefined #[acc, kv, numV (idx i), .obj r.obj])

/-- %TypedArray%.prototype.reverse spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.reverse -/
def taReverse : BuiltinFn := fun _ thisV _ _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.reverse"
  let len := r.length
  forIdx_ 0 (len / 2) fun lower => do
    let upper := len - lower - 1
    let lv ← taGet r.obj lower
    let uv ← taGet r.obj upper
    taSet r.obj lower uv
    taSet r.obj upper lv
  pure (.obj r.obj)

/-- SetTypedArrayFromTypedArray spec: https://tc39.es/ecma262/#sec-settypedarrayfromtypedarray -/
def setFromTypedArray (target : TARecord) (targetOffset : Sum Bool Int) (source : ObjId) : M Unit := do
  -- 2-4.
  let target ← reread target
  if target.isOutOfBounds then throwType "TypedArray.prototype.set: target is detached or out of bounds"
  let targetLength := target.length
  -- 5-8.
  let some src ← taRecord? source | throwType "not a typed array"
  if src.isOutOfBounds then throwType "TypedArray.prototype.set: source is detached or out of bounds"
  let srcLength := src.length
  -- 15-16.
  let off ← match targetOffset with
    | .inl _ => throwRange "offset is out of bounds"
    | .inr i => pure i.toNat
  if srcLength + off > targetLength then throwRange "offset is out of bounds"
  -- 17.
  if src.kind.isBigInt != target.kind.isBigInt then throwType "Content types of source and target typed arrays differ"
  -- 19-20. (the source's bytes, read before any are written)
  let srcBytes ← readBytes src.buf src.byteOffset (srcLength * src.kind.elementSize)
  -- 21-22.
  let targetByteIndex := off * target.kind.elementSize + target.byteOffset
  -- 23.
  if src.kind == target.kind then writeBytes target.buf targetByteIndex srcBytes
  -- 24.
  else
    let ses := src.kind.elementSize
    let tes := target.kind.elementSize
    modifyObj target.buf fun o => o.withKind fun kd => match kd with
      | .buffer d det ml sh =>
        .buffer ((List.range srcLength).foldl (fun d i =>
          let v := src.kind.ofRaw (bytesGet srcBytes (i * ses) ses true)
          bytesSet d (targetByteIndex + i * tes) tes (target.kind.toRaw v) true) d) det ml sh
      | kd => kd

/-- SetTypedArrayFromArrayLike spec: https://tc39.es/ecma262/#sec-settypedarrayfromarraylike -/
def setFromArrayLike (target : TARecord) (targetOffset : Sum Bool Int) (source : Value) : M Unit := do
  -- 1-3.
  let target ← reread target
  if target.isOutOfBounds then throwType "TypedArray.prototype.set: target is detached or out of bounds"
  let targetLength := target.length
  -- 4-5.
  let src ← toObj source
  let srcLength ← lengthOf src
  -- 6-7.
  let off ← match targetOffset with
    | .inl _ => throwRange "offset is out of bounds"
    | .inr i => pure i.toNat
  if srcLength + off > targetLength then throwRange "offset is out of bounds"
  -- 8-9.
  forIdx_ 0 srcLength fun k => do
    let v ← getIdx src k
    taSet target.obj (off + k) v

/-- %TypedArray%.prototype.set spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.set -/
def taSetMethod : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let target ← thisTA thisV "TypedArray.prototype.set"
  -- 4-5.
  let targetOffset ← toIntegerOrInfinity (arg args 1)
  match targetOffset with
  | .inl true => throwRange "offset is out of bounds"
  | .inr i => if i < 0 then throwRange "offset is out of bounds"
  | _ => pure ()
  -- 6-7.
  let source := arg args 0
  match source with
  | .obj so =>
    match ← objKind so with
    | .typedArray .. => setFromTypedArray target targetOffset so
    | _ => setFromArrayLike target targetOffset source
  | _ => setFromArrayLike target targetOffset source
  pure .undefined

/-- %TypedArray%.prototype.slice spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.slice -/
def taSlice : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let r ← validateTypedArray thisV "TypedArray.prototype.slice"
  let srcLen := r.length
  -- 4-9.
  let startIndex ← relIndex (arg args 0) srcLen
  let endIndex ← relEnd (arg args 1) srcLen
  -- 10-11.
  let count := endIndex - startIndex
  let a ← typedArraySpeciesCreate r #[numV count]
  -- 12.
  if count > 0 then
    let r ← reread r
    if r.isOutOfBounds then throwType "TypedArray.prototype.slice: the typed array is detached or out of bounds"
    let endIndex := min endIndex r.length
    let count := endIndex - startIndex
    if r.kind == a.kind then
      let es := r.kind.elementSize
      let srcByteIndex := startIndex * es + r.byteOffset
      let n := count * es
      -- (byte by byte, ascending, as the spec copies: it matters when both share a buffer)
      if a.buf == r.buf then
        modifyObj r.buf fun o => o.withKind fun kd => match kd with
          | .buffer d det ml sh =>
            .buffer ((List.range n).foldl (fun d i =>
              if srcByteIndex + i < d.size && a.byteOffset + i < d.size then
                d.set! (a.byteOffset + i) (d.get! (srcByteIndex + i)) else d) d) det ml sh
          | kd => kd
      else
        writeBytes a.buf a.byteOffset (← readBytes r.buf srcByteIndex n)
    else
      forIdx_ 0 count fun n => do
        let kv ← taGet r.obj (startIndex + n)
        setIdx a.obj n kv
  pure (.obj a.obj)

/-- CompareTypedArrayElements as "x > y" spec: https://tc39.es/ecma262/#sec-comparetypedarrayelements -/
def taCompareGt (cmp : Value) (x y : Value) : M Bool := do
  -- 2.
  if !cmp.isUndefined then
    let v ← toNum (← call cmp .undefined #[x, y])
    return F64.lt F64.zero v
  -- 3-10.
  pure <| match x, y with
  | .bigint a, .bigint b => a > b
  | .num a, .num b =>
    if a == .nan then b != .nan
    else if b == .nan then false
    else if F64.lt b a then true
    else if F64.lt a b then false
    else !a.isNeg && b.isNeg
  | _, _ => false

/-- %TypedArray%.prototype.sort spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.sort -/
def taSort : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let cmp := arg args 0
  if !cmp.isUndefined && !(← isCallable cmp) then throwType "The comparison function must be either a function or undefined"
  -- 2-4.
  let r ← validateTypedArray thisV "TypedArray.prototype.sort"
  let len := r.length
  -- 5-6.
  let sorted ← sortIndexedProperties r.obj len (taCompareGt cmp) false
  -- 7-8.
  forIdx_ 0 sorted.size fun j => taSet r.obj j sorted[j]!
  pure (.obj r.obj)

/-- %TypedArray%.prototype.subarray spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.subarray -/
def taSubarray : BuiltinFn := fun _ thisV args _ => do
  -- 1-5.
  let r ← thisTA thisV "TypedArray.prototype.subarray"
  -- 6.
  let srcLength := r.lengthOr0
  -- 7-9.
  let startIndex ← relIndex (arg args 0) srcLength
  -- 10-12.
  let es := r.kind.elementSize
  let beginByteOffset := r.byteOffset + startIndex * es
  -- 13-14.
  let argList ← if r.arrayLength.isNone && (arg args 1).isUndefined then
      pure #[Value.obj r.buf, numV beginByteOffset]
    else do
      let endIndex ← relEnd (arg args 1) srcLength
      let newLength := endIndex - startIndex
      pure #[Value.obj r.buf, numV beginByteOffset, numV newLength]
  -- 15.
  let a ← typedArraySpeciesCreate r argList
  pure (.obj a.obj)

/-- %TypedArray%.prototype.toLocaleString spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.tolocalestring -/
def taToLocaleString : BuiltinFn := fun _ thisV _ _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.toLocaleString"
  let len := r.length
  M.repeatFrom (0, JSStr.empty) fun (k, acc) => do
    if k ≥ len then return .inr (Value.str acc)
    M.tick
    let acc := if k > 0 then acc ++ JSStr.ofString "," else acc
    let e ← taGet r.obj k
    if e.isNullish then return .inl (k + 1, acc)
    let s ← toStr (← invoke e (.str "toLocaleString"))
    return .inl (k + 1, acc ++ s)

/-- %TypedArray%.prototype.toReversed spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.toreversed -/
def taToReversed : BuiltinFn := fun _ thisV _ _ => do
  let r ← validateTypedArray thisV "TypedArray.prototype.toReversed"
  let len := r.length
  let a ← typedArrayCreateSameType r len
  forIdx_ 0 len fun k => do taSet a.obj k (← taGet r.obj (len - k - 1))
  pure (.obj a.obj)

/-- %TypedArray%.prototype.toSorted spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.tosorted -/
def taToSorted : BuiltinFn := fun _ thisV args _ => do
  let cmp := arg args 0
  if !cmp.isUndefined && !(← isCallable cmp) then throwType "The comparison function must be either a function or undefined"
  let r ← validateTypedArray thisV "TypedArray.prototype.toSorted"
  let len := r.length
  let a ← typedArrayCreateSameType r len
  let sorted ← sortIndexedProperties r.obj len (taCompareGt cmp) false
  forIdx_ 0 sorted.size fun j => taSet a.obj j sorted[j]!
  pure (.obj a.obj)

/-- %TypedArray%.prototype.with spec: https://tc39.es/ecma262/#sec-%typedarray%.prototype.with -/
def taWith : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let r ← validateTypedArray thisV "TypedArray.prototype.with"
  let len := r.length
  -- 4-6.
  let actual : Int ← match ← toIntegerOrInfinity (arg args 0) with
    | .inl true => pure (-1)
    | .inl false => pure len
    | .inr i => pure (if i ≥ 0 then i else len + i)
  -- 7.
  let v ← toElementNumeric r.kind (arg args 1)
  -- 8.
  let r2 ← reread r
  let valid := actual ≥ 0 && (isValidIntegerIndex r2 (F64.ofInt actual)).isSome
  if !valid then throwRange "Invalid typed array index"
  -- 9-10.
  let a ← typedArrayCreateSameType r len
  forIdx_ 0 len fun k => do
    let fv ← if (k : Int) == actual then pure v else taGet r.obj k
    taSet a.obj k fv
  pure (.obj a.obj)

/-! ## Atomics -/

/-- ValidateIntegerTypedArray spec: https://tc39.es/ecma262/#sec-validateintegertypedarray -/
def validateIntegerTypedArray (v : Value) (waitable : Bool) : M TARecord := do
  -- 1.
  let r ← validateTypedArray v "Atomics"
  -- 3-4.
  if waitable then
    if r.kind != .int32 && r.kind != .bigInt64 then throwType "Atomics.wait/notify: not an Int32Array or BigInt64Array"
  else
    if !r.kind.isUnclampedInteger && !r.kind.isBigInt then throwType "Atomics: not an integer typed array"
  pure r

/-- ValidateAtomicAccess: the byte index in the buffer.
spec: https://tc39.es/ecma262/#sec-validateatomicaccess -/
def validateAtomicAccess (r : TARecord) (requestIndex : Value) : M Nat := do
  -- 1.
  let length := r.length
  -- 2-4.
  let accessIndex ← toIndex requestIndex
  if accessIndex ≥ length then throwRange "Atomics: index out of range"
  -- 5-6.
  pure (accessIndex * r.kind.elementSize + r.byteOffset)

/-- RevalidateAtomicAccess spec: https://tc39.es/ecma262/#sec-revalidateatomicaccess -/
def revalidateAtomicAccess (r : TARecord) (byteIndex : Nat) : M TARecord := do
  let r ← reread r
  if r.isOutOfBounds then throwType "Atomics: the typed array is detached or out of bounds"
  if byteIndex ≥ (r.bufLen.getD 0) then throwRange "Atomics: index out of range"
  pure r

/-- The value operand of an atomic operation: ToBigInt, or 𝔽(ToIntegerOrInfinity). -/
def atomicOperand (k : TAKind) (v : Value) : M Value := do
  if k.isBigInt then return .bigint (← toBigInt v)
  match ← toIntegerOrInfinity v with
  | .inl neg => pure (.num (.inf neg))
  | .inr i => pure (.num (F64.ofInt i))

/-- AtomicReadModifyWrite (`op` on the raw bits of the old and the operand values)
spec: https://tc39.es/ecma262/#sec-atomicreadmodifywrite -/
def atomicRMW (op : Nat → Nat → Nat → Nat) : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let r ← validateIntegerTypedArray (arg args 0) false
  let byteIndex ← validateAtomicAccess r (arg args 1)
  -- 2-3.
  let v ← atomicOperand r.kind (arg args 2)
  -- 4.
  let r ← revalidateAtomicAccess r byteIndex
  -- 5-7. GetModifySetValueInBuffer
  let es := r.kind.elementSize
  let old ← readObj r.buf fun o => match o.kind with
    | .buffer d _ _ _ => bytesGet d byteIndex es true
    | _ => 0
  let bitsMod := 2 ^ (8 * es)
  writeBufferBits r.buf byteIndex es (op old (r.kind.toRaw v) bitsMod % bitsMod)
  pure (r.kind.ofRaw old)

/-- Atomics.compareExchange spec: https://tc39.es/ecma262/#sec-atomics.compareexchange -/
def atomicsCompareExchange : BuiltinFn := fun _ _ args _ => do
  let r ← validateIntegerTypedArray (arg args 0) false
  let byteIndex ← validateAtomicAccess r (arg args 1)
  let expected ← atomicOperand r.kind (arg args 2)
  let replacement ← atomicOperand r.kind (arg args 3)
  let r ← revalidateAtomicAccess r byteIndex
  let es := r.kind.elementSize
  let old ← readObj r.buf fun o => match o.kind with
    | .buffer d _ _ _ => bytesGet d byteIndex es true
    | _ => 0
  if old == r.kind.toRaw expected then
    writeBufferBits r.buf byteIndex es (r.kind.toRaw replacement)
  pure (r.kind.ofRaw old)

/-- Atomics.isLockFree spec: https://tc39.es/ecma262/#sec-atomics.islockfree -/
def atomicsIsLockFree : BuiltinFn := fun _ _ args _ => do
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr n => pure (.bool (n == 1 || n == 2 || n == 4 || n == 8))
  | _ => pure (.bool false)

/-- Atomics.load spec: https://tc39.es/ecma262/#sec-atomics.load -/
def atomicsLoad : BuiltinFn := fun _ _ args _ => do
  let r ← validateIntegerTypedArray (arg args 0) false
  let byteIndex ← validateAtomicAccess r (arg args 1)
  let r ← revalidateAtomicAccess r byteIndex
  getValueFromBuffer r.buf byteIndex r.kind

/-- Atomics.store spec: https://tc39.es/ecma262/#sec-atomics.store -/
def atomicsStore : BuiltinFn := fun _ _ args _ => do
  let r ← validateIntegerTypedArray (arg args 0) false
  let byteIndex ← validateAtomicAccess r (arg args 1)
  let v ← atomicOperand r.kind (arg args 2)
  -- (-0 is stored and returned as +0)
  let v := match v with | .num x => if x.isZero then Value.num F64.zero else v | v => v
  let r ← revalidateAtomicAccess r byteIndex
  setValueInBuffer r.buf byteIndex r.kind v
  pure v

/-- Atomics.wait (DoWait, synchronous). The engine is single-threaded with no other agents:
nothing can notify a waiter, so a wait that would block times out at once (the agent can
suspend: LIMITATION (docs/es.md L21)).
spec: https://tc39.es/ecma262/#sec-dowait -/
def atomicsWait : BuiltinFn := fun _ _ args _ => do
  -- 1-3.
  let r ← validateIntegerTypedArray (arg args 0) true
  let some bi ← bufInfo? r.buf | throwType "not a buffer"
  if !bi.shared then throwType "Atomics.wait: not a shared typed array"
  -- 4.
  let i ← validateAtomicAccess r (arg args 1)
  -- 5-7.
  let v ← if r.kind == .bigInt64 then pure (Value.bigint (Num.BigInt.toBigInt64 (← toBigInt (arg args 2))))
    else pure (Value.num (F64.ofInt (← toInt32 (arg args 2))))
  -- 8-9.
  let _ ← toNum (arg args 3)
  -- 10-…: compare and (not) wait.
  let w ← getValueFromBuffer r.buf i r.kind
  let same := match v, w with
    | .bigint a, .bigint b => a == b
    | .num a, .num b => a == b
    | _, _ => false
  if !same then return .str "not-equal"
  pure (.str "timed-out")

/-- Atomics.notify spec: https://tc39.es/ecma262/#sec-atomics.notify -/
def atomicsNotify : BuiltinFn := fun _ _ args _ => do
  -- 1-2.
  let r ← validateIntegerTypedArray (arg args 0) true
  let _ ← validateAtomicAccess r (arg args 1)
  -- 3.
  if !(arg args 2).isUndefined then
    let _ ← toIntegerOrInfinity (arg args 2)
  -- 4-… (no waiters)
  pure (numV 0)

/-- Atomics.pause spec: https://tc39.es/ecma262/#sec-atomics.pause -/
def atomicsPause : BuiltinFn := fun _ _ args _ => do
  let n := arg args 0
  if !n.isUndefined then
    match n with
    | .num x => if !Conv.isIntegral x then throwType "Atomics.pause: argument must be an integral Number"
    | _ => throwType "Atomics.pause: argument must be an integral Number"
  pure .undefined

/-! ## Setup -/

def typedArrayDefs : Array BuiltinDef := #[
  ⟨"TypedArray", typedArrayAbstractCtor⟩,
  ⟨"TypedArray.from", typedArrayFrom⟩, ⟨"TypedArray.of", typedArrayOf⟩,
  ⟨"get TypedArray.prototype.buffer", taBuffer⟩,
  ⟨"get TypedArray.prototype.byteLength", taByteLength⟩,
  ⟨"get TypedArray.prototype.byteOffset", taByteOffset⟩,
  ⟨"get TypedArray.prototype.length", taLength⟩,
  ⟨"get TypedArray.prototype[Symbol.toStringTag]", taToStringTag⟩,
  ⟨"TypedArray.prototype.at", taAt⟩, ⟨"TypedArray.prototype.copyWithin", taCopyWithin⟩,
  ⟨"TypedArray.prototype.entries", taIter 2⟩, ⟨"TypedArray.prototype.keys", taIter 0⟩,
  ⟨"TypedArray.prototype.values", taIter 1⟩,
  ⟨"TypedArray.prototype.every", taEverySome false⟩, ⟨"TypedArray.prototype.some", taEverySome true⟩,
  ⟨"TypedArray.prototype.fill", taFill⟩, ⟨"TypedArray.prototype.filter", taFilter⟩,
  ⟨"TypedArray.prototype.find", taFind true false⟩, ⟨"TypedArray.prototype.findIndex", taFind true true⟩,
  ⟨"TypedArray.prototype.findLast", taFind false false⟩,
  ⟨"TypedArray.prototype.findLastIndex", taFind false true⟩,
  ⟨"TypedArray.prototype.forEach", taForEach⟩, ⟨"TypedArray.prototype.includes", taIncludes⟩,
  ⟨"TypedArray.prototype.indexOf", taIndexOf⟩, ⟨"TypedArray.prototype.join", taJoin⟩,
  ⟨"TypedArray.prototype.lastIndexOf", taLastIndexOf⟩, ⟨"TypedArray.prototype.map", taMap⟩,
  ⟨"TypedArray.prototype.reduce", taReduce false⟩, ⟨"TypedArray.prototype.reduceRight", taReduce true⟩,
  ⟨"TypedArray.prototype.reverse", taReverse⟩, ⟨"TypedArray.prototype.set", taSetMethod⟩,
  ⟨"TypedArray.prototype.slice", taSlice⟩, ⟨"TypedArray.prototype.sort", taSort⟩,
  ⟨"TypedArray.prototype.subarray", taSubarray⟩,
  ⟨"TypedArray.prototype.toLocaleString", taToLocaleString⟩,
  ⟨"TypedArray.prototype.toReversed", taToReversed⟩, ⟨"TypedArray.prototype.toSorted", taToSorted⟩,
  ⟨"TypedArray.prototype.with", taWith⟩,
  ⟨"Atomics.add", atomicRMW (fun a b _ => a + b)⟩,
  ⟨"Atomics.and", atomicRMW (fun a b _ => a &&& b)⟩,
  ⟨"Atomics.exchange", atomicRMW (fun _ b _ => b)⟩,
  ⟨"Atomics.or", atomicRMW (fun a b _ => a ||| b)⟩,
  ⟨"Atomics.sub", atomicRMW (fun a b m => a + (m - b % m))⟩,
  ⟨"Atomics.xor", atomicRMW (fun a b _ => a ^^^ b)⟩,
  ⟨"Atomics.compareExchange", atomicsCompareExchange⟩, ⟨"Atomics.isLockFree", atomicsIsLockFree⟩,
  ⟨"Atomics.load", atomicsLoad⟩, ⟨"Atomics.store", atomicsStore⟩, ⟨"Atomics.wait", atomicsWait⟩,
  ⟨"Atomics.notify", atomicsNotify⟩, ⟨"Atomics.pause", atomicsPause⟩] ++
  TAKind.all.map (fun k => ⟨k.name, typedArrayCtor k⟩)

/-- Creates %TypedArray%, the typed array constructors, and %Atomics%. -/
def typedArraySetup : M Unit := do
  let fp ← intrinsic "%Function.prototype%"
  let _ := fp
  -- %TypedArray%
  let tap ← newIntrinsicObject "%TypedArray.prototype%"
  let (tac, _) ← defConstructor "TypedArray" 0 "TypedArray" tap (global := false)
  defSpecies tac
  let _ ← defMethod tac (.str "from") "TypedArray.from" 1
  let _ ← defMethod tac (.str "of") "TypedArray.of" 0
  for nm in ["buffer", "byteLength", "byteOffset", "length"] do
    defGetter tap (.str (JSStr.ofString nm)) s!"get TypedArray.prototype.{nm}"
  defGetter tap (.sym WK.toStringTag) "get TypedArray.prototype[Symbol.toStringTag]"
  for (nm, len) in [("at", 1), ("copyWithin", 2), ("entries", 0), ("keys", 0), ("every", 1),
      ("some", 1), ("fill", 1), ("filter", 1), ("find", 1), ("findIndex", 1), ("findLast", 1),
      ("findLastIndex", 1), ("forEach", 1), ("includes", 1), ("indexOf", 1), ("join", 1),
      ("lastIndexOf", 1), ("map", 1), ("reduce", 1), ("reduceRight", 1), ("reverse", 0),
      ("set", 1), ("slice", 2), ("sort", 1), ("subarray", 2), ("toLocaleString", 0),
      ("toReversed", 0), ("toSorted", 1), ("with", 2)] do
    let _ ← defMethod tap (.str (JSStr.ofString nm)) s!"TypedArray.prototype.{nm}" len
  let vals ← defMethod tap (.str "values") "TypedArray.prototype.values" 0
  setOwn tap (.sym WK.iterator) (.data (.obj vals) true false true)
  -- (toString is %Array.prototype.toString%)
  let ap ← intrinsic "%Array.prototype%"
  match ← ownProp ap (.str kToString) with
  | some (.data f ..) => setOwn tap (.str kToString) (.data f true false true)
  | _ => pure ()
  -- The TypedArray constructors
  for k in TAKind.all do
    let p ← newIntrinsicObject s!"%{k.name}.prototype%" (some tap)
    let (c, _) ← defConstructor k.name 3 k.name p (some tac)
    defValue c (.str "BYTES_PER_ELEMENT") (numV k.elementSize)
    defValue p (.str "BYTES_PER_ELEMENT") (numV k.elementSize)
  -- Atomics
  let atom ← newIntrinsicObject "%Atomics%"
  defGlobal "Atomics" (.obj atom)
  defTag atom "Atomics"
  for (nm, len) in [("add", 3), ("and", 3), ("compareExchange", 4), ("exchange", 3),
      ("isLockFree", 1), ("load", 2), ("or", 3), ("store", 3), ("sub", 3), ("wait", 4),
      ("notify", 3), ("xor", 3), ("pause", 0)] do
    let _ ← defMethod atom (.str (JSStr.ofString nm)) s!"Atomics.{nm}" len

end ES.Builtins.Collections
