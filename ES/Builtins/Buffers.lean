import ES.Builtins.Array

/-!
# ArrayBuffer, SharedArrayBuffer, DataView

spec: https://tc39.es/ecma262/#sec-arraybuffer-objects,
https://tc39.es/ecma262/#sec-sharedarraybuffer-objects, https://tc39.es/ecma262/#sec-dataview-objects

A buffer is `Kind.buffer data detached maxLen shared`: its bytes (the current byte length is
`data.size`), whether it is detached, its [[ArrayBufferMaxByteLength]] (resizable/growable
buffers) and whether it is a SharedArrayBuffer. Single-threaded: a SharedArrayBuffer's block is
its own, and every memory order is the same.
-/

namespace ES.Builtins.Collections

open ES (F64)

/-- The largest Data Block the engine creates (2^31 bytes; larger requests are RangeErrors, as
CreateByteDataBlock allows: LIMITATION (docs/es.md L20)). -/
def maxAllocBytes : Nat := 2147483648

/-- The largest [[ArrayBufferMaxByteLength]] accepted (the engine never reserves it up front;
resizing past `maxAllocBytes` still fails). -/
def maxMaxByteLength : Nat := 4294967296

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray :=
  (List.range n).foldl (fun b _ => b.push 0) (ByteArray.emptyWithCapacity n)

/-- CreateByteDataBlock spec: https://tc39.es/ecma262/#sec-createbytedatablock -/
def createByteDataBlock (size : Nat) : M ByteArray := do
  if size > maxAllocBytes then throwRange "Array buffer allocation failed"
  pure (zeroBytes size)

/-- `bytes` resized to `n` (truncated, or extended with zeros). -/
def resizeBytes (d : ByteArray) (n : Nat) : ByteArray :=
  if n ≤ d.size then d.extract 0 n
  else (List.range (n - d.size)).foldl (fun b _ => b.push 0) d

/-- The bytes [off, off + len) of a buffer (a copy). -/
def readBytes (buf : ObjId) (off len : Nat) : M ByteArray := readObj buf fun o => match o.kind with
  | .buffer d _ _ _ => d.extract off (off + len)
  | _ => ByteArray.empty

/-- Writes bytes into a buffer at `off` (in place). -/
def writeBytes (buf : ObjId) (off : Nat) (bytes : ByteArray) : M Unit :=
  modifyObj buf fun o => o.withKind fun k => match k with
    | .buffer d det ml sh =>
      if off + bytes.size ≤ d.size then .buffer (bytes.copySlice 0 d off bytes.size) det ml sh
      else .buffer d det ml sh
    | k => k

/-- AllocateArrayBuffer (`shared`: AllocateSharedArrayBuffer)
spec: https://tc39.es/ecma262/#sec-allocatearraybuffer -/
def allocateArrayBuffer (ctor : Value) (byteLength : Nat) (maxLen : Option Nat := none)
    (shared := false) : M ObjId := do
  -- 2-3.
  if let some m := maxLen then
    if byteLength > m then throwRange "byteLength exceeds maxByteLength"
  -- 4.
  let proto ← getPrototypeFromConstructor ctor
    (if shared then "%SharedArrayBuffer.prototype%" else "%ArrayBuffer.prototype%")
  -- 5.
  let block ← createByteDataBlock byteLength
  -- 8.
  if let some m := maxLen then
    if m > maxMaxByteLength then throwRange "Invalid array buffer max length"
  alloc { proto := .obj proto, kind := .buffer block false maxLen shared }

/-- A new %ArrayBuffer% of `n` bytes. -/
def newArrayBuffer (n : Nat) : M ObjId := do
  allocateArrayBuffer (← intrinsicV "%ArrayBuffer%") n

/-- RequireInternalSlot(O, [[ArrayBufferData]]) and the IsSharedArrayBuffer check. -/
def thisBuffer (v : Value) (shared : Bool) (what : String) : M (ObjId × BufInfo) := do
  let .obj o := v | throwType s!"{what} called on incompatible receiver"
  match ← bufInfo? o with
  | some bi => if bi.shared != shared then throwType s!"{what} called on incompatible receiver" else pure (o, bi)
  | none => throwType s!"{what} called on incompatible receiver"

/-- CloneArrayBuffer spec: https://tc39.es/ecma262/#sec-clonearraybuffer -/
def cloneArrayBuffer (src : ObjId) (srcByteOffset srcLength : Nat) : M ObjId := do
  let target ← newArrayBuffer srcLength
  writeBytes target 0 (← readBytes src srcByteOffset srcLength)
  pure target

/-- DetachArrayBuffer spec: https://tc39.es/ecma262/#sec-detacharraybuffer -/
def detachArrayBuffer (b : ObjId) : M Unit :=
  modifyObj b fun o => o.withKind fun k => match k with
    | .buffer _ _ ml sh => .buffer ByteArray.empty true ml sh
    | k => k

/-- GetArrayBufferMaxByteLengthOption spec: https://tc39.es/ecma262/#sec-getarraybuffermaxbytelengthoption -/
def getMaxByteLengthOption (options : Value) : M (Option Nat) := do
  let .obj o := options | return none
  let m ← getProp o (.str "maxByteLength")
  if m.isUndefined then return none
  some <$> toIndex m

/-! ## ArrayBuffer -/

/-- ArrayBuffer(length [, options]) spec: https://tc39.es/ecma262/#sec-arraybuffer-length -/
def arrayBufferCtor (shared : Bool) : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then throwType "Constructor requires 'new'"
  -- 2.
  let byteLength ← toIndex (arg args 0)
  -- 3.
  let maxLen ← getMaxByteLengthOption (arg args 1)
  -- 4.
  pure (.obj (← allocateArrayBuffer nt byteLength maxLen shared))

/-- ArrayBuffer.isView spec: https://tc39.es/ecma262/#sec-arraybuffer.isview -/
def arrayBufferIsView : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return .bool false
  match ← objKind o with
  | .typedArray .. | .dataView .. => pure (.bool true)
  | _ => pure (.bool false)

/-- get ArrayBuffer.prototype.byteLength (and SharedArrayBuffer's)
spec: https://tc39.es/ecma262/#sec-get-arraybuffer.prototype.bytelength -/
def bufferByteLength (shared : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let (_, bi) ← thisBuffer thisV shared "byteLength"
  pure (numV (if bi.detached then 0 else bi.byteLength))

/-- get ArrayBuffer.prototype.maxByteLength
spec: https://tc39.es/ecma262/#sec-get-arraybuffer.prototype.maxbytelength -/
def bufferMaxByteLength (shared : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let (_, bi) ← thisBuffer thisV shared "maxByteLength"
  if bi.detached then return numV 0
  pure (numV (bi.maxLen.getD bi.byteLength))

/-- get ArrayBuffer.prototype.resizable / SharedArrayBuffer.prototype.growable
spec: https://tc39.es/ecma262/#sec-get-arraybuffer.prototype.resizable -/
def bufferResizable (shared : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let (_, bi) ← thisBuffer thisV shared "resizable"
  pure (.bool bi.maxLen.isSome)

/-- get ArrayBuffer.prototype.detached spec: https://tc39.es/ecma262/#sec-get-arraybuffer.prototype.detached -/
def bufferDetached : BuiltinFn := fun _ thisV _ _ => do
  let (_, bi) ← thisBuffer thisV false "detached"
  pure (.bool bi.detached)

/-- ArrayBuffer.prototype.resize spec: https://tc39.es/ecma262/#sec-arraybuffer.prototype.resize -/
def arrayBufferResize : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let (o, bi) ← thisBuffer thisV false "ArrayBuffer.prototype.resize"
  let some maxLen := bi.maxLen | throwType "ArrayBuffer.prototype.resize: not a resizable buffer"
  -- 4.
  let newByteLength ← toIndex (arg args 0)
  -- 5.
  let some bi ← bufInfo? o | throwType "not a buffer"
  if bi.detached then throwType "ArrayBuffer.prototype.resize: buffer is detached"
  -- 6.
  if newByteLength > maxLen then throwRange "ArrayBuffer.prototype.resize: new length exceeds maxByteLength"
  if newByteLength > maxAllocBytes then throwRange "Array buffer allocation failed"
  -- 7-15.
  modifyObj o fun ob => ob.withKind fun k => match k with
    | .buffer d det ml sh => .buffer (resizeBytes d newByteLength) det ml sh
    | k => k
  pure .undefined

/-- SharedArrayBuffer.prototype.grow spec: https://tc39.es/ecma262/#sec-sharedarraybuffer.prototype.grow -/
def sharedArrayBufferGrow : BuiltinFn := fun _ thisV args _ => do
  let (o, bi) ← thisBuffer thisV true "SharedArrayBuffer.prototype.grow"
  let some maxLen := bi.maxLen | throwType "SharedArrayBuffer.prototype.grow: not a growable buffer"
  let newByteLength ← toIndex (arg args 0)
  let some bi ← bufInfo? o | throwType "not a buffer"
  if newByteLength > maxLen then throwRange "SharedArrayBuffer.prototype.grow: new length exceeds maxByteLength"
  if newByteLength < bi.byteLength then throwRange "SharedArrayBuffer.prototype.grow: cannot shrink"
  if newByteLength > maxAllocBytes then throwRange "Array buffer allocation failed"
  modifyObj o fun ob => ob.withKind fun k => match k with
    | .buffer d det ml sh => .buffer (resizeBytes d newByteLength) det ml sh
    | k => k
  pure .undefined

/-- ArrayBuffer.prototype.slice / SharedArrayBuffer.prototype.slice
spec: https://tc39.es/ecma262/#sec-arraybuffer.prototype.slice -/
def bufferSlice (shared : Bool) : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let (o, bi) ← thisBuffer thisV shared "slice"
  -- 4.
  if bi.detached then throwType "slice: buffer is detached"
  -- 5.
  let len := bi.byteLength
  -- 6-9.
  let first ← relIndex (arg args 0) len
  let final ← relEnd (arg args 1) len
  -- 10.
  let newLen := final - first
  -- 11-12.
  let ctor ← speciesConstructor o (← intrinsicV (if shared then "%SharedArrayBuffer%" else "%ArrayBuffer%"))
  let new ← construct ctor #[numV newLen]
  -- 13-14.
  let .obj n := new | throwType "slice: species constructor returned a non-buffer"
  let some nbi ← bufInfo? n | throwType "slice: species constructor returned a non-buffer"
  if nbi.shared != shared then throwType "slice: species constructor returned a buffer of the wrong kind"
  -- 15.
  if nbi.detached then throwType "slice: species constructor returned a detached buffer"
  -- 16.
  if n == o then throwType "slice: species constructor returned the same buffer"
  -- 17.
  if nbi.byteLength < newLen then throwType "slice: species constructor returned a too small buffer"
  -- 19.
  let some bi ← bufInfo? o | throwType "not a buffer"
  if bi.detached then throwType "slice: buffer is detached"
  -- 22-23.
  let currentLen := bi.byteLength
  if first < currentLen then
    let count := min newLen (currentLen - first)
    writeBytes n 0 (← readBytes o first count)
  pure new

/-- ArrayBufferCopyAndDetach spec: https://tc39.es/ecma262/#sec-arraybuffercopyanddetach -/
def arrayBufferCopyAndDetach (thisV newLength : Value) (preserveResizability : Bool) : M Value := do
  -- 1-2.
  let (o, bi) ← thisBuffer thisV false "transfer"
  -- 3.
  let newByteLength ← if newLength.isUndefined then pure (if bi.detached then 0 else bi.byteLength)
    else toIndex newLength
  -- 4.
  let some bi ← bufInfo? o | throwType "not a buffer"
  if bi.detached then throwType "transfer: buffer is detached"
  -- 5.
  let newMax := if preserveResizability then bi.maxLen else none
  -- 7.
  let nb ← allocateArrayBuffer (← intrinsicV "%ArrayBuffer%") newByteLength newMax
  -- 8-11.
  let copyLength := min newByteLength bi.byteLength
  writeBytes nb 0 (← readBytes o 0 copyLength)
  -- 12.
  detachArrayBuffer o
  pure (.obj nb)

def arrayBufferTransfer (preserve : Bool) : BuiltinFn := fun _ thisV args _ =>
  arrayBufferCopyAndDetach thisV (arg args 0) preserve

/-! ## DataView -/

/-- A DataView With Buffer Witness Record, with the view's slots: (buffer, byteOffset,
byteLength (`none`: auto), the buffer's byte length (`none`: detached)).
spec: https://tc39.es/ecma262/#sec-dataview-with-buffer-witness-records -/
structure DVRecord where
  buf : ObjId
  byteOffset : Nat
  byteLength : Option Nat
  bufLen : Option Nat

/-- IsViewOutOfBounds spec: https://tc39.es/ecma262/#sec-isviewoutofbounds -/
def DVRecord.isOutOfBounds (r : DVRecord) : Bool :=
  match r.bufLen with
  | none => true
  | some bl =>
    let stop := match r.byteLength with | none => bl | some l => r.byteOffset + l
    r.byteOffset > bl || stop > bl

/-- GetViewByteLength spec: https://tc39.es/ecma262/#sec-getviewbytelength -/
def DVRecord.viewByteLength (r : DVRecord) : Nat :=
  match r.byteLength with
  | some l => l
  | none => (r.bufLen.getD 0) - r.byteOffset

/-- RequireInternalSlot(view, [[DataView]]) + MakeDataViewWithBufferWitnessRecord. -/
def thisDataView (v : Value) (what : String) : M DVRecord := do
  let .obj o := v | throwType s!"{what} called on incompatible receiver"
  let .dataView buf off len ← objKind o | throwType s!"{what} called on incompatible receiver"
  let bl ← readObj buf fun b => match b.kind with
    | .buffer d det _ _ => if det then none else some d.size
    | _ => none
  pure { buf, byteOffset := off, byteLength := len, bufLen := bl }

/-- DataView(buffer [, byteOffset [, byteLength]]) spec: https://tc39.es/ecma262/#sec-dataview-buffer-byteoffset-bytelength -/
def dataViewCtor : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then throwType "Constructor DataView requires 'new'"
  -- 2.
  let .obj buffer := arg args 0 | throwType "First argument to DataView constructor must be an ArrayBuffer"
  let some bi ← bufInfo? buffer | throwType "First argument to DataView constructor must be an ArrayBuffer"
  -- 3.
  let offset ← toIndex (arg args 1)
  -- 4.
  let some bi ← bufInfo? buffer | throwType "not a buffer"
  if bi.detached then throwType "DataView: buffer is detached"
  -- 5-6.
  let bufferByteLength := bi.byteLength
  if offset > bufferByteLength then throwRange "Start offset is outside the bounds of the buffer"
  -- 7.
  let fixed := bi.maxLen.isNone
  -- 8-9.
  let byteLength := arg args 2
  let viewByteLength : Option Nat ← if byteLength.isUndefined then
      pure (if fixed then some (bufferByteLength - offset) else none)
    else do
      let l ← toIndex byteLength
      if offset + l > bufferByteLength then throwRange "Invalid DataView length"
      pure (some l)
  -- 10.
  let proto ← getPrototypeFromConstructor nt "%DataView.prototype%"
  -- 11-14.
  let some bi ← bufInfo? buffer | throwType "not a buffer"
  if bi.detached then throwType "DataView: buffer is detached"
  if offset > bi.byteLength then throwRange "Start offset is outside the bounds of the buffer"
  if !byteLength.isUndefined then
    if offset + viewByteLength.getD 0 > bi.byteLength then throwRange "Invalid DataView length"
  -- 15-19.
  let o ← alloc { proto := .obj proto, kind := .dataView buffer offset viewByteLength }
  pure (.obj o)

/-- get DataView.prototype.buffer spec: https://tc39.es/ecma262/#sec-get-dataview.prototype.buffer -/
def dataViewBuffer : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisDataView thisV "DataView.prototype.buffer"
  pure (.obj r.buf)

/-- get DataView.prototype.byteLength spec: https://tc39.es/ecma262/#sec-get-dataview.prototype.bytelength -/
def dataViewByteLength : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisDataView thisV "DataView.prototype.byteLength"
  -- 5.
  if r.isOutOfBounds then return numV 0
  pure (numV r.viewByteLength)

/-- get DataView.prototype.byteOffset spec: https://tc39.es/ecma262/#sec-get-dataview.prototype.byteoffset -/
def dataViewByteOffset : BuiltinFn := fun _ thisV _ _ => do
  let r ← thisDataView thisV "DataView.prototype.byteOffset"
  -- 5.
  if r.isOutOfBounds then return numV 0
  pure (numV r.byteOffset)

/-- GetViewValue spec: https://tc39.es/ecma262/#sec-getviewvalue -/
def getViewValue (k : TAKind) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let _ ← thisDataView thisV "DataView.prototype.get"
  -- 3.
  let getIndex ← toIndex (arg args 0)
  -- 4.
  let little := toBoolean (arg args 1)
  -- 5-8.
  let r ← thisDataView thisV "DataView.prototype.get"
  if r.isOutOfBounds then throwType "DataView is out of bounds"
  let viewSize := r.viewByteLength
  -- 9-10.
  if getIndex + k.elementSize > viewSize then throwRange "Offset is outside the bounds of the DataView"
  -- 11-12.
  getValueFromBuffer r.buf (getIndex + r.byteOffset) k little

/-- SetViewValue spec: https://tc39.es/ecma262/#sec-setviewvalue -/
def setViewValue (k : TAKind) : BuiltinFn := fun _ thisV args _ => do
  let _ ← thisDataView thisV "DataView.prototype.set"
  -- 3.
  let getIndex ← toIndex (arg args 0)
  -- 4.
  let v ← if k.isBigInt then Value.bigint <$> toBigInt (arg args 1) else Value.num <$> toNum (arg args 1)
  -- 5.
  let little := toBoolean (arg args 2)
  -- 6-9.
  let r ← thisDataView thisV "DataView.prototype.set"
  if r.isOutOfBounds then throwType "DataView is out of bounds"
  let viewSize := r.viewByteLength
  -- 10-11.
  if getIndex + k.elementSize > viewSize then throwRange "Offset is outside the bounds of the DataView"
  -- 12-13.
  setValueInBuffer r.buf (getIndex + r.byteOffset) k v little
  pure .undefined

/-- The DataView method name part of an element type. -/
def dvName : TAKind → String
  | .int8 => "Int8" | .uint8 => "Uint8" | .uint8c => "Uint8Clamped" | .int16 => "Int16"
  | .uint16 => "Uint16" | .int32 => "Int32" | .uint32 => "Uint32" | .float16 => "Float16"
  | .float32 => "Float32" | .float64 => "Float64" | .bigInt64 => "BigInt64" | .bigUint64 => "BigUint64"

def dvKinds : Array TAKind := TAKind.all.filter (· != .uint8c)

/-- This file's behaviours. -/
def bufferDefs : Array BuiltinDef := #[
  ⟨"ArrayBuffer", arrayBufferCtor false⟩, ⟨"SharedArrayBuffer", arrayBufferCtor true⟩,
  ⟨"ArrayBuffer.isView", arrayBufferIsView⟩,
  ⟨"get ArrayBuffer.prototype.byteLength", bufferByteLength false⟩,
  ⟨"get SharedArrayBuffer.prototype.byteLength", bufferByteLength true⟩,
  ⟨"get ArrayBuffer.prototype.maxByteLength", bufferMaxByteLength false⟩,
  ⟨"get SharedArrayBuffer.prototype.maxByteLength", bufferMaxByteLength true⟩,
  ⟨"get ArrayBuffer.prototype.resizable", bufferResizable false⟩,
  ⟨"get SharedArrayBuffer.prototype.growable", bufferResizable true⟩,
  ⟨"get ArrayBuffer.prototype.detached", bufferDetached⟩,
  ⟨"ArrayBuffer.prototype.resize", arrayBufferResize⟩,
  ⟨"SharedArrayBuffer.prototype.grow", sharedArrayBufferGrow⟩,
  ⟨"ArrayBuffer.prototype.slice", bufferSlice false⟩,
  ⟨"SharedArrayBuffer.prototype.slice", bufferSlice true⟩,
  ⟨"ArrayBuffer.prototype.transfer", arrayBufferTransfer true⟩,
  ⟨"ArrayBuffer.prototype.transferToFixedLength", arrayBufferTransfer false⟩,
  ⟨"DataView", dataViewCtor⟩,
  ⟨"get DataView.prototype.buffer", dataViewBuffer⟩,
  ⟨"get DataView.prototype.byteLength", dataViewByteLength⟩,
  ⟨"get DataView.prototype.byteOffset", dataViewByteOffset⟩] ++
  dvKinds.map (fun k => ⟨s!"DataView.prototype.get{dvName k}", getViewValue k⟩) ++
  dvKinds.map (fun k => ⟨s!"DataView.prototype.set{dvName k}", setViewValue k⟩)

/-- Creates %ArrayBuffer%, %SharedArrayBuffer%, %DataView% and their prototypes. -/
def bufferSetup : M Unit := do
  -- ArrayBuffer
  let abp ← newIntrinsicObject "%ArrayBuffer.prototype%"
  let (abc, _) ← defConstructor "ArrayBuffer" 1 "ArrayBuffer" abp
  defSpecies abc
  let _ ← defMethod abc (.str "isView") "ArrayBuffer.isView" 1
  for nm in ["byteLength", "maxByteLength", "resizable", "detached"] do
    defGetter abp (.str (JSStr.ofString nm)) s!"get ArrayBuffer.prototype.{nm}"
  for (nm, len) in [("resize", 1), ("slice", 2), ("transfer", 0), ("transferToFixedLength", 0)] do
    let _ ← defMethod abp (.str (JSStr.ofString nm)) s!"ArrayBuffer.prototype.{nm}" len
  defTag abp "ArrayBuffer"
  -- SharedArrayBuffer
  let sbp ← newIntrinsicObject "%SharedArrayBuffer.prototype%"
  let (sbc, _) ← defConstructor "SharedArrayBuffer" 1 "SharedArrayBuffer" sbp
  defSpecies sbc
  for nm in ["byteLength", "maxByteLength", "growable"] do
    defGetter sbp (.str (JSStr.ofString nm)) s!"get SharedArrayBuffer.prototype.{nm}"
  for (nm, len) in [("grow", 1), ("slice", 2)] do
    let _ ← defMethod sbp (.str (JSStr.ofString nm)) s!"SharedArrayBuffer.prototype.{nm}" len
  defTag sbp "SharedArrayBuffer"
  -- DataView
  let dvp ← newIntrinsicObject "%DataView.prototype%"
  let _ ← defConstructor "DataView" 1 "DataView" dvp
  for nm in ["buffer", "byteLength", "byteOffset"] do
    defGetter dvp (.str (JSStr.ofString nm)) s!"get DataView.prototype.{nm}"
  for k in dvKinds do
    let _ ← defMethod dvp (.str (JSStr.ofString s!"get{dvName k}")) s!"DataView.prototype.get{dvName k}" 1
  for k in dvKinds do
    let _ ← defMethod dvp (.str (JSStr.ofString s!"set{dvName k}")) s!"DataView.prototype.set{dvName k}" 2
  defTag dvp "DataView"

end ES.Builtins.Collections
