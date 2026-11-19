import ES.Heap
import ES.NumBridge

/-!
# Objects' internal methods

spec: https://tc39.es/ecma262/#sec-ordinary-and-exotic-objects-behaviours

The essential internal methods dispatch on the object's `Kind`: ordinary objects (10.1), arrays
(10.4.2), String exotic objects (10.4.3), arguments objects (10.4.4), immutable prototype exotic
objects (10.4.7), and proxies (10.5). Proxies make the methods mutually recursive (a trap's result
is checked against the target's own methods, and the target may be a proxy), and so do the type
conversions they use (ToPropertyDescriptor reads a descriptor object, which may be a proxy), so
they are one mutual block with a depth parameter `n`: each nested internal-method call takes
one. Exhausting it throws a RangeError, as engines do on stack overflow; `maxDepth` is far beyond
any chain of proxies or prototypes a program builds without a cycle (a cycle of proxies is
infinite recursion in every engine).
-/

namespace ES

open ES (F64)

/-- The depth bound of the internal-method recursion (see the module docstring). -/
def maxDepth : Nat := 20000

def kLength : JSStr := "length"
def kPrototype : JSStr := "prototype"
def kConstructor : JSStr := "constructor"
def kName : JSStr := "name"
def kValue : JSStr := "value"
def kWritable : JSStr := "writable"
def kGet : JSStr := "get"
def kSet : JSStr := "set"
def kEnumerable : JSStr := "enumerable"
def kConfigurable : JSStr := "configurable"
def kDone : JSStr := "done"
def kNext : JSStr := "next"
def kToString : JSStr := "toString"
def kValueOf : JSStr := "valueOf"

/-! ## Values -/

/-- SameValue spec: https://tc39.es/ecma262/#sec-samevalue
(`F64` values are canonical: equal numbers are equal terms, NaN is one term, ±0 differ.) -/
def sameValue : Value → Value → Bool
  | .undefined, .undefined | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .sym a, .sym b => a == b
  | .bigint a, .bigint b => a == b
  | .obj a, .obj b => a == b
  | _, _ => false

/-- SameValueZero spec: https://tc39.es/ecma262/#sec-samevaluezero -/
def sameValueZero (x y : Value) : Bool :=
  match x, y with
  | .num a, .num b => a == b || (a.isZero && b.isZero)
  | _, _ => sameValue x y

/-- The key a value has in a Map/Set index (SameValueZero: -0 is +0). -/
def mapKey : Value → PropKey
  | .undefined => .str "u"
  | .null => .str "n"
  | .bool b => .str (if b then "t" else "f")
  | .num x => .str (JSStr.ofString ("#" ++ (if x.isZero then "0" else x.toDecimal)))
  | .str s => .str (JSStr.ofString "s" ++ s)
  | .sym id => .sym id
  | .bigint i => .str (JSStr.ofString ("b" ++ toString i))
  | .obj id => .str (JSStr.ofString ("o" ++ toString id))

/-- ToBoolean spec: https://tc39.es/ecma262/#sec-toboolean -/
def toBoolean : Value → Bool
  | .undefined | .null => false
  | .bool b => b
  | .num x => !(x.isZero || x == .nan)
  | .str s => !s.isEmpty
  | .sym _ => true
  | .bigint i => i != 0
  | .obj _ => true

def Value.isObject : Value → Bool | .obj _ => true | _ => false
def Value.isUndefined : Value → Bool | .undefined => true | _ => false
def Value.isNullish : Value → Bool | .undefined | .null => true | _ => false

/-- Number::toString for property keys and ToString. -/
def PropKey.ofNat (n : Nat) : PropKey := .str (JSStr.ofNat n)

/-- The value of an array index key. -/
def PropKey.arrayIndex? : PropKey → Option Nat
  | .str s => s.toArrayIndex?
  | .sym _ => none

/-- IsCallable spec: https://tc39.es/ecma262/#sec-iscallable -/
def isCallable (v : Value) : M Bool := match v with
  | .obj id => readObj id fun o => match o.kind with
    | .func _ | .builtin _ | .bound .. => true
    | .proxy _ _ c _ => c
    | _ => false
  | _ => pure false

/-- IsConstructor spec: https://tc39.es/ecma262/#sec-isconstructor -/
def isConstructor (v : Value) : M Bool := match v with
  | .obj id => do
    let k ← objKind id
    match k with
    | .func d => pure (match d.code.kind with
        | .normal => !d.code.isAsync && !d.code.isGenerator
        | .classConstructor _ => true
        | _ => false)
    | .builtin b => pure b.isCtor
    | .bound t _ _ => isConstructorId t
    | .proxy _ _ _ c => pure c
    | _ => pure false
  | _ => pure false
where
  /-- (a bound function's target: bound chains are finite and acyclic, built bottom-up) -/
  isConstructorId (t : ObjId) : M Bool := readObj t fun o => match o.kind with
    | .func d => match d.code.kind with
      | .normal => !d.code.isAsync && !d.code.isGenerator
      | .classConstructor _ => true
      | _ => false
    | .builtin b => b.isCtor
    | .proxy _ _ _ c => c
    | .bound .. => true  -- (Function.prototype.bind only makes constructors of constructors: checked there)
    | _ => false

/-! ## Property descriptors -/

/-- ValidateAndApplyPropertyDescriptor's decision on an object (`ext`: its [[Extensible]]):
whether it succeeds, and the property to store (`none`: unchanged).
spec: https://tc39.es/ecma262/#sec-validateandapplypropertydescriptor -/
def validateAndApply (ext : Bool) (desc : PropDesc) : Option Property → Bool × Option Property
  -- 2.
  | none =>
    -- a.
    if !ext then (false, none)
    -- c.
    else if desc.isAccessor then
      (true, some (.accessor (desc.get.getD .undefined) (desc.set.getD .undefined)
        (desc.enumerable.getD false) (desc.configurable.getD false)))
    -- d.
    else
      (true, some (.data (desc.value.getD .undefined) (desc.writable.getD false)
        (desc.enumerable.getD false) (desc.configurable.getD false)))
  | some cur =>
    -- 4.
    if desc.value.isNone && desc.writable.isNone && desc.get.isNone && desc.set.isNone &&
       desc.enumerable.isNone && desc.configurable.isNone then (true, none) else
    -- 5.
    let curAcc := match cur with | .accessor .. => true | .data .. => false
    let bad : Bool := !cur.configurable && (
      -- a.
      desc.configurable == some true ||
      -- b.
      (match desc.enumerable with | some e => e != cur.enumerable | none => false) ||
      -- c.
      (!desc.isGeneric && desc.isAccessor != curAcc) ||
      -- d.
      (match cur with
       | .accessor g s _ _ =>
         (match desc.get with | some g' => !sameValue g' g | none => false) ||
         (match desc.set with | some s' => !sameValue s' s | none => false)
       -- e.
       | .data v w _ _ => !w && (desc.writable == some true ||
         (match desc.value with | some v' => !sameValue v' v | none => false))))
    if bad then (false, none) else
    -- 6.
    let conf := desc.configurable.getD cur.configurable
    let enum := desc.enumerable.getD cur.enumerable
    let p : Property := match cur with
      | .data v w _ _ =>
        if desc.isAccessor then .accessor (desc.get.getD .undefined) (desc.set.getD .undefined) enum conf
        else .data (desc.value.getD v) (desc.writable.getD w) enum conf
      | .accessor g s _ _ =>
        if desc.isData then .data (desc.value.getD .undefined) (desc.writable.getD false) enum conf
        else .accessor (desc.get.getD g) (desc.set.getD s) enum conf
    (true, some p)

/-- IsCompatiblePropertyDescriptor spec: https://tc39.es/ecma262/#sec-iscompatiblepropertydescriptor -/
def isCompatibleDesc (ext : Bool) (desc : PropDesc) (cur : Option Property) : Bool :=
  (validateAndApply ext desc cur).1

/-- CompletePropertyDescriptor spec: https://tc39.es/ecma262/#sec-completepropertydescriptor -/
def completeDesc (d : PropDesc) : Property :=
  if d.isAccessor then .accessor (d.get.getD .undefined) (d.set.getD .undefined)
    (d.enumerable.getD false) (d.configurable.getD false)
  else .data (d.value.getD .undefined) (d.writable.getD false) (d.enumerable.getD false)
    (d.configurable.getD false)

/-- OrdinaryDefineOwnProperty spec: https://tc39.es/ecma262/#sec-ordinarydefineownproperty -/
def ordinaryDefineOwnProperty (o : ObjId) (k : PropKey) (desc : PropDesc) : M Bool := do
  let (cur, ext) ← readObj o fun ob => (ob.props.get? k, ob.extensible)
  let (ok, p) := validateAndApply ext desc cur
  if let some p := p then setOwn o k p
  pure ok

/-- FromPropertyDescriptor spec: https://tc39.es/ecma262/#sec-frompropertydescriptor -/
def fromPropertyDescriptor (d : PropDesc) : M Value := do
  let o ← newObject
  let put (k : JSStr) (v : Value) : M Unit := setOwn o k (.data v true true true)
  if let some v := d.value then put kValue v
  if let some w := d.writable then put kWritable (.bool w)
  if let some g := d.get then put kGet g
  if let some s := d.set then put kSet s
  if let some e := d.enumerable then put kEnumerable (.bool e)
  if let some c := d.configurable then put kConfigurable (.bool c)
  pure (.obj o)

/-- The keys of an ordinary object in OrdinaryOwnPropertyKeys order: array indices ascending,
then strings, then symbols, each in creation order.
spec: https://tc39.es/ecma262/#sec-ordinaryownpropertykeys -/
def orderedKeys (order : Array PropKey) : Array PropKey :=
  let idx := order.filterMap (fun k => k.arrayIndex?.map (·, k))
  let idx := idx.qsort (fun a b => a.1 < b.1) |>.map (·.2)
  let strs := order.filter fun k => match k with | .str s => s.toArrayIndex?.isNone | .sym _ => false
  let syms := order.filter fun k => match k with | .sym _ => true | _ => false
  idx ++ strs ++ syms

/-- Reads a mapped arguments object's binding. -/
def argMapGet (env : EnvId) (name : JSStr) : M Value := readEnv env fun e => match e with
  | .func b .. | .decl b _ => ((b.get? name).bind (·.value)).getD .undefined
  | _ => .undefined

def argMapSet (env : EnvId) (name : JSStr) (v : Value) : M Unit := modifyEnv env fun e =>
  let upd (b : Std.HashMap JSStr Binding) := b.modify name fun bd => { bd with value := some v }
  match e with
  | .func b o ts tv f nt => .func (upd b) o ts tv f nt
  | .decl b o => .decl (upd b) o
  | e => e

/-- Whether the arguments object `o` maps key `k`, and to which binding. -/
def argMapped (mapped : Option (EnvId × Array (Option JSStr))) (k : PropKey) : Option (EnvId × JSStr) :=
  match mapped, k.arrayIndex? with
  | some (env, names), some i => (names[i]?.bind id).map (env, ·)
  | _, _ => none

def argUnmap (o : ObjId) (k : PropKey) : M Unit := modifyObj o fun ob => ob.withKind fun kd =>
  match kd, k.arrayIndex? with
  | .arguments (some (env, names)), some i => .arguments (some (env, names.set! i none))
  | kd, _ => kd

/-- StringGetOwnProperty spec: https://tc39.es/ecma262/#sec-stringgetownproperty -/
def stringGetOwnProperty (s : JSStr) (k : PropKey) : Option Property :=
  match k with
  | .str ks => match ks.toIndex? with
    | some i => if i < s.length then some (.data (.str (s.slice i (i + 1))) false true false) else none
    | none => none
  | .sym _ => none

/-- A module namespace's export value: the binding its resolution names (the target module's
environment binding, or that module's namespace).
spec: https://tc39.es/ecma262/#sec-module-namespace-exotic-objects-get-p-receiver -/
def moduleNSGet (m : Nat) (name : JSStr) : M (Option Value) := do
  let r ← readS fun s => (s.modules[m]?.map (·.nsBindings)).getD #[]
  match r.find? (·.1 == name) with
  | none => pure none
  | some (_, tm, bn) =>
    let (env, ns) ← readS fun s => match s.modules[tm]? with
      | some mr => (mr.env, mr.ns)
      | none => (none, none)
    match bn with
    | none => match ns with
      | some ns => pure (some (.obj ns))
      | none => M.halt "internal: namespace not created"
    | some bn =>
      let some env := env | throwError .referenceError s!"{bn} is not initialized"
      let v ← readEnv env fun e => match e with
        | .module b _ _ => (b.get? bn).map (·.value)
        | _ => none
      match v with
      | some (some v) => pure (some v)
      | _ => throwError .referenceError s!"Cannot access '{bn}' before initialization"

def kTrapGetPrototypeOf : JSStr := "getPrototypeOf"

/-- The proxy's handler and target, or a TypeError if revoked.
spec: https://tc39.es/ecma262/#sec-validatenonrevokedproxy -/
def proxyParts (o : ObjId) : M (ObjId × ObjId) := do
  match ← objKind o with
  | .proxy (some t) (some h) _ _ => pure (t, h)
  | _ => throwType "Cannot perform operation on a revoked proxy"

def keyToValue : PropKey → Value
  | .str s => .str s
  | .sym id => .sym id

/-- ToObject spec: https://tc39.es/ecma262/#sec-toobject -/
def toObject (v : Value) : M ObjId := do
  match v with
  | .obj o => pure o
  | .undefined | .null => throwType "Cannot convert undefined or null to object"
  | .bool _ => wrap "%Boolean.prototype%" v
  | .num _ => wrap "%Number.prototype%" v
  | .str s => do
    let o ← wrap "%String.prototype%" v
    setOwn o (.str kLength) (.data (.num (Conv.ofNat s.length)) false false false)
    pure o
  | .sym _ => wrap "%Symbol.prototype%" v
  | .bigint _ => wrap "%BigInt.prototype%" v
where
  wrap (proto : String) (v : Value) : M ObjId := do
    let p ← intrinsic proto
    alloc { proto := .obj p, kind := .primitive v }


/-! ## Array buffers and typed arrays: the parts the internal methods need

spec: https://tc39.es/ecma262/#sec-arraybuffer-objects,
https://tc39.es/ecma262/#sec-typedarray-exotic-objects -/

namespace TAKind

/-- The Element Size column of the TypedArray constructors table.
spec: https://tc39.es/ecma262/#table-the-typedarray-constructors -/
def elementSize : TAKind → Nat
  | .int8 | .uint8 | .uint8c => 1
  | .int16 | .uint16 | .float16 => 2
  | .int32 | .uint32 | .float32 => 4
  | .float64 | .bigInt64 | .bigUint64 => 8

/-- IsBigIntElementType (the [[ContentType]] is BigInt).
spec: https://tc39.es/ecma262/#sec-isbigintelementtype -/
def isBigInt : TAKind → Bool
  | .bigInt64 | .bigUint64 => true
  | _ => false

/-- IsUnclampedIntegerElementType spec: https://tc39.es/ecma262/#sec-isunclampedintegerelementtype -/
def isUnclampedInteger : TAKind → Bool
  | .int8 | .uint8 | .int16 | .uint16 | .int32 | .uint32 => true
  | _ => false

/-- The [[TypedArrayName]]. -/
def name : TAKind → String
  | .int8 => "Int8Array" | .uint8 => "Uint8Array" | .uint8c => "Uint8ClampedArray"
  | .int16 => "Int16Array" | .uint16 => "Uint16Array" | .int32 => "Int32Array"
  | .uint32 => "Uint32Array" | .float16 => "Float16Array" | .float32 => "Float32Array"
  | .float64 => "Float64Array" | .bigInt64 => "BigInt64Array" | .bigUint64 => "BigUint64Array"

def all : Array TAKind := #[.int8, .uint8, .uint8c, .int16, .uint16, .int32, .uint32, .float16,
  .float32, .float64, .bigInt64, .bigUint64]

/-- NumericToRawBytes as an unsigned integer of `elementSize` bytes (the value must already be
a Number for Number types, a BigInt for BigInt types).
spec: https://tc39.es/ecma262/#sec-numerictorawbytes -/
def toRaw (k : TAKind) (v : Value) : Nat :=
  match k, v with
  | .float16, .num x => (Num.toFloat16Bits x).toNat
  | .float32, .num x => (Num.toFloat32Bits x).toNat
  | .float64, .num x => (Num.toFloat64Bits x).toNat
  | .uint8c, .num x => Num.toUint8Clamp x
  | .bigInt64, .bigint i | .bigUint64, .bigint i => (Num.BigInt.asUintN 64 i).toNat
  | k, .num x => Num.toUintMod (8 * k.elementSize) x
  | _, _ => 0

/-- RawBytesToNumeric from an unsigned integer of `elementSize` bytes.
spec: https://tc39.es/ecma262/#sec-rawbytestonumeric -/
def ofRaw (k : TAKind) (bits : Nat) : Value :=
  match k with
  | .float16 => .num (Num.ofFloat16Bits bits.toUInt16)
  | .float32 => .num (Num.ofFloat32Bits bits.toUInt32)
  | .float64 => .num (Num.ofFloat64Bits bits.toUInt64)
  | .int8 => .num (F64.ofInt (Num.signedOf 8 bits))
  | .int16 => .num (F64.ofInt (Num.signedOf 16 bits))
  | .int32 => .num (F64.ofInt (Num.signedOf 32 bits))
  | .bigInt64 => .bigint (Num.signedOf 64 bits)
  | .bigUint64 => .bigint bits
  | _ => .num (F64.ofInt bits)

end TAKind

/-- Reads `size` bytes at `idx` as an unsigned integer (little- or big-endian). -/
def bytesGet (d : ByteArray) (idx size : Nat) (little : Bool) : Nat :=
  (List.range size).foldl (fun acc i =>
    let b := (d.get! (idx + (if little then size - 1 - i else i))).toNat
    acc * 256 + b) 0

/-- Writes `bits` as `size` bytes at `idx` (little- or big-endian). -/
def bytesSet (d : ByteArray) (idx size bits : Nat) (little : Bool) : ByteArray :=
  (List.range size).foldl (fun d i =>
    let b := ((bits >>> (8 * i)) % 256).toUInt8
    d.set! (idx + (if little then i else size - 1 - i)) b) d

/-- An array buffer's state: its byte length, whether it is detached, its max byte length
(resizable buffers), whether it is shared. -/
structure BufInfo where
  byteLength : Nat
  detached : Bool
  maxLen : Option Nat
  shared : Bool

/-- The buffer slots of an object, if it is an ArrayBuffer or SharedArrayBuffer. -/
def bufInfo? (b : ObjId) : M (Option BufInfo) := readObj b fun o => match o.kind with
  | .buffer d det ml sh => some { byteLength := d.size, detached := det, maxLen := ml, shared := sh }
  | _ => none

/-- A TypedArray With Buffer Witness Record (with the typed array's slots).
spec: https://tc39.es/ecma262/#sec-typedarray-with-buffer-witness-records -/
structure TARecord where
  obj : ObjId
  kind : TAKind
  buf : ObjId
  byteOffset : Nat
  /-- [[ArrayLength]] (`none`: auto, length-tracking) -/
  arrayLength : Option Nat
  /-- [[CachedBufferByteLength]] (`none`: detached) -/
  bufLen : Option Nat
  deriving Inhabited

namespace TARecord

/-- IsTypedArrayOutOfBounds spec: https://tc39.es/ecma262/#sec-istypedarrayoutofbounds -/
def isOutOfBounds (r : TARecord) : Bool :=
  match r.bufLen with
  -- 2.
  | none => true
  | some bl =>
    -- 3-6.
    let start := r.byteOffset
    let stop := match r.arrayLength with
      | none => bl
      | some l => start + l * r.kind.elementSize
    -- 7.
    start > bl || stop > bl

/-- TypedArrayLength (assumes not out of bounds) spec: https://tc39.es/ecma262/#sec-typedarraylength -/
def length (r : TARecord) : Nat :=
  match r.arrayLength with
  -- 3.
  | some l => l
  -- 4-7.
  | none => match r.bufLen with
    | some bl => (bl - r.byteOffset) / r.kind.elementSize
    | none => 0

/-- TypedArrayByteLength spec: https://tc39.es/ecma262/#sec-typedarraybytelength -/
def byteLength (r : TARecord) : Nat :=
  if r.isOutOfBounds then 0 else r.length * r.kind.elementSize

/-- TypedArrayLength, 0 when out of bounds. -/
def lengthOr0 (r : TARecord) : Nat := if r.isOutOfBounds then 0 else r.length

end TARecord

/-- MakeTypedArrayWithBufferWitnessRecord (`none`: not a typed array).
spec: https://tc39.es/ecma262/#sec-maketypedarraywithbufferwitnessrecord -/
def taRecord? (o : ObjId) : M (Option TARecord) := do
  match ← objKind o with
  | .typedArray k buf off len =>
    let bl ← readObj buf fun b => match b.kind with
      | .buffer d det _ _ => if det then none else some d.size
      | _ => none
    pure (some { obj := o, kind := k, buf, byteOffset := off, arrayLength := len, bufLen := bl })
  | _ => pure none

/-- IsValidIntegerIndex (the index as a Nat when valid).
spec: https://tc39.es/ecma262/#sec-isvalidintegerindex -/
def isValidIntegerIndex (r : TARecord) (index : F64) : Option Nat :=
  -- 1.
  if r.bufLen.isNone then none
  -- 2-3.
  else if !Conv.isIntegral index then none
  else if index.isNeg && index.isZero then none
  else
    -- 4-5.
    if r.isOutOfBounds then none else
    -- 6-7.
    match Conv.truncInt index with
    | some i => if i < 0 || i ≥ r.length then none else some i.toNat
    | none => none

/-- CanonicalNumericIndexString for property keys (`none`: not a numeric string). A canonical
numeric string starts with a digit, `-`, `I` (Infinity) or `N` (NaN): others are skipped fast.
spec: https://tc39.es/ecma262/#sec-canonicalnumericindexstring -/
def canonicalNumericKey? : PropKey → Option F64
  | .sym _ => none
  | .str s =>
    if s.isEmpty then none else
    let c := s.get 0
    if !((0x30 ≤ c && c ≤ 0x39) || c == 0x2D || c == 0x49 || c == 0x4E) then none else
    -- 2.
    if s == JSStr.ofString "-0" then some (.fin true 0 (-1074)) else
    -- 3-4.
    let n := stringToNumber s
    if numberToJSStr n == s then some n else none

/-- GetValueFromBuffer (single-threaded: the ordering is immaterial).
spec: https://tc39.es/ecma262/#sec-getvaluefrombuffer -/
def getValueFromBuffer (buf : ObjId) (byteIndex : Nat) (k : TAKind) (little : Bool := true) : M Value :=
  readObj buf fun o => match o.kind with
    | .buffer d _ _ _ =>
      if byteIndex + k.elementSize ≤ d.size then k.ofRaw (bytesGet d byteIndex k.elementSize little)
      else k.ofRaw 0
    | _ => .undefined

/-- Writes raw bits to a buffer (in place). -/
def writeBufferBits (buf : ObjId) (byteIndex size bits : Nat) (little : Bool := true) : M Unit :=
  modifyObj buf fun o => o.withKind fun kd => match kd with
    | .buffer d det ml sh =>
      if byteIndex + size ≤ d.size then .buffer (bytesSet d byteIndex size bits little) det ml sh
      else .buffer d det ml sh
    | kd => kd

/-- SetValueInBuffer (the value already converted to the element type's Number or BigInt).
spec: https://tc39.es/ecma262/#sec-setvalueinbuffer -/
def setValueInBuffer (buf : ObjId) (byteIndex : Nat) (k : TAKind) (v : Value) (little : Bool := true) : M Unit :=
  writeBufferBits buf byteIndex k.elementSize (k.toRaw v) little

/-- TypedArrayGetElement spec: https://tc39.es/ecma262/#sec-typedarraygetelement -/
def typedArrayGetElement (o : ObjId) (index : F64) : M Value := do
  let some r ← taRecord? o | pure .undefined
  -- 1.
  match isValidIntegerIndex r index with
  | none => pure .undefined
  | some i =>
    -- 2-6.
    getValueFromBuffer r.buf (i * r.kind.elementSize + r.byteOffset) r.kind

/-- IsTypedArrayFixedLength spec: https://tc39.es/ecma262/#sec-istypedarrayfixedlength -/
def isTypedArrayFixedLength (r : TARecord) : M Bool := do
  -- 1.
  if r.arrayLength.isNone then return false
  -- 2-3.
  match ← bufInfo? r.buf with
  | some bi => pure (!(bi.maxLen.isSome && !bi.shared))
  | none => pure true

/-! ## The internal methods -/

mutual

/-- [[GetPrototypeOf]] -/
def getPrototypeOf : Nat → ObjId → M Value
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-getprototypeof
      let (target, handler) ← proxyParts o
      let trap ← getMethod n (.obj handler) (.str "getPrototypeOf")
      match trap with
      | none => getPrototypeOf n target
      | some trap =>
        let proto ← call trap (.obj handler) #[.obj target]
        match proto with
        | .obj _ | .null => pure ()
        | _ => throwType "getPrototypeOf trap returned neither object nor null"
        if ← isExtensible n target then return proto
        let targetProto ← getPrototypeOf n target
        if !sameValue proto targetProto then
          throwType "getPrototypeOf trap result differs from the non-extensible target's prototype"
        pure proto
    | _ => objProto o

/-- [[SetPrototypeOf]] -/
def setPrototypeOf : Nat → ObjId → Value → M Bool
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, v => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-setprototypeof-v
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "setPrototypeOf") with
      | none => setPrototypeOf n target v
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target, v])
        if !r then return false
        if ← isExtensible n target then return true
        let targetProto ← getPrototypeOf n target
        if !sameValue v targetProto then
          throwType "setPrototypeOf trap returned true for a non-extensible target with another prototype"
        pure true
    | _ =>
      -- spec: https://tc39.es/ecma262/#sec-ordinarysetprototypeof
      let (current, ext, immut) ← readObj o fun ob => (ob.proto, ob.extensible, ob.immutableProto)
      -- (immutable prototype exotic objects: SetImmutablePrototype)
      if immut then return sameValue v current
      -- 3.
      if sameValue v current then return true
      -- 4.
      if !ext then return false
      -- 5-8. (cycle check: stop at a proxy)
      let cyc ← M.repeatFrom v fun p => match p with
        | .obj pid => do
          if pid == o then return .inr true
          match ← objKind pid with
          | .proxy .. => return .inr false
          | _ => return .inl (← objProto pid)
        | _ => return .inr false
      if cyc then return false
      -- 9.
      modifyObj o fun ob => { ob with proto := v }
      pure true

/-- [[IsExtensible]] -/
def isExtensible : Nat → ObjId → M Bool
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    match ← objKind o with
    | .proxy .. => do
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "isExtensible") with
      | none => isExtensible n target
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target])
        let t ← isExtensible n target
        if r != t then throwType "isExtensible trap result does not reflect the target's extensibility"
        pure r
    | _ => readObj o (·.extensible)

/-- [[PreventExtensions]] -/
def preventExtensions : Nat → ObjId → M Bool
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    match ← objKind o with
    | .proxy .. => do
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "preventExtensions") with
      | none => preventExtensions n target
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target])
        if r && (← isExtensible n target) then
          throwType "preventExtensions trap returned true but the target is extensible"
        pure r
    | .typedArray .. => do
      -- spec: https://tc39.es/ecma262/#sec-typedarray-preventextensions
      -- 2.
      let some r ← taRecord? o | pure false
      if !(← isTypedArrayFixedLength r) then return false
      -- 3.
      modifyObj o fun ob => { ob with extensible := false }
      pure true
    | _ =>
      modifyObj o fun ob => { ob with extensible := false }
      pure true

/-- [[GetOwnProperty]] -/
def getOwnProperty : Nat → ObjId → PropKey → M (Option Property)
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k => do
    match ← objKind o with
    | .primitive (.str s) =>
      -- spec: https://tc39.es/ecma262/#sec-string-exotic-objects-getownproperty-p
      match ← ownProp o k with
      | some p => pure (some p)
      | none => pure (stringGetOwnProperty s k)
    | .arguments mapped =>
      -- spec: https://tc39.es/ecma262/#sec-arguments-exotic-objects-getownproperty-p
      match ← ownProp o k with
      | none => pure none
      | some p => match argMapped mapped k, p with
        | some (env, name), .data _ w e c => pure (some (.data (← argMapGet env name) w e c))
        | _, p => pure (some p)
    | .proxy .. => proxyGetOwnProperty n o k
    | .moduleNS m exports =>
      -- spec: https://tc39.es/ecma262/#sec-module-namespace-exotic-objects-getownproperty-p
      match k with
      | .sym _ => ownProp o k
      | .str ks =>
        if !exports.contains ks then pure none
        else match ← moduleNSGet m ks with
          | some v => pure (some (.data v true true false))
          | none => pure none
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-getownproperty
      match canonicalNumericKey? k with
      | some idx =>
        let v ← typedArrayGetElement o idx
        if v.isUndefined then pure none else pure (some (.data v true true true))
      | none => ownProp o k
    | _ => ownProp o k

/-- [[GetOwnProperty]] of a proxy.
spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-getownproperty-p -/
def proxyGetOwnProperty : Nat → ObjId → PropKey → M (Option Property)
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k => do
    let (target, handler) ← proxyParts o
    match ← getMethod n (.obj handler) (.str "getOwnPropertyDescriptor") with
    | none => getOwnProperty n target k
    | some trap =>
      -- 8.
      let r ← call trap (.obj handler) #[.obj target, keyToValue k]
      -- 9.
      if !r.isObject && !r.isUndefined then
        throwType "getOwnPropertyDescriptor trap returned neither object nor undefined"
      -- 10.
      let targetDesc ← getOwnProperty n target k
      -- 11.
      if r.isUndefined then
        match targetDesc with
        | none => return none
        | some td =>
          if !td.configurable then throwType "getOwnPropertyDescriptor trap hid a non-configurable property"
          if !(← isExtensible n target) then throwType "getOwnPropertyDescriptor trap hid a property of a non-extensible target"
          return none
      -- 12-14.
      let ext ← isExtensible n target
      let rd ← toPropertyDescriptor n r
      let result := completeDesc rd
      -- 15.
      if !isCompatibleDesc ext (PropDesc.ofProp result) targetDesc then
        throwType "getOwnPropertyDescriptor trap returned an incompatible descriptor"
      -- 16.
      if !result.configurable then
        match targetDesc with
        | none => throwType "getOwnPropertyDescriptor trap reported a non-configurable property the target lacks"
        | some td =>
          if td.configurable then throwType "getOwnPropertyDescriptor trap reported non-configurable for a configurable property"
          -- c.
          match rd.writable, td with
          | some false, .data _ true _ _ => throwType "getOwnPropertyDescriptor trap reported non-writable for a writable property"
          | _, _ => pure ()
      pure (some result)

/-- [[DefineOwnProperty]] -/
def defineOwnProperty : Nat → ObjId → PropKey → PropDesc → M Bool
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, desc => do
    match ← objKind o with
    | .array =>
      -- spec: https://tc39.es/ecma262/#sec-array-exotic-objects-defineownproperty-p-desc
      if k == .str kLength then arraySetLength n o desc
      else match k.arrayIndex? with
        | some index => do
          let lenProp ← ownProp o (.str kLength)
          let (length, lenWritable) := match lenProp with
            | some (.data (.num l) w _ _) => ((Conv.toNat? l).getD 0, w)
            | _ => (0, true)
          if index ≥ length && !lenWritable then return false
          if !(← ordinaryDefineOwnProperty o k desc) then return false
          if index ≥ length then
            setOwn o (.str kLength) (.data (.num (Conv.ofNat (index + 1))) lenWritable false false)
          pure true
        | none => ordinaryDefineOwnProperty o k desc
    | .primitive (.str s) =>
      -- spec: https://tc39.es/ecma262/#sec-string-exotic-objects-defineownproperty-p-desc
      match stringGetOwnProperty s k with
      | some sd => do
        let ext ← readObj o (·.extensible)
        pure (isCompatibleDesc ext desc (some sd))
      | none => ordinaryDefineOwnProperty o k desc
    | .arguments mapped =>
      -- spec: https://tc39.es/ecma262/#sec-arguments-exotic-objects-defineownproperty-p-desc
      let m := argMapped mapped k
      let newDesc ← match m with
        | some (env, name) =>
          if desc.isData && desc.value.isNone && desc.writable == some false then
            pure { desc with value := some (← argMapGet env name) }
          else pure desc
        | none => pure desc
      if !(← ordinaryDefineOwnProperty o k newDesc) then return false
      if let some (env, name) := m then
        if desc.isAccessor then argUnmap o k
        else
          if let some v := desc.value then argMapSet env name v
          if desc.writable == some false then argUnmap o k
      pure true
    | .proxy .. => proxyDefineOwnProperty n o k desc
    | .moduleNS m exports =>
      -- spec: https://tc39.es/ecma262/#sec-module-namespace-exotic-objects-defineownproperty-p-desc
      match k with
      | .sym _ => ordinaryDefineOwnProperty o k desc
      | .str ks =>
        if !exports.contains ks then return false
        let some v ← moduleNSGet m ks | return false
        if desc.configurable == some true || desc.enumerable == some false || desc.isAccessor ||
           desc.writable == some false then return false
        match desc.value with
        | some dv => pure (sameValue dv v)
        | none => pure true
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-defineownproperty
      match canonicalNumericKey? k with
      | some idx =>
        let some r ← taRecord? o | return false
        -- i.
        if (isValidIntegerIndex r idx).isNone then return false
        -- ii-v.
        if desc.configurable == some false then return false
        if desc.enumerable == some false then return false
        if desc.isAccessor then return false
        if desc.writable == some false then return false
        -- vi.
        if let some v := desc.value then typedArraySetElementD n o idx v
        pure true
      | none => ordinaryDefineOwnProperty o k desc
    | _ => ordinaryDefineOwnProperty o k desc

/-- [[DefineOwnProperty]] of a proxy.
spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-defineownproperty-p-desc -/
def proxyDefineOwnProperty : Nat → ObjId → PropKey → PropDesc → M Bool
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, desc => do
    let (target, handler) ← proxyParts o
    match ← getMethod n (.obj handler) (.str "defineProperty") with
    | none => defineOwnProperty n target k desc
    | some trap =>
      let descObj ← fromPropertyDescriptor desc
      let r := toBoolean (← call trap (.obj handler) #[.obj target, keyToValue k, descObj])
      if !r then return false
      let targetDesc ← getOwnProperty n target k
      let ext ← isExtensible n target
      let settingConfigFalse := desc.configurable == some false
      match targetDesc with
      | none =>
        if !ext then throwType "defineProperty trap added a property to a non-extensible target"
        if settingConfigFalse then throwType "defineProperty trap defined a non-configurable property the target lacks"
      | some td =>
        if !isCompatibleDesc ext desc (some td) then throwType "defineProperty trap result is incompatible with the target's property"
        if settingConfigFalse && td.configurable then throwType "defineProperty trap: non-configurable for a configurable target property"
        match td with
        | .data _ true _ false =>
          if desc.writable == some false then throwType "defineProperty trap: non-writable for a writable non-configurable property"
        | _ => pure ()
      pure true

/-- ArraySetLength spec: https://tc39.es/ecma262/#sec-arraysetlength -/
def arraySetLength : Nat → ObjId → PropDesc → M Bool
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, a, desc => do
    -- 1.
    let some v := desc.value | ordinaryDefineOwnProperty a (.str kLength) desc
    -- 3-4.
    let newLenN ← toNumber n v
    let numberLen ← toNumber n v
    let newLen := Conv.toUint32 newLenN
    -- 5.
    if !(Conv.toNat? numberLen == some newLen) then throwRange "Invalid array length"
    -- 6.
    let newLenDesc := { desc with value := some (.num (Conv.ofNat newLen)) }
    -- 7-9.
    let (oldLen, oldWritable) ← readObj a fun ob => match ob.props.get? (.str kLength) with
      | some (.data (.num l) w _ _) => ((Conv.toNat? l).getD 0, w)
      | _ => (0, true)
    -- 10.
    if newLen ≥ oldLen then return ← ordinaryDefineOwnProperty a (.str kLength) newLenDesc
    -- 11.
    if !oldWritable then return false
    -- 12-13.
    let newWritable := newLenDesc.writable != some false
    let newLenDesc := if newWritable then newLenDesc else { newLenDesc with writable := some true }
    -- 14-15.
    if !(← ordinaryDefineOwnProperty a (.str kLength) newLenDesc) then return false
    -- 16.
    let keys ← readObj a fun ob => ob.props.keys.filterMap fun k =>
      match k.arrayIndex? with | some i => if i ≥ newLen then some i else none | none => none
    let keys := keys.qsort (· > ·)
    let failed ← M.foldArr keys none fun acc i => do
      if acc.isSome then return acc
      let k := PropKey.ofNat i
      let configurable ← readObj a fun ob => (ob.props.get? k).map (·.configurable)
      match configurable with
      | some false => return some i
      | _ => modifyObj a (·.withProps (·.erase k)); return none
    if let some i := failed then
      let d := { newLenDesc with value := some (.num (Conv.ofNat (i + 1))) }
      let d := if newWritable then d else { d with writable := some false }
      let _ ← ordinaryDefineOwnProperty a (.str kLength) d
      return false
    -- 17.
    if !newWritable then
      let _ ← ordinaryDefineOwnProperty a (.str kLength) { writable := some false }
    pure true

/-- [[HasProperty]] -/
def hasProperty : Nat → ObjId → PropKey → M Bool
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-hasproperty-p
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "has") with
      | none => hasProperty n target k
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target, keyToValue k])
        if !r then
          if let some td ← getOwnProperty n target k then
            if !td.configurable then throwType "has trap hid a non-configurable property"
            if !(← isExtensible n target) then throwType "has trap hid a property of a non-extensible target"
        pure r
    | .moduleNS _ exports => match k with
      | .str ks => pure (exports.contains ks)
      | .sym _ => pure (← ownProp o k).isSome
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-hasproperty
      match canonicalNumericKey? k with
      | some idx =>
        let some r ← taRecord? o | return false
        pure (isValidIntegerIndex r idx).isSome
      | none =>
        if (← ownProp o k).isSome then return true
        match ← getPrototypeOf n o with
        | .obj p => hasProperty n p k
        | _ => pure false
    | _ =>
      -- spec: https://tc39.es/ecma262/#sec-ordinaryhasproperty
      if (← getOwnProperty n o k).isSome then return true
      match ← getPrototypeOf n o with
      | .obj p => hasProperty n p k
      | _ => pure false

/-- [[Get]] -/
def get : Nat → ObjId → PropKey → Value → M Value
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, receiver => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-get-p-receiver
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "get") with
      | none => get n target k receiver
      | some trap =>
        let v ← call trap (.obj handler) #[.obj target, keyToValue k, receiver]
        if let some td ← getOwnProperty n target k then
          if !td.configurable then
            match td with
            | .data tv false _ _ =>
              if !sameValue v tv then throwType "get trap result differs from a non-writable, non-configurable property"
            | .accessor .undefined _ _ _ =>
              if !v.isUndefined then throwType "get trap returned a value for an accessor without a getter"
            | _ => pure ()
        pure v
    | .arguments mapped =>
      -- spec: https://tc39.es/ecma262/#sec-arguments-exotic-objects-get-p-receiver
      match argMapped mapped k with
      | some (env, name) => if (← ownProp o k).isSome then argMapGet env name else ordinaryGet n o k receiver
      | none => ordinaryGet n o k receiver
    | .moduleNS m exports => match k with
      | .sym _ => ordinaryGet n o k receiver
      | .str ks => if exports.contains ks then pure ((← moduleNSGet m ks).getD .undefined) else pure .undefined
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-get
      match canonicalNumericKey? k with
      | some idx => typedArrayGetElement o idx
      | none => ordinaryGet n o k receiver
    | _ => ordinaryGet n o k receiver

/-- OrdinaryGet spec: https://tc39.es/ecma262/#sec-ordinaryget -/
def ordinaryGet : Nat → ObjId → PropKey → Value → M Value
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, receiver => do
    -- 1.
    match ← getOwnProperty n o k with
    -- 2.
    | none => match ← getPrototypeOf n o with
      | .obj p => get n p k receiver
      | _ => pure .undefined
    -- 3.
    | some (.data v ..) => pure v
    -- 4-6.
    | some (.accessor g _ _ _) => if g.isUndefined then pure .undefined else call g receiver #[]

/-- [[Set]] -/
def set : Nat → ObjId → PropKey → Value → Value → M Bool
  | 0, _, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, v, receiver => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-set-p-v-receiver
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "set") with
      | none => set n target k v receiver
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target, keyToValue k, v, receiver])
        if !r then return false
        if let some td ← getOwnProperty n target k then
          if !td.configurable then
            match td with
            | .data tv false _ _ =>
              if !sameValue v tv then throwType "set trap changed a non-writable, non-configurable property"
            | .accessor _ .undefined _ _ => throwType "set trap succeeded for an accessor without a setter"
            | _ => pure ()
        pure true
    | .arguments mapped =>
      -- spec: https://tc39.es/ecma262/#sec-arguments-exotic-objects-set-p-v-receiver
      let isMapped := match receiver with
        | .obj r => r == o && (argMapped mapped k).isSome
        | _ => false
      if isMapped then
        if (← ownProp o k).isSome then
          if let some (env, name) := argMapped mapped k then argMapSet env name v
      ordinarySet n o k v receiver
    | .moduleNS .. => pure false
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-set
      match canonicalNumericKey? k with
      | some idx =>
        -- i.
        if sameValue receiver (.obj o) then
          typedArraySetElementD n o idx v
          return true
        -- ii.
        let some r ← taRecord? o | return true
        if (isValidIntegerIndex r idx).isNone then return true
        ordinarySet n o k v receiver
      | none => ordinarySet n o k v receiver
    | _ => ordinarySet n o k v receiver

/-- OrdinarySet and OrdinarySetWithOwnDescriptor
spec: https://tc39.es/ecma262/#sec-ordinarysetwithowndescriptor -/
def ordinarySet : Nat → ObjId → PropKey → Value → Value → M Bool
  | 0, _, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k, v, receiver => do
    let ownDesc ← getOwnProperty n o k
    -- 1.
    let ownDesc ← match ownDesc with
      | some d => pure d
      | none => match ← getPrototypeOf n o with
        | .obj p => return ← set n p k v receiver
        | _ => pure (.data .undefined true true true)
    match ownDesc with
    -- 2.
    | .data _ w _ _ =>
      if !w then return false
      let .obj r := receiver | return false
      match ← getOwnProperty n r k with
      | some (.accessor ..) => pure false
      | some (.data _ false _ _) => pure false
      | some (.data ..) => defineOwnProperty n r k { value := some v }
      | none => defineOwnProperty n r k (PropDesc.data v)
    -- 3-7.
    | .accessor _ setter _ _ =>
      if setter.isUndefined then return false
      let _ ← call setter receiver #[v]
      pure true

/-- [[Delete]] -/
def delete : Nat → ObjId → PropKey → M Bool
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k => do
    match ← objKind o with
    | .proxy .. => do
      -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-delete-p
      let (target, handler) ← proxyParts o
      match ← getMethod n (.obj handler) (.str "deleteProperty") with
      | none => delete n target k
      | some trap =>
        let r := toBoolean (← call trap (.obj handler) #[.obj target, keyToValue k])
        if !r then return false
        match ← getOwnProperty n target k with
        | none => pure true
        | some td =>
          if !td.configurable then throwType "deleteProperty trap deleted a non-configurable property"
          if !(← isExtensible n target) then throwType "deleteProperty trap deleted a property of a non-extensible target"
          pure true
    | .arguments mapped =>
      let r ← ordinaryDelete n o k
      if r && (argMapped mapped k).isSome then argUnmap o k
      pure r
    | .moduleNS _ exports => match k with
      | .sym _ => ordinaryDelete n o k
      | .str ks => pure !(exports.contains ks)
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-delete
      match canonicalNumericKey? k with
      | some idx =>
        let some r ← taRecord? o | return true
        pure (isValidIntegerIndex r idx).isNone
      | none => ordinaryDelete n o k
    | _ => ordinaryDelete n o k

/-- OrdinaryDelete spec: https://tc39.es/ecma262/#sec-ordinarydelete -/
def ordinaryDelete : Nat → ObjId → PropKey → M Bool
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, k => do
    match ← getOwnProperty n o k with
    | none => pure true
    | some p =>
      if p.configurable then modifyObj o (·.withProps (·.erase k)); pure true
      else pure false

/-- [[OwnPropertyKeys]] -/
def ownPropertyKeys : Nat → ObjId → M (Array PropKey)
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    match ← objKind o with
    | .primitive (.str s) =>
      -- spec: https://tc39.es/ecma262/#sec-string-exotic-objects-ownpropertykeys
      let own ← readObj o (orderedKeys ·.props.keys)
      let idx := (Array.range s.length).map PropKey.ofNat
      let rest := own.filter fun k => match k.arrayIndex? with | some i => i ≥ s.length | none => true
      pure (idx ++ rest)
    | .proxy .. => proxyOwnKeys n o
    | .moduleNS _ exports => do
      let syms ← readObj o fun ob => ob.props.keys.filter fun k => match k with | .sym _ => true | _ => false
      pure (exports.map PropKey.str ++ syms)
    | .typedArray .. =>
      -- spec: https://tc39.es/ecma262/#sec-typedarray-ownpropertykeys
      let some r ← taRecord? o | return #[]
      -- 3.
      let idx := if r.isOutOfBounds then #[] else (Array.range r.length).map PropKey.ofNat
      -- 4-5.
      let own ← readObj o (orderedKeys ·.props.keys)
      pure (idx ++ own)
    | _ => readObj o (orderedKeys ·.props.keys)

/-- [[OwnPropertyKeys]] of a proxy.
spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-ownpropertykeys -/
def proxyOwnKeys : Nat → ObjId → M (Array PropKey)
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    let (target, handler) ← proxyParts o
    match ← getMethod n (.obj handler) (.str "ownKeys") with
    | none => ownPropertyKeys n target
    | some trap =>
      -- 7-8.
      let arr ← call trap (.obj handler) #[.obj target]
      let elems ← createListFromArrayLike n arr true
      let keys : Array PropKey := elems.filterMap fun v => match v with
        | .str s => some (.str s) | .sym i => some (.sym i) | _ => none
      -- 9.
      let dup := (keys.foldl (fun (acc : Std.HashSet PropKey × Bool) k =>
        (acc.1.insert k, acc.2 || acc.1.contains k)) ({}, false)).2
      if dup then throwType "ownKeys trap result contains duplicate entries"
      -- 10-16.
      let ext ← isExtensible n target
      let targetKeys ← ownPropertyKeys n target
      let (cfg, noncfg) ← M.foldArr targetKeys (#[], #[]) fun (c, nc) k => do
        match ← getOwnProperty n target k with
        | some p => if p.configurable then pure (c.push k, nc) else pure (c, nc.push k)
        | none => pure (c.push k, nc)
      -- 17.
      if ext && noncfg.isEmpty then return keys
      -- 18-20.
      let unchecked := keys
      let unchecked ← M.foldArr noncfg unchecked fun u k => do
        if !u.contains k then throwType "ownKeys trap result omits a non-configurable key"
        pure (u.filter (· != k))
      -- 21.
      if ext then return keys
      -- 22.
      let unchecked ← M.foldArr cfg unchecked fun u k => do
        if !u.contains k then throwType "ownKeys trap result omits a key of a non-extensible target"
        pure (u.filter (· != k))
      -- 23.
      if !unchecked.isEmpty then throwType "ownKeys trap result adds keys to a non-extensible target"
      pure keys

/-- TypedArraySetElement spec: https://tc39.es/ecma262/#sec-typedarraysetelement -/
def typedArraySetElementD : Nat → ObjId → F64 → Value → M Unit
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, index, v => do
    let some r ← taRecord? o | pure ()
    -- 1-2.
    let numValue ← if r.kind.isBigInt then Value.bigint <$> toBigIntD n v else Value.num <$> toNumber n v
    -- 3. (the buffer may have changed during the conversion)
    let some r ← taRecord? o | pure ()
    match isValidIntegerIndex r index with
    | some i => setValueInBuffer r.buf (i * r.kind.elementSize + r.byteOffset) r.kind numValue
    | none => pure ()

/-- ToBigInt spec: https://tc39.es/ecma262/#sec-tobigint -/
def toBigIntD : Nat → Value → M Int
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v => do
    -- 1.
    let prim ← toPrimitive n v (some true)
    -- 2.
    match prim with
    | .undefined | .null => throwType "Cannot convert undefined or null to a BigInt"
    | .bool b => pure (if b then 1 else 0)
    | .bigint i => pure i
    | .num _ => throwType "Cannot convert a Number to a BigInt"
    | .str s => match Num.BigInt.stringToBigInt s with
      | some i => pure i
      | none => throwError .syntaxError "Cannot convert string to a BigInt"
    | .sym _ => throwType "Cannot convert a Symbol value to a BigInt"
    | .obj _ => throwType "Cannot convert object to a BigInt"

-- Operations the internal methods use

/-- GetMethod(V, P) spec: https://tc39.es/ecma262/#sec-getmethod -/
def getMethod : Nat → Value → PropKey → M (Option Value)
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v, k => do
    let f ← getV n v k
    if f.isNullish then return none
    if !(← isCallable f) then throwType "property is not a function"
    pure (some f)

/-- GetV(V, P) spec: https://tc39.es/ecma262/#sec-getv -/
def getV : Nat → Value → PropKey → M Value
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v, k => do
    match v with
    | .obj o => get n o k v
    | .undefined | .null => throwType "Cannot read properties of null or undefined"
    | _ =>
      let o ← toObject v
      get n o k v

/-- ToPropertyDescriptor spec: https://tc39.es/ecma262/#sec-topropertydescriptor -/
def toPropertyDescriptor : Nat → Value → M PropDesc
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v => do
    -- 1.
    let .obj o := v | throwType "Property description must be an object"
    let field (name : JSStr) : M (Option Value) := do
      if ← hasProperty n o (.str name) then pure (some (← get n o (.str name) v)) else pure none
    -- 3-14.
    let enumerable := (← field kEnumerable).map toBoolean
    let configurable := (← field kConfigurable).map toBoolean
    let value ← field kValue
    let writable := (← field kWritable).map toBoolean
    let getter ← field kGet
    if let some g := getter then
      if !g.isUndefined && !(← isCallable g) then throwType "Getter must be a function"
    let setter ← field kSet
    if let some s := setter then
      if !s.isUndefined && !(← isCallable s) then throwType "Setter must be a function"
    -- 15.
    if (getter.isSome || setter.isSome) && (value.isSome || writable.isSome) then
      throwType "Invalid property descriptor. Cannot both specify accessors and a value or writable attribute"
    pure { value, writable, get := getter, set := setter, enumerable, configurable }

/-- CreateListFromArrayLike (`keysOnly`: elements must be Strings or Symbols)
spec: https://tc39.es/ecma262/#sec-createlistfromarraylike -/
def createListFromArrayLike : Nat → Value → Bool → M (Array Value)
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v, keysOnly => do
    let .obj o := v | throwType "CreateListFromArrayLike called on non-object"
    let len ← lengthOfArrayLike n o
    M.foldArr (Array.range len) (Array.mkEmpty len) fun acc i => do
      let e ← get n o (PropKey.ofNat i) v
      if keysOnly then match e with
        | .str _ | .sym _ => pure ()
        | _ => throwType "ownKeys trap result elements must be strings or symbols"
      pure (acc.push e)

/-- LengthOfArrayLike spec: https://tc39.es/ecma262/#sec-lengthofarraylike -/
def lengthOfArrayLike : Nat → ObjId → M Nat
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o => do
    let v ← get n o (.str kLength) (.obj o)
    toLength n v

/-- ToLength spec: https://tc39.es/ecma262/#sec-tolength -/
def toLength : Nat → Value → M Nat
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v => do
    let x ← toNumber n v
    pure <| match Conv.toIntegerOrInf x with
      | .inl true => 0
      | .inl false => 9007199254740991
      | .inr i => if i ≤ 0 then 0 else min i.toNat 9007199254740991

/-- ToPrimitive (`hint`: none = default, some true = number, some false = string)
spec: https://tc39.es/ecma262/#sec-toprimitive -/
def toPrimitive : Nat → Value → Option Bool → M Value
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v, hint => do
    let .obj o := v | pure v
    -- a-b.
    match ← getMethod n v (.sym WK.toPrimitive) with
    | some exotic =>
      let h : JSStr := match hint with | none => "default" | some true => "number" | some false => "string"
      let r ← call exotic v #[.str h]
      if r.isObject then throwType "Cannot convert object to primitive value"
      pure r
    | none => ordinaryToPrimitive n o (hint.getD true)

/-- OrdinaryToPrimitive spec: https://tc39.es/ecma262/#sec-ordinarytoprimitive -/
def ordinaryToPrimitive : Nat → ObjId → Bool → M Value
  | 0, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, o, numberHint => do
    let names := if numberHint then #[kValueOf, kToString] else #[kToString, kValueOf]
    let r ← M.foldArr names none fun acc name => do
      if acc.isSome then return acc
      let m ← get n o (.str name) (.obj o)
      if ← isCallable m then
        let r ← call m (.obj o) #[]
        if !r.isObject then return some r
      pure none
    match r with
    | some r => pure r
    | none => throwType "Cannot convert object to primitive value"

/-- ToNumber spec: https://tc39.es/ecma262/#sec-tonumber -/
def toNumber : Nat → Value → M F64
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v => do
    match v with
    | .num x => pure x
    | .undefined => pure .nan
    | .null => pure F64.zero
    | .bool b => pure (if b then F64.one else F64.zero)
    | .str s => pure (stringToNumber s)
    | .sym _ => throwType "Cannot convert a Symbol value to a number"
    | .bigint _ => throwType "Cannot convert a BigInt value to a number"
    | .obj _ => do
      let p ← toPrimitive n v (some true)
      toNumber n p

/-- ToString spec: https://tc39.es/ecma262/#sec-tostring -/
def toJSString : Nat → Value → M JSStr
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, v => do
    match v with
    | .str s => pure s
    | .undefined => pure "undefined"
    | .null => pure "null"
    | .bool b => pure (if b then "true" else "false")
    | .num x => pure (numberToJSStr x)
    | .bigint i => pure (JSStr.ofString (toString i))
    | .sym _ => throwType "Cannot convert a Symbol value to a string"
    | .obj _ => do
      let p ← toPrimitive n v (some false)
      toJSString n p

end

/-! ## Entry points (with the full depth) -/

namespace Obj'
def getPrototypeOf (o : ObjId) : M Value := ES.getPrototypeOf maxDepth o
def setPrototypeOf (o : ObjId) (v : Value) : M Bool := ES.setPrototypeOf maxDepth o v
def isExtensible (o : ObjId) : M Bool := ES.isExtensible maxDepth o
def preventExtensions (o : ObjId) : M Bool := ES.preventExtensions maxDepth o
def getOwnProperty (o : ObjId) (k : PropKey) : M (Option Property) := ES.getOwnProperty maxDepth o k
def defineOwnProperty (o : ObjId) (k : PropKey) (d : PropDesc) : M Bool := ES.defineOwnProperty maxDepth o k d
def hasProperty (o : ObjId) (k : PropKey) : M Bool := ES.hasProperty maxDepth o k
def get (o : ObjId) (k : PropKey) (receiver : Value) : M Value := ES.get maxDepth o k receiver
def set (o : ObjId) (k : PropKey) (v : Value) (receiver : Value) : M Bool := ES.set maxDepth o k v receiver
def delete (o : ObjId) (k : PropKey) : M Bool := ES.delete maxDepth o k
def ownPropertyKeys (o : ObjId) : M (Array PropKey) := ES.ownPropertyKeys maxDepth o
end Obj'

/-- TypedArraySetElement spec: https://tc39.es/ecma262/#sec-typedarraysetelement -/
def typedArraySetElement (o : ObjId) (index : F64) (v : Value) : M Unit :=
  ES.typedArraySetElementD maxDepth o index v

/-- ToBigInt spec: https://tc39.es/ecma262/#sec-tobigint -/
def toBigInt (v : Value) : M Int := ES.toBigIntD maxDepth v

end ES
