import ES.Realm

/-!
# Fundamental objects and the core of the standard library

spec: https://tc39.es/ecma262/#sec-fundamental-objects (Object, Function, Boolean, Symbol,
Error), https://tc39.es/ecma262/#sec-iteration (iterator prototypes),
https://tc39.es/ecma262/#sec-generator-objects, https://tc39.es/ecma262/#sec-reflection
(Reflect, Proxy), and the parts of Promise, Array, String, Number and Math the rest builds on.
-/

namespace ES

open ES (F64)

/-! ## Object -/

/-- Object(value) spec: https://tc39.es/ecma262/#sec-object-value -/
def objectCtor : BuiltinFn := fun self _ args nt => do
  -- 1.
  if !nt.isUndefined && !sameValue nt (.obj self) then
    return .obj (← ordinaryCreateFromConstructor nt "%Object.prototype%")
  let v := arg args 0
  -- 2.
  if v.isNullish then return .obj (← newObject)
  -- 3.
  pure (.obj (← toObject v))

def toObj (v : Value) : M ObjId := toObject v

/-- Object.assign spec: https://tc39.es/ecma262/#sec-object.assign -/
def objectAssign : BuiltinFn := fun _ _ args _ => do
  let to ← toObj (arg args 0)
  M.forArr (args.extract 1 args.size) fun src => do
    if src.isNullish then return
    let from_ ← toObj src
    let keys ← Obj'.ownPropertyKeys from_
    M.forArr keys fun k => do
      match ← Obj'.getOwnProperty from_ k with
      | some p => if p.enumerable then setProp to k (← getProp from_ k)
      | none => pure ()
  pure (.obj to)

/-- ObjectDefineProperties spec: https://tc39.es/ecma262/#sec-objectdefineproperties -/
def objectDefineProperties (o : ObjId) (props : Value) : M Unit := do
  let p ← toObj props
  let keys ← Obj'.ownPropertyKeys p
  let descs ← M.foldArr keys #[] fun acc k => do
    match ← Obj'.getOwnProperty p k with
    | some pr =>
      if pr.enumerable then
        let dobj ← getProp p k
        pure (acc.push (k, ← toPropertyDescriptor maxDepth dobj))
      else pure acc
    | none => pure acc
  M.forArr descs fun (k, d) => definePropertyOrThrow o k d

def objectCreate : BuiltinFn := fun _ _ args _ => do
  let proto := arg args 0
  match proto with
  | .obj _ | .null => pure ()
  | _ => throwType "Object prototype may only be an Object or null"
  let o ← ordinaryObjectCreate proto
  if !(arg args 1).isUndefined then objectDefineProperties o (arg args 1)
  pure (.obj o)

def objectDefineProperty : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | throwType "Object.defineProperty called on non-object"
  let k ← toPropertyKey (arg args 1)
  let d ← toPropertyDescriptor maxDepth (arg args 2)
  definePropertyOrThrow o k d
  pure (.obj o)

def objectDefinePropertiesFn : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | throwType "Object.defineProperties called on non-object"
  objectDefineProperties o (arg args 1)
  pure (.obj o)

def objectEntriesLike (kind : Nat) : BuiltinFn := fun _ _ args _ => do
  let o ← toObj (arg args 0)
  createArrayFromList (← enumerableOwnProperties o kind)

def objectFreezeSeal (frozen : Bool) : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return arg args 0
  if !(← setIntegrityLevel o frozen) then throwType "Cannot freeze/seal object"
  pure (.obj o)

def objectIsFrozenSealed (frozen : Bool) : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return .bool true
  pure (.bool (← testIntegrityLevel o frozen))

def objectGetOwnPropertyDescriptor : BuiltinFn := fun _ _ args _ => do
  let o ← toObj (arg args 0)
  let k ← toPropertyKey (arg args 1)
  match ← Obj'.getOwnProperty o k with
  | some p => fromPropertyDescriptor (PropDesc.ofProp p)
  | none => pure .undefined

def objectGetOwnPropertyDescriptors : BuiltinFn := fun _ _ args _ => do
  let o ← toObj (arg args 0)
  let keys ← Obj'.ownPropertyKeys o
  let r ← newObject
  M.forArr keys fun k => do
    if let some p ← Obj'.getOwnProperty o k then
      let d ← fromPropertyDescriptor (PropDesc.ofProp p)
      let _ ← createDataProperty r k d
  pure (.obj r)

/-- GetOwnPropertyKeys spec: https://tc39.es/ecma262/#sec-getownpropertykeys -/
def getOwnPropertyKeys (v : Value) (symbols : Bool) : M Value := do
  let o ← toObj v
  let keys ← Obj'.ownPropertyKeys o
  createArrayFromList (keys.filterMap fun k => match k, symbols with
    | .str s, false => some (.str s)
    | .sym i, true => some (.sym i)
    | _, _ => none)

def objectGetPrototypeOf : BuiltinFn := fun _ _ args _ => do
  Obj'.getPrototypeOf (← toObj (arg args 0))

def objectSetPrototypeOf : BuiltinFn := fun _ _ args _ => do
  let o ← requireObjectCoercible (arg args 0)
  let proto := arg args 1
  match proto with
  | .obj _ | .null => pure ()
  | _ => throwType "Object prototype may only be an Object or null"
  let .obj oid := o | return o
  if !(← Obj'.setPrototypeOf oid proto) then throwType "Cannot set prototype"
  pure o

def objectIsExtensible : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return .bool false
  pure (.bool (← Obj'.isExtensible o))

def objectPreventExtensions : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return arg args 0
  if !(← Obj'.preventExtensions o) then throwType "Cannot prevent extensions"
  pure (.obj o)

def objectIs : BuiltinFn := fun _ _ args _ => pure (.bool (sameValue (arg args 0) (arg args 1)))

def objectHasOwn : BuiltinFn := fun _ _ args _ => do
  let o ← toObj (arg args 0)
  let k ← toPropertyKey (arg args 1)
  pure (.bool (← hasOwnProperty o k))

/-- Object.fromEntries spec: https://tc39.es/ecma262/#sec-object.fromentries -/
def objectFromEntries : BuiltinFn := fun _ _ args _ => do
  let iterable ← requireObjectCoercible (arg args 0)
  let o ← newObject
  let r ← getIterator iterable
  M.repeatFrom r fun r => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr (Value.obj o)
    | some entry => withIterClose r do
      let .obj e := entry | throwType "Iterator value is not an entry object"
      let k ← getProp e (PropKey.ofNat 0)
      let v ← getProp e (PropKey.ofNat 1)
      let pk ← toPropertyKey k
      createDataPropertyOrThrow o pk v
      return .inl r

def objProtoHasOwnProperty : BuiltinFn := fun _ thisV args _ => do
  let k ← toPropertyKey (arg args 0)
  let o ← toObj thisV
  pure (.bool (← hasOwnProperty o k))

def objProtoIsPrototypeOf : BuiltinFn := fun _ thisV args _ => do
  let .obj v := arg args 0 | return .bool false
  let o ← toObj thisV
  M.repeatFrom v fun cur => do
    match ← Obj'.getPrototypeOf cur with
    | .obj p => if p == o then return .inr (Value.bool true) else return .inl p
    | _ => return .inr (.bool false)

def objProtoPropertyIsEnumerable : BuiltinFn := fun _ thisV args _ => do
  let k ← toPropertyKey (arg args 0)
  let o ← toObj thisV
  match ← Obj'.getOwnProperty o k with
  | some p => pure (.bool p.enumerable)
  | none => pure (.bool false)

/-- The builtinTag of Object.prototype.toString. -/
def builtinTag (o : ObjId) : M String := do
  if ← isArray (.obj o) then return "Array"
  match ← objKind o with
  | .arguments _ => pure "Arguments"
  | .func _ | .builtin _ | .bound .. => pure "Function"
  | .proxy _ _ c _ => pure (if c then "Function" else "Object")
  | .error => pure "Error"
  | .primitive (.bool _) => pure "Boolean"
  | .primitive (.num _) => pure "Number"
  | .primitive (.str _) => pure "String"
  | .date _ => pure "Date"
  | .regexp .. => pure "RegExp"
  | _ => pure "Object"

/-- Object.prototype.toString spec: https://tc39.es/ecma262/#sec-object.prototype.tostring -/
def objProtoToString : BuiltinFn := fun _ thisV _ _ => do
  match thisV with
  | .undefined => pure (.str "[object Undefined]")
  | .null => pure (.str "[object Null]")
  | _ =>
    let o ← toObj thisV
    let tag ← builtinTag o
    let t ← getProp o (.sym WK.toStringTag)
    let tag := match t with | .str s => s | _ => JSStr.ofString tag
    pure (.str (JSStr.ofString "[object " ++ tag ++ JSStr.ofString "]"))

def objProtoToLocaleString : BuiltinFn := fun _ thisV _ _ => invoke thisV (.str kToString)

def objProtoValueOf : BuiltinFn := fun _ thisV _ _ => do pure (.obj (← toObj thisV))

def objProtoGetProto : BuiltinFn := fun _ thisV _ _ => do Obj'.getPrototypeOf (← toObj thisV)

def objProtoSetProto : BuiltinFn := fun _ thisV args _ => do
  let _ ← requireObjectCoercible thisV
  let proto := arg args 0
  match proto with
  | .obj _ | .null =>
    let .obj o := thisV | return .undefined
    if !(← Obj'.setPrototypeOf o proto) then throwType "Object.prototype.__proto__ setter failed"
    pure .undefined
  | _ => pure .undefined

/-- Annex B __defineGetter__ etc. spec: https://tc39.es/ecma262/#sec-object.prototype.__defineGetter__ -/
def objProtoDefineAccessor (isGetter : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  if !(← isCallable (arg args 1)) then throwType "Getter/setter must be a function"
  let d : PropDesc := if isGetter then { get := some (arg args 1), enumerable := some true, configurable := some true }
    else { set := some (arg args 1), enumerable := some true, configurable := some true }
  let k ← toPropertyKey (arg args 0)
  definePropertyOrThrow o k d
  pure .undefined

def objProtoLookupAccessor (isGetter : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let k ← toPropertyKey (arg args 0)
  M.repeatFrom o fun cur => do
    match ← Obj'.getOwnProperty cur k with
    | some (.accessor g s _ _) => return .inr (if isGetter then g else s)
    | some _ => return .inr .undefined
    | none => match ← Obj'.getPrototypeOf cur with
      | .obj p => return .inl p
      | _ => return .inr .undefined

/-! ## Function -/

def functionPrototypeFn : BuiltinFn := fun _ _ _ _ => pure .undefined

def funcProtoCall : BuiltinFn := fun _ thisV args _ => do
  if !(← isCallable thisV) then throwType "Function.prototype.call called on non-callable"
  call thisV (arg args 0) (args.extract 1 args.size)

def funcProtoApply : BuiltinFn := fun _ thisV args _ => do
  if !(← isCallable thisV) then throwType "Function.prototype.apply was called on a non-function"
  let argArray := arg args 1
  if argArray.isNullish then return ← call thisV (arg args 0) #[]
  let xs ← listFromArrayLike argArray
  call thisV (arg args 0) xs

/-- Function.prototype.bind spec: https://tc39.es/ecma262/#sec-function.prototype.bind -/
def funcProtoBind : BuiltinFn := fun _ thisV args _ => do
  -- 2.
  if !(← isCallable thisV) then throwType "Bind must be called on a function"
  let .obj target := thisV | throwType "Bind must be called on a function"
  -- 3. BoundFunctionCreate
  let proto ← Obj'.getPrototypeOf target
  let isCtor ← isConstructor thisV
  let _ := isCtor
  let f ← alloc { proto, kind := .bound target (arg args 0) (args.extract 1 args.size) }
  -- 4-8.
  let argCount := args.size - (min 1 args.size)
  let L ← do
    if ← hasOwnProperty target (.str kLength) then
      let tl ← getProp target (.str kLength)
      match tl with
      | .num x => pure <| match Conv.toIntegerOrInf x with
        | .inl false => Value.num (.inf false)
        | .inl true => numV 0
        | .inr i => intV (max 0 (i - argCount))
      | _ => pure (numV 0)
    else pure (numV 0)
  setOwn f (.str kLength) (.data L false false true)
  -- 9-11.
  let tn ← getProp target (.str kName)
  let tn := match tn with | .str s => s | _ => JSStr.empty
  setOwn f (.str kName) (.data (.str (JSStr.ofString "bound " ++ tn)) false false true)
  pure (.obj f)

/-- Function.prototype.toString spec: https://tc39.es/ecma262/#sec-function.prototype.tostring -/
def funcProtoToString : BuiltinFn := fun _ thisV _ _ => do
  let .obj f := thisV | throwType "Function.prototype.toString requires that 'this' be a Function"
  match ← objKind f with
  | .func d =>
    let sp := match d.code with | .mk _ _ _ _ _ _ i => i.span
    let txt := String.Pos.Raw.extract d.source ⟨sp.start⟩ ⟨sp.stop⟩
    pure (.str (JSStr.ofString txt))
  | .builtin _ | .bound .. =>
    let nm ← getProp f (.str kName)
    let nm := match nm with | .str s => s | _ => JSStr.empty
    pure (.str (JSStr.ofString "function " ++ nm ++ JSStr.ofString "() { [native code] }"))
  | .proxy _ _ true _ => pure (.str "function () { [native code] }")
  | _ => throwType "Function.prototype.toString requires that 'this' be a Function"

def funcProtoHasInstance : BuiltinFn := fun _ thisV args _ => do
  pure (.bool (← ordinaryHasInstance thisV (arg args 0)))

/-- %ThrowTypeError% spec: https://tc39.es/ecma262/#sec-%throwtypeerror% -/
def throwTypeErrorFn : BuiltinFn := fun _ _ _ _ =>
  throwType "'caller', 'callee', and 'arguments' properties may not be accessed on strict mode functions or the arguments objects for calls to them"

/-! ## Errors -/

def kCause : JSStr := "cause"

/-- InstallErrorCause spec: https://tc39.es/ecma262/#sec-installerrorcause -/
def installErrorCause (o : ObjId) (options : Value) : M Unit := do
  let .obj opts := options | return
  if ← Obj'.hasProperty opts (.str kCause) then
    let c ← getProp opts (.str kCause)
    createNonEnumDataPropertyOrThrow o (.str kCause) c

/-- The Error and NativeError constructors. spec: https://tc39.es/ecma262/#sec-error-message -/
def errorCtor (protoName : String) : BuiltinFn := fun self _ args nt => do
  let nt := if nt.isUndefined then Value.obj self else nt
  let o ← ordinaryCreateFromConstructor nt protoName .error
  let msg := arg args 0
  if !msg.isUndefined then
    let m ← toStr msg
    createNonEnumDataPropertyOrThrow o (.str kMessage) (.str m)
  installErrorCause o (arg args 1)
  pure (.obj o)

/-- AggregateError spec: https://tc39.es/ecma262/#sec-aggregate-error -/
def aggregateErrorCtor : BuiltinFn := fun self _ args nt => do
  let nt := if nt.isUndefined then Value.obj self else nt
  let o ← ordinaryCreateFromConstructor nt "%AggregateError.prototype%" .error
  let msg := arg args 1
  if !msg.isUndefined then
    let m ← toStr msg
    createNonEnumDataPropertyOrThrow o (.str kMessage) (.str m)
  installErrorCause o (arg args 2)
  let errs ← iterableToList (arg args 0)
  let arr ← createArrayFromList errs
  createNonEnumDataPropertyOrThrow o (.str "errors") arr
  pure (.obj o)

/-- Error.prototype.toString spec: https://tc39.es/ecma262/#sec-error.prototype.tostring -/
def errorProtoToString : BuiltinFn := fun _ thisV _ _ => do
  let .obj o := thisV | throwType "Error.prototype.toString called on non-object"
  let name ← getProp o (.str kName)
  let name ← if name.isUndefined then pure (JSStr.ofString "Error") else toStr name
  let msg ← getProp o (.str kMessage)
  let msg ← if msg.isUndefined then pure JSStr.empty else toStr msg
  if name.isEmpty then return .str msg
  if msg.isEmpty then return .str name
  pure (.str (name ++ JSStr.ofString ": " ++ msg))

def errorIsError : BuiltinFn := fun _ _ args _ => do
  let .obj o := arg args 0 | return .bool false
  match ← objKind o with
  | .error => pure (.bool true)
  | _ => pure (.bool false)

/-! ## Symbol -/

def symbolCtor : BuiltinFn := fun _ _ args nt => do
  if !nt.isUndefined then throwType "Symbol is not a constructor"
  let d := arg args 0
  let desc ← if d.isUndefined then pure none else some <$> toStr d
  pure (.sym (← newSymbol desc))

def thisSymbolValue (v : Value) : M SymId := do
  match v with
  | .sym i => pure i
  | .obj o => match ← objKind o with
    | .primitive (.sym i) => pure i
    | _ => throwType "Symbol.prototype method called on incompatible receiver"
  | _ => throwType "Symbol.prototype method called on incompatible receiver"

/-- SymbolDescriptiveString spec: https://tc39.es/ecma262/#sec-symboldescriptivestring -/
def symbolDescriptiveString (i : SymId) : M JSStr := do
  let d ← readS fun s => (s.symbols[i]?).bind (fun x => x)
  pure (JSStr.ofString "Symbol(" ++ d.getD JSStr.empty ++ JSStr.ofString ")")

def symbolProtoToString : BuiltinFn := fun _ thisV _ _ => do
  pure (.str (← symbolDescriptiveString (← thisSymbolValue thisV)))

def symbolProtoValueOf : BuiltinFn := fun _ thisV _ _ => do pure (.sym (← thisSymbolValue thisV))

def symbolProtoDescription : BuiltinFn := fun _ thisV _ _ => do
  let i ← thisSymbolValue thisV
  match ← readS (fun s => (s.symbols[i]?).bind (fun x => x)) with
  | some d => pure (.str d)
  | none => pure .undefined

def symbolFor : BuiltinFn := fun _ _ args _ => do
  let key ← toStr (arg args 0)
  match ← readS (·.symRegistry.get? key) with
  | some i => pure (.sym i)
  | none =>
    let i ← newSymbol (some key)
    modify fun s => { s with symRegistry := s.symRegistry.insert key i }
    pure (.sym i)

def symbolKeyFor : BuiltinFn := fun _ _ args _ => do
  let .sym i := arg args 0 | throwType "Symbol.keyFor: argument is not a symbol"
  let found ← readS fun s => s.symRegistry.fold (fun acc k v => if v == i then some k else acc) none
  match found with
  | some k => pure (.str k)
  | none => pure .undefined

/-! ## Boolean -/

def booleanCtor : BuiltinFn := fun _ _ args nt => do
  let b := toBoolean (arg args 0)
  if nt.isUndefined then return .bool b
  let o ← ordinaryCreateFromConstructor nt "%Boolean.prototype%" (.primitive (.bool b))
  pure (.obj o)

def thisBooleanValue (v : Value) : M Bool := do
  match v with
  | .bool b => pure b
  | .obj o => match ← objKind o with
    | .primitive (.bool b) => pure b
    | _ => throwType "Boolean.prototype method called on incompatible receiver"
  | _ => throwType "Boolean.prototype method called on incompatible receiver"

def booleanProtoToString : BuiltinFn := fun _ thisV _ _ => do
  pure (.str (if ← thisBooleanValue thisV then "true" else "false"))
def booleanProtoValueOf : BuiltinFn := fun _ thisV _ _ => do pure (.bool (← thisBooleanValue thisV))

/-! ## Iterators and generators -/

def returnThis : BuiltinFn := fun _ thisV _ _ => pure thisV

/-- CreateArrayIterator: an iterator over an array-like, of keys (0), values (1) or entries (2).
spec: https://tc39.es/ecma262/#sec-createarrayiterator -/
def createArrayIterator (o : Value) (kind : Nat) : M Value := do
  let proto ← intrinsic "%ArrayIteratorPrototype%"
  let it ← alloc { proto := .obj proto, kind := .internal "Array Iterator" #[o, numV 0, numV kind] }
  pure (.obj it)

/-- %ArrayIteratorPrototype%.next spec: https://tc39.es/ecma262/#sec-%arrayiteratorprototype%.next -/
def arrayIteratorNext : BuiltinFn := fun _ thisV _ _ => do
  let .obj it := thisV | throwType "next method called on incompatible receiver"
  let .internal "Array Iterator" sl ← objKind it | throwType "next method called on incompatible receiver"
  let o := sl[0]!
  let .obj a := o | createIterResult .undefined true
  let idx := match sl[1]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  let kind := match sl[2]! with | .num x => (Conv.toNat? x).getD 1 | _ => 1
  -- (typed arrays: TypeError when out of bounds; a throw completes the iterator)
  let len ← M.tryCatch (do
      match ← taRecord? a with
      | some r =>
        if r.isOutOfBounds then throwType "Cannot iterate a detached or out-of-bounds typed array"
        pure r.length
      | none => lengthOf a)
    fun e => do
      modifyObj it fun ob => { ob with kind := .internal "Array Iterator" #[.undefined, numV idx, numV kind] }
      M.throwV e
  if idx ≥ len then
    modifyObj it fun ob => { ob with kind := .internal "Array Iterator" #[.undefined, numV idx, numV kind] }
    return ← createIterResult .undefined true
  modifyObj it fun ob => { ob with kind := .internal "Array Iterator" #[o, numV (idx + 1), numV kind] }
  if kind == 0 then return ← createIterResult (numV idx) false
  let v ← getProp a (PropKey.ofNat idx)
  if kind == 1 then return ← createIterResult v false
  createIterResult (← createArrayFromList #[numV idx, v]) false

def arrayProtoValues (kind : Nat) : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  createArrayIterator (.obj o) kind

/-- GeneratorValidate + GeneratorResume / GeneratorResumeAbrupt (`mode`: 0 next, 1 return, 2 throw).
spec: https://tc39.es/ecma262/#sec-generatorresume -/
def generatorResume (mode : Nat) : BuiltinFn := fun _ thisV args _ => do
  let .obj g := thisV | throwType "next method called on incompatible receiver"
  let .coroutine st f le ve false true sl ← objKind g | throwType "next method called on incompatible receiver"
  let v := arg args 0
  let setState (st' : GenState) : M Unit := modifyObj g fun o => { o with kind := .coroutine st' f le ve false true sl }
  if st == .executing then throwType "Generator is already running"
  -- (GeneratorResumeAbrupt: a generator that has not started completes at once)
  let st ← if st == .suspendedStart && mode != 0 then do setState .completed; pure GenState.completed else pure st
  if st == .completed then
    match mode with
    | 0 => return ← createIterResult .undefined true
    | 1 => return ← createIterResult v true
    | _ => M.throwV v
  setState .executing
  let o := match mode with | 0 => Outcome.normal v | 1 => .ret v | _ => .throw v
  let realm ← readS (·.realm)
  let r ← M.request (.resume g o)
  modify fun s => { s with realm }
  match r with
  | .normal res => setState .suspendedYield; pure res
  | .ret res => setState .completed; pure res
  | .throw e => setState .completed; M.throwV e

/-! ## Reflect -/

def reflectTarget (v : Value) : M ObjId := do
  let .obj o := v | throwType "Reflect method called on non-object"
  pure o

def reflectApply : BuiltinFn := fun _ _ args _ => do
  if !(← isCallable (arg args 0)) then throwType "Reflect.apply target is not callable"
  let xs ← listFromArrayLike (arg args 2)
  call (arg args 0) (arg args 1) xs

def reflectConstruct : BuiltinFn := fun _ _ args _ => do
  let t := arg args 0
  if !(← isConstructor t) then throwType "Reflect.construct target is not a constructor"
  let nt := if args.size < 3 then t else arg args 2
  if !(← isConstructor nt) then throwType "Reflect.construct newTarget is not a constructor"
  let xs ← listFromArrayLike (arg args 1)
  construct t xs (some nt)

def reflectDefineProperty : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  let k ← toPropertyKey (arg args 1)
  let d ← toPropertyDescriptor maxDepth (arg args 2)
  pure (.bool (← Obj'.defineOwnProperty o k d))

def reflectDeleteProperty : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  pure (.bool (← Obj'.delete o (← toPropertyKey (arg args 1))))

def reflectGet : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  let k ← toPropertyKey (arg args 1)
  let receiver := if args.size < 3 then Value.obj o else arg args 2
  Obj'.get o k receiver

def reflectGetOwnPropertyDescriptor : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  match ← Obj'.getOwnProperty o (← toPropertyKey (arg args 1)) with
  | some p => fromPropertyDescriptor (PropDesc.ofProp p)
  | none => pure .undefined

def reflectGetPrototypeOf : BuiltinFn := fun _ _ args _ => do Obj'.getPrototypeOf (← reflectTarget (arg args 0))

def reflectHas : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  pure (.bool (← Obj'.hasProperty o (← toPropertyKey (arg args 1))))

def reflectIsExtensible : BuiltinFn := fun _ _ args _ => do pure (.bool (← Obj'.isExtensible (← reflectTarget (arg args 0))))

def reflectOwnKeys : BuiltinFn := fun _ _ args _ => do
  let keys ← Obj'.ownPropertyKeys (← reflectTarget (arg args 0))
  createArrayFromList (keys.map keyToValue)

def reflectPreventExtensions : BuiltinFn := fun _ _ args _ => do pure (.bool (← Obj'.preventExtensions (← reflectTarget (arg args 0))))

def reflectSet : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  let k ← toPropertyKey (arg args 1)
  let receiver := if args.size < 4 then Value.obj o else arg args 3
  pure (.bool (← Obj'.set o k (arg args 2) receiver))

def reflectSetPrototypeOf : BuiltinFn := fun _ _ args _ => do
  let o ← reflectTarget (arg args 0)
  let p := arg args 1
  match p with
  | .obj _ | .null => pure (.bool (← Obj'.setPrototypeOf o p))
  | _ => throwType "Object prototype may only be an Object or null"

/-! ## Proxy -/

/-- ProxyCreate spec: https://tc39.es/ecma262/#sec-proxycreate -/
def proxyCreate (target handler : Value) : M ObjId := do
  let .obj t := target | throwType "Cannot create proxy with a non-object as target or handler"
  let .obj h := handler | throwType "Cannot create proxy with a non-object as target or handler"
  let callable ← isCallable target
  let ctor ← isConstructor target
  alloc { proto := .null, kind := .proxy (some t) (some h) callable ctor }

def proxyCtor : BuiltinFn := fun _ _ args nt => do
  if nt.isUndefined then throwType "Constructor Proxy requires 'new'"
  pure (.obj (← proxyCreate (arg args 0) (arg args 1)))

def proxyRevocable : BuiltinFn := fun _ _ args _ => do
  let p ← proxyCreate (arg args 0) (arg args 1)
  let revoker ← makeBuiltinFn "ProxyRevoker" 0 JSStr.empty #[.obj p]
  let r ← newObject
  createDataPropertyOrThrow r (.str "proxy") (.obj p)
  createDataPropertyOrThrow r (.str "revoke") (.obj revoker)
  pure (.obj r)

def proxyRevoker : BuiltinFn := fun self _ _ _ => do
  let sl ← builtinSlots self
  if let .obj p := sl[0]! then
    setBuiltinSlots self #[.null]
    modifyObj p fun o => o.withKind fun k => match k with
      | .proxy _ _ c k => .proxy none none c k
      | k => k
  pure .undefined

/-! ## Promise (constructor and prototype) -/

/-- Promise(executor) spec: https://tc39.es/ecma262/#sec-promise-executor -/
def promiseCtor : BuiltinFn := fun _ _ args nt => do
  if nt.isUndefined then throwType "Promise constructor cannot be invoked without 'new'"
  let executor := arg args 0
  if !(← isCallable executor) then throwType "Promise resolver is not a function"
  let p ← ordinaryCreateFromConstructor nt "%Promise.prototype%" (.promise .pending .undefined #[] #[] false)
  let (res, rej) ← createResolvingFunctions p
  match ← M.attempt (call executor .undefined #[res, rej]) with
  | .error e => let _ ← call rej .undefined #[e]
  | .ok _ => pure ()
  pure (.obj p)

/-- Promise.prototype.then spec: https://tc39.es/ecma262/#sec-promise.prototype.then -/
def promiseProtoThen : BuiltinFn := fun _ thisV args _ => do
  if !(← IsPromise thisV) then throwType "Promise.prototype.then called on incompatible receiver"
  let .obj p := thisV | throwType "not a promise"
  let c ← speciesConstructor p (← intrinsicV "%Promise%")
  let cap ← newPromiseCapability c
  performPromiseThen p (arg args 0) (arg args 1) (some cap)

def promiseProtoCatch : BuiltinFn := fun _ thisV args _ => invoke thisV (.str "then") #[.undefined, arg args 0]

def promiseResolveStatic : BuiltinFn := fun _ thisV args _ => do
  if !thisV.isObject then throwType "PromiseResolve called on non-object"
  promiseResolve thisV (arg args 0)

def promiseRejectStatic : BuiltinFn := fun _ thisV args _ => do
  let cap ← newPromiseCapability thisV
  let _ ← call cap.reject .undefined #[arg args 0]
  pure cap.promise

def speciesGetter : BuiltinFn := fun _ thisV _ _ => pure thisV

/-! ## Array (the core; the rest is in `Builtins/Array.lean`) -/

/-- Array(...values) spec: https://tc39.es/ecma262/#sec-array -/
def arrayCtor : BuiltinFn := fun self _ args nt => do
  let nt := if nt.isUndefined then Value.obj self else nt
  let proto ← getPrototypeFromConstructor nt "%Array.prototype%"
  if args.size == 0 then return .obj (← arrayCreate 0 (some proto))
  if args.size == 1 then
    let len := args[0]!
    match len with
    | .num x =>
      let some il := Conv.toNat? x | throwRange "Invalid array length"
      if Conv.toUint32 x != il then throwRange "Invalid array length"
      return .obj (← arrayCreate il (some proto))
    | _ =>
      let a ← arrayCreate 0 (some proto)
      createDataPropertyOrThrow a (PropKey.ofNat 0) len
      return .obj a
  let a ← arrayCreate 0 (some proto)
  M.forArr (Array.range args.size) fun i => createDataPropertyOrThrow a (PropKey.ofNat i) args[i]!
  pure (.obj a)

def arrayIsArray : BuiltinFn := fun _ _ args _ => do pure (.bool (← isArray (arg args 0)))

/-- Array.prototype.join spec: https://tc39.es/ecma262/#sec-array.prototype.join -/
def arrayProtoJoin : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let sep ← if (arg args 0).isUndefined then pure (JSStr.ofString ",") else toStr (arg args 0)
  let r ← M.foldArr (Array.range len) JSStr.empty fun acc k => do
    let acc := if k > 0 then acc ++ sep else acc
    let e ← getProp o (PropKey.ofNat k)
    if e.isNullish then pure acc else pure (acc ++ (← toStr e))
  pure (.str r)

def arrayProtoToString : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let f ← getProp o (.str "join")
  if ← isCallable f then call f (.obj o) #[]
  else objProtoToString 0 (.obj o) #[] .undefined

def arrayProtoPush : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len + args.size > 9007199254740991 then throwType "Pushing elements past 2^53-1 length"
  M.forArr (Array.range args.size) fun i => setProp o (PropKey.ofNat (len + i)) args[i]!
  let nl := numV (len + args.size)
  setProp o (.str kLength) nl
  pure nl

/-! ## String, Number, Math (the core) -/

def stringCtor : BuiltinFn := fun _ _ args nt => do
  let s ← if args.size == 0 then pure JSStr.empty
    else match args[0]!, nt with
      | .sym i, .undefined => symbolDescriptiveString i
      | v, _ => toStr v
  if nt.isUndefined then return .str s
  let proto ← getPrototypeFromConstructor nt "%String.prototype%"
  let o ← alloc { proto := .obj proto, kind := .primitive (.str s) }
  setOwn o (.str kLength) (.data (numV s.length) false false false)
  pure (.obj o)

def thisStringValue (v : Value) : M JSStr := do
  match v with
  | .str s => pure s
  | .obj o => match ← objKind o with
    | .primitive (.str s) => pure s
    | _ => throwType "String.prototype method called on incompatible receiver"
  | _ => throwType "String.prototype method called on incompatible receiver"

def stringProtoToString : BuiltinFn := fun _ thisV _ _ => do pure (.str (← thisStringValue thisV))

def numberCtor : BuiltinFn := fun _ _ args nt => do
  let n ← if args.size == 0 then pure F64.zero else do
    match ← toNumeric args[0]! with
    | .bigint i => pure (F64.ofInt i)
    | .num x => pure x
    | _ => pure F64.zero
  if nt.isUndefined then return .num n
  let o ← ordinaryCreateFromConstructor nt "%Number.prototype%" (.primitive (.num n))
  pure (.obj o)

def thisNumberValue (v : Value) : M F64 := do
  match v with
  | .num x => pure x
  | .obj o => match ← objKind o with
    | .primitive (.num x) => pure x
    | _ => throwType "Number.prototype method called on incompatible receiver"
  | _ => throwType "Number.prototype method called on incompatible receiver"

def numberProtoValueOf : BuiltinFn := fun _ thisV _ _ => do pure (.num (← thisNumberValue thisV))
def numberProtoToString : BuiltinFn := fun _ thisV _ _ => do pure (.str (numberToJSStr (← thisNumberValue thisV)))

def mathPow : BuiltinFn := fun _ _ args _ => do
  let b ← toNum (arg args 0)
  let e ← toNum (arg args 1)
  pure (.num (NumOps.pow b e))

/-! ## Setup -/

def coreBuiltins : Array BuiltinDef := #[
  ⟨"FunctionPrototype", functionPrototypeFn⟩,
  ⟨"Object", objectCtor⟩, ⟨"Object.assign", objectAssign⟩, ⟨"Object.create", objectCreate⟩,
  ⟨"Object.defineProperty", objectDefineProperty⟩, ⟨"Object.defineProperties", objectDefinePropertiesFn⟩,
  ⟨"Object.keys", objectEntriesLike 0⟩, ⟨"Object.values", objectEntriesLike 1⟩,
  ⟨"Object.entries", objectEntriesLike 2⟩, ⟨"Object.freeze", objectFreezeSeal true⟩,
  ⟨"Object.seal", objectFreezeSeal false⟩, ⟨"Object.isFrozen", objectIsFrozenSealed true⟩,
  ⟨"Object.isSealed", objectIsFrozenSealed false⟩,
  ⟨"Object.getOwnPropertyDescriptor", objectGetOwnPropertyDescriptor⟩,
  ⟨"Object.getOwnPropertyDescriptors", objectGetOwnPropertyDescriptors⟩,
  ⟨"Object.getOwnPropertyNames", fun _ _ args _ => getOwnPropertyKeys (arg args 0) false⟩,
  ⟨"Object.getOwnPropertySymbols", fun _ _ args _ => getOwnPropertyKeys (arg args 0) true⟩,
  ⟨"Object.getPrototypeOf", objectGetPrototypeOf⟩, ⟨"Object.setPrototypeOf", objectSetPrototypeOf⟩,
  ⟨"Object.isExtensible", objectIsExtensible⟩, ⟨"Object.preventExtensions", objectPreventExtensions⟩,
  ⟨"Object.is", objectIs⟩, ⟨"Object.hasOwn", objectHasOwn⟩, ⟨"Object.fromEntries", objectFromEntries⟩,
  ⟨"Object.prototype.hasOwnProperty", objProtoHasOwnProperty⟩,
  ⟨"Object.prototype.isPrototypeOf", objProtoIsPrototypeOf⟩,
  ⟨"Object.prototype.propertyIsEnumerable", objProtoPropertyIsEnumerable⟩,
  ⟨"Object.prototype.toString", objProtoToString⟩,
  ⟨"Object.prototype.toLocaleString", objProtoToLocaleString⟩,
  ⟨"Object.prototype.valueOf", objProtoValueOf⟩,
  ⟨"get Object.prototype.__proto__", objProtoGetProto⟩, ⟨"set Object.prototype.__proto__", objProtoSetProto⟩,
  ⟨"Object.prototype.__defineGetter__", objProtoDefineAccessor true⟩,
  ⟨"Object.prototype.__defineSetter__", objProtoDefineAccessor false⟩,
  ⟨"Object.prototype.__lookupGetter__", objProtoLookupAccessor true⟩,
  ⟨"Object.prototype.__lookupSetter__", objProtoLookupAccessor false⟩,
  ⟨"Function.prototype.call", funcProtoCall⟩, ⟨"Function.prototype.apply", funcProtoApply⟩,
  ⟨"Function.prototype.bind", funcProtoBind⟩, ⟨"Function.prototype.toString", funcProtoToString⟩,
  ⟨"Function.prototype[Symbol.hasInstance]", funcProtoHasInstance⟩,
  ⟨"ThrowTypeError", throwTypeErrorFn⟩,
  ⟨"Error", errorCtor "%Error.prototype%"⟩, ⟨"TypeError", errorCtor "%TypeError.prototype%"⟩,
  ⟨"RangeError", errorCtor "%RangeError.prototype%"⟩, ⟨"ReferenceError", errorCtor "%ReferenceError.prototype%"⟩,
  ⟨"SyntaxError", errorCtor "%SyntaxError.prototype%"⟩, ⟨"EvalError", errorCtor "%EvalError.prototype%"⟩,
  ⟨"URIError", errorCtor "%URIError.prototype%"⟩, ⟨"AggregateError", aggregateErrorCtor⟩,
  ⟨"Error.prototype.toString", errorProtoToString⟩, ⟨"Error.isError", errorIsError⟩,
  ⟨"Symbol", symbolCtor⟩, ⟨"Symbol.for", symbolFor⟩, ⟨"Symbol.keyFor", symbolKeyFor⟩,
  ⟨"Symbol.prototype.toString", symbolProtoToString⟩, ⟨"Symbol.prototype.valueOf", symbolProtoValueOf⟩,
  ⟨"get Symbol.prototype.description", symbolProtoDescription⟩,
  ⟨"Boolean", booleanCtor⟩, ⟨"Boolean.prototype.toString", booleanProtoToString⟩,
  ⟨"Boolean.prototype.valueOf", booleanProtoValueOf⟩,
  ⟨"returnThis", returnThis⟩,
  ⟨"%ArrayIteratorPrototype%.next", arrayIteratorNext⟩,
  ⟨"Array.prototype.values", arrayProtoValues 1⟩, ⟨"Array.prototype.keys", arrayProtoValues 0⟩,
  ⟨"Array.prototype.entries", arrayProtoValues 2⟩,
  ⟨"Generator.prototype.next", generatorResume 0⟩, ⟨"Generator.prototype.return", generatorResume 1⟩,
  ⟨"Generator.prototype.throw", generatorResume 2⟩,
  ⟨"Reflect.apply", reflectApply⟩, ⟨"Reflect.construct", reflectConstruct⟩,
  ⟨"Reflect.defineProperty", reflectDefineProperty⟩, ⟨"Reflect.deleteProperty", reflectDeleteProperty⟩,
  ⟨"Reflect.get", reflectGet⟩, ⟨"Reflect.getOwnPropertyDescriptor", reflectGetOwnPropertyDescriptor⟩,
  ⟨"Reflect.getPrototypeOf", reflectGetPrototypeOf⟩, ⟨"Reflect.has", reflectHas⟩,
  ⟨"Reflect.isExtensible", reflectIsExtensible⟩, ⟨"Reflect.ownKeys", reflectOwnKeys⟩,
  ⟨"Reflect.preventExtensions", reflectPreventExtensions⟩, ⟨"Reflect.set", reflectSet⟩,
  ⟨"Reflect.setPrototypeOf", reflectSetPrototypeOf⟩,
  ⟨"Proxy", proxyCtor⟩, ⟨"Proxy.revocable", proxyRevocable⟩, ⟨"ProxyRevoker", proxyRevoker⟩,
  ⟨"Promise", promiseCtor⟩, ⟨"Promise.prototype.then", promiseProtoThen⟩,
  ⟨"Promise.prototype.catch", promiseProtoCatch⟩, ⟨"Promise.resolve", promiseResolveStatic⟩,
  ⟨"Promise.reject", promiseRejectStatic⟩, ⟨"get [Symbol.species]", speciesGetter⟩,
  ⟨"Array", arrayCtor⟩, ⟨"Array.isArray", arrayIsArray⟩, ⟨"Array.prototype.join", arrayProtoJoin⟩,
  ⟨"Array.prototype.toString", arrayProtoToString⟩, ⟨"Array.prototype.push", arrayProtoPush⟩,
  ⟨"String", stringCtor⟩, ⟨"String.prototype.toString", stringProtoToString⟩,
  ⟨"String.prototype.valueOf", stringProtoToString⟩,
  ⟨"Number", numberCtor⟩, ⟨"Number.prototype.valueOf", numberProtoValueOf⟩,
  ⟨"Number.prototype.toString", numberProtoToString⟩,
  ⟨"Math.pow", mathPow⟩]

/-- Defines `%Name%[Symbol.species]` (a getter returning this). -/
def defSpecies (c : ObjId) : M Unit := do
  let g ← makeBuiltinFn "get [Symbol.species]" 0 "get [Symbol.species]"
  setOwn c (.sym WK.species) (.accessor (.obj g) .undefined false true)

def defTag (o : ObjId) (tag : String) : M Unit :=
  setOwn o (.sym WK.toStringTag) (.data (.str (JSStr.ofString tag)) false false true)

/-- The core intrinsics of a realm. -/
def coreSetup : M Unit := do
  let (op, fp) ← readS fun s => (s.curRealm.objectProto, s.curRealm.functionProto)
  -- %ThrowTypeError%
  let tte ← makeBuiltinFn "ThrowTypeError" 0 JSStr.empty
  modifyObj tte fun o => { o with extensible := false }
  setOwn tte (.str kLength) (.data (numV 0) false false false)
  setOwn tte (.str kName) (.data (.str JSStr.empty) false false false)
  regIntrinsic "%ThrowTypeError%" tte
  -- Object
  let (oc, _) ← defConstructor "Object" 1 "Object" op
  for (nm, len) in [("assign", 2), ("create", 2), ("defineProperty", 3), ("defineProperties", 2),
      ("keys", 1), ("values", 1), ("entries", 1), ("freeze", 1), ("seal", 1), ("isFrozen", 1),
      ("isSealed", 1), ("getOwnPropertyDescriptor", 2), ("getOwnPropertyDescriptors", 1),
      ("getOwnPropertyNames", 1), ("getOwnPropertySymbols", 1), ("getPrototypeOf", 1),
      ("setPrototypeOf", 2), ("isExtensible", 1), ("preventExtensions", 1), ("is", 2), ("hasOwn", 2),
      ("fromEntries", 1)] do
    let _ ← defMethod oc (.str (JSStr.ofString nm)) s!"Object.{nm}" len
  for (nm, len) in [("hasOwnProperty", 1), ("isPrototypeOf", 1), ("propertyIsEnumerable", 1),
      ("toString", 0), ("toLocaleString", 0), ("valueOf", 0), ("__defineGetter__", 2),
      ("__defineSetter__", 2), ("__lookupGetter__", 1), ("__lookupSetter__", 1)] do
    let _ ← defMethod op (.str (JSStr.ofString nm)) s!"Object.prototype.{nm}" len
  defGetter op (.str "__proto__") "get Object.prototype.__proto__" (some "set Object.prototype.__proto__")
  -- Function.prototype
  for (nm, len) in [("call", 1), ("apply", 2), ("bind", 1), ("toString", 0)] do
    let _ ← defMethod fp (.str (JSStr.ofString nm)) s!"Function.prototype.{nm}" len
  let hi ← makeBuiltinFn "Function.prototype[Symbol.hasInstance]" 1 "[Symbol.hasInstance]"
  setOwn fp (.sym WK.hasInstance) (.data (.obj hi) false false false)
  setOwn fp (.str "caller") (.accessor (.obj tte) (.obj tte) false true)
  setOwn fp (.str "arguments") (.accessor (.obj tte) (.obj tte) false true)
  -- Errors
  let ep ← newIntrinsicObject "%Error.prototype%"
  let (ec, _) ← defConstructor "Error" 1 "Error" ep
  let _ ← defMethod ec (.str "isError") "Error.isError" 1
  setOwn ep (.str kName) (.data (.str "Error") true false true)
  setOwn ep (.str kMessage) (.data (.str JSStr.empty) true false true)
  let _ ← defMethod ep (.str kToString) "Error.prototype.toString" 0
  for nm in ["TypeError", "RangeError", "ReferenceError", "SyntaxError", "EvalError", "URIError", "AggregateError"] do
    let p ← newIntrinsicObject s!"%{nm}.prototype%" (some ep)
    let _ ← defConstructor nm (if nm == "AggregateError" then 2 else 1) nm p (some ec)
    setOwn p (.str kName) (.data (.str (JSStr.ofString nm)) true false true)
    setOwn p (.str kMessage) (.data (.str JSStr.empty) true false true)
  -- Symbol
  let sp ← newIntrinsicObject "%Symbol.prototype%"
  let (sc, _) ← defConstructor "Symbol" 0 "Symbol" sp
  for i in [0:WK.names.size - 1] do
    let nm := (WK.names[i]!.drop 7).toString
    setOwn sc (.str (JSStr.ofString nm)) (.data (.sym i) false false false)
  let _ ← defMethod sc (.str "for") "Symbol.for" 1
  let _ ← defMethod sc (.str "keyFor") "Symbol.keyFor" 1
  let _ ← defMethod sp (.str kToString) "Symbol.prototype.toString" 0
  let _ ← defMethod sp (.str kValueOf) "Symbol.prototype.valueOf" 0
  defGetter sp (.str "description") "get Symbol.prototype.description"
  let tp ← makeBuiltinFn "Symbol.prototype.valueOf" 1 "[Symbol.toPrimitive]"
  setOwn sp (.sym WK.toPrimitive) (.data (.obj tp) false false true)
  defTag sp "Symbol"
  -- Boolean
  let bp ← newIntrinsicObject "%Boolean.prototype%" none (.primitive (.bool false))
  let _ ← defConstructor "Boolean" 1 "Boolean" bp
  let _ ← defMethod bp (.str kToString) "Boolean.prototype.toString" 0
  let _ ← defMethod bp (.str kValueOf) "Boolean.prototype.valueOf" 0
  -- String, Number (core)
  let strp ← newIntrinsicObject "%String.prototype%" none (.primitive (.str JSStr.empty))
  setOwn strp (.str kLength) (.data (numV 0) false false false)
  let _ ← defConstructor "String" 1 "String" strp
  let _ ← defMethod strp (.str kToString) "String.prototype.toString" 0
  let _ ← defMethod strp (.str kValueOf) "String.prototype.valueOf" 0
  let np ← newIntrinsicObject "%Number.prototype%" none (.primitive (.num F64.zero))
  let _ ← defConstructor "Number" 1 "Number" np
  let _ ← defMethod np (.str kToString) "Number.prototype.toString" 1
  let _ ← defMethod np (.str kValueOf) "Number.prototype.valueOf" 0
  let bigp ← newIntrinsicObject "%BigInt.prototype%"
  let _ := bigp
  -- Iterators
  let ip ← newIntrinsicObject "%Iterator.prototype%"
  let _ ← defMethod ip (.sym WK.iterator) "returnThis" 0 (some "[Symbol.iterator]")
  let aip ← newIntrinsicObject "%ArrayIteratorPrototype%" (some ip)
  let _ ← defMethod aip (.str kNext) "%ArrayIteratorPrototype%.next" 0
  defTag aip "Array Iterator"
  -- Array (core)
  let ap ← newIntrinsicObject "%Array.prototype%" none .array
  setOwn ap (.str kLength) (.data (numV 0) true false false)
  let (ac, _) ← defConstructor "Array" 1 "Array" ap
  defSpecies ac
  let _ ← defMethod ac (.str "isArray") "Array.isArray" 1
  for (nm, len) in [("join", 1), ("toString", 0), ("push", 1), ("keys", 0), ("entries", 0)] do
    let _ ← defMethod ap (.str (JSStr.ofString nm)) s!"Array.prototype.{nm}" len
  let vals ← defMethod ap (.str "values") "Array.prototype.values" 0
  setOwn ap (.sym WK.iterator) (.data (.obj vals) true false true)
  regIntrinsic "%Array.prototype.values%" vals
  -- Generators
  let gfp ← newIntrinsicObject "%GeneratorFunction.prototype%" (some fp)
  let gp ← newIntrinsicObject "%GeneratorFunction.prototype.prototype%" (some ip)
  regIntrinsic "%GeneratorPrototype%" gp
  setOwn gfp (.str kPrototype) (.data (.obj gp) false false true)
  setOwn gp (.str kConstructor) (.data (.obj gfp) false false true)
  defTag gfp "GeneratorFunction"
  defTag gp "Generator"
  for (nm, len) in [("next", 1), ("return", 1), ("throw", 1)] do
    let _ ← defMethod gp (.str (JSStr.ofString nm)) s!"Generator.prototype.{nm}" len
  let afp ← newIntrinsicObject "%AsyncFunction.prototype%" (some fp)
  defTag afp "AsyncFunction"
  let agfp ← newIntrinsicObject "%AsyncGeneratorFunction.prototype%" (some fp)
  let aip' ← newIntrinsicObject "%AsyncIteratorPrototype%"
  let agp ← newIntrinsicObject "%AsyncGeneratorFunction.prototype.prototype%" (some aip')
  regIntrinsic "%AsyncGeneratorPrototype%" agp
  setOwn agfp (.str kPrototype) (.data (.obj agp) false false true)
  setOwn agp (.str kConstructor) (.data (.obj agfp) false false true)
  defTag agfp "AsyncGeneratorFunction"
  defTag agp "AsyncGenerator"
  -- Reflect
  let rf ← newIntrinsicObject "%Reflect%"
  defGlobal "Reflect" (.obj rf)
  defTag rf "Reflect"
  for (nm, len) in [("apply", 3), ("construct", 2), ("defineProperty", 3), ("deleteProperty", 2),
      ("get", 2), ("getOwnPropertyDescriptor", 2), ("getPrototypeOf", 1), ("has", 2),
      ("isExtensible", 1), ("ownKeys", 1), ("preventExtensions", 1), ("set", 3), ("setPrototypeOf", 2)] do
    let _ ← defMethod rf (.str (JSStr.ofString nm)) s!"Reflect.{nm}" len
  -- Proxy
  let pc ← makeBuiltinFn "Proxy" 2 "Proxy" #[] true
  regIntrinsic "%Proxy%" pc
  defGlobal "Proxy" (.obj pc)
  let _ ← defMethod pc (.str "revocable") "Proxy.revocable" 2
  -- Promise
  let pp ← newIntrinsicObject "%Promise.prototype%"
  let (pcc, _) ← defConstructor "Promise" 1 "Promise" pp
  defSpecies pcc
  let _ ← defMethod pp (.str "then") "Promise.prototype.then" 2
  let _ ← defMethod pp (.str "catch") "Promise.prototype.catch" 1
  let _ ← defMethod pcc (.str "resolve") "Promise.resolve" 1
  let _ ← defMethod pcc (.str "reject") "Promise.reject" 1
  defTag pp "Promise"
  -- Math (core)
  let mo ← newIntrinsicObject "%Math%"
  defGlobal "Math" (.obj mo)
  defTag mo "Math"
  let _ ← defMethod mo (.str "pow") "Math.pow" 2
  -- %eval% placeholder (the interpreter's)
  let ev ← makeBuiltinFn "eval" 1 "eval"
  regIntrinsic "%eval%" ev
  defGlobal "eval" (.obj ev)
  pure ()

end ES
