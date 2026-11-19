import ES.Object

/-!
# Abstract operations

spec: https://tc39.es/ecma262/#sec-abstract-operations — type conversion (7.1), testing and
comparison (7.2), operations on objects (7.3), iterators (7.4); and the operators' semantics that
do not depend on syntax (13.15.3 ApplyStringOrNumericBinaryOperator, equality, relational).
-/

namespace ES

open ES (F64)

/-! ## Operations on objects (7.3) -/

/-- Get(O, P) spec: https://tc39.es/ecma262/#sec-get-o-p -/
def getProp (o : ObjId) (k : PropKey) : M Value := Obj'.get o k (.obj o)

/-- GetV(V, P) spec: https://tc39.es/ecma262/#sec-getv -/
def getVProp (v : Value) (k : PropKey) : M Value := getV maxDepth v k

/-- GetMethod(V, P) spec: https://tc39.es/ecma262/#sec-getmethod -/
def getMethodOf (v : Value) (k : PropKey) : M (Option Value) := getMethod maxDepth v k

/-- Set(O, P, V, Throw) spec: https://tc39.es/ecma262/#sec-set-o-p-v-throw -/
def setProp (o : ObjId) (k : PropKey) (v : Value) (throwOnFail := true) : M Unit := do
  let ok ← Obj'.set o k v (.obj o)
  if !ok && throwOnFail then throwType s!"Cannot assign to read only property '{keyDesc k}' of object"
where keyDesc : PropKey → String | .str s => s.toString | .sym _ => "Symbol()"

/-- CreateDataProperty spec: https://tc39.es/ecma262/#sec-createdataproperty -/
def createDataProperty (o : ObjId) (k : PropKey) (v : Value) : M Bool :=
  Obj'.defineOwnProperty o k (PropDesc.data v)

/-- CreateDataPropertyOrThrow spec: https://tc39.es/ecma262/#sec-createdatapropertyorthrow -/
def createDataPropertyOrThrow (o : ObjId) (k : PropKey) (v : Value) : M Unit := do
  if !(← createDataProperty o k v) then throwType "Cannot define property"

/-- CreateNonEnumerableDataPropertyOrThrow -/
def createNonEnumDataPropertyOrThrow (o : ObjId) (k : PropKey) (v : Value) : M Unit := do
  if !(← Obj'.defineOwnProperty o k (PropDesc.data v true false true)) then throwType "Cannot define property"

/-- DefinePropertyOrThrow spec: https://tc39.es/ecma262/#sec-definepropertyorthrow -/
def definePropertyOrThrow (o : ObjId) (k : PropKey) (d : PropDesc) : M Unit := do
  if !(← Obj'.defineOwnProperty o k d) then throwType "Cannot redefine property"

/-- DeletePropertyOrThrow spec: https://tc39.es/ecma262/#sec-deletepropertyorthrow -/
def deletePropertyOrThrow (o : ObjId) (k : PropKey) : M Unit := do
  if !(← Obj'.delete o k) then throwType "Cannot delete property"

/-- HasOwnProperty spec: https://tc39.es/ecma262/#sec-hasownproperty -/
def hasOwnProperty (o : ObjId) (k : PropKey) : M Bool := do
  pure (← Obj'.getOwnProperty o k).isSome

/-- Invoke(V, P, args) spec: https://tc39.es/ecma262/#sec-invoke -/
def invoke (v : Value) (k : PropKey) (args : Array Value := #[]) : M Value := do
  let f ← getVProp v k
  call f v args

/-! ## Type conversion (7.1) -/

def toPrim (v : Value) (hint : Option Bool := none) : M Value := toPrimitive maxDepth v hint
def toNum (v : Value) : M F64 := toNumber maxDepth v
def toStr (v : Value) : M JSStr := toJSString maxDepth v

/-- ToNumeric: a Number or a BigInt. spec: https://tc39.es/ecma262/#sec-tonumeric -/
def toNumeric (v : Value) : M Value := do
  let p ← toPrim v (some true)
  match p with
  | .bigint _ => pure p
  | _ => pure (.num (← toNum p))

/-- ToPropertyKey spec: https://tc39.es/ecma262/#sec-topropertykey -/
def toPropertyKey (v : Value) : M PropKey := do
  match v with
  | .str s => pure (.str s)
  | .sym i => pure (.sym i)
  | _ =>
    let p ← toPrim v (some false)
    match p with
    | .sym i => pure (.sym i)
    | _ => pure (.str (← toStr p))

/-- ToIntegerOrInfinity: `.inl neg` for ±∞. spec: https://tc39.es/ecma262/#sec-tointegerorinfinity -/
def toIntegerOrInfinity (v : Value) : M (Sum Bool Int) := do
  pure (Conv.toIntegerOrInf (← toNum v))

/-- ToIntegerOrInfinity clamped to a range (the common "relative index" pattern). -/
def toIntClamp (v : Value) (lo hi : Int) : M Int := do
  pure <| match ← toIntegerOrInfinity v with
    | .inl true => lo
    | .inl false => hi
    | .inr i => max lo (min hi i)

def toLen (v : Value) : M Nat := toLength maxDepth v

/-- ToIndex spec: https://tc39.es/ecma262/#sec-toindex -/
def toIndex (v : Value) : M Nat := do
  let i ← toIntegerOrInfinity v
  match i with
  | .inr i => if i < 0 || i > 9007199254740991 then throwRange "Invalid index" else pure i.toNat
  | .inl _ => throwRange "Invalid index"

def toUint32 (v : Value) : M Nat := do pure (Conv.toUint32 (← toNum v))
def toInt32 (v : Value) : M Int := do pure (Conv.toInt32 (← toNum v))

/-- RequireObjectCoercible spec: https://tc39.es/ecma262/#sec-requireobjectcoercible -/
def requireObjectCoercible (v : Value) : M Value := do
  if v.isNullish then throwType "Cannot convert undefined or null to object" else pure v

def lengthOf (o : ObjId) : M Nat := lengthOfArrayLike maxDepth o

/-- CanonicalNumericIndexString spec: https://tc39.es/ecma262/#sec-canonicalnumericindexstring -/
def canonicalNumericIndexString (s : JSStr) : Option F64 :=
  if s == JSStr.ofString "-0" then some (.fin true 0 (-1074)) else
  let n := stringToNumber s
  if numberToJSStr n == s then some n else none

/-! ## Testing and comparison (7.2) -/

/-- IsArray spec: https://tc39.es/ecma262/#sec-isarray -/
def isArray (v : Value) : M Bool := do
  let .obj o := v | return false
  M.repeatFrom o fun o => do
    match ← objKind o with
    | .array => return .inr true
    | .proxy t _ _ _ => match t with
      | some t => return .inl t
      | none => throwType "Cannot perform 'IsArray' on a proxy that has been revoked"
    | _ => return .inr false

/-- typeof spec: https://tc39.es/ecma262/#sec-typeof-operator -/
def typeOf (v : Value) : M JSStr := do
  match v with
  | .undefined => pure "undefined"
  | .null => pure "object"
  | .bool _ => pure "boolean"
  | .num _ => pure "number"
  | .str _ => pure "string"
  | .sym _ => pure "symbol"
  | .bigint _ => pure "bigint"
  | .obj _ => pure (if ← isCallable v then "function" else "object")

/-- IsStrictlyEqual spec: https://tc39.es/ecma262/#sec-isstrictlyequal -/
def isStrictlyEqual (x y : Value) : Bool :=
  match x, y with
  | .num a, .num b => if a == .nan || b == .nan then false else a == b || (a.isZero && b.isZero)
  | _, _ => sameValue x y

/-- The exact comparison of a BigInt and a Number: `none` when the Number is NaN. -/
def compareBigNum (i : Int) (x : F64) : Option Ordering :=
  match x with
  | .nan => none
  | .inf neg => some (if neg then .gt else .lt)
  | _ => match x.toRat with
    | some (neg, p, q) =>
      -- i ? (±p/q)  ⇔  i·q ? ±p
      let lhs := i * q
      let rhs : Int := if neg then -(p : Int) else p
      some (compare lhs rhs)
    | none => none

/-- StringToBigInt (`none`: undefined). spec: https://tc39.es/ecma262/#sec-stringtobigint -/
def stringToBigInt? (s : JSStr) : Option Int := Num.BigInt.stringToBigInt s

/-- IsLooselyEqual spec: https://tc39.es/ecma262/#sec-islooselyequal -/
def isLooselyEqual (x y : Value) : M Bool :=
  M.repeatFrom (x, y) fun (x, y) => do
    match x, y with
    -- 1.
    | .undefined, .undefined | .null, .null | .undefined, .null | .null, .undefined => return .inr true
    | .num _, .num _ | .str _, .str _ | .bool _, .bool _ | .sym _, .sym _ | .bigint _, .bigint _
    | .obj _, .obj _ => return .inr (isStrictlyEqual x y)
    -- 2-3. (covered) 4. (Annex B [[IsHTMLDDA]]: none)
    -- 5-6.
    | .num _, .str s => return .inl (x, .num (stringToNumber s))
    | .str s, .num _ => return .inl (.num (stringToNumber s), y)
    -- 7-8.
    | .bigint i, .str s => return .inr (match stringToBigInt? s with | some j => i == j | none => false)
    | .str _, .bigint _ => return .inl (y, x)
    -- 9-10.
    | .bool b, _ => return .inl (.num (NumOps.ofBool b), y)
    | _, .bool b => return .inl (x, .num (NumOps.ofBool b))
    -- 11-12.
    | .num _, .obj _ | .str _, .obj _ | .bigint _, .obj _ | .sym _, .obj _ =>
      return .inl (x, ← toPrim y)
    | .obj _, .num _ | .obj _, .str _ | .obj _, .bigint _ | .obj _, .sym _ =>
      return .inl (← toPrim x, y)
    -- 13.
    | .bigint i, .num n | .num n, .bigint i => return .inr (compareBigNum i n == some .eq)
    -- 14.
    | _, _ => return .inr false

/-- IsLessThan (`leftFirst`: evaluation order of the conversions). `none` is undefined (NaN).
spec: https://tc39.es/ecma262/#sec-islessthan -/
def isLessThan (x y : Value) (leftFirst : Bool) : M (Option Bool) := do
  -- 1-2.
  let (px, py) ← if leftFirst then do
      let px ← toPrim x (some true); let py ← toPrim y (some true); pure (px, py)
    else do
      let py ← toPrim y (some true); let px ← toPrim x (some true); pure (px, py)
  match px, py with
  -- 3.
  | .str a, .str b => pure (some (a.lt b))
  | .bigint i, .str s => pure ((stringToBigInt? s).map (i < ·))
  | .str s, .bigint i => pure ((stringToBigInt? s).map (· < i))
  | _, _ =>
    -- 4.
    let nx ← toNumeric px
    let ny ← toNumeric py
    match nx, ny with
    | .num a, .num b => pure (if a == .nan || b == .nan then none else some (Conv.ltF a b))
    | .bigint a, .bigint b => pure (some (a < b))
    | .bigint a, .num b => pure ((compareBigNum a b).map (· == .lt))
    | .num a, .bigint b => pure ((compareBigNum b a).map (· == .gt))
    | _, _ => pure none

/-! ## Function objects -/

/-- GetFunctionRealm spec: https://tc39.es/ecma262/#sec-getfunctionrealm -/
def getFunctionRealm (f : ObjId) : M Nat := do
  M.repeatFrom f fun f => do
    match ← objKind f with
    | .func d => return .inr d.realm
    | .builtin b => return .inr b.realm
    | .bound t _ _ => return .inl t
    | .proxy t _ _ _ => match t with
      | some t => return .inl t
      | none => throwType "Cannot get the realm of a revoked proxy"
    | _ => return .inr (← readS (·.realm))

/-- GetPrototypeFromConstructor spec: https://tc39.es/ecma262/#sec-getprototypefromconstructor -/
def getPrototypeFromConstructor (ctor : Value) (defaultProto : String) : M ObjId := do
  let .obj c := ctor | intrinsic defaultProto
  let proto ← getProp c (.str kPrototype)
  match proto with
  | .obj p => pure p
  | _ =>
    let realm ← getFunctionRealm c
    intrinsicOf realm defaultProto

/-- OrdinaryCreateFromConstructor spec: https://tc39.es/ecma262/#sec-ordinarycreatefromconstructor -/
def ordinaryCreateFromConstructor (ctor : Value) (defaultProto : String) (kind : Kind := .ordinary) : M ObjId := do
  let proto ← getPrototypeFromConstructor ctor defaultProto
  alloc { proto := .obj proto, kind }

/-- SpeciesConstructor spec: https://tc39.es/ecma262/#sec-speciesconstructor -/
def speciesConstructor (o : ObjId) (defaultCtor : Value) : M Value := do
  let c ← getProp o (.str kConstructor)
  if c.isUndefined then return defaultCtor
  let .obj co := c | throwType "object.constructor is not an object"
  let s ← getProp co (.sym WK.species)
  if s.isNullish then return defaultCtor
  if ← isConstructor s then return s
  throwType "object.constructor[Symbol.species] is not a constructor"

/-- OrdinaryHasInstance spec: https://tc39.es/ecma262/#sec-ordinaryhasinstance -/
def ordinaryHasInstance (c : Value) (o : Value) : M Bool := do
  -- 1.
  if !(← isCallable c) then return false
  let .obj cid := c | return false
  -- 2.
  if let .bound t _ _ ← objKind cid then
    return ← instanceofOperator o (.obj t)
  -- 3.
  let .obj oid := o | return false
  -- 4-5.
  let p ← getProp cid (.str kPrototype)
  let .obj _ := p | throwType "Function has non-object prototype in instanceof check"
  -- 6.
  M.repeatFrom oid fun cur => do
    match ← Obj'.getPrototypeOf cur with
    | .obj nxt => if sameValue (.obj nxt) p then return .inr true else return .inl nxt
    | _ => return .inr false
where
  /-- InstanceofOperator (for bound targets: bound chains are finite). -/
  instanceofOperator (v target : Value) : M Bool := do
    let .obj _ := target | throwType "Right-hand side of 'instanceof' is not an object"
    match ← getMethodOf target (.sym WK.hasInstance) with
    | some h => pure (toBoolean (← call h target #[v]))
    | none =>
      if !(← isCallable target) then throwType "Right-hand side of 'instanceof' is not callable"
      -- (a bound function's target: no further binding check needed at this depth)
      let .obj tid := target | return false
      let .obj oid := v | return false
      let p ← getProp tid (.str kPrototype)
      let .obj _ := p | throwType "Function has non-object prototype in instanceof check"
      M.repeatFrom oid fun cur => do
        match ← Obj'.getPrototypeOf cur with
        | .obj nxt => if sameValue (.obj nxt) p then return .inr true else return .inl nxt
        | _ => return .inr false

/-- InstanceofOperator spec: https://tc39.es/ecma262/#sec-instanceofoperator -/
def instanceofOperator (v target : Value) : M Bool := do
  let .obj _ := target | throwType "Right-hand side of 'instanceof' is not an object"
  match ← getMethodOf target (.sym WK.hasInstance) with
  | some h => pure (toBoolean (← call h target #[v]))
  | none =>
    if !(← isCallable target) then throwType "Right-hand side of 'instanceof' is not callable"
    ordinaryHasInstance target v

/-- SetFunctionName spec: https://tc39.es/ecma262/#sec-setfunctionname -/
def setFunctionName (f : ObjId) (name : PropKey) (pfx : Option String := none) : M Unit := do
  let base : JSStr ← match name with
    | .str s => pure s
    | .sym id => do
      let d ← readS fun s => (s.symbols[id]?).bind (fun x => x)
      pure (match d with | some d => JSStr.ofString "[" ++ d ++ JSStr.ofString "]" | none => JSStr.empty)
  let n := match pfx with
    | some p => JSStr.ofString (p ++ " ") ++ base
    | none => base
  let _ ← Obj'.defineOwnProperty f (.str kName) (PropDesc.data (.str n) false false true)

/-- SetFunctionLength spec: https://tc39.es/ecma262/#sec-setfunctionlength -/
def setFunctionLength (f : ObjId) (len : Nat) : M Unit := do
  let _ ← Obj'.defineOwnProperty f (.str kLength) (PropDesc.data (.num (Conv.ofNat len)) false false true)

/-! ## Arrays -/

/-- ArrayCreate spec: https://tc39.es/ecma262/#sec-arraycreate -/
def arrayCreate (len : Nat) (proto : Option ObjId := none) : M ObjId := do
  if len > 4294967295 then throwRange "Invalid array length"
  let proto ← match proto with
    | some p => pure p
    | none => readS (·.curRealm.arrayProto)
  let a ← alloc { proto := .obj proto, kind := .array }
  setOwn a (.str kLength) (.data (.num (Conv.ofNat len)) true false false)
  pure a

/-- CreateArrayFromList spec: https://tc39.es/ecma262/#sec-createarrayfromlist -/
def createArrayFromList (xs : Array Value) : M Value := do
  let a ← arrayCreate 0
  -- (fresh array: the properties are defined directly, in index order)
  modifyObj a fun ob => ob.withProps fun pm =>
    let pm := (xs.zipIdx).foldl (fun pm (v, i) => pm.insert (PropKey.ofNat i) (.data v true true true)) pm
    pm.insert (.str kLength) (.data (.num (Conv.ofNat xs.size)) true false false)
  pure (.obj a)

/-- CreateListFromArrayLike spec: https://tc39.es/ecma262/#sec-createlistfromarraylike -/
def listFromArrayLike (v : Value) : M (Array Value) := createListFromArrayLike maxDepth v false

/-! ## Iterators (7.4) -/

/-- An Iterator Record. spec: https://tc39.es/ecma262/#sec-iterator-records -/
structure IterRecord where
  iter : Value
  next : Value
  done : Bool := false
  deriving Inhabited

/-- CreateIterResultObject spec: https://tc39.es/ecma262/#sec-createiterresultobject -/
def createIterResult (v : Value) (done : Bool) : M Value := do
  let o ← newObject
  setOwn o (.str kValue) (.data v true true true)
  setOwn o (.str kDone) (.data (.bool done) true true true)
  pure (.obj o)

/-- GetIteratorDirect spec: https://tc39.es/ecma262/#sec-getiteratordirect -/
def getIteratorDirect (o : Value) : M IterRecord := do
  let next ← getVProp o (.str kNext)
  pure { iter := o, next }

/-- GetIteratorFromMethod spec: https://tc39.es/ecma262/#sec-getiteratorfrommethod -/
def getIteratorFromMethod (o : Value) (method : Value) : M IterRecord := do
  let it ← call method o #[]
  if !it.isObject then throwType "Result of the Symbol.iterator method is not an object"
  getIteratorDirect it

/-- GetIterator(obj, sync) spec: https://tc39.es/ecma262/#sec-getiterator -/
def getIterator (o : Value) : M IterRecord := do
  match ← getMethodOf o (.sym WK.iterator) with
  | some m => getIteratorFromMethod o m
  | none => throwType "object is not iterable"

/-- IteratorNext spec: https://tc39.es/ecma262/#sec-iteratornext -/
def iteratorNext (r : IterRecord) (v : Option Value := none) : M Value := do
  let res ← call r.next r.iter (match v with | some v => #[v] | none => #[])
  if !res.isObject then throwType "Iterator result is not an object"
  pure res

/-- IteratorComplete spec: https://tc39.es/ecma262/#sec-iteratorcomplete -/
def iteratorComplete (res : Value) : M Bool := do pure (toBoolean (← getVProp res (.str kDone)))

/-- IteratorValue spec: https://tc39.es/ecma262/#sec-iteratorvalue -/
def iteratorValue (res : Value) : M Value := getVProp res (.str kValue)

/-- IteratorStepValue: the next value, or `none` when done. A throw from `next`, `done` or
`value` marks the record done (the caller must not close it).
spec: https://tc39.es/ecma262/#sec-iteratorstepvalue -/
def iteratorStepValue (r : IterRecord) : M (IterRecord × Option Value) := do
  let res ← M.tryCatch (iteratorNext r) fun e => do
    M.throwV e
  let done ← iteratorComplete res
  if done then return ({ r with done := true }, none)
  let v ← iteratorValue res
  pure (r, some v)

/-- IteratorClose with a normal completion (`completion` is the value to return). With a throw
completion use `iteratorCloseOnThrow`.
spec: https://tc39.es/ecma262/#sec-iteratorclose -/
def iteratorClose (r : IterRecord) : M Unit := do
  let ret ← getMethodOf r.iter (.str "return")
  match ret with
  | none => pure ()
  | some f =>
    let inner ← call f r.iter #[]
    if !inner.isObject then throwType "Iterator result is not an object"

/-- IteratorClose with a throw completion: the original exception wins.
spec: https://tc39.es/ecma262/#sec-iteratorclose -/
def iteratorCloseOnThrow {α} (r : IterRecord) (e : Value) : M α := do
  let _ ← M.attempt do
    match ← getMethodOf r.iter (.str "return") with
    | some f => let _ ← call f r.iter #[]; pure ()
    | none => pure ()
  M.throwV e

/-- Runs `body` and closes the iterator if it throws. -/
def withIterClose {α} (r : IterRecord) (body : M α) : M α :=
  M.tryCatch body fun e =>
    -- (a generator's `return` unwinding (WK.genReturn) is a return completion: errors from
    -- closing propagate)
    match e with
    | .sym 15 => do iteratorClose r; M.throwV e
    | _ => iteratorCloseOnThrow r e

/-- IteratorToList spec: https://tc39.es/ecma262/#sec-iteratortolist -/
def iteratorToList (r : IterRecord) : M (Array Value) :=
  M.repeatFrom (r, (#[] : Array Value)) fun (r, acc) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | some v => pure (.inl (r, acc.push v))
    | none => pure (.inr acc)

/-- Iterates an iterable to a list (GetIterator + IteratorToList). -/
def iterableToList (v : Value) : M (Array Value) := do
  iteratorToList (← getIterator v)

/-! ## Objects -/

/-- EnumerableOwnProperties (`kind`: 0 keys, 1 values, 2 entries)
spec: https://tc39.es/ecma262/#sec-enumerableownproperties -/
def enumerableOwnProperties (o : ObjId) (kind : Nat) : M (Array Value) := do
  let keys ← Obj'.ownPropertyKeys o
  M.foldArr keys #[] fun acc k => do
    let .str s := k | return acc
    match ← Obj'.getOwnProperty o k with
    | some p =>
      if !p.enumerable then return acc
      if kind == 0 then return acc.push (.str s)
      let v ← getProp o k
      if kind == 1 then return acc.push v
      return acc.push (← createArrayFromList #[.str s, v])
    | none => return acc

/-- CopyDataProperties spec: https://tc39.es/ecma262/#sec-copydataproperties -/
def copyDataProperties (target : ObjId) (source : Value) (excluded : Array PropKey) : M Unit := do
  if source.isNullish then return
  let from_ ← toObject source
  let keys ← Obj'.ownPropertyKeys from_
  M.forArr keys fun k => do
    if excluded.contains k then return
    match ← Obj'.getOwnProperty from_ k with
    | some p =>
      if p.enumerable then
        let v ← getProp from_ k
        let _ ← createDataProperty target k v
    | none => pure ()

/-- SetIntegrityLevel (`frozen`: frozen vs sealed) spec: https://tc39.es/ecma262/#sec-setintegritylevel -/
def setIntegrityLevel (o : ObjId) (frozen : Bool) : M Bool := do
  if !(← Obj'.preventExtensions o) then return false
  let keys ← Obj'.ownPropertyKeys o
  M.forArr keys fun k => do
    if !frozen then definePropertyOrThrow o k { configurable := some false }
    else
      match ← Obj'.getOwnProperty o k with
      | some (.accessor ..) => definePropertyOrThrow o k { configurable := some false }
      | some (.data ..) => definePropertyOrThrow o k { configurable := some false, writable := some false }
      | none => pure ()
  pure true

/-- TestIntegrityLevel spec: https://tc39.es/ecma262/#sec-testintegritylevel -/
def testIntegrityLevel (o : ObjId) (frozen : Bool) : M Bool := do
  if ← Obj'.isExtensible o then return false
  let keys ← Obj'.ownPropertyKeys o
  M.foldArr keys true fun acc k => do
    if !acc then return false
    match ← Obj'.getOwnProperty o k with
    | some p =>
      if p.configurable then return false
      match p with
      | .data _ true _ _ => return !frozen
      | _ => return true
    | none => return true

/-! ## Operators (13.15.3) -/

/-- The result of a binary numeric operator on Numbers.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-add (and its siblings) -/
def numberBinOp (op : BinOp) (a b : F64) : F64 :=
  match op with
  | .add => Conv.addF a b
  | .sub => Conv.subF a b
  | .mul => Conv.mulF a b
  | .div => a.div b
  | .mod => NumOps.rem a b
  | .exp => NumOps.pow a b
  | .shl => F64.ofInt (Conv.toInt32 (F64.ofInt (Conv.toInt32 a * 2 ^ (Conv.toUint32 b % 32))))
  | .sar => F64.ofInt (Int.fdiv (Conv.toInt32 a) (2 ^ (Conv.toUint32 b % 32)))
  | .shr => F64.ofInt ((Conv.toUint32 a / 2 ^ (Conv.toUint32 b % 32) : Nat) : Int)
  | .bitAnd => F64.ofInt (Conv.toInt32 (F64.ofInt (Conv.intAnd (Conv.toInt32 a) (Conv.toInt32 b))))
  | .bitOr => F64.ofInt (Conv.toInt32 (F64.ofInt (Conv.intOr (Conv.toInt32 a) (Conv.toInt32 b))))
  | .bitXor => F64.ofInt (Conv.toInt32 (F64.ofInt (Conv.intXor (Conv.toInt32 a) (Conv.toInt32 b))))
  | _ => .nan

/-- The result of a binary operator on BigInts (`.error`: RangeError — division by zero, a
negative exponent, or a result past the engine's BigInt size limit).
spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-add (and its siblings) -/
def bigintBinOp (op : BinOp) (a b : Int) : Except String Int :=
  match op with
  | .add => .ok (a + b)
  | .sub => .ok (a - b)
  | .mul => if Num.BigInt.bitLen a + Num.BigInt.bitLen b > Num.BigInt.maxBits then
      .error "Maximum BigInt size exceeded" else .ok (a * b)
  | .div => Num.BigInt.divide a b
  | .mod => Num.BigInt.remainder a b
  | .exp => Num.BigInt.exponentiate a b
  | .shl => Num.BigInt.leftShift a b
  | .sar => Num.BigInt.signedRightShift a b
  | .bitAnd => .ok (Num.BigInt.bitwiseAND a b)
  | .bitOr => .ok (Num.BigInt.bitwiseOR a b)
  | .bitXor => .ok (Num.BigInt.bitwiseXOR a b)
  | _ => .error "invalid BigInt operator"

/-- ApplyStringOrNumericBinaryOperator spec: https://tc39.es/ecma262/#sec-applystringornumericbinaryoperator -/
def applyBinaryOp (op : BinOp) (l r : Value) : M Value := do
  -- 1.
  let (l, r) ← if op == .add then do
      let lp ← toPrim l
      let rp ← toPrim r
      match lp, rp with
      | .str _, _ | _, .str _ =>
        let ls ← toStr lp
        let rs ← toStr rp
        return .str (ls ++ rs)
      | _, _ => pure (lp, rp)
    else pure (l, r)
  -- 3-4.
  let ln ← toNumeric l
  let rn ← toNumeric r
  match ln, rn with
  | .num a, .num b => pure (.num (numberBinOp op a b))
  | .bigint a, .bigint b =>
    if op == .shr then throwType "BigInts have no unsigned right shift, use >> instead"
    match bigintBinOp op a b with
    | .ok i => pure (.bigint i)
    | .error m => throwRange m
  | _, _ => throwType "Cannot mix BigInt and other types, use explicit conversions"

end ES
