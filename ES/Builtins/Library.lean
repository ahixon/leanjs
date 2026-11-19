import ES.Builtins.Core

/-!
# Map, Set, WeakMap, WeakSet, WeakRef, FinalizationRegistry, Iterator helpers, Promise statics, Date, remaining Object/Function/Error/Reflect members

spec: https://tc39.es/ecma262/#sec-keyed-collections (Map, Set, WeakMap, WeakSet),
https://tc39.es/ecma262/#sec-managing-memory (WeakRef, FinalizationRegistry),
https://tc39.es/ecma262/#sec-iterator-objects (Iterator, iterator helpers),
https://tc39.es/ecma262/#sec-promise-objects (the Promise statics and `finally`),
https://tc39.es/ecma262/#sec-date-objects (Date).

- Map/Set data are `Kind.mapData` (insertion-ordered entries, deleted ones `none` so live
  iterators and `forEach` keep their positions; an index by SameValueZero key, `mapKey`).
- Weak collections hold their keys strongly: there is no garbage collector (docs/es.md L1), so
  `WeakRef.prototype.deref` always returns the target and finalization callbacks never run.
- Iterator helpers are generator-like objects (`Kind.internal "Iterator Helper"`): built-in state
  machines whose slots hold the closure's state between `next` calls, not coroutines.
- Date: the local time zone is UTC. LIMITATION (docs/es.md L4): no host time zone data, so
  LocalTZA is 0 and local time equals UTC; and the pure core has no clock, so the current time
  is the host's `State.hostData` "now" (a Number) when set, else a deterministic clock driven
  by the fuel used (`currentTime`).
-/

namespace ES.Builtins.Library

open ES (F64)

/-! ## Shared helpers -/

def kSize : JSStr := "size"
def kHas : JSStr := "has"
def kKeys : JSStr := "keys"
def kThen : JSStr := "then"
def kResolve : JSStr := "resolve"
def kReturn : JSStr := "return"

/-- A slot holding a non-negative integral Number, as a `Nat` (0 otherwise). -/
def natOf (v : Value) : Nat := match v with
  | .num x => (Conv.toNat? x).getD 0
  | _ => 0

/-- The slots of a `Kind.internal` object. -/
def slotsOf (o : ObjId) : M (Array Value) := readObj o fun ob => match ob.kind with
  | .internal _ s => s
  | _ => #[]

/-- One slot of a `Kind.internal` object. -/
def slotAt (o : ObjId) (i : Nat) : M Value := readObj o fun ob => match ob.kind with
  | .internal _ s => s[i]?.getD .undefined
  | _ => .undefined

def setSlot (o : ObjId) (i : Nat) (v : Value) : M Unit := modifyObj o fun ob => ob.withKind fun k =>
  match k with
  | .internal t s => .internal t (s.set! i v)
  | k => k

/-- The object `v` if it is a `Kind.internal` object with the given tag. -/
def internalWithTag (v : Value) (tag : String) : M (Option ObjId) := do
  let .obj o := v | return none
  let ok ← readObj o fun ob => match ob.kind with
    | .internal t _ => t == tag
    | _ => false
  pure (if ok then some o else none)

/-- Closes `{ [[Iterator]]: o, [[NextMethod]]: undefined }` with a throw completion of a new
error: the iterator helpers' argument validation failures.
spec: https://tc39.es/ecma262/#sec-iteratorclose -/
def closeAndThrow {α} (o : Value) (k : ErrorKind) (msg : String) : M α := do
  let e ← makeError k msg
  iteratorCloseOnThrow { iter := o, next := .undefined } e

/-- IteratorStep without reading the value: whether the iterator is done.
spec: https://tc39.es/ecma262/#sec-iteratorstep -/
def iteratorStepDone (r : IterRecord) : M Bool := do
  let res ← iteratorNext r
  iteratorComplete res

/-! ## Map and Set -/

/-- CanonicalizeKeyedCollectionKey spec: https://tc39.es/ecma262/#sec-canonicalizekeyedcollectionkey -/
def canonKey (v : Value) : Value := match v with
  | .num x => if x.isZero then .num F64.zero else v
  | _ => v

abbrev Entries := Array (Option (Value × Value))

/-- RequireInternalSlot(v, [[MapData]] / [[SetData]] / [[WeakMapData]] / [[WeakSetData]]).
spec: https://tc39.es/ecma262/#sec-requireinternalslot -/
def requireColl (v : Value) (isSet weak : Bool) (what : String) : M ObjId := do
  let .obj o := v | throwType s!"Method {what} called on incompatible receiver"
  let ok ← readObj o fun ob => match ob.kind with
    | .mapData _ _ s w => s == isSet && w == weak
    | _ => false
  if ok then pure o else throwType s!"Method {what} called on incompatible receiver"

def collGet (o : ObjId) (k : Value) : M (Option Value) := readObj o fun ob => match ob.kind with
  | .mapData es idx _ _ => match idx.get? (mapKey k) with
    | some i => match es[i]? with
      | some (some (_, v)) => some v
      | _ => none
    | none => none
  | _ => none

def collHas (o : ObjId) (k : Value) : M Bool := readObj o fun ob => match ob.kind with
  | .mapData _ idx _ _ => idx.contains (mapKey k)
  | _ => false

/-- Sets the entry of `k` (appended if new). -/
def collSet (o : ObjId) (k v : Value) : M Unit := modifyObj o fun ob => ob.withKind fun kd =>
  match kd with
  | .mapData es idx s w =>
    let key := mapKey k
    match idx.get? key with
    | some i => .mapData (es.set! i (some (k, v))) idx s w
    | none =>
      let n := es.size
      .mapData (es.push (some (k, v))) (idx.insert key n) s w
  | kd => kd

/-- Replaces the entry of `k` with empty; whether there was one. -/
def collDelete (o : ObjId) (k : Value) : M Bool := do
  let key := mapKey k
  let found ← readObj o fun ob => match ob.kind with
    | .mapData _ idx _ _ => idx.get? key
    | _ => none
  match found with
  | none => pure false
  | some i =>
    modifyObj o fun ob => ob.withKind fun kd => match kd with
      | .mapData es idx s w => .mapData (es.set! i none) (idx.erase key) s w
      | kd => kd
    pure true

/-- The number of non-empty entries. -/
def collSize (o : ObjId) : M Nat := readObj o fun ob => match ob.kind with
  | .mapData es _ _ _ => es.foldl (fun n e => if e.isSome then n + 1 else n) 0
  | _ => 0

/-- The entry at position `i` (`none`: past the end; `some none`: empty). -/
def collEntryAt (o : ObjId) (i : Nat) : M (Option (Option (Value × Value))) := readObj o fun ob =>
  match ob.kind with
  | .mapData es _ _ _ => es[i]?
  | _ => none

/-- The number of positions (empty ones included): "the number of elements of
O.[[SetData]]". -/
def collLength (o : ObjId) : M Nat := readObj o fun ob => match ob.kind with
  | .mapData es _ _ _ => es.size
  | _ => 0

/-- The first non-empty entry at or after `i`. -/
def nextLive (es : Entries) (i : Nat) : Option (Nat × Value × Value) :=
  if h : i < es.size then
    match es[i] with
    | some (k, v) => some (i, k, v)
    | none => nextLive es (i + 1)
  else none
termination_by es.size - i

/-- AddEntriesFromIterable spec: https://tc39.es/ecma262/#sec-add-entries-from-iterable -/
def addEntriesFromIterable (target : ObjId) (iterable : Value) (adder : Value) : M Value := do
  -- 1.
  let r ← getIterator iterable
  -- 2.
  M.repeatFrom r fun r => do
    -- a-b.
    let (r, next) ← iteratorStepValue r
    match next with
    | none => return .inr (.obj target)
    | some next => withIterClose r do
      -- c.
      let .obj no := next | throwType "Iterator value is not an entry object"
      -- d-g.
      let k ← getProp no (PropKey.ofNat 0)
      let v ← getProp no (PropKey.ofNat 1)
      -- h-i.
      let _ ← call adder (.obj target) #[k, v]
      return .inl r

/-- Adds each value of an iterable with `adder` (the Set and WeakSet constructors' loop).
spec: https://tc39.es/ecma262/#sec-set-iterable -/
def addValuesFromIterable (target : ObjId) (iterable : Value) (adder : Value) : M Value := do
  let r ← getIterator iterable
  M.repeatFrom r fun r => do
    let (r, next) ← iteratorStepValue r
    match next with
    | none => return .inr (.obj target)
    | some next => withIterClose r do
      let _ ← call adder (.obj target) #[next]
      return .inl r

/-- Map(iterable), WeakMap(iterable). spec: https://tc39.es/ecma262/#sec-map-iterable -/
def mapCtor (weak : Bool) : BuiltinFn := fun _ _ args nt => do
  let nm := if weak then "WeakMap" else "Map"
  -- 1.
  if nt.isUndefined then throwType s!"Constructor {nm} requires 'new'"
  -- 2.
  let m ← ordinaryCreateFromConstructor nt s!"%{nm}.prototype%" (.mapData #[] {} false weak)
  -- 3.
  let iterable := arg args 0
  if iterable.isNullish then return .obj m
  -- 4-5.
  let adder ← getProp m (.str "set")
  if !(← isCallable adder) then throwType s!"'{nm}.prototype.set' is not a function"
  -- 6.
  addEntriesFromIterable m iterable adder

/-- Set(iterable), WeakSet(iterable). spec: https://tc39.es/ecma262/#sec-set-iterable -/
def setCtor (weak : Bool) : BuiltinFn := fun _ _ args nt => do
  let nm := if weak then "WeakSet" else "Set"
  -- 1.
  if nt.isUndefined then throwType s!"Constructor {nm} requires 'new'"
  -- 2.
  let s ← ordinaryCreateFromConstructor nt s!"%{nm}.prototype%" (.mapData #[] {} true weak)
  -- 3.
  let iterable := arg args 0
  if iterable.isNullish then return .obj s
  -- 4-5.
  let adder ← getProp s (.str "add")
  if !(← isCallable adder) then throwType s!"'{nm}.prototype.add' is not a function"
  -- 6-7.
  addValuesFromIterable s iterable adder

/-- Map.prototype.clear / Set.prototype.clear: every entry replaced with empty.
spec: https://tc39.es/ecma262/#sec-map.prototype.clear -/
def collClear (isSet : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let o ← requireColl thisV isSet false (if isSet then "Set.prototype.clear" else "Map.prototype.clear")
  modifyObj o fun ob => ob.withKind fun kd => match kd with
    | .mapData es _ s w => .mapData (es.map fun _ => none) {} s w
    | kd => kd
  pure .undefined

/-- Map.prototype.delete / Set.prototype.delete.
spec: https://tc39.es/ecma262/#sec-map.prototype.delete -/
def collDeleteFn (isSet : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV isSet false (if isSet then "Set.prototype.delete" else "Map.prototype.delete")
  pure (.bool (← collDelete o (canonKey (arg args 0))))

/-- Map.prototype.has / Set.prototype.has. spec: https://tc39.es/ecma262/#sec-map.prototype.has -/
def collHasFn (isSet : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV isSet false (if isSet then "Set.prototype.has" else "Map.prototype.has")
  pure (.bool (← collHas o (canonKey (arg args 0))))

/-- Map.prototype.get spec: https://tc39.es/ecma262/#sec-map.prototype.get -/
def mapGet : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV false false "Map.prototype.get"
  pure ((← collGet o (canonKey (arg args 0))).getD .undefined)

/-- Map.prototype.set spec: https://tc39.es/ecma262/#sec-map.prototype.set -/
def mapSet : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV false false "Map.prototype.set"
  -- 3-5.
  collSet o (canonKey (arg args 0)) (arg args 1)
  -- 6.
  pure thisV

/-- Set.prototype.add spec: https://tc39.es/ecma262/#sec-set.prototype.add -/
def setAdd : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV true false "Set.prototype.add"
  let v := canonKey (arg args 0)
  if !(← collHas o v) then collSet o v v
  pure thisV

/-- get Map.prototype.size / get Set.prototype.size.
spec: https://tc39.es/ecma262/#sec-get-map.prototype.size -/
def collSizeFn (isSet : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let o ← requireColl thisV isSet false (if isSet then "get Set.prototype.size" else "get Map.prototype.size")
  pure (numV (← collSize o))

/-- Map.prototype.forEach / Set.prototype.forEach: entries added during the loop are visited,
deleted ones skipped. spec: https://tc39.es/ecma262/#sec-map.prototype.foreach -/
def collForEach (isSet : Bool) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV isSet false (if isSet then "Set.prototype.forEach" else "Map.prototype.forEach")
  -- 3.
  let fn := arg args 0
  if !(← isCallable fn) then throwType "forEach callback is not a function"
  let thisArg := arg args 1
  -- 4-6.
  M.repeatFrom 0 fun i => do
    match ← collEntryAt o i with
    | none => return .inr .undefined
    | some none => return .inl (i + 1)
    | some (some (k, v)) =>
      let _ ← call fn thisArg (if isSet then #[k, k, .obj o] else #[v, k, .obj o])
      return .inl (i + 1)

/-- CreateMapIterator / CreateSetIterator (`kind`: 0 keys, 1 values, 2 entries).
spec: https://tc39.es/ecma262/#sec-createmapiterator -/
def createCollIterator (o : ObjId) (kind : Nat) (isSet : Bool) : M Value := do
  let (tag, proto) := if isSet then ("Set Iterator", "%SetIteratorPrototype%")
    else ("Map Iterator", "%MapIteratorPrototype%")
  let p ← intrinsic proto
  let it ← alloc { proto := .obj p, kind := .internal tag #[.obj o, numV 0, numV kind] }
  pure (.obj it)

/-- Map.prototype.{keys,values,entries}, Set.prototype.{values,entries}.
spec: https://tc39.es/ecma262/#sec-map.prototype.entries -/
def collIterFn (isSet : Bool) (kind : Nat) : BuiltinFn := fun _ thisV _ _ => do
  let o ← requireColl thisV isSet false (if isSet then "Set.prototype.values" else "Map.prototype.entries")
  createCollIterator o kind isSet

/-- %MapIteratorPrototype%.next / %SetIteratorPrototype%.next: the generator closure of
CreateMapIterator as a state machine (the position of the next entry; the collection is
dropped once done). spec: https://tc39.es/ecma262/#sec-%mapiteratorprototype%.next -/
def collIteratorNext (isSet : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let tag := if isSet then "Set Iterator" else "Map Iterator"
  let some it ← internalWithTag thisV tag
    | throwType s!"%{tag}Prototype%.next called on incompatible receiver"
  let sl ← slotsOf it
  let .obj m := sl[0]! | createIterResult .undefined true
  let idx := natOf sl[1]!
  let kind := natOf sl[2]!
  let found ← readObj m fun ob => match ob.kind with
    | .mapData es _ _ _ => nextLive es idx
    | _ => none
  match found with
  | none =>
    setSlot it 0 .undefined
    createIterResult .undefined true
  | some (i, k, v) =>
    setSlot it 1 (numV (i + 1))
    match kind with
    | 0 => createIterResult k false
    | 1 => createIterResult v false
    | _ => createIterResult (← createArrayFromList #[k, v]) false

/-! ### Grouping -/

/-- GroupBy (`propertyKeys`: the PROPERTY key coercion, else ZERO) with AddValueToKeyedGroup.
spec: https://tc39.es/ecma262/#sec-groupby -/
def groupBy (items callback : Value) (propertyKeys : Bool) : M (Array (Value × Array Value)) := do
  -- 1.
  let _ ← requireObjectCoercible items
  -- 2.
  if !(← isCallable callback) then throwType "callback is not a function"
  -- 3-4.
  let r ← getIterator items
  -- 5-6.
  let st : IterRecord × Array (Value × Array Value) × Std.HashMap PropKey Nat × Nat := (r, #[], {}, 0)
  M.repeatFrom st fun (r, groups, index, k) => do
    -- a.
    if k ≥ 9007199254740991 then
      let e ← makeError .typeError "Too many elements to group"
      return ← iteratorCloseOnThrow r e
    -- b-c.
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr groups
    | some value =>
      -- e-f.
      let key ← withIterClose r (call callback .undefined #[value, numV k])
      -- g-h.
      let key ← if propertyKeys then do pure (keyToValue (← withIterClose r (toPropertyKey key)))
        else pure (canonKey key)
      -- i. AddValueToKeyedGroup spec: https://tc39.es/ecma262/#sec-add-value-to-keyed-group
      let mk := mapKey key
      match index.get? mk with
      | some i => return .inl (r, groups.modify i (fun (kk, es) => (kk, es.push value)), index, k + 1)
      | none =>
        let n := groups.size
        return .inl (r, groups.push (key, #[value]), index.insert mk n, k + 1)

/-- Map.groupBy spec: https://tc39.es/ecma262/#sec-map.groupby -/
def mapGroupBy : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let groups ← groupBy (arg args 0) (arg args 1) false
  -- 2.
  let p ← intrinsic "%Map.prototype%"
  let m ← alloc { proto := .obj p, kind := .mapData #[] {} false false }
  -- 3.
  M.forArr groups fun (k, es) => do
    let arr ← createArrayFromList es
    collSet m k arr
  -- 4.
  pure (.obj m)

/-- Object.groupBy spec: https://tc39.es/ecma262/#sec-object.groupby -/
def objectGroupBy : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let groups ← groupBy (arg args 0) (arg args 1) true
  -- 2.
  let o ← ordinaryObjectCreate .null
  -- 3.
  M.forArr groups fun (k, es) => do
    let arr ← createArrayFromList es
    createDataPropertyOrThrow o (← toPropertyKey k) arr
  -- 4.
  pure (.obj o)

/-! ### Set methods -/

/-- A Set Record (`size = none`: +∞). spec: https://tc39.es/ecma262/#sec-set-records -/
structure SetRec where
  obj : Value
  size : Option Nat
  has : Value
  keys : Value

/-- GetSetRecord spec: https://tc39.es/ecma262/#sec-getsetrecord -/
def getSetRecord (v : Value) : M SetRec := do
  -- 1.
  let .obj o := v | throwType "The argument must be a set-like object"
  -- 2.
  let rawSize ← getProp o (.str kSize)
  -- 3-4.
  let numSize ← toNum rawSize
  if numSize == .nan then throwType "The 'size' property must be a number"
  -- 5-6.
  let size ← match Conv.toIntegerOrInf numSize with
    | .inl false => pure none
    | .inl true => throwRange "The 'size' property must not be negative"
    | .inr i => if i < 0 then throwRange "The 'size' property must not be negative" else pure (some i.toNat)
  -- 7-8.
  let has ← getProp o (.str kHas)
  if !(← isCallable has) then throwType "The 'has' property must be a function"
  -- 9-10.
  let keys ← getProp o (.str kKeys)
  if !(← isCallable keys) then throwType "The 'keys' property must be a function"
  -- 11.
  pure { obj := v, size, has, keys }

/-- `n ≤ size` (size +∞ when `none`). -/
def leSize (n : Nat) (size : Option Nat) : Bool := match size with
  | none => true
  | some s => n ≤ s

/-- A new Set of the current realm whose data is a copy of `o`'s (positions kept). -/
def copySet (o : ObjId) : M ObjId := do
  let (es, idx) ← readObj o fun ob => match ob.kind with
    | .mapData es idx _ _ => (es, idx)
    | _ => (#[], {})
  let p ← intrinsic "%Set.prototype%"
  alloc { proto := .obj p, kind := .mapData es idx true false }

def newSet : M ObjId := do
  let p ← intrinsic "%Set.prototype%"
  alloc { proto := .obj p, kind := .mapData #[] {} true false }

/-- Runs `f` on each non-empty element of `o`'s set data in order (elements appended during the
loop are visited), until it returns `some r`. -/
def forEachLive {α} (o : ObjId) (dflt : α) (f : Value → M (Option α)) : M α :=
  M.repeatFrom 0 fun i => do
    match ← collEntryAt o i with
    | none => return .inr dflt
    | some none => return .inl (i + 1)
    | some (some (k, _)) =>
      match ← f k with
      | some r => return .inr r
      | none => return .inl (i + 1)

/-- Runs `f` on each value of an iterator record until it returns `some r` (then the iterator is
not closed by this loop: `f` decides). -/
def forEachKey {α} (r : IterRecord) (dflt : α) (f : Value → M (Option α)) : M α :=
  M.repeatFrom r fun r => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr dflt
    | some v =>
      match ← f (canonKey v) with
      | some x => return .inr x
      | none => return .inl r

/-- Set.prototype.union spec: https://tc39.es/ecma262/#sec-set.prototype.union -/
def setUnion : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.union"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
  -- 5.
  let res ← copySet o
  -- 6-7.
  forEachKey keysIter () fun v => do
    if !(← collHas res v) then collSet res v v
    pure none
  -- 8-9.
  pure (.obj res)

/-- Set.prototype.intersection spec: https://tc39.es/ecma262/#sec-set.prototype.intersection -/
def setIntersection : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.intersection"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  let res ← newSet
  -- 5.
  if leSize (← collSize o) rec_.size then
    forEachLive o () fun e => do
      let inOther := toBoolean (← call rec_.has rec_.obj #[e])
      if inOther then
        let e := canonKey e
        if !(← collHas res e) then collSet res e e
      pure none
  -- 6.
  else
    let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
    forEachKey keysIter () fun v => do
      if (← collHas o v) && !(← collHas res v) then collSet res v v
      pure none
  -- 7-8.
  pure (.obj res)

/-- Set.prototype.difference spec: https://tc39.es/ecma262/#sec-set.prototype.difference -/
def setDifference : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.difference"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  let res ← copySet o
  -- 5.
  if leSize (← collSize o) rec_.size then
    -- a.
    let thisSize ← collLength o
    -- b-c. (over the copy's positions)
    M.forArr (Array.range thisSize) fun i => do
      match ← collEntryAt res i with
      | some (some (e, _)) =>
        if toBoolean (← call rec_.has rec_.obj #[e]) then
          let _ ← collDelete res e
      | _ => pure ()
  -- 6.
  else
    let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
    forEachKey keysIter () fun v => do
      let _ ← collDelete res v
      pure none
  -- 7-8.
  pure (.obj res)

/-- Set.prototype.symmetricDifference
spec: https://tc39.es/ecma262/#sec-set.prototype.symmetricdifference -/
def setSymmetricDifference : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.symmetricDifference"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
  -- 5.
  let res ← copySet o
  -- 6.
  forEachKey keysIter () fun v => do
    let alreadyInResult ← collHas res v
    if ← collHas o v then
      if alreadyInResult then let _ ← collDelete res v
    else if !alreadyInResult then collSet res v v
    pure none
  -- 7-8.
  pure (.obj res)

/-- Set.prototype.isSubsetOf spec: https://tc39.es/ecma262/#sec-set.prototype.issubsetof -/
def setIsSubsetOf : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.isSubsetOf"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  if !leSize (← collSize o) rec_.size then return .bool false
  -- 5-8.
  forEachLive o (Value.bool true) fun e => do
    if !toBoolean (← call rec_.has rec_.obj #[e]) then return some (.bool false)
    pure none

/-- Set.prototype.isSupersetOf spec: https://tc39.es/ecma262/#sec-set.prototype.issupersetof -/
def setIsSupersetOf : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.isSupersetOf"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  let n ← collSize o
  if (match rec_.size with | none => true | some s => n < s) then return .bool false
  -- 5.
  let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
  -- 6.
  forEachKey keysIter (Value.bool true) fun v => do
    if !(← collHas o v) then
      iteratorClose keysIter
      return some (.bool false)
    pure none

/-- Set.prototype.isDisjointFrom spec: https://tc39.es/ecma262/#sec-set.prototype.isdisjointfrom -/
def setIsDisjointFrom : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireColl thisV true false "Set.prototype.isDisjointFrom"
  -- 3.
  let rec_ ← getSetRecord (arg args 0)
  -- 4.
  if leSize (← collSize o) rec_.size then
    forEachLive o (Value.bool true) fun e => do
      if toBoolean (← call rec_.has rec_.obj #[e]) then return some (.bool false)
      pure none
  -- 5.
  else
    let keysIter ← getIteratorFromMethod rec_.obj rec_.keys
    forEachKey keysIter (Value.bool true) fun v => do
      if ← collHas o v then
        iteratorClose keysIter
        return some (.bool false)
      pure none

/-! ## WeakMap, WeakSet, WeakRef, FinalizationRegistry -/

/-- CanBeHeldWeakly spec: https://tc39.es/ecma262/#sec-canbeheldweakly -/
def canBeHeldWeakly (v : Value) : M Bool := match v with
  -- 1.
  | .obj _ => pure true
  -- 2.
  | .sym i => do
    let registered ← readS fun s => s.symRegistry.fold (fun acc _ j => acc || j == i) false
    pure !registered
  -- 3.
  | _ => pure false

/-- WeakMap.prototype.delete / WeakSet.prototype.delete.
spec: https://tc39.es/ecma262/#sec-weakmap.prototype.delete -/
def weakDelete (isSet : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV isSet true (if isSet then "WeakSet.prototype.delete" else "WeakMap.prototype.delete")
  let k := arg args 0
  if !(← canBeHeldWeakly k) then return .bool false
  pure (.bool (← collDelete o k))

/-- WeakMap.prototype.has / WeakSet.prototype.has.
spec: https://tc39.es/ecma262/#sec-weakmap.prototype.has -/
def weakHas (isSet : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV isSet true (if isSet then "WeakSet.prototype.has" else "WeakMap.prototype.has")
  let k := arg args 0
  if !(← canBeHeldWeakly k) then return .bool false
  pure (.bool (← collHas o k))

/-- WeakMap.prototype.get spec: https://tc39.es/ecma262/#sec-weakmap.prototype.get -/
def weakMapGet : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV false true "WeakMap.prototype.get"
  let k := arg args 0
  if !(← canBeHeldWeakly k) then return .undefined
  pure ((← collGet o k).getD .undefined)

/-- WeakMap.prototype.set spec: https://tc39.es/ecma262/#sec-weakmap.prototype.set -/
def weakMapSet : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV false true "WeakMap.prototype.set"
  let k := arg args 0
  if !(← canBeHeldWeakly k) then throwType "Invalid value used as weak map key"
  collSet o k (arg args 1)
  pure thisV

/-- WeakSet.prototype.add spec: https://tc39.es/ecma262/#sec-weakset.prototype.add -/
def weakSetAdd : BuiltinFn := fun _ thisV args _ => do
  let o ← requireColl thisV true true "WeakSet.prototype.add"
  let v := arg args 0
  if !(← canBeHeldWeakly v) then throwType "Invalid value used in weak set"
  if !(← collHas o v) then collSet o v v
  pure thisV

/-- WeakRef(target) spec: https://tc39.es/ecma262/#sec-weak-ref-target -/
def weakRefCtor : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then throwType "Constructor WeakRef requires 'new'"
  -- 2.
  let target := arg args 0
  if !(← canBeHeldWeakly target) then throwType "WeakRef: invalid target"
  -- 3-6. (AddToKeptObjects: everything is kept, docs/es.md L1)
  let o ← ordinaryCreateFromConstructor nt "%WeakRef.prototype%" (.internal "WeakRef" #[target])
  pure (.obj o)

/-- WeakRef.prototype.deref spec: https://tc39.es/ecma262/#sec-weak-ref.prototype.deref -/
def weakRefDeref : BuiltinFn := fun _ thisV _ _ => do
  let some o ← internalWithTag thisV "WeakRef" | throwType "WeakRef.prototype.deref called on incompatible receiver"
  slotAt o 0

/-- FinalizationRegistry(cleanupCallback): slots are the callback, then (target, held value,
unregister token) triples (`undefined` token: empty).
spec: https://tc39.es/ecma262/#sec-finalization-registry-cleanup-callback -/
def finRegCtor : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then throwType "Constructor FinalizationRegistry requires 'new'"
  -- 2.
  let cb := arg args 0
  if !(← isCallable cb) then throwType "FinalizationRegistry: cleanup must be callable"
  -- 3-8.
  let o ← ordinaryCreateFromConstructor nt "%FinalizationRegistry.prototype%" (.internal "FinalizationRegistry" #[cb])
  pure (.obj o)

/-- FinalizationRegistry.prototype.register
spec: https://tc39.es/ecma262/#sec-finalization-registry.prototype.register -/
def finRegRegister : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let some o ← internalWithTag thisV "FinalizationRegistry"
    | throwType "FinalizationRegistry.prototype.register called on incompatible receiver"
  let (target, held, token) := (arg args 0, arg args 1, arg args 2)
  -- 3.
  if !(← canBeHeldWeakly target) then throwType "FinalizationRegistry.prototype.register: invalid target"
  -- 4.
  if sameValue target held then throwType "FinalizationRegistry.prototype.register: target and holdings must not be same"
  -- 5.
  if !(← canBeHeldWeakly token) && !token.isUndefined then
    throwType "FinalizationRegistry.prototype.register: invalid unregister token"
  -- 6-7.
  modifyObj o fun ob => ob.withKind fun k => match k with
    | .internal t s => .internal t ((s.push target).push held |>.push token)
    | k => k
  -- 8.
  pure .undefined

/-- FinalizationRegistry.prototype.unregister
spec: https://tc39.es/ecma262/#sec-finalization-registry.prototype.unregister -/
def finRegUnregister : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let some o ← internalWithTag thisV "FinalizationRegistry"
    | throwType "FinalizationRegistry.prototype.unregister called on incompatible receiver"
  let token := arg args 0
  -- 3.
  if !(← canBeHeldWeakly token) then throwType "Invalid unregisterToken"
  -- 4-5.
  let sl ← slotsOf o
  let cells := (Array.range ((sl.size - 1) / 3)).map fun i => (sl[1 + 3 * i]!, sl[2 + 3 * i]!, sl[3 + 3 * i]!)
  let kept := cells.filter fun (_, _, tk) => tk.isUndefined || !sameValue tk token
  let removed := kept.size != cells.size
  let sl' := kept.foldl (fun acc (a, b, c) => ((acc.push a).push b).push c) #[sl[0]!]
  modifyObj o fun ob => { ob with kind := .internal "FinalizationRegistry" sl' }
  -- 6.
  pure (.bool removed)

/-! ## Iterators -/

/-- Iterator() spec: https://tc39.es/ecma262/#sec-iterator-constructor -/
def iteratorCtor : BuiltinFn := fun self _ _ nt => do
  -- 1.
  if nt.isUndefined || sameValue nt (.obj self) then throwType "Abstract class Iterator not directly constructable"
  -- 2.
  pure (.obj (← ordinaryCreateFromConstructor nt "%Iterator.prototype%"))

/-- GetIteratorFlattenable (`iterateStrings`: ITERATE-STRING-PRIMITIVES, else REJECT-PRIMITIVES).
spec: https://tc39.es/ecma262/#sec-getiteratorflattenable -/
def getIteratorFlattenable (obj : Value) (iterateStrings : Bool) : M IterRecord := do
  -- 1.
  match obj with
  | .obj _ => pure ()
  | .str _ => if !iterateStrings then throwType "Iterator.prototype.flatMap: mapper result is not an object"
  | _ => throwType "Value is not an iterable or an iterator"
  -- 2.
  let method ← getMethodOf obj (.sym WK.iterator)
  -- 3-4.
  let iterator ← match method with
    | none => pure obj
    | some m => call m obj #[]
  -- 5.
  if !iterator.isObject then throwType "Iterator is not an object"
  -- 6.
  getIteratorDirect iterator

/-- Iterator.from spec: https://tc39.es/ecma262/#sec-iterator.from -/
def iteratorFrom : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let r ← getIteratorFlattenable (arg args 0) true
  -- 2-3.
  let ic ← intrinsicV "%Iterator%"
  if ← ordinaryHasInstance ic r.iter then return r.iter
  -- 4-6.
  let p ← intrinsic "%WrapForValidIteratorPrototype%"
  let w ← alloc { proto := .obj p, kind := .internal "WrapForValidIterator" #[r.iter, r.next] }
  pure (.obj w)

/-- %WrapForValidIteratorPrototype%.next
spec: https://tc39.es/ecma262/#sec-%wrapforvaliditeratorprototype%.next -/
def wrapNext : BuiltinFn := fun _ thisV _ _ => do
  let some o ← internalWithTag thisV "WrapForValidIterator" | throwType "next called on incompatible receiver"
  let sl ← slotsOf o
  call sl[1]! sl[0]! #[]

/-- %WrapForValidIteratorPrototype%.return
spec: https://tc39.es/ecma262/#sec-%wrapforvaliditeratorprototype%.return -/
def wrapReturn : BuiltinFn := fun _ thisV _ _ => do
  let some o ← internalWithTag thisV "WrapForValidIterator" | throwType "return called on incompatible receiver"
  let iterator ← slotAt o 0
  match ← getMethodOf iterator (.str kReturn) with
  | none => createIterResult .undefined true
  | some f => call f iterator #[]

/-- get Iterator.prototype.constructor / get Iterator.prototype[@@toStringTag]
spec: https://tc39.es/ecma262/#sec-get-iterator.prototype.constructor -/
def iterProtoCtorGet : BuiltinFn := fun _ _ _ _ => intrinsicV "%Iterator%"

/-- spec: https://tc39.es/ecma262/#sec-get-iterator.prototype-%symbol.tostringtag% -/
def iterProtoTagGet : BuiltinFn := fun _ _ _ _ => pure (.str "Iterator")

/-- SetterThatIgnoresPrototypeProperties(this, home, p, v) (`home`: an intrinsic's name).
spec: https://tc39.es/ecma262/#sec-SetterThatIgnoresPrototypeProperties -/
def setterThatIgnoresPrototypeProperties (thisV : Value) (homeName : String) (p : PropKey) (v : Value) : M Unit := do
  let home ← intrinsic homeName
  -- 1.
  let .obj o := thisV | throwType "setter called on non-object"
  -- 2.
  if o == home then throwType "Cannot assign to read only property of a prototype object"
  -- 3-5.
  match ← Obj'.getOwnProperty o p with
  | none => createDataPropertyOrThrow o p v
  | some _ => setProp o p v

/-- set Iterator.prototype.constructor / set Iterator.prototype[@@toStringTag]
spec: https://tc39.es/ecma262/#sec-set-iterator.prototype.constructor -/
def setterIgnoringProto (p : PropKey) : BuiltinFn := fun _ thisV args _ => do
  setterThatIgnoresPrototypeProperties thisV "%Iterator.prototype%" p (arg args 0)
  pure .undefined

/-! ## Error.prototype.stack (the error-stack-accessor proposal) -/

def kStack : JSStr := "stack"

/-- get Error.prototype.stack: an implementation-defined string (here empty: the engine keeps no
call stacks) for objects with [[ErrorData]].
spec: https://tc39.es/proposal-error-stack-accessor/#sec-get-error.prototype.stack -/
def errorStackGet : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let .obj o := thisV | throwType "Error.prototype.stack getter called on non-object"
  -- 3.
  match ← objKind o with
  | .error => pure (.str JSStr.empty)
  | _ => pure .undefined

/-- set Error.prototype.stack spec: https://tc39.es/proposal-error-stack-accessor/#sec-set-error.prototype.stack -/
def errorStackSet : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  if !thisV.isObject then throwType "Error.prototype.stack setter called on non-object"
  -- 3.
  let v := arg args 0
  let .str _ := v | throwType "Error.prototype.stack must be set to a string"
  -- 4.
  setterThatIgnoresPrototypeProperties thisV "%Error.prototype%" (.str kStack) v
  pure .undefined

/-- %Iterator.prototype%[@@dispose] spec: https://tc39.es/ecma262/#sec-%iteratorprototype%-%symbol.dispose% -/
def iterProtoDispose : BuiltinFn := fun _ thisV _ _ => do
  match ← getMethodOf thisV (.str kReturn) with
  | some f => let _ ← call f thisV #[]; pure .undefined
  | none => pure .undefined

/-- %AsyncIteratorPrototype%[@@asyncDispose]
spec: https://tc39.es/ecma262/#sec-%asynciteratorprototype%-%symbol.asyncdispose% -/
def asyncIterProtoDispose : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let pc ← intrinsicV "%Promise%"
  let cap ← newPromiseCapability pc
  let reject (e : Value) : M Value := do let _ ← call cap.reject .undefined #[e]; pure cap.promise
  -- 3-4.
  match ← M.attempt (getMethodOf thisV (.str kReturn)) with
  | .error e => reject e
  -- 5.
  | .ok none => let _ ← call cap.resolve .undefined #[.undefined]; pure cap.promise
  -- 6.
  | .ok (some f) =>
    match ← M.attempt (do let res ← call f thisV #[]; promiseResolve pc res) with
    | .error e => reject e
    | .ok w =>
      let .obj wo := w | reject w
      let unwrap ← makeBuiltinFn "AsyncIteratorDisposeUnwrap" 1 JSStr.empty
      let _ ← performPromiseThen wo (.obj unwrap) .undefined (some cap)
      pure cap.promise

/-! ### Iterator helper objects

Slots: 0 kind (0 map, 1 filter, 2 take, 3 drop, 4 flatMap, 5 chunks, 6 windows), 1 generator
state (0 suspended-start, 1 suspended-yield, 2 executing, 3 completed), 2–3 the underlying
iterator record, 4 the function or size, 5 the counter or remaining count (+∞ allowed),
6–7 flatMap's inner iterator record (`undefined`: none) or windows' "allow-partial" flag,
8 chunks/windows "final value yielded", 9… the chunks/windows buffer. -/

def helperTag : String := "Iterator Helper"

/-- CreateIteratorFromClosure(closure, "Iterator Helper", %IteratorHelperPrototype%) with
[[UnderlyingIterator]] = `r`. spec: https://tc39.es/ecma262/#sec-createiteratorfromclosure -/
def createHelper (kind : Nat) (r : IterRecord) (fn count : Value) (extra : Value := .undefined) : M Value := do
  let p ← intrinsic "%IteratorHelperPrototype%"
  let slots : Array Value := #[numV kind, numV 0, r.iter, r.next, fn, count, extra, .undefined, .bool false]
  let o ← alloc { proto := .obj p, kind := .internal helperTag slots }
  pure (.obj o)

def remIsZero (v : Value) : Bool := match v with
  | .num (.inf _) => false
  | _ => natOf v == 0

def remDec (v : Value) : Value := match v with
  | .num (.inf _) => v
  | _ => numV (natOf v - 1)

def helperBuf (h : ObjId) : M (Array Value) := do
  let sl ← slotsOf h
  pure (sl.extract 9 sl.size)

def setHelperBuf (h : ObjId) (buf : Array Value) : M Unit := modifyObj h fun ob => ob.withKind fun k =>
  match k with
  | .internal t s => .internal t (s.extract 0 9 ++ buf)
  | k => k

/-- Runs an iterator helper's closure from where it is suspended to its next Yield (`some v`)
or its return (`none`): the closures of Iterator.prototype.map, filter, take, drop, flatMap
(spec: https://tc39.es/ecma262/#sec-iterator.prototype.map and the following sections) and
chunks, windows (spec: https://tc39.es/proposal-iterator-chunking/#sec-iterator.prototype.chunks). -/
def helperRun (h : ObjId) : M (Option Value) := do
  let sl ← slotsOf h
  let kind := natOf sl[0]!
  let r : IterRecord := { iter := sl[2]!, next := sl[3]! }
  let fn := sl[4]!
  match kind with
  | 0 =>
    -- map 5.b: value, mapped, Yield(mapped)
    let (_, v) ← iteratorStepValue r
    let some v := v | return none
    let counter ← slotAt h 5
    let mapped ← withIterClose r (call fn .undefined #[v, counter])
    setSlot h 5 (numV (natOf counter + 1))
    return some mapped
  | 1 =>
    -- filter 5.b
    M.repeatFrom () fun _ => do
      let (_, v) ← iteratorStepValue r
      let some v := v | return .inr none
      let counter ← slotAt h 5
      let selected ← withIterClose r (call fn .undefined #[v, counter])
      setSlot h 5 (numV (natOf counter + 1))
      if toBoolean selected then return .inr (some v) else return .inl ()
  | 2 =>
    -- take 10.b
    let rem ← slotAt h 5
    if remIsZero rem then
      iteratorClose r
      return none
    setSlot h 5 (remDec rem)
    let (_, v) ← iteratorStepValue r
    return v
  | 3 =>
    -- drop 10.b: skip, then yield the rest
    let done ← M.repeatFrom () fun _ => do
      let rem ← slotAt h 5
      if remIsZero rem then return .inr false
      setSlot h 5 (remDec rem)
      if ← iteratorStepDone r then return .inr true
      return .inl ()
    if done then return none
    let (_, v) ← iteratorStepValue r
    return v
  | 4 =>
    -- flatMap 5.b
    M.repeatFrom () fun _ => do
      let inner ← slotAt h 6
      if inner.isUndefined then
        let (_, v) ← iteratorStepValue r
        let some v := v | return .inr none
        let counter ← slotAt h 5
        let mapped ← withIterClose r (call fn .undefined #[v, counter])
        let ir ← withIterClose r (getIteratorFlattenable mapped false)
        setSlot h 6 ir.iter
        setSlot h 7 ir.next
        setSlot h 5 (numV (natOf counter + 1))
        return .inl ()
      else
        let ir : IterRecord := { iter := inner, next := ← slotAt h 7 }
        let (_, v) ← withIterClose r (iteratorStepValue ir)
        match v with
        | none =>
          setSlot h 6 .undefined
          return .inl ()
        | some v => return .inr (some v)
  | 5 =>
    -- chunks
    if toBoolean sl[8]! then return none
    let size := natOf fn
    M.repeatFrom () fun _ => do
      let (_, v) ← iteratorStepValue r
      match v with
      | none =>
        let buf ← helperBuf h
        if buf.size > 0 then
          setSlot h 8 (.bool true)
          setHelperBuf h #[]
          return .inr (some (← createArrayFromList buf))
        return .inr none
      | some v =>
        let buf := (← helperBuf h).push v
        if buf.size == size then
          setHelperBuf h #[]
          return .inr (some (← createArrayFromList buf))
        setHelperBuf h buf
        return .inl ()
  | _ =>
    -- windows
    if toBoolean sl[8]! then return none
    let size := natOf fn
    let allowPartial := toBoolean sl[6]!
    M.repeatFrom () fun _ => do
      let (_, v) ← iteratorStepValue r
      match v with
      | none =>
        let buf ← helperBuf h
        if allowPartial && buf.size > 0 && buf.size < size then
          setSlot h 8 (.bool true)
          return .inr (some (← createArrayFromList buf))
        return .inr none
      | some v =>
        let buf ← helperBuf h
        let buf := if buf.size == size then buf.extract 1 buf.size else buf
        let buf := buf.push v
        setHelperBuf h buf
        if buf.size == size then return .inr (some (← createArrayFromList buf))
        return .inl ()

def requireHelper (thisV : Value) : M ObjId := do
  let some h ← internalWithTag thisV helperTag | throwType "Iterator Helper method called on incompatible receiver"
  pure h

/-- %IteratorHelperPrototype%.next: GeneratorResume(this, undefined, "Iterator Helper").
spec: https://tc39.es/ecma262/#sec-%iteratorhelperprototype%.next -/
def helperNext : BuiltinFn := fun _ thisV _ _ => do
  let h ← requireHelper thisV
  -- GeneratorValidate
  let st := natOf (← slotAt h 1)
  if st == 2 then throwType "Generator is already running"
  if st == 3 then return ← createIterResult .undefined true
  setSlot h 1 (numV 2)
  match ← M.attempt (helperRun h) with
  | .ok (some v) =>
    setSlot h 1 (numV 1)
    createIterResult v false
  | .ok none =>
    setSlot h 1 (numV 3)
    createIterResult .undefined true
  | .error e =>
    setSlot h 1 (numV 3)
    M.throwV e

/-- %IteratorHelperPrototype%.return
spec: https://tc39.es/ecma262/#sec-%iteratorhelperprototype%.return -/
def helperReturn : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let h ← requireHelper thisV
  let sl ← slotsOf h
  let st := natOf sl[1]!
  let r : IterRecord := { iter := sl[2]!, next := sl[3]! }
  -- 4.
  if st == 0 then
    setSlot h 1 (numV 3)
    iteratorClose r
    return ← createIterResult .undefined true
  -- 5-6. GeneratorResumeAbrupt(O, return completion): the suspended Yield's
  -- IfAbruptCloseIterator closes the iterators.
  if st == 2 then throwType "Generator is already running"
  if st == 3 then return ← createIterResult .undefined true
  setSlot h 1 (numV 2)
  let inner := sl[6]!
  let res ← M.attempt do
    if natOf sl[0]! == 4 && !inner.isUndefined then
      -- flatMap: close the inner iterator, then the outer one
      match ← M.attempt (iteratorClose { iter := inner, next := sl[7]! }) with
      | .error e => iteratorCloseOnThrow r e
      | .ok () => iteratorClose r
    else iteratorClose r
  setSlot h 1 (numV 3)
  match res with
  | .error e => M.throwV e
  | .ok () => createIterResult .undefined true

/-- The receiver of an Iterator.prototype method (steps 1-2: an Object). -/
def iterThis (thisV : Value) (what : String) : M Value := do
  let .obj _ := thisV | throwType s!"Iterator.prototype.{what} called on non-object"
  pure thisV

/-- Iterator.prototype.map (0), filter (1), flatMap (4).
spec: https://tc39.es/ecma262/#sec-iterator.prototype.map -/
def iterProtoMapLike (kind : Nat) (what : String) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← iterThis thisV what
  -- 3-4.
  let fn := arg args 0
  if !(← isCallable fn) then closeAndThrow o .typeError s!"Iterator.prototype.{what}: argument is not a function"
  -- 5.
  let r ← getIteratorDirect o
  -- 6-9.
  createHelper kind r fn (numV 0)

/-- Iterator.prototype.take (2) / drop (3). spec: https://tc39.es/ecma262/#sec-iterator.prototype.take -/
def iterProtoTakeDrop (kind : Nat) (what : String) : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let o ← iterThis thisV what
  -- 4-5.
  let numLimit ← M.tryCatch (toNum (arg args 0)) fun e => iteratorCloseOnThrow { iter := o, next := .undefined } e
  -- 6.
  if numLimit == .nan then closeAndThrow o .rangeError s!"Iterator.prototype.{what}: limit must be a number"
  -- 7-8.
  let lim ← match Conv.toIntegerOrInf numLimit with
    | .inl false => pure (Value.num (.inf false))
    | .inl true => closeAndThrow o .rangeError s!"Iterator.prototype.{what}: limit must be positive"
    | .inr i =>
      if i < 0 then closeAndThrow o .rangeError s!"Iterator.prototype.{what}: limit must be positive"
      else if i > 9007199254740991 then closeAndThrow o .rangeError s!"Iterator.prototype.{what}: limit is too large"
      else pure (numV i.toNat)
  -- 9.
  let r ← getIteratorDirect o
  -- 10-13.
  createHelper kind r .undefined lim

/-- The chunk/window size argument: an integral Number in [1, 2^32 − 1].
spec: https://tc39.es/proposal-iterator-chunking/#sec-iterator.prototype.chunks -/
def chunkSizeArg (o : Value) (v : Value) (what : String) : M Nat := do
  match v with
  | .num x =>
    if x == .nan || !Conv.isIntegral x then closeAndThrow o .typeError s!"Iterator.prototype.{what}: size must be an integral number"
    let i := (Conv.truncInt x).getD 0
    if i < 1 || i > 4294967295 then closeAndThrow o .rangeError s!"Iterator.prototype.{what}: size out of range"
    pure i.toNat
  | _ => closeAndThrow o .typeError s!"Iterator.prototype.{what}: size must be a number"

/-- Iterator.prototype.chunks spec: https://tc39.es/proposal-iterator-chunking/#sec-iterator.prototype.chunks -/
def iterProtoChunks : BuiltinFn := fun _ thisV args _ => do
  let o ← iterThis thisV "chunks"
  let size ← chunkSizeArg o (arg args 0) "chunks"
  let r ← getIteratorDirect o
  createHelper 5 r (numV size) .undefined

/-- Iterator.prototype.windows spec: https://tc39.es/proposal-iterator-chunking/#sec-iterator.prototype.windows -/
def iterProtoWindows : BuiltinFn := fun _ thisV args _ => do
  let o ← iterThis thisV "windows"
  let size ← chunkSizeArg o (arg args 0) "windows"
  let allowPartial ← match arg args 1 with
    | .undefined => pure false
    | .str s =>
      if s == JSStr.ofString "only-full" then pure false
      else if s == JSStr.ofString "allow-partial" then pure true
      else closeAndThrow o .typeError "Iterator.prototype.windows: invalid 'undersized' value"
    | _ => closeAndThrow o .typeError "Iterator.prototype.windows: invalid 'undersized' value"
  let r ← getIteratorDirect o
  createHelper 6 r (numV size) .undefined (.bool allowPartial)

/-- Iterator.prototype.reduce spec: https://tc39.es/ecma262/#sec-iterator.prototype.reduce -/
def iterProtoReduce : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← iterThis thisV "reduce"
  -- 3-4.
  let fn := arg args 0
  if !(← isCallable fn) then closeAndThrow o .typeError "Iterator.prototype.reduce: argument is not a function"
  -- 5.
  let r ← getIteratorDirect o
  -- 6-7.
  let (r, acc, counter) ← if args.size < 2 then do
      let (r, v) ← iteratorStepValue r
      match v with
      | none => throwType "Reduce of empty iterator with no initial value"
      | some v => pure (r, v, 1)
    else pure (r, args[1]!, 0)
  -- 8.
  M.repeatFrom (r, acc, counter) fun (r, acc, counter) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr acc
    | some v =>
      let acc ← withIterClose r (call fn .undefined #[acc, v, numV counter])
      return .inl (r, acc, counter + 1)

/-- Iterator.prototype.toArray spec: https://tc39.es/ecma262/#sec-iterator.prototype.toarray -/
def iterProtoToArray : BuiltinFn := fun _ thisV _ _ => do
  let o ← iterThis thisV "toArray"
  let r ← getIteratorDirect o
  createArrayFromList (← iteratorToList r)

/-- Iterator.prototype.some (0), every (1), find (2), forEach (3).
spec: https://tc39.es/ecma262/#sec-iterator.prototype.some -/
def iterProtoSearch (mode : Nat) (what : String) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← iterThis thisV what
  -- 3-4.
  let fn := arg args 0
  if !(← isCallable fn) then closeAndThrow o .typeError s!"Iterator.prototype.{what}: argument is not a function"
  -- 5.
  let r ← getIteratorDirect o
  -- 6.
  M.repeatFrom (r, 0) fun (r, counter) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr (match mode with | 0 => .bool false | 1 => .bool true | _ => .undefined)
    | some v =>
      let res ← withIterClose r (call fn .undefined #[v, numV counter])
      match mode with
      | 0 =>
        if toBoolean res then
          iteratorClose r
          return .inr (.bool true)
      | 1 =>
        if !toBoolean res then
          iteratorClose r
          return .inr (.bool false)
      | 2 =>
        if toBoolean res then
          iteratorClose r
          return .inr v
      | _ => pure ()
      return .inl (r, counter + 1)

/-- Iterator.prototype.includes spec: https://tc39.es/proposal-iterator-includes/#sec-iterator.prototype.includes -/
def iterProtoIncludes : BuiltinFn := fun _ thisV args _ => do
  let o ← iterThis thisV "includes"
  let search := arg args 0
  -- the number of elements to skip (`none`: +∞)
  let toSkip : Option Nat ← match arg args 1 with
    | .undefined => pure (some 0)
    | .num x =>
      match x with
      | .nan => closeAndThrow o .typeError "Iterator.prototype.includes: skippedElements must be an integer"
      | .inf false => pure none
      | .inf true => closeAndThrow o .rangeError "Iterator.prototype.includes: skippedElements must not be negative"
      | _ =>
        if !Conv.isIntegral x then closeAndThrow o .typeError "Iterator.prototype.includes: skippedElements must be an integer"
        let i := (Conv.truncInt x).getD 0
        if i < 0 then closeAndThrow o .rangeError "Iterator.prototype.includes: skippedElements must not be negative"
        if i > 9007199254740991 then closeAndThrow o .rangeError "Iterator.prototype.includes: skippedElements is too large"
        pure (some i.toNat)
    | _ => closeAndThrow o .typeError "Iterator.prototype.includes: skippedElements must be a number"
  let r ← getIteratorDirect o
  M.repeatFrom (r, 0) fun (r, skipped) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr (.bool false)
    | some v =>
      let skip := match toSkip with
        | none => true
        | some n => skipped < n
      if skip then return .inl (r, skipped + 1)
      if sameValueZero v search then
        iteratorClose r
        return .inr (.bool true)
      return .inl (r, skipped)

/-- Iterator.prototype.join spec: https://tc39.es/proposal-iterator-join/#sec-iterator.prototype.join -/
def iterProtoJoin : BuiltinFn := fun _ thisV args _ => do
  let o ← iterThis thisV "join"
  let sepV := arg args 0
  let sep ← if sepV.isUndefined then pure (JSStr.ofString ",") else
    M.tryCatch (toStr sepV) fun e => iteratorCloseOnThrow { iter := o, next := .undefined } e
  let r ← getIteratorDirect o
  M.repeatFrom (r, (#[] : Array JSStr)) fun (r, parts) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr (Value.str (JSStr.join parts sep))
    | some v =>
      let s ← if v.isNullish then pure JSStr.empty else withIterClose r (toStr v)
      return .inl (r, parts.push s)

/-! ## Promise statics -/

/-- GetPromiseResolve spec: https://tc39.es/ecma262/#sec-getpromiseresolve -/
def getPromiseResolve (c : Value) : M Value := do
  -- 1.
  let r ← getVProp c (.str kResolve)
  -- 2.
  if !(← isCallable r) then throwType "Promise resolve is not a function"
  -- 3.
  pure r

/-- A new AggregateError with the given errors (no message).
spec: https://tc39.es/ecma262/#sec-performpromiseany -/
def newAggregateError (errors : Array Value) : M Value := do
  let proto ← intrinsic "%AggregateError.prototype%"
  let e ← alloc { proto := .obj proto, kind := .error }
  let arr ← createArrayFromList errors
  definePropertyOrThrow e (.str "errors") (PropDesc.data arr true false true)
  pure (.obj e)

/-- The resolve/reject element functions of Promise.all (0), allSettled fulfilled (1) and
rejected (2), and Promise.any's reject element functions (3). Slots: the shared
[[AlreadyCalled]] record, [[Index]], the combinator's record (slot 0 the remaining elements
count, then the values or errors), the capability's resolve and reject.
spec: https://tc39.es/ecma262/#sec-promise.all-resolve-element-functions -/
def promiseElement (mode : Nat) : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let (.obj ac, index, .obj rec_, capResolve, capReject) := (s[0]!, natOf s[1]!, s[2]!, s[3]!, s[4]!)
    | M.halt "internal: promise element function slots"
  -- 1-3.
  let called ← readObj ac fun o => match o.kind with
    | .internal _ s => toBoolean (s[0]?.getD (.bool false))
    | _ => true
  if called then return .undefined
  modifyObj ac fun o => { o with kind := .internal "AlreadyCalled" #[.bool true] }
  -- 4-8.
  let x := arg args 0
  let v ← match mode with
    | 1 | 2 =>
      let o ← newObject
      createDataPropertyOrThrow o (.str "status") (.str (if mode == 1 then "fulfilled" else "rejected"))
      createDataPropertyOrThrow o (.str (if mode == 1 then "value" else "reason")) x
      pure (Value.obj o)
    | _ => pure x
  setSlot rec_ (index + 1) v
  -- 9-10.
  let remaining := natOf (← slotAt rec_ 0) - 1
  setSlot rec_ 0 (numV remaining)
  if remaining == 0 then
    let vals := (← slotsOf rec_).extract 1
    if mode == 3 then
      let err ← newAggregateError vals
      return ← call capReject .undefined #[err]
    return ← call capResolve .undefined #[← createArrayFromList vals]
  -- 11.
  pure .undefined

/-- PerformPromiseAll (0), PerformPromiseAllSettled (1), PerformPromiseAny (2),
PerformPromiseRace (3). An abrupt completion is returned with whether the iterator is done.
spec: https://tc39.es/ecma262/#sec-performpromiseall -/
def performCombinator (which : Nat) (r : IterRecord) (c : Value) (cap : Capability) (promiseResolve : Value) :
    M (Except (Value × Bool) Value) := do
  -- 1-3. (values/errors and remainingElementsCount, in one record)
  let rec_ ← alloc { kind := .internal "PromiseCombinator" #[numV 1] }
  -- 4.
  M.repeatFrom (r, 0) fun (r, index) => do
    -- a.
    match ← M.attempt (iteratorStepValue r) with
    | .error e => return .inr (.error (e, true))
    | .ok (_, none) =>
      -- b.
      if which == 3 then return .inr (.ok cap.promise)
      let fin ← M.attempt do
        let remaining := natOf (← slotAt rec_ 0) - 1
        setSlot rec_ 0 (numV remaining)
        if remaining == 0 then
          let vals := (← slotsOf rec_).extract 1
          if which == 2 then M.throwV (← newAggregateError vals)
          let _ ← call cap.resolve .undefined #[← createArrayFromList vals]
      match fin with
      | .error e => return .inr (.error (e, true))
      | .ok () => return .inr (.ok cap.promise)
    | .ok (r, some next) =>
      let step ← M.attempt do
        -- d.
        if which != 3 then
          modifyObj rec_ fun o => o.withKind fun k => match k with
            | .internal t s => .internal t (s.push .undefined)
            | k => k
        let nextPromise ← call promiseResolve c #[next]
        if which == 3 then
          let _ ← invoke nextPromise (.str kThen) #[cap.resolve, cap.reject]
          return
        -- e-k.
        let ac ← alloc { kind := .internal "AlreadyCalled" #[.bool false] }
        let slots : Array Value := #[.obj ac, numV index, .obj rec_, cap.resolve, cap.reject]
        let mk (mode : Nat) : M Value := do
          pure (.obj (← makeBuiltinFn s!"PromiseElement{mode}" 1 JSStr.empty slots))
        -- l.
        let remaining := natOf (← slotAt rec_ 0)
        setSlot rec_ 0 (numV (remaining + 1))
        -- m.
        match which with
        | 0 => let _ ← invoke nextPromise (.str kThen) #[← mk 0, cap.reject]
        | 1 =>
          let onF ← mk 1
          let onR ← mk 2
          let _ ← invoke nextPromise (.str kThen) #[onF, onR]
        | _ => let _ ← invoke nextPromise (.str kThen) #[cap.resolve, ← mk 3]
      match step with
      | .error e => return .inr (.error (e, false))
      | .ok () => return .inl (r, index + 1)

/-- Promise.all (0), allSettled (1), any (2), race (3).
spec: https://tc39.es/ecma262/#sec-promise.all -/
def promiseCombinator (which : Nat) : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let c := thisV
  -- 2.
  let cap ← newPromiseCapability c
  let rejectWith (e : Value) : M Value := do
    let _ ← call cap.reject .undefined #[e]
    pure cap.promise
  -- 3-4.
  match ← M.attempt (getPromiseResolve c) with
  | .error e => rejectWith e
  | .ok pr =>
  -- 5-6.
  match ← M.attempt (getIterator (arg args 0)) with
  | .error e => rejectWith e
  | .ok r =>
  -- 7.
  match ← performCombinator which r c cap pr with
  | .ok v => pure v
  | .error (e, done) =>
    -- 8.
    if !done then
      let _ ← M.attempt (iteratorCloseOnThrow (α := Unit) r e)
    rejectWith e

/-- Promise.withResolvers spec: https://tc39.es/ecma262/#sec-promise.withResolvers -/
def promiseWithResolvers : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let cap ← newPromiseCapability thisV
  -- 3-6.
  let o ← newObject
  createDataPropertyOrThrow o (.str "promise") cap.promise
  createDataPropertyOrThrow o (.str "resolve") cap.resolve
  createDataPropertyOrThrow o (.str "reject") cap.reject
  pure (.obj o)

/-- Promise.try: a promise the callback's value resolves (a promise of the receiver is returned
as is), or one its exception rejects.
spec: https://tc39.es/ecma262/#sec-promise.try -/
def promiseTry : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  if !thisV.isObject then throwType "Promise.try called on non-object"
  -- 3.
  match ← M.attempt (call (arg args 0) .undefined (args.extract 1 args.size)) with
  -- 4.
  | .error e =>
    let cap ← newPromiseCapability thisV
    let _ ← call cap.reject .undefined #[e]
    pure cap.promise
  -- 5.
  | .ok v => promiseResolve thisV v

/-- Promise.prototype.finally spec: https://tc39.es/ecma262/#sec-promise.prototype.finally -/
def promiseProtoFinally : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj p := thisV | throwType "Promise.prototype.finally called on non-object"
  -- 3-4.
  let c ← speciesConstructor p (← intrinsicV "%Promise%")
  -- 5-6.
  let onFinally := arg args 0
  let (tf, cf) ← if !(← isCallable onFinally) then pure (onFinally, onFinally) else do
    let tf ← makeBuiltinFn "Promise.thenFinally" 1 JSStr.empty #[onFinally, c]
    let cf ← makeBuiltinFn "Promise.catchFinally" 1 JSStr.empty #[onFinally, c]
    pure (Value.obj tf, Value.obj cf)
  -- 7.
  invoke thisV (.str kThen) #[tf, cf]

/-- The thenFinally (`isCatch` false) and catchFinally closures of Promise.prototype.finally.
spec: https://tc39.es/ecma262/#sec-promise.prototype.finally -/
def promiseFinallyFn (isCatch : Bool) : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let (onFinally, c) := (s[0]!, s[1]!)
  let value := arg args 0
  -- i-ii.
  let result ← call onFinally .undefined #[]
  -- iii.
  let p ← promiseResolve c result
  -- iv-vi.
  let thunk ← makeBuiltinFn (if isCatch then "Promise.thrower" else "Promise.valueThunk") 0 JSStr.empty #[value]
  invoke p (.str kThen) #[.obj thunk]

/-! ## Date -/

/-- LocalTZA: LIMITATION (docs/es.md L4) the local time zone is UTC. -/
def localOffset : Int := 0

/-- LocalTime spec: https://tc39.es/ecma262/#sec-localtime -/
def localTime (t : F64) : F64 :=
  if localOffset == 0 || !t.isFinite then t else F64.add t (F64.ofInt localOffset)

/-- UTC(t) spec: https://tc39.es/ecma262/#sec-utc-t -/
def utcTime (t : F64) : F64 :=
  if localOffset == 0 || !t.isFinite then t else F64.sub t (F64.ofInt localOffset)

/-- The epoch of the deterministic clock (2023-11-14T22:13:20Z), in ms. -/
def clockBase : Nat := 1700000000000

/-- The current time value: the host's `hostData` "now" when set; else a deterministic clock
that advances with the work done. LIMITATION (docs/es.md L4): the pure core has no clock, so
time is `clockBase` plus one millisecond per 1000 steps of fuel used (fuel only decreases, so
the clock is monotonic and busy-waiting loops on `Date.now()` terminate).
spec: https://tc39.es/ecma262/#sec-date.now -/
def currentTime : M F64 := do
  match ← readS (·.hostData.get? "now") with
  | some (.num x) => pure (Num.Date.timeClip x)
  | _ =>
    let fuel ← readS (·.fuel)
    pure (F64.ofInt (clockBase + (1000000000000 - min fuel 1000000000000) / 1000))

/-- thisTimeValue / RequireInternalSlot(this, [[DateValue]]).
spec: https://tc39.es/ecma262/#sec-thistimevalue -/
def thisDate (v : Value) : M (ObjId × F64) := do
  let .obj o := v | throwType "this is not a Date object."
  match ← objKind o with
  | .date t => pure (o, t)
  | _ => throwType "this is not a Date object."

def setDateValue (o : ObjId) (t : F64) : M Unit := modifyObj o fun ob => { ob with kind := .date t }

def nanV : Value := .num .nan

/-- Date(...values) spec: https://tc39.es/ecma262/#sec-date -/
def dateCtor : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if nt.isUndefined then
    return .str (JSStr.ofString (Num.Date.toDateString (← currentTime) localOffset))
  -- 2-5.
  let dv ← match args.size with
    | 0 => currentTime
    | 1 => do
      let value := args[0]!
      let dateTv ← match value with
        | .obj o => do
          match ← objKind o with
          | .date t => pure (some t)
          | _ => pure none
        | _ => pure none
      let tv ← match dateTv with
        | some t => pure t
        | none => do
          let v ← toPrim value
          match v with
          | .str s => pure (Num.Date.parse s localOffset)
          | _ => toNum v
      pure (Num.Date.timeClip tv)
    | _ => do
      let y ← toNum args[0]!
      let m ← toNum args[1]!
      let opt (i : Nat) (d : F64) : M F64 := if args.size > i then toNum args[i]! else pure d
      let dt ← opt 2 Num.one
      let h ← opt 3 F64.zero
      let mi ← opt 4 F64.zero
      let s ← opt 5 F64.zero
      let milli ← opt 6 F64.zero
      let yr := Num.Date.makeFullYear y
      let finalDate := Num.Date.makeDate (Num.Date.makeDay yr m dt) (Num.Date.makeTime h mi s milli)
      pure (Num.Date.timeClip (utcTime finalDate))
  -- 6-8.
  let o ← ordinaryCreateFromConstructor nt "%Date.prototype%" (.date dv)
  pure (.obj o)

/-- Date.now spec: https://tc39.es/ecma262/#sec-date.now -/
def dateNow : BuiltinFn := fun _ _ _ _ => do pure (.num (← currentTime))

/-- Date.parse spec: https://tc39.es/ecma262/#sec-date.parse -/
def dateParse : BuiltinFn := fun _ _ args _ => do
  let s ← toStr (arg args 0)
  pure (.num (Num.Date.parse s localOffset))

/-- Date.UTC spec: https://tc39.es/ecma262/#sec-date.utc -/
def dateUTC : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let y ← toNum (arg args 0)
  -- 2-7.
  let opt (i : Nat) (d : F64) : M F64 := if args.size > i then toNum args[i]! else pure d
  let m ← opt 1 F64.zero
  let dt ← opt 2 Num.one
  let h ← opt 3 F64.zero
  let mi ← opt 4 F64.zero
  let s ← opt 5 F64.zero
  let milli ← opt 6 F64.zero
  -- 8.
  let yr := Num.Date.makeFullYear y
  -- 9.
  pure (.num (Num.Date.timeClip (Num.Date.makeDate (Num.Date.makeDay yr m dt) (Num.Date.makeTime h mi s milli))))

/-- The Date.prototype getters: a field of LocalTime(t) (`isLocal`) or of t.
spec: https://tc39.es/ecma262/#sec-date.prototype.getdate -/
def dateGetter (isLocal : Bool) (f : Int → Int) : BuiltinFn := fun _ thisV _ _ => do
  -- 1-3.
  let (_, t) ← thisDate thisV
  -- 4.
  match Num.Date.tv? t with
  | none => pure nanV
  -- 5.
  | some _ => pure (intV (f (Num.truncInt (if isLocal then localTime t else t))))

/-- Date.prototype.getTime / valueOf spec: https://tc39.es/ecma262/#sec-date.prototype.gettime -/
def dateGetTime : BuiltinFn := fun _ thisV _ _ => do
  let (_, t) ← thisDate thisV
  pure (.num t)

/-- Date.prototype.getTimezoneOffset spec: https://tc39.es/ecma262/#sec-date.prototype.gettimezoneoffset -/
def dateGetTimezoneOffset : BuiltinFn := fun _ thisV _ _ => do
  let (_, t) ← thisDate thisV
  match Num.Date.tv? t with
  | none => pure nanV
  | some _ => pure (.num (F64.div (F64.sub t (localTime t)) (F64.ofInt Num.Date.msPerMinute)))

/-- The Date.prototype setters (`isLocal`: the local-time ones; else the UTC ones), each
following its section's steps.
spec: https://tc39.es/ecma262/#sec-date.prototype.setdate -/
def dateSetter (name : String) (isLocal : Bool) : BuiltinFn := fun _ thisV args _ =>
  open Num.Date in do
  -- 1-3.
  let (o, t) ← thisDate thisV
  let toL (t : F64) : F64 := if isLocal then localTime t else t
  let toU (t : F64) : F64 := if isLocal then utcTime t else t
  let optNum (i : Nat) : M (Option F64) := if args.size > i then some <$> toNum args[i]! else pure none
  let fI (n : Nat) : F64 := F64.ofInt n
  let dayF (ti : Int) : F64 := F64.ofInt (day ti)
  let twd (ti : Int) : F64 := F64.ofInt (timeWithinDay ti)
  let finish (newDate : F64) : M Value := do
    let u := timeClip (toU newDate)
    setDateValue o u
    pure (.num u)
  match name with
  | "Date" =>
    -- setDate 4-9.
    let dt ← toNum (arg args 0)
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    finish (makeDate (makeDay (F64.ofInt (yearFromTime ti)) (fI (monthFromTime ti)) dt) (twd ti))
  | "FullYear" =>
    -- setFullYear 4-11.
    let y ← toNum (arg args 0)
    let t := if t == .nan then F64.zero else toL t
    let ti := Num.truncInt t
    let m ← (·.getD (fI (monthFromTime ti))) <$> optNum 1
    let dt ← (·.getD (fI (dateFromTime ti))) <$> optNum 2
    finish (makeDate (makeDay y m dt) (twd ti))
  | "Hours" =>
    -- setHours 4-16.
    let h ← toNum (arg args 0)
    let m ← optNum 1
    let s ← optNum 2
    let ms ← optNum 3
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    let m := m.getD (fI (minFromTime ti))
    let s := s.getD (fI (secFromTime ti))
    let ms := ms.getD (fI (msFromTime ti))
    finish (makeDate (dayF ti) (makeTime h m s ms))
  | "Milliseconds" =>
    -- setMilliseconds 4-10.
    let ms ← toNum (arg args 0)
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    finish (makeDate (dayF ti) (makeTime (fI (hourFromTime ti)) (fI (minFromTime ti)) (fI (secFromTime ti)) ms))
  | "Minutes" =>
    -- setMinutes 4-14.
    let m ← toNum (arg args 0)
    let s ← optNum 1
    let ms ← optNum 2
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    let s := s.getD (fI (secFromTime ti))
    let ms := ms.getD (fI (msFromTime ti))
    finish (makeDate (dayF ti) (makeTime (fI (hourFromTime ti)) m s ms))
  | "Month" =>
    -- setMonth 4-12.
    let m ← toNum (arg args 0)
    let dt ← optNum 1
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    let dt := dt.getD (fI (dateFromTime ti))
    finish (makeDate (makeDay (F64.ofInt (yearFromTime ti)) m dt) (twd ti))
  | "Seconds" =>
    -- setSeconds 4-12.
    let s ← toNum (arg args 0)
    let ms ← optNum 1
    if t == .nan then return nanV
    let ti := Num.truncInt (toL t)
    let ms := ms.getD (fI (msFromTime ti))
    finish (makeDate (dayF ti) (makeTime (fI (hourFromTime ti)) (fI (minFromTime ti)) s ms))
  | _ =>
    -- setYear (Annex B) 4-9. spec: https://tc39.es/ecma262/#sec-date.prototype.setyear
    let y ← toNum (arg args 0)
    let t := if t == .nan then F64.zero else toL t
    let ti := Num.truncInt t
    let yyyy := makeFullYear y
    let d := makeDay yyyy (fI (monthFromTime ti)) (fI (dateFromTime ti))
    finish (makeDate d (twd ti))

/-- Date.prototype.setTime spec: https://tc39.es/ecma262/#sec-date.prototype.settime -/
def dateSetTime : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let (o, _) ← thisDate thisV
  -- 3-5.
  let t ← toNum (arg args 0)
  let v := Num.Date.timeClip t
  setDateValue o v
  pure (.num v)

/-- Date.prototype's string methods (`kind`: 0 toString, 1 toDateString, 2 toTimeString,
3 toUTCString, 4 toISOString; the toLocale* ones use 0–2: implementation-defined formats).
spec: https://tc39.es/ecma262/#sec-date.prototype.tostring -/
def dateToStr (kind : Nat) : BuiltinFn := fun _ thisV _ _ => do
  let (_, tv) ← thisDate thisV
  let s := match kind with
    | 0 => Num.Date.toDateString tv localOffset
    | 1 => Num.Date.toDateOnlyString tv localOffset
    | 2 => Num.Date.toTimeString tv localOffset
    | 3 => Num.Date.toUTCString tv
    | _ => (Num.Date.toISOString tv).getD ""
  if kind == 4 && !tv.isFinite then throwRange "Invalid time value"
  pure (.str (JSStr.ofString s))

/-- Date.prototype.toJSON spec: https://tc39.es/ecma262/#sec-date.prototype.tojson -/
def dateToJSON : BuiltinFn := fun _ thisV _ _ => do
  -- 1.
  let o ← toObject thisV
  -- 2.
  let tv ← toPrim (.obj o) (some true)
  -- 3.
  if let .num x := tv then
    if !x.isFinite then return .null
  -- 4.
  invoke (.obj o) (.str "toISOString") #[]

/-- Date.prototype[@@toPrimitive] spec: https://tc39.es/ecma262/#sec-date.prototype-%symbol.toprimitive% -/
def dateToPrimitive : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj o := thisV | throwType "Date.prototype[Symbol.toPrimitive] called on non-object"
  -- 3-5.
  let tryNumber ← match arg args 0 with
    | .str s =>
      if s == JSStr.ofString "string" || s == JSStr.ofString "default" then pure false
      else if s == JSStr.ofString "number" then pure true
      else throwType "Invalid hint"
    | _ => throwType "Invalid hint"
  -- 6.
  ordinaryToPrimitive maxDepth o tryNumber


/-! ## Explicit resource management: SuppressedError, DisposableStack, AsyncDisposableStack

A DisposableStack/AsyncDisposableStack is `Kind.internal "DisposableStack"`/
`"AsyncDisposableStack"`: slot 0 is [[DisposableState]] (`true`: disposed), then its
[[DisposeCapability]]'s resources as (value, async hint, method) triples. -/

/-- SuppressedError(error, suppressed, message) spec: https://tc39.es/ecma262/#sec-suppressederror-constructor -/
def suppressedErrorCtor : BuiltinFn := fun self _ args nt => do
  -- 1.
  let nt := if nt.isUndefined then Value.obj self else nt
  -- 2.
  let o ← ordinaryCreateFromConstructor nt "%SuppressedError.prototype%" .error
  -- 3.
  let msg := arg args 2
  if !msg.isUndefined then
    let m ← toStr msg
    createNonEnumDataPropertyOrThrow o (.str kMessage) (.str m)
  -- 4-5.
  createNonEnumDataPropertyOrThrow o (.str "error") (arg args 0)
  createNonEnumDataPropertyOrThrow o (.str "suppressed") (arg args 1)
  -- 6.
  pure (.obj o)

/-- A newly created SuppressedError object with [[error]] and [[suppressed]] (DisposeResources
step 3.c.iii). spec: https://tc39.es/ecma262/#sec-disposeresources -/
def newSuppressedError (error suppressed : Value) : M Value := do
  let proto ← intrinsic "%SuppressedError.prototype%"
  let e ← alloc { proto := .obj proto, kind := .error }
  createNonEnumDataPropertyOrThrow e (.str "error") error
  createNonEnumDataPropertyOrThrow e (.str "suppressed") suppressed
  pure (.obj e)

/-- The closure GetDisposeMethod makes of a sync @@dispose method for async disposal.
spec: https://tc39.es/ecma262/#sec-getdisposemethod -/
def asyncFromSyncDispose : BuiltinFn := fun self thisV _ _ => do
  let method := (← builtinSlots self)[0]?.getD .undefined
  -- a-b.
  let cap ← newPromiseCapability (← intrinsicV "%Promise%")
  -- c-d.
  match ← M.attempt (call method thisV #[]) with
  | .error e => let _ ← call cap.reject .undefined #[e]
  -- e.
  | .ok _ => let _ ← call cap.resolve .undefined #[.undefined]
  -- f.
  pure cap.promise

/-- GetDisposeMethod spec: https://tc39.es/ecma262/#sec-getdisposemethod -/
def getDisposeMethod (v : Value) (isAsync : Bool) : M Value := do
  -- 1.
  if isAsync then
    match ← getMethodOf v (.sym WK.asyncDispose) with
    | some m => return m
    | none =>
      match ← getMethodOf v (.sym WK.dispose) with
      | some m => return .obj (← makeBuiltinFn "AsyncFromSyncDispose" 0 JSStr.empty #[m])
      | none => return .undefined
  -- 2-3.
  pure ((← getMethodOf v (.sym WK.dispose)).getD .undefined)

/-- AddDisposableResource (with CreateDisposableResource): appends a (value, hint, method)
triple to the stack object `o`'s resources.
spec: https://tc39.es/ecma262/#sec-adddisposableresource -/
def addDisposableResource (o : ObjId) (v : Value) (isAsync : Bool) (method : Option Value := none) : M Unit := do
  let triple ← match method with
    -- 1.
    | none =>
      -- a.
      if v.isNullish && !isAsync then return
      -- c. CreateDisposableResource(V, hint)
      if v.isNullish then pure #[Value.undefined, .bool isAsync, .undefined]
      else
        if !v.isObject then throwType "Resource must be an object"
        let m ← getDisposeMethod v isAsync
        if m.isUndefined then throwType "Resource has no dispose method"
        pure #[v, .bool isAsync, m]
    -- 2.
    | some m =>
      if !(← isCallable m) then throwType "Dispose method is not callable"
      pure #[Value.undefined, .bool isAsync, m]
  -- 3.
  modifyObj o fun ob => ob.withKind fun k => match k with
    | .internal t s => .internal t (s ++ triple)
    | k => k

/-- The stack object `thisV` (RequireInternalSlot([[DisposableState]] / [[AsyncDisposableState]])). -/
def requireStack (thisV : Value) (isAsync : Bool) (what : String) : M ObjId := do
  let tag := if isAsync then "AsyncDisposableStack" else "DisposableStack"
  let some o ← internalWithTag thisV tag | throwType s!"{tag}.prototype.{what} called on incompatible receiver"
  pure o

def stackDisposed (o : ObjId) : M Bool := do pure (toBoolean (← slotAt o 0))

/-- DisposableStack() / AsyncDisposableStack() spec: https://tc39.es/ecma262/#sec-disposablestack -/
def stackCtor (isAsync : Bool) : BuiltinFn := fun _ _ _ nt => do
  let tag := if isAsync then "AsyncDisposableStack" else "DisposableStack"
  -- 1.
  if nt.isUndefined then throwType s!"Constructor {tag} requires 'new'"
  -- 2-5.
  let o ← ordinaryCreateFromConstructor nt s!"%{tag}.prototype%" (.internal tag #[.bool false])
  pure (.obj o)

/-- DisposableStack.prototype.adopt / AsyncDisposableStack.prototype.adopt
spec: https://tc39.es/ecma262/#sec-disposablestack.prototype.adopt -/
def stackAdopt (isAsync : Bool) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← requireStack thisV isAsync "adopt"
  -- 3.
  if ← stackDisposed o then throwError .referenceError "The stack is already disposed"
  -- 4.
  let (value, onDispose) := (arg args 0, arg args 1)
  if !(← isCallable onDispose) then throwType "onDispose is not a function"
  -- 5-6.
  let f ← makeBuiltinFn "DisposableStackAdoptClosure" 0 JSStr.empty #[value, onDispose]
  -- 7.
  addDisposableResource o .undefined isAsync (some (.obj f))
  -- 8.
  pure value

/-- The closure of `adopt`: calls onDispose with the value. -/
def stackAdoptClosure : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  call (s[1]?.getD .undefined) .undefined #[s[0]?.getD .undefined]

/-- DisposableStack.prototype.defer spec: https://tc39.es/ecma262/#sec-disposablestack.prototype.defer -/
def stackDefer (isAsync : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireStack thisV isAsync "defer"
  if ← stackDisposed o then throwError .referenceError "The stack is already disposed"
  let onDispose := arg args 0
  if !(← isCallable onDispose) then throwType "onDispose is not a function"
  addDisposableResource o .undefined isAsync (some onDispose)
  pure .undefined

/-- DisposableStack.prototype.use spec: https://tc39.es/ecma262/#sec-disposablestack.prototype.use -/
def stackUse (isAsync : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← requireStack thisV isAsync "use"
  if ← stackDisposed o then throwError .referenceError "The stack is already disposed"
  let value := arg args 0
  addDisposableResource o value isAsync
  pure value

/-- get DisposableStack.prototype.disposed spec: https://tc39.es/ecma262/#sec-get-disposablestack.prototype.disposed -/
def stackDisposedGet (isAsync : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let o ← requireStack thisV isAsync "disposed"
  pure (.bool (← stackDisposed o))

/-- DisposableStack.prototype.move spec: https://tc39.es/ecma262/#sec-disposablestack.prototype.move -/
def stackMove (isAsync : Bool) : BuiltinFn := fun _ thisV _ _ => do
  let tag := if isAsync then "AsyncDisposableStack" else "DisposableStack"
  -- 1-2.
  let o ← requireStack thisV isAsync "move"
  -- 3.
  if ← stackDisposed o then throwError .referenceError "The stack is already disposed"
  -- 4-6.
  let resources := (← slotsOf o).extract 1
  let n ← ordinaryCreateFromConstructor (← intrinsicV s!"%{tag}%") s!"%{tag}.prototype%"
    (.internal tag (#[Value.bool false] ++ resources))
  -- 7-8.
  modifyObj o fun ob => { ob with kind := .internal tag #[.bool true] }
  -- 9.
  pure (.obj n)

/-- The resources of a stack as triples, last added first. -/
def resourcesReversed (sl : Array Value) : Array (Value × Bool × Value) :=
  let n := (sl.size - 1) / 3
  (Array.range n).reverse.map fun i => (sl[1 + 3 * i]!, toBoolean sl[2 + 3 * i]!, sl[3 + 3 * i]!)

/-- DisposeResources for synchronous resources (no Await).
spec: https://tc39.es/ecma262/#sec-disposeresources -/
def disposeResourcesSync (resources : Array (Value × Bool × Value)) (completion : Except Value Value) :
    M Value := do
  -- 3.
  let completion ← M.foldArr resources completion fun comp (v, _, method) => do
    -- c.
    if method.isUndefined then return comp
    match ← M.attempt (call method v #[]) with
    | .ok _ => pure comp
    | .error e =>
      match comp with
      | .error c => pure (.error (← newSuppressedError e c))
      | .ok _ => pure (.error e)
  -- 7.
  match completion with
  | .ok v => pure v
  | .error e => M.throwV e

/-- DisposableStack.prototype.dispose spec: https://tc39.es/ecma262/#sec-disposablestack.prototype.dispose -/
def stackDispose : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let o ← requireStack thisV false "dispose"
  -- 3.
  if ← stackDisposed o then return .undefined
  -- 4.
  let sl ← slotsOf o
  modifyObj o fun ob => { ob with kind := .internal "DisposableStack" #[.bool true] }
  -- 5.
  disposeResourcesSync (resourcesReversed sl) (.ok .undefined)

/-! ### AsyncDisposableStack.prototype.disposeAsync: DisposeResources with Await, as a state
machine continued by promise reactions. Slots of the "AsyncDispose" record: 0 the capability's
resolve, 1 its reject, 2 the completion is a throw, 3 the completion's value, 4 needsAwait,
5 hasAwaited, 6 the number of resources left, 7 the phase being awaited (1: an Await before a
sync resource, 2: a resource's result, 3: the final Await), 8… the resources, last added first. -/

/-- Merges a throw `e` into the record's completion (DisposeResources step 3.c.iii). -/
def asyncDisposeMerge (st : ObjId) (e : Value) : M Unit := do
  let sl ← slotsOf st
  if toBoolean sl[2]! then
    setSlot st 3 (← newSuppressedError e sl[3]!)
  else
    setSlot st 2 (.bool true)
    setSlot st 3 e

/-- Await(v) in the dispose state machine: `true` if it suspended (a reaction resumes the
machine), `false` if PromiseResolve threw (merged as the result's throw).
spec: https://tc39.es/ecma262/#await -/
def asyncDisposeAwait (st : ObjId) (v : Value) (phase : Nat) : M Bool := do
  match ← M.attempt (promiseResolve (← intrinsicV "%Promise%") v) with
  | .error e =>
    asyncDisposeMerge st e
    pure false
  | .ok p =>
    let .obj po := p | pure false
    setSlot st 7 (numV phase)
    let onF ← makeBuiltinFn "AsyncDisposeResume" 1 JSStr.empty #[.obj st, .bool false]
    let onR ← makeBuiltinFn "AsyncDisposeResume" 1 JSStr.empty #[.obj st, .bool true]
    let _ ← performPromiseThen po (.obj onF) (.obj onR) none
    pure true

/-- Runs DisposeResources from where it stands until it awaits or completes (then the
capability is resolved or rejected). spec: https://tc39.es/ecma262/#sec-disposeresources -/
def asyncDisposeRun (st : ObjId) : M Unit :=
  M.repeatFrom () fun _ => do
    let sl ← slotsOf st
    let left := natOf sl[6]!
    let needsAwait := toBoolean sl[4]!
    let hasAwaited := toBoolean sl[5]!
    if left == 0 then
      -- 4.
      if needsAwait && !hasAwaited then
        setSlot st 4 (.bool false)
        setSlot st 5 (.bool true)
        if ← asyncDisposeAwait st .undefined 3 then return .inr ()
      -- 6-7. (disposeAsync 7-8)
      if toBoolean sl[2]! then
        let _ ← call sl[1]! .undefined #[sl[3]!]
      else
        let _ ← call sl[0]! .undefined #[.undefined]
      return .inr ()
    let base := 8 + 3 * ((sl.size - 8) / 3 - left)
    let (v, isAsync, method) := (sl[base]!, toBoolean sl[base + 1]!, sl[base + 2]!)
    -- 3.b.
    if !isAsync && needsAwait && !hasAwaited then
      setSlot st 4 (.bool false)
      if ← asyncDisposeAwait st .undefined 1 then return .inr ()
      return .inl ()
    setSlot st 6 (numV (left - 1))
    -- 3.c.
    if !method.isUndefined then
      match ← M.attempt (call method v #[]) with
      | .ok r =>
        if isAsync then
          setSlot st 5 (.bool true)
          if ← asyncDisposeAwait st r 2 then return .inr ()
        return .inl ()
      | .error e =>
        asyncDisposeMerge st e
        return .inl ()
    -- 3.d.
    setSlot st 4 (.bool true)
    return .inl ()

/-- The reaction that resumes the dispose state machine after an Await. -/
def asyncDisposeResume : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let .obj st := s[0]! | M.halt "internal: dispose record"
  let isReject := toBoolean s[1]!
  let phase := natOf (← slotAt st 7)
  if phase == 2 && isReject then asyncDisposeMerge st (arg args 0)
  if phase == 3 then
    -- the final Await: complete
    setSlot st 4 (.bool false)
  asyncDisposeRun st
  pure .undefined

/-- AsyncDisposableStack.prototype.disposeAsync
spec: https://tc39.es/ecma262/#sec-asyncdisposablestack.prototype.disposeAsync -/
def stackDisposeAsync : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let cap ← newPromiseCapability (← intrinsicV "%Promise%")
  -- 3.
  let some o ← internalWithTag thisV "AsyncDisposableStack" | do
    let e ← makeError .typeError "AsyncDisposableStack.prototype.disposeAsync called on incompatible receiver"
    let _ ← call cap.reject .undefined #[e]
    return cap.promise
  -- 4.
  if ← stackDisposed o then
    let _ ← call cap.resolve .undefined #[.undefined]
    return cap.promise
  -- 5.
  let sl ← slotsOf o
  modifyObj o fun ob => { ob with kind := .internal "AsyncDisposableStack" #[.bool true] }
  -- 6-8.
  let res := resourcesReversed sl
  let flat := res.foldl (fun acc (v, a, m) => ((acc.push v).push (.bool a)).push m) #[]
  let st ← alloc { kind := .internal "AsyncDispose" (#[cap.resolve, cap.reject, .bool false, .undefined,
    .bool false, .bool false, numV res.size, numV 0] ++ flat) }
  match ← M.attempt (asyncDisposeRun st) with
  | .error e => let _ ← call cap.reject .undefined #[e]
  | .ok () => pure ()
  -- 9.
  pure cap.promise

/-! ## The table and setup -/

def defs : Array BuiltinDef := #[
  -- Map, Set, WeakMap, WeakSet
  ⟨"Map", mapCtor false⟩, ⟨"Map.groupBy", mapGroupBy⟩, ⟨"Object.groupBy", objectGroupBy⟩,
  ⟨"Map.prototype.clear", collClear false⟩, ⟨"Map.prototype.delete", collDeleteFn false⟩,
  ⟨"Map.prototype.forEach", collForEach false⟩, ⟨"Map.prototype.get", mapGet⟩,
  ⟨"Map.prototype.has", collHasFn false⟩, ⟨"Map.prototype.set", mapSet⟩,
  ⟨"Map.prototype.keys", collIterFn false 0⟩, ⟨"Map.prototype.values", collIterFn false 1⟩,
  ⟨"Map.prototype.entries", collIterFn false 2⟩, ⟨"get Map.prototype.size", collSizeFn false⟩,
  ⟨"%MapIteratorPrototype%.next", collIteratorNext false⟩,
  ⟨"Set", setCtor false⟩, ⟨"Set.prototype.add", setAdd⟩, ⟨"Set.prototype.clear", collClear true⟩,
  ⟨"Set.prototype.delete", collDeleteFn true⟩, ⟨"Set.prototype.forEach", collForEach true⟩,
  ⟨"Set.prototype.has", collHasFn true⟩, ⟨"Set.prototype.values", collIterFn true 1⟩,
  ⟨"Set.prototype.entries", collIterFn true 2⟩, ⟨"get Set.prototype.size", collSizeFn true⟩,
  ⟨"Set.prototype.union", setUnion⟩, ⟨"Set.prototype.intersection", setIntersection⟩,
  ⟨"Set.prototype.difference", setDifference⟩,
  ⟨"Set.prototype.symmetricDifference", setSymmetricDifference⟩,
  ⟨"Set.prototype.isSubsetOf", setIsSubsetOf⟩, ⟨"Set.prototype.isSupersetOf", setIsSupersetOf⟩,
  ⟨"Set.prototype.isDisjointFrom", setIsDisjointFrom⟩,
  ⟨"%SetIteratorPrototype%.next", collIteratorNext true⟩,
  ⟨"WeakMap", mapCtor true⟩, ⟨"WeakMap.prototype.delete", weakDelete false⟩,
  ⟨"WeakMap.prototype.get", weakMapGet⟩, ⟨"WeakMap.prototype.has", weakHas false⟩,
  ⟨"WeakMap.prototype.set", weakMapSet⟩,
  ⟨"WeakSet", setCtor true⟩, ⟨"WeakSet.prototype.add", weakSetAdd⟩,
  ⟨"WeakSet.prototype.delete", weakDelete true⟩, ⟨"WeakSet.prototype.has", weakHas true⟩,
  ⟨"WeakRef", weakRefCtor⟩, ⟨"WeakRef.prototype.deref", weakRefDeref⟩,
  ⟨"FinalizationRegistry", finRegCtor⟩,
  ⟨"FinalizationRegistry.prototype.register", finRegRegister⟩,
  ⟨"FinalizationRegistry.prototype.unregister", finRegUnregister⟩,
  -- Iterators
  ⟨"Iterator", iteratorCtor⟩, ⟨"Iterator.from", iteratorFrom⟩,
  ⟨"%WrapForValidIteratorPrototype%.next", wrapNext⟩,
  ⟨"%WrapForValidIteratorPrototype%.return", wrapReturn⟩,
  ⟨"get Iterator.prototype.constructor", iterProtoCtorGet⟩,
  ⟨"set Iterator.prototype.constructor", setterIgnoringProto (.str kConstructor)⟩,
  ⟨"get Iterator.prototype[Symbol.toStringTag]", iterProtoTagGet⟩,
  ⟨"set Iterator.prototype[Symbol.toStringTag]", setterIgnoringProto (.sym WK.toStringTag)⟩,
  ⟨"get Error.prototype.stack", errorStackGet⟩, ⟨"set Error.prototype.stack", errorStackSet⟩,
  ⟨"Iterator.prototype.map", iterProtoMapLike 0 "map"⟩,
  ⟨"Iterator.prototype.filter", iterProtoMapLike 1 "filter"⟩,
  ⟨"Iterator.prototype.flatMap", iterProtoMapLike 4 "flatMap"⟩,
  ⟨"Iterator.prototype.take", iterProtoTakeDrop 2 "take"⟩,
  ⟨"Iterator.prototype.drop", iterProtoTakeDrop 3 "drop"⟩,
  ⟨"Iterator.prototype.chunks", iterProtoChunks⟩, ⟨"Iterator.prototype.windows", iterProtoWindows⟩,
  ⟨"Iterator.prototype.reduce", iterProtoReduce⟩, ⟨"Iterator.prototype.toArray", iterProtoToArray⟩,
  ⟨"Iterator.prototype.some", iterProtoSearch 0 "some"⟩,
  ⟨"Iterator.prototype.every", iterProtoSearch 1 "every"⟩,
  ⟨"Iterator.prototype.find", iterProtoSearch 2 "find"⟩,
  ⟨"Iterator.prototype.forEach", iterProtoSearch 3 "forEach"⟩,
  ⟨"Iterator.prototype.includes", iterProtoIncludes⟩, ⟨"Iterator.prototype.join", iterProtoJoin⟩,
  ⟨"Iterator.prototype[Symbol.dispose]", iterProtoDispose⟩,
  ⟨"%AsyncIteratorPrototype%[Symbol.asyncDispose]", asyncIterProtoDispose⟩,
  ⟨"AsyncIteratorDisposeUnwrap", fun _ _ _ _ => pure .undefined⟩,
  ⟨"%IteratorHelperPrototype%.next", helperNext⟩, ⟨"%IteratorHelperPrototype%.return", helperReturn⟩,
  -- Promise
  ⟨"Promise.all", promiseCombinator 0⟩, ⟨"Promise.allSettled", promiseCombinator 1⟩,
  ⟨"Promise.any", promiseCombinator 2⟩, ⟨"Promise.race", promiseCombinator 3⟩,
  ⟨"PromiseElement0", promiseElement 0⟩, ⟨"PromiseElement1", promiseElement 1⟩,
  ⟨"PromiseElement2", promiseElement 2⟩, ⟨"PromiseElement3", promiseElement 3⟩,
  ⟨"Promise.withResolvers", promiseWithResolvers⟩, ⟨"Promise.try", promiseTry⟩,
  ⟨"Promise.prototype.finally", promiseProtoFinally⟩,
  ⟨"Promise.thenFinally", promiseFinallyFn false⟩, ⟨"Promise.catchFinally", promiseFinallyFn true⟩,
  ⟨"Promise.valueThunk", fun self _ _ _ => do pure ((← builtinSlots self)[0]?.getD .undefined)⟩,
  ⟨"Promise.thrower", fun self _ _ _ => do M.throwV ((← builtinSlots self)[0]?.getD .undefined)⟩,
  -- Explicit resource management
  ⟨"SuppressedError", suppressedErrorCtor⟩, ⟨"AsyncFromSyncDispose", asyncFromSyncDispose⟩,
  ⟨"DisposableStack", stackCtor false⟩, ⟨"AsyncDisposableStack", stackCtor true⟩,
  ⟨"DisposableStack.prototype.adopt", stackAdopt false⟩,
  ⟨"AsyncDisposableStack.prototype.adopt", stackAdopt true⟩,
  ⟨"DisposableStackAdoptClosure", stackAdoptClosure⟩,
  ⟨"DisposableStack.prototype.defer", stackDefer false⟩,
  ⟨"AsyncDisposableStack.prototype.defer", stackDefer true⟩,
  ⟨"DisposableStack.prototype.use", stackUse false⟩, ⟨"AsyncDisposableStack.prototype.use", stackUse true⟩,
  ⟨"get DisposableStack.prototype.disposed", stackDisposedGet false⟩,
  ⟨"get AsyncDisposableStack.prototype.disposed", stackDisposedGet true⟩,
  ⟨"DisposableStack.prototype.move", stackMove false⟩,
  ⟨"AsyncDisposableStack.prototype.move", stackMove true⟩,
  ⟨"DisposableStack.prototype.dispose", stackDispose⟩,
  ⟨"AsyncDisposableStack.prototype.disposeAsync", stackDisposeAsync⟩,
  ⟨"AsyncDisposeResume", asyncDisposeResume⟩,
  -- Date
  ⟨"Date", dateCtor⟩, ⟨"Date.now", dateNow⟩, ⟨"Date.parse", dateParse⟩, ⟨"Date.UTC", dateUTC⟩,
  ⟨"Date.prototype.getDate", dateGetter true (fun t => Num.Date.dateFromTime t)⟩,
  ⟨"Date.prototype.getDay", dateGetter true (fun t => Num.Date.weekDay t)⟩,
  ⟨"Date.prototype.getFullYear", dateGetter true Num.Date.yearFromTime⟩,
  ⟨"Date.prototype.getHours", dateGetter true (fun t => Num.Date.hourFromTime t)⟩,
  ⟨"Date.prototype.getMilliseconds", dateGetter true (fun t => Num.Date.msFromTime t)⟩,
  ⟨"Date.prototype.getMinutes", dateGetter true (fun t => Num.Date.minFromTime t)⟩,
  ⟨"Date.prototype.getMonth", dateGetter true (fun t => Num.Date.monthFromTime t)⟩,
  ⟨"Date.prototype.getSeconds", dateGetter true (fun t => Num.Date.secFromTime t)⟩,
  ⟨"Date.prototype.getYear", dateGetter true (fun t => Num.Date.yearFromTime t - 1900)⟩,
  ⟨"Date.prototype.getUTCDate", dateGetter false (fun t => Num.Date.dateFromTime t)⟩,
  ⟨"Date.prototype.getUTCDay", dateGetter false (fun t => Num.Date.weekDay t)⟩,
  ⟨"Date.prototype.getUTCFullYear", dateGetter false Num.Date.yearFromTime⟩,
  ⟨"Date.prototype.getUTCHours", dateGetter false (fun t => Num.Date.hourFromTime t)⟩,
  ⟨"Date.prototype.getUTCMilliseconds", dateGetter false (fun t => Num.Date.msFromTime t)⟩,
  ⟨"Date.prototype.getUTCMinutes", dateGetter false (fun t => Num.Date.minFromTime t)⟩,
  ⟨"Date.prototype.getUTCMonth", dateGetter false (fun t => Num.Date.monthFromTime t)⟩,
  ⟨"Date.prototype.getUTCSeconds", dateGetter false (fun t => Num.Date.secFromTime t)⟩,
  ⟨"Date.prototype.getTime", dateGetTime⟩,
  ⟨"Date.prototype.getTimezoneOffset", dateGetTimezoneOffset⟩,
  ⟨"Date.prototype.setDate", dateSetter "Date" true⟩,
  ⟨"Date.prototype.setFullYear", dateSetter "FullYear" true⟩,
  ⟨"Date.prototype.setHours", dateSetter "Hours" true⟩,
  ⟨"Date.prototype.setMilliseconds", dateSetter "Milliseconds" true⟩,
  ⟨"Date.prototype.setMinutes", dateSetter "Minutes" true⟩,
  ⟨"Date.prototype.setMonth", dateSetter "Month" true⟩,
  ⟨"Date.prototype.setSeconds", dateSetter "Seconds" true⟩,
  ⟨"Date.prototype.setYear", dateSetter "Year" true⟩,
  ⟨"Date.prototype.setUTCDate", dateSetter "Date" false⟩,
  ⟨"Date.prototype.setUTCFullYear", dateSetter "FullYear" false⟩,
  ⟨"Date.prototype.setUTCHours", dateSetter "Hours" false⟩,
  ⟨"Date.prototype.setUTCMilliseconds", dateSetter "Milliseconds" false⟩,
  ⟨"Date.prototype.setUTCMinutes", dateSetter "Minutes" false⟩,
  ⟨"Date.prototype.setUTCMonth", dateSetter "Month" false⟩,
  ⟨"Date.prototype.setUTCSeconds", dateSetter "Seconds" false⟩,
  ⟨"Date.prototype.setTime", dateSetTime⟩,
  ⟨"Date.prototype.toString", dateToStr 0⟩, ⟨"Date.prototype.toDateString", dateToStr 1⟩,
  ⟨"Date.prototype.toTimeString", dateToStr 2⟩, ⟨"Date.prototype.toUTCString", dateToStr 3⟩,
  ⟨"Date.prototype.toISOString", dateToStr 4⟩,
  ⟨"Date.prototype.toLocaleString", dateToStr 0⟩, ⟨"Date.prototype.toLocaleDateString", dateToStr 1⟩,
  ⟨"Date.prototype.toLocaleTimeString", dateToStr 2⟩,
  ⟨"Date.prototype.toJSON", dateToJSON⟩, ⟨"Date.prototype[Symbol.toPrimitive]", dateToPrimitive⟩]

/-- Defines methods `nm` (behaviour `pfx ++ nm`) with their lengths. -/
def defMethods (o : ObjId) (pfx : String) (ms : List (String × Nat)) : M Unit := do
  for (nm, len) in ms do
    let _ ← defMethod o (.str (JSStr.ofString nm)) (pfx ++ nm) len

/-- Creates this module's intrinsics in the realm being created (runs after `coreSetup`). -/
def setup : M Unit := do
  let ip ← intrinsic "%Iterator.prototype%"
  -- Map
  let mp ← newIntrinsicObject "%Map.prototype%"
  let (mc, _) ← defConstructor "Map" 0 "Map" mp
  let _ ← defMethod mc (.str "groupBy") "Map.groupBy" 2
  defSpecies mc
  defMethods mp "Map.prototype." [("clear", 0), ("delete", 1)]
  let me ← defMethod mp (.str "entries") "Map.prototype.entries" 0
  defMethods mp "Map.prototype." [("forEach", 1), ("get", 1), ("has", 1), ("keys", 0), ("set", 2)]
  defGetter mp (.str kSize) "get Map.prototype.size"
  defMethods mp "Map.prototype." [("values", 0)]
  setOwn mp (.sym WK.iterator) (.data (.obj me) true false true)
  defTag mp "Map"
  let mip ← newIntrinsicObject "%MapIteratorPrototype%" (some ip)
  let _ ← defMethod mip (.str kNext) "%MapIteratorPrototype%.next" 0
  defTag mip "Map Iterator"
  -- Set
  let sp ← newIntrinsicObject "%Set.prototype%"
  let (sc, _) ← defConstructor "Set" 0 "Set" sp
  defSpecies sc
  defMethods sp "Set.prototype." [("add", 1), ("clear", 0), ("delete", 1), ("difference", 1),
    ("entries", 0), ("forEach", 1), ("has", 1), ("intersection", 1), ("isDisjointFrom", 1),
    ("isSubsetOf", 1), ("isSupersetOf", 1)]
  defGetter sp (.str kSize) "get Set.prototype.size"
  defMethods sp "Set.prototype." [("symmetricDifference", 1), ("union", 1)]
  let sv ← defMethod sp (.str "values") "Set.prototype.values" 0
  setOwn sp (.str kKeys) (.data (.obj sv) true false true)
  setOwn sp (.sym WK.iterator) (.data (.obj sv) true false true)
  defTag sp "Set"
  let sip ← newIntrinsicObject "%SetIteratorPrototype%" (some ip)
  let _ ← defMethod sip (.str kNext) "%SetIteratorPrototype%.next" 0
  defTag sip "Set Iterator"
  -- WeakMap, WeakSet
  let wmp ← newIntrinsicObject "%WeakMap.prototype%"
  let _ ← defConstructor "WeakMap" 0 "WeakMap" wmp
  defMethods wmp "WeakMap.prototype." [("delete", 1), ("get", 1), ("has", 1), ("set", 2)]
  defTag wmp "WeakMap"
  let wsp ← newIntrinsicObject "%WeakSet.prototype%"
  let _ ← defConstructor "WeakSet" 0 "WeakSet" wsp
  defMethods wsp "WeakSet.prototype." [("add", 1), ("delete", 1), ("has", 1)]
  defTag wsp "WeakSet"
  -- WeakRef, FinalizationRegistry
  let wrp ← newIntrinsicObject "%WeakRef.prototype%"
  let _ ← defConstructor "WeakRef" 1 "WeakRef" wrp
  defMethods wrp "WeakRef.prototype." [("deref", 0)]
  defTag wrp "WeakRef"
  let frp ← newIntrinsicObject "%FinalizationRegistry.prototype%"
  let _ ← defConstructor "FinalizationRegistry" 1 "FinalizationRegistry" frp
  defMethods frp "FinalizationRegistry.prototype." [("register", 2), ("unregister", 1)]
  defTag frp "FinalizationRegistry"
  -- Iterator
  let (itc, _) ← defConstructor "Iterator" 0 "Iterator" ip
  let _ ← defMethod itc (.str "from") "Iterator.from" 1
  defGetter ip (.str kConstructor) "get Iterator.prototype.constructor" (some "set Iterator.prototype.constructor")
  defGetter ip (.sym WK.toStringTag) "get Iterator.prototype[Symbol.toStringTag]"
    (some "set Iterator.prototype[Symbol.toStringTag]")
  defMethods ip "Iterator.prototype." [("chunks", 1), ("drop", 1), ("every", 1), ("filter", 1),
    ("find", 1), ("flatMap", 1), ("forEach", 1), ("includes", 1), ("join", 1), ("map", 1),
    ("reduce", 1), ("some", 1), ("take", 1), ("toArray", 0), ("windows", 1)]
  let _ ← defMethod ip (.sym WK.dispose) "Iterator.prototype[Symbol.dispose]" 0
  let hp ← newIntrinsicObject "%IteratorHelperPrototype%" (some ip)
  defMethods hp "%IteratorHelperPrototype%." [("next", 0), ("return", 0)]
  defTag hp "Iterator Helper"
  let wp ← newIntrinsicObject "%WrapForValidIteratorPrototype%" (some ip)
  defMethods wp "%WrapForValidIteratorPrototype%." [("next", 0), ("return", 0)]
  let aip ← intrinsic "%AsyncIteratorPrototype%"
  if (← ownProp aip (.sym WK.asyncIterator)).isNone then
    let _ ← defMethod aip (.sym WK.asyncIterator) "returnThis" 0
  let _ ← defMethod aip (.sym WK.asyncDispose) "%AsyncIteratorPrototype%[Symbol.asyncDispose]" 0
  -- Promise
  let pc ← intrinsic "%Promise%"
  let pp ← intrinsic "%Promise.prototype%"
  defMethods pc "Promise." [("all", 1), ("allSettled", 1), ("any", 1), ("race", 1), ("try", 1),
    ("withResolvers", 0)]
  defMethods pp "Promise.prototype." [("finally", 1)]
  -- Error.prototype.stack
  let ep ← intrinsic "%Error.prototype%"
  defGetter ep (.str kStack) "get Error.prototype.stack" (some "set Error.prototype.stack")
  -- SuppressedError
  let ec ← intrinsic "%Error%"
  let sep ← newIntrinsicObject "%SuppressedError.prototype%" (some ep)
  let _ ← defConstructor "SuppressedError" 3 "SuppressedError" sep (some ec)
  setOwn sep (.str kName) (.data (.str "SuppressedError") true false true)
  setOwn sep (.str kMessage) (.data (.str JSStr.empty) true false true)
  -- DisposableStack, AsyncDisposableStack
  let dsp ← newIntrinsicObject "%DisposableStack.prototype%"
  let _ ← defConstructor "DisposableStack" 0 "DisposableStack" dsp
  defMethods dsp "DisposableStack.prototype." [("adopt", 2), ("defer", 1)]
  let dd ← defMethod dsp (.str "dispose") "DisposableStack.prototype.dispose" 0
  defGetter dsp (.str "disposed") "get DisposableStack.prototype.disposed"
  defMethods dsp "DisposableStack.prototype." [("move", 0), ("use", 1)]
  setOwn dsp (.sym WK.dispose) (.data (.obj dd) true false true)
  defTag dsp "DisposableStack"
  let adsp ← newIntrinsicObject "%AsyncDisposableStack.prototype%"
  let _ ← defConstructor "AsyncDisposableStack" 0 "AsyncDisposableStack" adsp
  defMethods adsp "AsyncDisposableStack.prototype." [("adopt", 2), ("defer", 1)]
  let ad ← defMethod adsp (.str "disposeAsync") "AsyncDisposableStack.prototype.disposeAsync" 0
  defGetter adsp (.str "disposed") "get AsyncDisposableStack.prototype.disposed"
  defMethods adsp "AsyncDisposableStack.prototype." [("move", 0), ("use", 1)]
  setOwn adsp (.sym WK.asyncDispose) (.data (.obj ad) true false true)
  defTag adsp "AsyncDisposableStack"
  -- Object.groupBy
  let oc ← intrinsic "%Object%"
  let _ ← defMethod oc (.str "groupBy") "Object.groupBy" 2
  -- Date
  let dp ← newIntrinsicObject "%Date.prototype%"
  let (dc, _) ← defConstructor "Date" 7 "Date" dp
  defMethods dc "Date." [("now", 0), ("parse", 1), ("UTC", 7)]
  defMethods dp "Date.prototype." [("getDate", 0), ("getDay", 0), ("getFullYear", 0), ("getHours", 0),
    ("getMilliseconds", 0), ("getMinutes", 0), ("getMonth", 0), ("getSeconds", 0), ("getTime", 0),
    ("getTimezoneOffset", 0), ("getUTCDate", 0), ("getUTCDay", 0), ("getUTCFullYear", 0),
    ("getUTCHours", 0), ("getUTCMilliseconds", 0), ("getUTCMinutes", 0), ("getUTCMonth", 0),
    ("getUTCSeconds", 0), ("getYear", 0), ("setDate", 1), ("setFullYear", 3), ("setHours", 4),
    ("setMilliseconds", 1), ("setMinutes", 3), ("setMonth", 2), ("setSeconds", 2), ("setTime", 1),
    ("setUTCDate", 1), ("setUTCFullYear", 3), ("setUTCHours", 4), ("setUTCMilliseconds", 1),
    ("setUTCMinutes", 3), ("setUTCMonth", 2), ("setUTCSeconds", 2), ("setYear", 1),
    ("toDateString", 0), ("toISOString", 0), ("toJSON", 1), ("toLocaleDateString", 0),
    ("toLocaleString", 0), ("toLocaleTimeString", 0), ("toString", 0), ("toTimeString", 0)]
  let utc ← defMethod dp (.str "toUTCString") "Date.prototype.toUTCString" 0
  setOwn dp (.str "toGMTString") (.data (.obj utc) true false true)
  let _ ← defMethod dp (.str kValueOf) "Date.prototype.getTime" 0 (some "valueOf")
  let tp ← makeBuiltinFn "Date.prototype[Symbol.toPrimitive]" 1 "[Symbol.toPrimitive]"
  setOwn dp (.sym WK.toPrimitive) (.data (.obj tp) false false true)

end ES.Builtins.Library
