import ES.Builtins.Core

/-!
# Array: the constructor's functions and Array.prototype's methods

spec: https://tc39.es/ecma262/#sec-array-objects (the core — the constructor, `isArray`,
`join`/`toString`/`push`, the iterators — is in `Builtins/Core.lean`).
-/

namespace ES.Builtins.Collections

open ES (F64)

/-! ## Helpers -/

/-- 2^53 - 1 -/
def maxSafe : Nat := 9007199254740991

/-- Runs `body k` for k = start, start + 1, … below `stop` (one fuel step each) until it returns
a result. -/
def forIdx {α} (start stop : Nat) (body : Nat → M (Option α)) : M (Option α) :=
  M.repeatFrom start fun k => do
    if k ≥ stop then return .inr none
    M.tick
    match ← body k with
    | some r => return .inr (some r)
    | none => return .inl (k + 1)

/-- Runs `body k` for k = start, start + 1, … below `stop`. -/
def forIdx_ (start stop : Nat) (body : Nat → M Unit) : M Unit := do
  let _ ← forIdx (α := Unit) start stop fun k => do body k; pure none

/-- Runs `body k` for k = start, start - 1, …, 0 (`start = none`: no iterations) until it
returns a result. -/
def forIdxDown {α} (start : Option Nat) (body : Nat → M (Option α)) : M (Option α) :=
  -- (the state is k + 1, 0 when done)
  M.repeatFrom (match start with | some k => k + 1 | none => 0) fun j => do
    if j == 0 then return .inr none
    M.tick
    match ← body (j - 1) with
    | some r => return .inr (some r)
    | none => return .inl (j - 1)

@[inline] def idxKey (k : Nat) : PropKey := PropKey.ofNat k
@[inline] def getIdx (o : ObjId) (k : Nat) : M Value := getProp o (idxKey k)
@[inline] def hasIdx (o : ObjId) (k : Nat) : M Bool := Obj'.hasProperty o (idxKey k)
@[inline] def setIdx (o : ObjId) (k : Nat) (v : Value) : M Unit := setProp o (idxKey k) v
@[inline] def setLen (o : ObjId) (n : Nat) : M Unit := setProp o (.str kLength) (numV n)

/-- A relative index (ToIntegerOrInfinity, negative counting from the end) clamped to [0, len]
(the start/end steps of slice, fill, copyWithin, …). -/
def relIndex (v : Value) (len : Nat) : M Nat := do
  match ← toIntegerOrInfinity v with
  | .inl true => pure 0
  | .inl false => pure len
  | .inr i => pure (if i < 0 then (max 0 ((len : Int) + i)).toNat else min i.toNat len)

/-- `relIndex`, `len` when undefined (an end argument). -/
def relEnd (v : Value) (len : Nat) : M Nat := if v.isUndefined then pure len else relIndex v len

/-- Checks a callback argument is callable. -/
def requireCallable (f : Value) (what : String) : M Unit := do
  if !(← isCallable f) then throwType s!"{what}: callback is not a function"

/-- ArraySpeciesCreate spec: https://tc39.es/ecma262/#sec-arrayspeciescreate -/
def arraySpeciesCreate (orig : ObjId) (length : Nat) : M ObjId := do
  -- 1-2.
  if !(← isArray (.obj orig)) then return ← arrayCreate length
  -- 3.
  let mut c ← getProp orig (.str kConstructor)
  -- 4.
  if ← isConstructor c then
    let .obj cid := c | pure ()
    let thisRealm ← readS (·.realm)
    let realmC ← getFunctionRealm cid
    if thisRealm != realmC then
      let arr ← intrinsicOf realmC "%Array%"
      if arr == cid then c := .undefined
  -- 5.
  if let .obj cid := c then
    c ← getProp cid (.sym WK.species)
    if c matches .null then c := .undefined
  -- 6.
  if c.isUndefined then return ← arrayCreate length
  -- 7.
  if !(← isConstructor c) then throwType "object.constructor[Symbol.species] is not a constructor"
  -- 8.
  match ← construct c #[numV length] with
  | .obj a => pure a
  | _ => throwType "species constructor returned a non-object"

/-- IsConcatSpreadable spec: https://tc39.es/ecma262/#sec-isconcatspreadable -/
def isConcatSpreadable (v : Value) : M Bool := do
  -- 1.
  let .obj o := v | return false
  -- 2.
  let s ← getProp o (.sym WK.isConcatSpreadable)
  -- 3.
  if !s.isUndefined then return toBoolean s
  -- 4.
  isArray v

/-- Merge sort with a comparator that may throw (a stable sort, as the spec requires of
SortIndexedProperties' implementation-defined sort). `cmp x y` is "x > y" (x goes after y).
The recursion halves the array, so a depth of 64 covers any array (sizes are below 2^53). -/
def mergeSort (cmp : Value → Value → M Bool) : Nat → Array Value → M (Array Value)
  | 0, xs => pure xs
  | d + 1, xs => do
    if xs.size ≤ 1 then return xs
    let mid := xs.size / 2
    let l ← mergeSort cmp d (xs.extract 0 mid)
    let r ← mergeSort cmp d (xs.extract mid xs.size)
    -- (merge: take from the left unless the left element is greater)
    M.repeatFrom (0, 0, Array.mkEmpty xs.size) fun (i, j, acc) => do
      if h : i < l.size then
        if h2 : j < r.size then
          M.tick
          if ← cmp l[i] r[j] then return .inl (i, j + 1, acc.push r[j])
          else return .inl (i + 1, j, acc.push l[i])
        else return .inr (acc ++ l.extract i l.size)
      else return .inr (acc ++ r.extract j r.size)

/-- SortCompare (as "x > y") spec: https://tc39.es/ecma262/#sec-sortcompare -/
def sortCompareGt (comparefn : Value) (x y : Value) : M Bool := do
  -- 1-4.
  match x, y with
  | .undefined, .undefined => return false
  | .undefined, _ => return true
  | _, .undefined => return false
  | _, _ => pure ()
  -- 5.
  if !comparefn.isUndefined then
    let v ← toNum (← call comparefn .undefined #[x, y])
    -- (NaN is +0)
    return F64.lt F64.zero v
  -- 6-12.
  let xs ← toStr x
  let ys ← toStr y
  pure (ys.lt xs)

/-- SortIndexedProperties (`skipHoles`: skip-holes vs read-through-holes)
spec: https://tc39.es/ecma262/#sec-sortindexedproperties -/
def sortIndexedProperties (o : ObjId) (len : Nat) (cmp : Value → Value → M Bool) (skipHoles : Bool) :
    M (Array Value) := do
  -- 1-3.
  let items ← M.repeatFrom (0, (#[] : Array Value)) fun (k, items) => do
    if k ≥ len then return .inr items
    M.tick
    -- a-b.
    let kRead ← if skipHoles then hasIdx o k else pure true
    -- c.
    if kRead then return .inl (k + 1, items.push (← getIdx o k))
    return .inl (k + 1, items)
  -- 4-5.
  mergeSort cmp 64 items

/-! ## The Array constructor's functions -/

/-- Array.from spec: https://tc39.es/ecma262/#sec-array.from -/
def arrayFrom : BuiltinFn := fun _ thisV args _ => do
  let items := arg args 0
  let mapfn := arg args 1
  let thisArg := arg args 2
  -- 1.
  let c := thisV
  -- 2-3.
  let mapping := !mapfn.isUndefined
  if mapping then requireCallable mapfn "Array.from"
  -- 4.
  let usingIterator ← getMethodOf items (.sym WK.iterator)
  -- 5.
  if let some m := usingIterator then
    -- a-b.
    let a ← if ← isConstructor c then construct c #[] else pure (.obj (← arrayCreate 0))
    let .obj a := a | throwType "Array.from: constructor returned a non-object"
    -- c.
    let r ← getIteratorFromMethod items m
    -- d-e.
    return ← M.repeatFrom (r, 0) fun (r, k) => do
      M.tick
      -- i.
      if k ≥ maxSafe then
        let e ← makeError .typeError "Array.from: too many elements"
        iteratorCloseOnThrow r e
      -- iii.
      let (r, next) ← iteratorStepValue r
      match next with
      -- iv.
      | none => setLen a k; return .inr (Value.obj a)
      | some v =>
        withIterClose r do
          -- v-vi.
          let mapped ← if mapping then call mapfn thisArg #[v, numV k] else pure v
          -- vii-viii.
          createDataPropertyOrThrow a (idxKey k) mapped
          return .inl (r, k + 1)
  -- 6-8.
  let arrayLike ← toObj items
  let len ← lengthOf arrayLike
  -- 9-10.
  let a ← if ← isConstructor c then construct c #[numV len] else pure (.obj (← arrayCreate len))
  let .obj a := a | throwType "Array.from: constructor returned a non-object"
  -- 11-12.
  forIdx_ 0 len fun k => do
    let kv ← getIdx arrayLike k
    let mapped ← if mapping then call mapfn thisArg #[kv, numV k] else pure kv
    createDataPropertyOrThrow a (idxKey k) mapped
  -- 13-14.
  setLen a len
  pure (.obj a)

/-- Array.of spec: https://tc39.es/ecma262/#sec-array.of -/
def arrayOf : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let len := args.size
  let c := thisV
  -- 3-4.
  let a ← if ← isConstructor c then construct c #[numV len] else pure (.obj (← arrayCreate len))
  let .obj a := a | throwType "Array.of: constructor returned a non-object"
  -- 5-6.
  forIdx_ 0 len fun k => createDataPropertyOrThrow a (idxKey k) args[k]!
  -- 7-8.
  setLen a len
  pure (.obj a)

/-! ## Array.prototype -/

/-- Array.prototype.at spec: https://tc39.es/ecma262/#sec-array.prototype.at -/
def arrayAt : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let k : Int ← match ← toIntegerOrInfinity (arg args 0) with
    | .inl _ => pure (-1)
    | .inr i => pure (if i ≥ 0 then i else len + i)
  if k < 0 || k ≥ len then return .undefined
  getIdx o k.toNat

/-- Array.prototype.concat spec: https://tc39.es/ecma262/#sec-array.prototype.concat -/
def arrayConcat : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let o ← toObj thisV
  let a ← arraySpeciesCreate o 0
  -- 3-4.
  let items := #[Value.obj o] ++ args
  let n ← M.foldArr items 0 fun n e => do
    M.tick
    -- a.
    if ← isConcatSpreadable e then
      let .obj eo := e | pure n
      let len ← lengthOf eo
      if n + len > maxSafe then throwType "concat: result too long"
      M.repeatFrom (n, 0) fun (n, k) => do
        if k ≥ len then return .inr n
        M.tick
        if ← hasIdx eo k then
          createDataPropertyOrThrow a (idxKey n) (← getIdx eo k)
        return .inl (n + 1, k + 1)
    else
      if n ≥ maxSafe then throwType "concat: result too long"
      createDataPropertyOrThrow a (idxKey n) e
      pure (n + 1)
  -- 5.
  setLen a n
  pure (.obj a)

/-- Array.prototype.copyWithin spec: https://tc39.es/ecma262/#sec-array.prototype.copywithin -/
def arrayCopyWithin : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let to ← relIndex (arg args 0) len
  let fr ← relIndex (arg args 1) len
  let final ← relEnd (arg args 2) len
  -- 11.
  let count : Int := min ((final : Int) - fr) ((len : Int) - to)
  -- 12-13.
  let (dir, fr, to) : Int × Int × Int :=
    if (fr : Int) < to && (to : Int) < fr + count then (-1, fr + count - 1, to + count - 1)
    else (1, fr, to)
  -- 14.
  M.repeatFrom (fr, to, count) fun (fr, to, count) => do
    if count ≤ 0 then return .inr (Value.obj o)
    M.tick
    let fk := idxKey fr.toNat
    let tk := idxKey to.toNat
    if ← Obj'.hasProperty o fk then setProp o tk (← getProp o fk)
    else deletePropertyOrThrow o tk
    return .inl (fr + dir, to + dir, count - 1)

/-- every (`some` = false), some (`some` = true) spec: https://tc39.es/ecma262/#sec-array.prototype.every -/
def arrayEverySome (isSome : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let cb := arg args 0
  requireCallable cb (if isSome then "Array.prototype.some" else "Array.prototype.every")
  let r ← forIdx 0 len fun k => do
    if ← hasIdx o k then
      let kv ← getIdx o k
      let t := toBoolean (← call cb (arg args 1) #[kv, numV k, .obj o])
      if t == isSome then return some ()
    pure none
  pure (.bool (if r.isSome then isSome else !isSome))

/-- Array.prototype.fill spec: https://tc39.es/ecma262/#sec-array.prototype.fill -/
def arrayFill : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let k ← relIndex (arg args 1) len
  let final ← relEnd (arg args 2) len
  forIdx_ k final fun k => setIdx o k (arg args 0)
  pure (.obj o)

/-- Array.prototype.filter spec: https://tc39.es/ecma262/#sec-array.prototype.filter -/
def arrayFilter : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let cb := arg args 0
  requireCallable cb "Array.prototype.filter"
  let a ← arraySpeciesCreate o 0
  let _ ← M.repeatFrom (0, 0) fun (k, to) => do
    if k ≥ len then return .inr ()
    M.tick
    if ← hasIdx o k then
      let kv ← getIdx o k
      if toBoolean (← call cb (arg args 1) #[kv, numV k, .obj o]) then
        createDataPropertyOrThrow a (idxKey to) kv
        return .inl (k + 1, to + 1)
    return .inl (k + 1, to)
  pure (.obj a)

/-- FindViaPredicate (ascending or descending); the index (-1: none) and value.
spec: https://tc39.es/ecma262/#sec-findviapredicate -/
def findViaPredicate (o : ObjId) (len : Nat) (ascending : Bool) (pred thisArg : Value) : M (Int × Value) := do
  requireCallable pred "find"
  let body (k : Nat) : M (Option (Int × Value)) := do
    let kv ← getIdx o k
    if toBoolean (← call pred thisArg #[kv, numV k, .obj o]) then return some ((k : Int), kv)
    pure none
  let r ← if ascending then forIdx 0 len body else forIdxDown (if len == 0 then none else some (len - 1)) body
  pure (r.getD (-1, .undefined))

/-- find/findIndex/findLast/findLastIndex spec: https://tc39.es/ecma262/#sec-array.prototype.find -/
def arrayFind (ascending wantIndex : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let (i, v) ← findViaPredicate o len ascending (arg args 0) (arg args 1)
  pure (if wantIndex then intV i else v)

/-- FlattenIntoArray (`depth = none`: +∞); returns the next target index. The recursion depth
is bounded by `fuel` (each nesting level one; exhausting it is a RangeError, like the stack
overflow engines report for deeply nested or cyclic arrays).
spec: https://tc39.es/ecma262/#sec-flattenintoarray -/
def flattenIntoArray (target source : ObjId) (sourceLen start : Nat) (depth : Option Nat)
    (mapper : Option (Value × Value)) : Nat → M Nat
  | 0 => throwRange "Maximum call stack size exceeded"
  | fuel + 1 => do
    M.repeatFrom (0, start) fun (si, ti) => do
      if si ≥ sourceLen then return .inr ti
      M.tick
      if !(← hasIdx source si) then return .inl (si + 1, ti)
      let el ← getIdx source si
      let el ← match mapper with
        | some (f, thisArg) => call f thisArg #[el, numV si, .obj source]
        | none => pure el
      let shouldFlatten ← if depth != some 0 then isArray el else pure false
      if shouldFlatten then
        let .obj eo := el | return .inl (si + 1, ti)
        let newDepth := depth.map (· - 1)
        let elLen ← lengthOf eo
        let ti ← flattenIntoArray target eo elLen ti newDepth none fuel
        return .inl (si + 1, ti)
      if ti ≥ maxSafe then throwType "flat: result too long"
      createDataPropertyOrThrow target (idxKey ti) el
      return .inl (si + 1, ti + 1)

/-- The nesting bound of `flattenIntoArray`. -/
def flatFuel : Nat := 10000

/-- Array.prototype.flat spec: https://tc39.es/ecma262/#sec-array.prototype.flat -/
def arrayFlat : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let sourceLen ← lengthOf o
  let depth : Option Nat ← if (arg args 0).isUndefined then pure (some 1) else
    match ← toIntegerOrInfinity (arg args 0) with
    | .inl true => pure (some 0)
    | .inl false => pure none
    | .inr i => pure (some (max 0 i).toNat)
  let a ← arraySpeciesCreate o 0
  let _ ← flattenIntoArray a o sourceLen 0 depth none flatFuel
  pure (.obj a)

/-- Array.prototype.flatMap spec: https://tc39.es/ecma262/#sec-array.prototype.flatmap -/
def arrayFlatMap : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let sourceLen ← lengthOf o
  requireCallable (arg args 0) "Array.prototype.flatMap"
  let a ← arraySpeciesCreate o 0
  let _ ← flattenIntoArray a o sourceLen 0 (some 1) (some (arg args 0, arg args 1)) flatFuel
  pure (.obj a)

/-- Array.prototype.forEach spec: https://tc39.es/ecma262/#sec-array.prototype.foreach -/
def arrayForEach : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let cb := arg args 0
  requireCallable cb "Array.prototype.forEach"
  forIdx_ 0 len fun k => do
    if ← hasIdx o k then
      let kv ← getIdx o k
      let _ ← call cb (arg args 1) #[kv, numV k, .obj o]
  pure .undefined

/-- The start index of includes/indexOf (`none`: no element to look at).
spec: https://tc39.es/ecma262/#sec-array.prototype.includes (steps 4-10) -/
def searchStart (fromIndex : Value) (len : Nat) : M (Option Nat) := do
  match ← toIntegerOrInfinity fromIndex with
  | .inl false => pure none
  | .inl true => pure (some 0)
  | .inr n => pure (some (if n ≥ 0 then n.toNat else (max 0 ((len : Int) + n)).toNat))

/-- Array.prototype.includes spec: https://tc39.es/ecma262/#sec-array.prototype.includes -/
def arrayIncludes : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len == 0 then return .bool false
  let some k ← searchStart (arg args 1) len | return .bool false
  let r ← forIdx k len fun k => do
    if sameValueZero (← getIdx o k) (arg args 0) then return some () else pure none
  pure (.bool r.isSome)

/-- Array.prototype.indexOf spec: https://tc39.es/ecma262/#sec-array.prototype.indexof -/
def arrayIndexOf : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len == 0 then return intV (-1)
  let some k ← searchStart (arg args 1) len | return intV (-1)
  let r ← forIdx k len fun k => do
    if ← hasIdx o k then
      if isStrictlyEqual (← getIdx o k) (arg args 0) then return some k
    pure none
  pure (match r with | some k => numV k | none => intV (-1))

/-- Array.prototype.lastIndexOf spec: https://tc39.es/ecma262/#sec-array.prototype.lastindexof -/
def arrayLastIndexOf : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len == 0 then return intV (-1)
  let n ← if args.size > 1 then toIntegerOrInfinity (arg args 1) else pure (.inr ((len : Int) - 1))
  let start : Option Nat := match n with
    | .inl true => none
    | .inl false => some (len - 1)
    | .inr n => if n ≥ 0 then some (min n.toNat (len - 1))
      else if (len : Int) + n < 0 then none else some ((len : Int) + n).toNat
  let r ← forIdxDown start fun k => do
    if ← hasIdx o k then
      if isStrictlyEqual (← getIdx o k) (arg args 0) then return some k
    pure none
  pure (match r with | some k => numV k | none => intV (-1))

/-- Array.prototype.map spec: https://tc39.es/ecma262/#sec-array.prototype.map -/
def arrayMap : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let cb := arg args 0
  requireCallable cb "Array.prototype.map"
  let a ← arraySpeciesCreate o len
  forIdx_ 0 len fun k => do
    if ← hasIdx o k then
      let kv ← getIdx o k
      let mv ← call cb (arg args 1) #[kv, numV k, .obj o]
      createDataPropertyOrThrow a (idxKey k) mv
  pure (.obj a)

/-- Array.prototype.pop spec: https://tc39.es/ecma262/#sec-array.prototype.pop -/
def arrayPop : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len == 0 then
    setLen o 0
    return .undefined
  let newLen := len - 1
  let el ← getIdx o newLen
  deletePropertyOrThrow o (idxKey newLen)
  setLen o newLen
  pure el

/-- reduce / reduceRight spec: https://tc39.es/ecma262/#sec-array.prototype.reduce -/
def arrayReduce (right : Bool) : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let cb := arg args 0
  requireCallable cb (if right then "Array.prototype.reduceRight" else "Array.prototype.reduce")
  if len == 0 && args.size < 2 then throwType "Reduce of empty array with no initial value"
  -- (positions in visiting order: i ↦ the index)
  let idx (i : Nat) : Nat := if right then len - 1 - i else i
  let (start, acc) ← if args.size ≥ 2 then pure (0, args[1]!) else do
    let r ← forIdx 0 len fun i => do
      if ← hasIdx o (idx i) then return some (i, ← getIdx o (idx i)) else pure none
    match r with
    | some (i, v) => pure (i + 1, v)
    | none => throwType "Reduce of empty array with no initial value"
  M.repeatFrom (start, acc) fun (i, acc) => do
    if i ≥ len then return .inr acc
    M.tick
    let k := idx i
    if ← hasIdx o k then
      let kv ← getIdx o k
      return .inl (i + 1, ← call cb .undefined #[acc, kv, numV k, .obj o])
    return .inl (i + 1, acc)

/-- Array.prototype.reverse spec: https://tc39.es/ecma262/#sec-array.prototype.reverse -/
def arrayReverse : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let middle := len / 2
  forIdx_ 0 middle fun lower => do
    let upper := len - lower - 1
    let lowerExists ← hasIdx o lower
    let lowerValue ← if lowerExists then getIdx o lower else pure .undefined
    let upperExists ← hasIdx o upper
    let upperValue ← if upperExists then getIdx o upper else pure .undefined
    if lowerExists && upperExists then
      setIdx o lower upperValue
      setIdx o upper lowerValue
    else if !lowerExists && upperExists then
      setIdx o lower upperValue
      deletePropertyOrThrow o (idxKey upper)
    else if lowerExists && !upperExists then
      deletePropertyOrThrow o (idxKey lower)
      setIdx o upper lowerValue
  pure (.obj o)

/-- Array.prototype.shift spec: https://tc39.es/ecma262/#sec-array.prototype.shift -/
def arrayShift : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  if len == 0 then
    setLen o 0
    return .undefined
  let first ← getIdx o 0
  forIdx_ 1 len fun k => do
    if ← hasIdx o k then setIdx o (k - 1) (← getIdx o k)
    else deletePropertyOrThrow o (idxKey (k - 1))
  deletePropertyOrThrow o (idxKey (len - 1))
  setLen o (len - 1)
  pure first

/-- Array.prototype.slice spec: https://tc39.es/ecma262/#sec-array.prototype.slice -/
def arraySlice : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let k ← relIndex (arg args 0) len
  let final ← relEnd (arg args 1) len
  let count := final - k
  let a ← arraySpeciesCreate o count
  let n ← M.repeatFrom (k, 0) fun (k, n) => do
    if k ≥ final then return .inr n
    M.tick
    if ← hasIdx o k then createDataPropertyOrThrow a (idxKey n) (← getIdx o k)
    return .inl (k + 1, n + 1)
  setLen a n
  pure (.obj a)

/-- Array.prototype.sort spec: https://tc39.es/ecma262/#sec-array.prototype.sort -/
def arraySort : BuiltinFn := fun _ thisV args _ => do
  let cmp := arg args 0
  -- 1.
  if !cmp.isUndefined && !(← isCallable cmp) then throwType "The comparison function must be either a function or undefined"
  -- 2-3.
  let o ← toObj thisV
  let len ← lengthOf o
  -- 4-5.
  let sorted ← sortIndexedProperties o len (sortCompareGt cmp) true
  -- 6-9.
  forIdx_ 0 sorted.size fun j => setIdx o j sorted[j]!
  forIdx_ sorted.size len fun j => deletePropertyOrThrow o (idxKey j)
  pure (.obj o)

/-- The actual delete/skip count of splice and toSpliced (steps 8-10). -/
def spliceCount (args : Array Value) (len actualStart : Nat) : M Nat := do
  if args.size == 0 then pure 0
  else if args.size == 1 then pure (len - actualStart)
  else
    let dc ← toIntClamp args[1]! 0 ((len : Int) - actualStart)
    pure dc.toNat

/-- Array.prototype.splice spec: https://tc39.es/ecma262/#sec-array.prototype.splice -/
def arraySplice : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let actualStart ← relIndex (arg args 0) len
  let items := args.extract 2 args.size
  let itemCount := items.size
  let dc ← spliceCount args len actualStart
  if len + itemCount - dc > maxSafe then throwType "splice: result too long"
  let a ← arraySpeciesCreate o dc
  forIdx_ 0 dc fun k => do
    if ← hasIdx o (actualStart + k) then
      createDataPropertyOrThrow a (idxKey k) (← getIdx o (actualStart + k))
  setLen a dc
  if itemCount < dc then
    forIdx_ actualStart (len - dc) fun k => do
      let fr := k + dc
      let to := k + itemCount
      if ← hasIdx o fr then setIdx o to (← getIdx o fr)
      else deletePropertyOrThrow o (idxKey to)
    -- (k from len down to len - dc + itemCount + 1: delete k - 1)
    let lo := len - dc + itemCount
    let _ ← forIdxDown (α := Unit) (if len > lo then some (len - 1) else none) fun j => do
      if j < lo then return some ()
      deletePropertyOrThrow o (idxKey j)
      pure none
  else if itemCount > dc then
    -- (k from len - dc down to actualStart + 1)
    let hi := len - dc
    let _ ← forIdxDown (α := Unit) (if hi > actualStart then some hi else none) fun k => do
      if k ≤ actualStart then return some ()
      let fr := k + dc - 1
      let to := k + itemCount - 1
      if ← hasIdx o fr then setIdx o to (← getIdx o fr)
      else deletePropertyOrThrow o (idxKey to)
      pure none
  forIdx_ 0 itemCount fun i => setIdx o (actualStart + i) items[i]!
  setLen o (len - dc + itemCount)
  pure (.obj a)

/-- Array.prototype.toLocaleString spec: https://tc39.es/ecma262/#sec-array.prototype.tolocalestring -/
def arrayToLocaleString : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  -- (the list separator: "," as browsers use)
  M.repeatFrom (0, JSStr.empty) fun (k, r) => do
    if k ≥ len then return .inr (Value.str r)
    M.tick
    let r := if k > 0 then r ++ JSStr.ofString "," else r
    let e ← getIdx o k
    if e.isNullish then return .inl (k + 1, r)
    let s ← toStr (← invoke e (.str "toLocaleString"))
    return .inl (k + 1, r ++ s)

/-- Array.prototype.toReversed spec: https://tc39.es/ecma262/#sec-array.prototype.toreversed -/
def arrayToReversed : BuiltinFn := fun _ thisV _ _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let a ← arrayCreate len
  forIdx_ 0 len fun k => do
    createDataPropertyOrThrow a (idxKey k) (← getIdx o (len - k - 1))
  pure (.obj a)

/-- Array.prototype.toSorted spec: https://tc39.es/ecma262/#sec-array.prototype.tosorted -/
def arrayToSorted : BuiltinFn := fun _ thisV args _ => do
  let cmp := arg args 0
  if !cmp.isUndefined && !(← isCallable cmp) then throwType "The comparison function must be either a function or undefined"
  let o ← toObj thisV
  let len ← lengthOf o
  let a ← arrayCreate len
  let sorted ← sortIndexedProperties o len (sortCompareGt cmp) false
  forIdx_ 0 sorted.size fun j => createDataPropertyOrThrow a (idxKey j) sorted[j]!
  pure (.obj a)

/-- Array.prototype.toSpliced spec: https://tc39.es/ecma262/#sec-array.prototype.tospliced -/
def arrayToSpliced : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let actualStart ← relIndex (arg args 0) len
  let items := args.extract 2 args.size
  let skip ← spliceCount args len actualStart
  let newLen := len + items.size - skip
  if newLen > maxSafe then throwType "toSpliced: result too long"
  let a ← arrayCreate newLen
  forIdx_ 0 actualStart fun i => do createDataPropertyOrThrow a (idxKey i) (← getIdx o i)
  forIdx_ 0 items.size fun j => createDataPropertyOrThrow a (idxKey (actualStart + j)) items[j]!
  let i0 := actualStart + items.size
  let r0 := actualStart + skip
  forIdx_ i0 newLen fun i => do createDataPropertyOrThrow a (idxKey i) (← getIdx o (r0 + (i - i0)))
  pure (.obj a)

/-- Array.prototype.unshift spec: https://tc39.es/ecma262/#sec-array.prototype.unshift -/
def arrayUnshift : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let argCount := args.size
  if argCount > 0 then
    if len + argCount > maxSafe then throwType "unshift: result too long"
    -- (k from len down to 1)
    let _ ← forIdxDown (α := Unit) (if len > 0 then some len else none) fun k => do
      if k == 0 then return some ()
      let fr := k - 1
      let to := k + argCount - 1
      if ← hasIdx o fr then setIdx o to (← getIdx o fr)
      else deletePropertyOrThrow o (idxKey to)
      pure none
    forIdx_ 0 argCount fun j => setIdx o j args[j]!
  setLen o (len + argCount)
  pure (numV (len + argCount))

/-- Array.prototype.with spec: https://tc39.es/ecma262/#sec-array.prototype.with -/
def arrayWith : BuiltinFn := fun _ thisV args _ => do
  let o ← toObj thisV
  let len ← lengthOf o
  let actual : Int ← match ← toIntegerOrInfinity (arg args 0) with
    | .inl _ => pure (-1)
    | .inr i => pure (if i ≥ 0 then i else len + i)
  if actual ≥ len || actual < 0 then throwRange "Invalid index"
  let a ← arrayCreate len
  forIdx_ 0 len fun k => do
    let v ← if (k : Int) == actual then pure (arg args 1) else getIdx o k
    createDataPropertyOrThrow a (idxKey k) v
  pure (.obj a)

/-! ## Array.fromAsync

spec: https://tc39.es/ecma262/#sec-array.fromasync

A built-in async function: its closure runs until an Await, which becomes a promise reaction
whose handler (a built-in with the state object and the await's position in its slots) runs
the steps after it. The state object's slots: 0 resolve, 1 reject, 2 the promise, 3 A, 4 k,
5 the iterator, 6 its next method, 7 mapfn, 8 thisArg, 9 arrayLike, 10 len, 11 mapping,
12 the completion an AsyncIteratorClose returns after its await. -/

def faGet (st : ObjId) (i : Nat) : M Value := readObj st fun o => match o.kind with
  | .internal _ sl => sl[i]?.getD .undefined
  | _ => .undefined

def faSet (st : ObjId) (i : Nat) (v : Value) : M Unit := modifyObj st fun o => o.withKind fun k =>
  match k with
  | .internal t sl => .internal t (sl.set! i v)
  | k => k

def faNat (st : ObjId) (i : Nat) : M Nat := do
  match ← faGet st i with
  | .num x => pure ((Conv.toNat? x).getD 0)
  | _ => pure 0

/-- Await(v) in the closure: continues at `phase` when `v` settles.
spec: https://tc39.es/ecma262/#await -/
def faAwait (st : ObjId) (phase : Nat) (v : Value) : M Unit := do
  let p ← promiseResolve (← intrinsicV "%Promise%") v
  let onF ← makeBuiltinFn "Array.fromAsync continuation" 1 JSStr.empty #[.obj st, numV phase, .bool false]
  let onR ← makeBuiltinFn "Array.fromAsync continuation" 1 JSStr.empty #[.obj st, numV phase, .bool true]
  let .obj pid := p | M.halt "internal: PromiseResolve returned a non-object"
  let _ ← performPromiseThen pid (.obj onF) (.obj onR) none

/-- The closure completes with a throw: the promise is rejected. -/
def faReject (st : ObjId) (e : Value) : M Unit := do
  let _ ← call (← faGet st 1) .undefined #[e]

/-- AsyncIteratorClose(iteratorRecord, throw e), then the rejection.
spec: https://tc39.es/ecma262/#sec-asynciteratorclose -/
def faCloseReject (st : ObjId) (e : Value) : M Unit := do
  let iter ← faGet st 5
  -- 3-4.
  let r ← M.attempt do
    match ← getMethodOf iter (.str "return") with
    | none => pure false
    | some f =>
      let inner ← call f iter #[]
      faSet st 12 e
      faAwait st 4 inner
      pure true
  -- 5.
  match r with
  | .ok true => pure ()
  | _ => faReject st e

/-- Step 3.h.iv, from 1. to 4.: the iterator's next result, awaited. -/
def faIterNext (st : ObjId) : M Unit := do
  let k ← faNat st 4
  -- 1.
  if k ≥ maxSafe then
    faCloseReject st (← makeError .typeError "Array.fromAsync: too many elements")
    return
  -- 3-4.
  match ← M.attempt (do faAwait st 0 (← call (← faGet st 6) (← faGet st 5) #[])) with
  | .ok _ => pure ()
  | .error e => faReject st e

/-- Step 3.i.vii, 1. to 3.: the array-like's next element, awaited (or the end). -/
def faArrayNext (st : ObjId) : M Unit := do
  let k ← faNat st 4
  let len ← faNat st 10
  let .obj a ← faGet st 3 | pure ()
  let .obj al ← faGet st 9 | pure ()
  if k < len then
    match ← M.attempt (do faAwait st 2 (← getIdx al k)) with
    | .ok _ => pure ()
    | .error e => faReject st e
  else
    -- viii-ix.
    match ← M.attempt (setLen a len) with
    | .ok _ => let _ ← call (← faGet st 0) .undefined #[.obj a]
    | .error e => faReject st e

/-- CreateDataPropertyOrThrow(A, Pk, mappedValue), then the next element. -/
def faDefine (st : ObjId) (v : Value) (isIter : Bool) : M Unit := do
  let k ← faNat st 4
  let .obj a ← faGet st 3 | pure ()
  match ← M.attempt (createDataPropertyOrThrow a (idxKey k) v) with
  | .error e => if isIter then faCloseReject st e else faReject st e
  | .ok _ =>
    faSet st 4 (numV (k + 1))
    if isIter then faIterNext st else faArrayNext st

/-- Step 3.h.iv, from 5.: the awaited next result. -/
def faIterResult (st : ObjId) (v : Value) : M Unit := do
  let k ← faNat st 4
  let .obj a ← faGet st 3 | pure ()
  let r ← M.attempt do
    -- 5.
    if !v.isObject then throwType "Iterator result is not an object"
    -- 6-7.
    if ← iteratorComplete v then
      setLen a k
      let _ ← call (← faGet st 0) .undefined #[.obj a]
      return none
    -- 8.
    some <$> iteratorValue v
  match r with
  | .error e => faReject st e
  | .ok none => pure ()
  | .ok (some nv) =>
    -- 9-10.
    if toBoolean (← faGet st 11) then
      match ← M.attempt (call (← faGet st 7) (← faGet st 8) #[nv, numV k]) with
      | .error e => faCloseReject st e
      | .ok mv =>
        match ← M.attempt (faAwait st 1 mv) with
        | .error e => faCloseReject st e
        | .ok _ => pure ()
    else faDefine st nv true

/-- Step 3.i.vii, from 4.: the awaited element. -/
def faArrayValue (st : ObjId) (v : Value) : M Unit := do
  let k ← faNat st 4
  if toBoolean (← faGet st 11) then
    match ← M.attempt (do faAwait st 3 (← call (← faGet st 7) (← faGet st 8) #[v, numV k])) with
    | .error e => faReject st e
    | .ok _ => pure ()
  else faDefine st v false

/-- The reaction handlers of the closure's awaits. -/
def fromAsyncContinuation : BuiltinFn := fun self _ args _ => do
  let sl ← builtinSlots self
  let .obj st := sl[0]! | return .undefined
  let phase := match sl[1]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  let isReject := toBoolean sl[2]!
  let v := arg args 0
  match phase with
  | 0 => if isReject then faReject st v else faIterResult st v
  | 1 => if isReject then faCloseReject st v else faDefine st v true
  | 2 => if isReject then faReject st v else faArrayValue st v
  | 3 => if isReject then faReject st v else faDefine st v false
  | _ => faReject st (← faGet st 12)
  pure .undefined

/-- fromAsyncClosure up to its first Await. -/
def fromAsyncStart (st : ObjId) (c asyncItems mapfn : Value) : M Unit := do
  -- a-b.
  let mapping := !mapfn.isUndefined
  if mapping then requireCallable mapfn "Array.fromAsync"
  faSet st 11 (.bool mapping)
  -- c-d.
  let usingAsync ← getMethodOf asyncItems (.sym WK.asyncIterator)
  let usingSync ← if usingAsync.isNone then getMethodOf asyncItems (.sym WK.iterator) else pure none
  -- e-g.
  let iterRec ← match usingAsync, usingSync with
    | some m, _ => some <$> getIteratorFromMethod asyncItems m
    | none, some m => do some <$> createAsyncFromSyncIterator (← getIteratorFromMethod asyncItems m)
    | none, none => pure none
  match iterRec with
  -- h.
  | some r =>
    let a ← if ← isConstructor c then construct c #[] else pure (.obj (← arrayCreate 0))
    faSet st 3 a
    faSet st 5 r.iter
    faSet st 6 r.next
    faIterNext st
  -- i.
  | none =>
    let arrayLike ← toObj asyncItems
    let len ← lengthOf arrayLike
    let a ← if ← isConstructor c then construct c #[numV len] else pure (.obj (← arrayCreate len))
    faSet st 3 a
    faSet st 9 (.obj arrayLike)
    faSet st 10 (numV len)
    faArrayNext st

/-- Array.fromAsync spec: https://tc39.es/ecma262/#sec-array.fromasync -/
def arrayFromAsync : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let cap ← newIntrinsicPromise
  let st ← alloc { kind := .internal "Array.fromAsync" #[cap.resolve, cap.reject, cap.promise,
    .undefined, numV 0, .undefined, .undefined, arg args 1, arg args 2, .undefined, numV 0,
    .bool false, .undefined] }
  -- 3-4.
  match ← M.attempt (fromAsyncStart st thisV (arg args 0) (arg args 1)) with
  | .error e => faReject st e
  | .ok _ => pure ()
  -- 5.
  pure cap.promise

/-- This file's behaviours. -/
def arrayDefs : Array BuiltinDef := #[
  ⟨"Array.from", arrayFrom⟩, ⟨"Array.of", arrayOf⟩, ⟨"Array.fromAsync", arrayFromAsync⟩,
  ⟨"Array.fromAsync continuation", fromAsyncContinuation⟩,
  ⟨"Array.prototype.at", arrayAt⟩, ⟨"Array.prototype.concat", arrayConcat⟩,
  ⟨"Array.prototype.copyWithin", arrayCopyWithin⟩, ⟨"Array.prototype.every", arrayEverySome false⟩,
  ⟨"Array.prototype.some", arrayEverySome true⟩, ⟨"Array.prototype.fill", arrayFill⟩,
  ⟨"Array.prototype.filter", arrayFilter⟩, ⟨"Array.prototype.find", arrayFind true false⟩,
  ⟨"Array.prototype.findIndex", arrayFind true true⟩, ⟨"Array.prototype.findLast", arrayFind false false⟩,
  ⟨"Array.prototype.findLastIndex", arrayFind false true⟩, ⟨"Array.prototype.flat", arrayFlat⟩,
  ⟨"Array.prototype.flatMap", arrayFlatMap⟩, ⟨"Array.prototype.forEach", arrayForEach⟩,
  ⟨"Array.prototype.includes", arrayIncludes⟩, ⟨"Array.prototype.indexOf", arrayIndexOf⟩,
  ⟨"Array.prototype.lastIndexOf", arrayLastIndexOf⟩, ⟨"Array.prototype.map", arrayMap⟩,
  ⟨"Array.prototype.pop", arrayPop⟩, ⟨"Array.prototype.reduce", arrayReduce false⟩,
  ⟨"Array.prototype.reduceRight", arrayReduce true⟩, ⟨"Array.prototype.reverse", arrayReverse⟩,
  ⟨"Array.prototype.shift", arrayShift⟩, ⟨"Array.prototype.slice", arraySlice⟩,
  ⟨"Array.prototype.sort", arraySort⟩, ⟨"Array.prototype.splice", arraySplice⟩,
  ⟨"Array.prototype.toLocaleString", arrayToLocaleString⟩,
  ⟨"Array.prototype.toReversed", arrayToReversed⟩, ⟨"Array.prototype.toSorted", arrayToSorted⟩,
  ⟨"Array.prototype.toSpliced", arrayToSpliced⟩, ⟨"Array.prototype.unshift", arrayUnshift⟩,
  ⟨"Array.prototype.with", arrayWith⟩]

/-- Adds the methods to %Array% and %Array.prototype%. -/
def arraySetup : M Unit := do
  let ac ← intrinsic "%Array%"
  let ap ← intrinsic "%Array.prototype%"
  let _ ← defMethod ac (.str "from") "Array.from" 1
  let _ ← defMethod ac (.str "of") "Array.of" 0
  let _ ← defMethod ac (.str "fromAsync") "Array.fromAsync" 1
  for (nm, len) in [("at", 1), ("concat", 1), ("copyWithin", 2), ("every", 1), ("some", 1),
      ("fill", 1), ("filter", 1), ("find", 1), ("findIndex", 1), ("findLast", 1),
      ("findLastIndex", 1), ("flat", 0), ("flatMap", 1), ("forEach", 1), ("includes", 1),
      ("indexOf", 1), ("lastIndexOf", 1), ("map", 1), ("pop", 0), ("reduce", 1),
      ("reduceRight", 1), ("reverse", 0), ("shift", 0), ("slice", 2), ("sort", 1), ("splice", 2),
      ("toLocaleString", 0), ("toReversed", 0), ("toSorted", 1), ("toSpliced", 2),
      ("unshift", 1), ("with", 2)] do
    let _ ← defMethod ap (.str (JSStr.ofString nm)) s!"Array.prototype.{nm}" len
  -- %Array.prototype%[@@unscopables] spec: https://tc39.es/ecma262/#sec-array.prototype-%symbol.unscopables%
  let u ← ordinaryObjectCreate .null
  for nm in ["at", "copyWithin", "entries", "fill", "find", "findIndex", "findLast",
      "findLastIndex", "flat", "flatMap", "includes", "keys", "toReversed", "toSorted",
      "toSpliced", "values"] do
    setOwn u (.str (JSStr.ofString nm)) (.data (.bool true) true true true)
  setOwn ap (.sym WK.unscopables) (.data (.obj u) false false true)

end ES.Builtins.Collections
