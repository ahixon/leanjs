import ES.Builtins.Core

/-!
# Number, Math, BigInt, and the global functions (isNaN, isFinite, parseInt, parseFloat, the URI
functions, Annex B escape/unescape)

spec: https://tc39.es/ecma262/#sec-number-objects
spec: https://tc39.es/ecma262/#sec-math-object
spec: https://tc39.es/ecma262/#sec-bigint-objects
spec: https://tc39.es/ecma262/#sec-function-properties-of-the-global-object
spec: https://tc39.es/ecma262/#sec-additional-properties-of-the-global-object
-/

namespace ES.Builtins.Text

open ES (F64)

/-! ## Helpers -/

/-- A Number constant from its shortest decimal representation. -/
def numLit (s : String) : F64 := Num.stringToNumber (JSStr.ofString s)

/-- ToIntegerOrInfinity as a Number. -/
def toIntegerF (v : Value) : M F64 := do pure (Num.toIntegerOrInfinity (← toNum v))

/-- Defines a method on `o` whose behaviour is named `{pfx}.{nm}`. -/
def defMethods (o : ObjId) (pfx : String) (ms : List (String × Nat)) : M Unit := do
  for (nm, len) in ms do
    let _ ← defMethod o (.str (JSStr.ofString nm)) s!"{pfx}.{nm}" len

/-- An uppercase two-digit hexadecimal byte. -/
def hexByte (b : Nat) (upper := true) : JSStr :=
  let ds := if upper then "0123456789ABCDEF" else "0123456789abcdef"
  JSStr.ofString (String.ofList [ds.toList[b / 16 % 16]!, ds.toList[b % 16]!])

/-- The value of a hexadecimal digit code unit (none if not one). -/
def hexVal (u : UInt16) : Option Nat :=
  if 48 ≤ u && u ≤ 57 then some (u.toNat - 48)
  else if 65 ≤ u && u ≤ 70 then some (u.toNat - 55)
  else if 97 ≤ u && u ≤ 102 then some (u.toNat - 87)
  else none

/-! ## Number -/

/-- Number.prototype.toString(radix) spec: https://tc39.es/ecma262/#sec-number.prototype.tostring -/
def numberProtoToString : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let x ← thisNumberValue thisV
  -- 2-3.
  let radix := arg args 0
  let r ← if radix.isUndefined then pure 10 else do
    match Conv.toIntegerOrInf (← toNum radix) with
    | .inr i => if 2 ≤ i && i ≤ 36 then pure i.toNat else throwRange "toString() radix must be between 2 and 36"
    | .inl _ => throwRange "toString() radix must be between 2 and 36"
  -- 4-5.
  pure (.str (Num.toJSStr x r))

/-- Number.prototype.toLocaleString spec: https://tc39.es/ecma262/#sec-number.prototype.tolocalestring -/
def numberProtoToLocaleString : BuiltinFn := fun _ thisV _ _ => do
  pure (.str (Num.toJSStr (← thisNumberValue thisV)))

/-- Number.prototype.toFixed spec: https://tc39.es/ecma262/#sec-number.prototype.tofixed -/
def numberProtoToFixed : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let x ← thisNumberValue thisV
  -- 2.
  let f ← toIntegerF (arg args 0)
  -- 4-.
  match Num.toFixed x f with
  | some s => pure (.str (JSStr.ofString s))
  | none => throwRange "toFixed() digits argument must be between 0 and 100"

/-- Number.prototype.toExponential spec: https://tc39.es/ecma262/#sec-number.prototype.toexponential -/
def numberProtoToExponential : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let x ← thisNumberValue thisV
  -- 2.
  let fd := arg args 0
  let f ← if fd.isUndefined then pure none else some <$> toIntegerF fd
  match Num.toExponential x f with
  | some s => pure (.str (JSStr.ofString s))
  | none => throwRange "toExponential() argument must be between 0 and 100"

/-- Number.prototype.toPrecision spec: https://tc39.es/ecma262/#sec-number.prototype.toprecision -/
def numberProtoToPrecision : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let x ← thisNumberValue thisV
  -- 2.
  let pv := arg args 0
  let p ← if pv.isUndefined then pure none else some <$> toIntegerF pv
  match Num.toPrecision x p with
  | some s => pure (.str (JSStr.ofString s))
  | none => throwRange "toPrecision() argument must be between 1 and 100"

/-- Number.isFinite spec: https://tc39.es/ecma262/#sec-number.isfinite -/
def numberIsFinite : BuiltinFn := fun _ _ args _ => do
  match arg args 0 with
  | .num x => pure (.bool (Num.isFinite x))
  | _ => pure (.bool false)

/-- Number.isInteger spec: https://tc39.es/ecma262/#sec-number.isinteger -/
def numberIsInteger : BuiltinFn := fun _ _ args _ => do
  match arg args 0 with
  | .num x => pure (.bool (Num.isIntegral x))
  | _ => pure (.bool false)

/-- Number.isNaN spec: https://tc39.es/ecma262/#sec-number.isnan -/
def numberIsNaN : BuiltinFn := fun _ _ args _ => do
  match arg args 0 with
  | .num x => pure (.bool (Num.isNaN x))
  | _ => pure (.bool false)

/-- Number.isSafeInteger spec: https://tc39.es/ecma262/#sec-number.issafeinteger -/
def numberIsSafeInteger : BuiltinFn := fun _ _ args _ => do
  match arg args 0 with
  | .num x =>
    match Num.toInt? x with
    | some i => pure (.bool (i.natAbs ≤ 9007199254740991))
    | none => pure (.bool false)
  | _ => pure (.bool false)

/-! ## Global functions -/

/-- isNaN(number) spec: https://tc39.es/ecma262/#sec-isnan-number -/
def globalIsNaN : BuiltinFn := fun _ _ args _ => do
  pure (.bool (Num.isNaN (← toNum (arg args 0))))

/-- isFinite(number) spec: https://tc39.es/ecma262/#sec-isfinite-number -/
def globalIsFinite : BuiltinFn := fun _ _ args _ => do
  pure (.bool (Num.isFinite (← toNum (arg args 0))))

/-- parseFloat(string) spec: https://tc39.es/ecma262/#sec-parsefloat-string -/
def globalParseFloat : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let s ← toStr (arg args 0)
  pure (.num (Num.parseFloat s))

/-- parseInt(string, radix) spec: https://tc39.es/ecma262/#sec-parseint-string-radix -/
def globalParseInt : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let s ← toStr (arg args 0)
  -- 6.
  let r ← toInt32 (arg args 1)
  pure (.num (Num.parseInt s r))

/-- The code units `Encode`/`Decode` leave alone: uriAlpha, DecimalDigit, uriMark. -/
def isAlwaysUnescaped (u : UInt16) : Bool :=
  (65 ≤ u && u ≤ 90) || (97 ≤ u && u ≤ 122) || (48 ≤ u && u ≤ 57) ||
    "-_.!~*'()".any (·.toNat == u.toNat)

/-- uriReserved and "#" -/
def isReservedOrHash (u : UInt16) : Bool := ";/?:@&=+$,#".any (·.toNat == u.toNat)

/-- The UTF-8 octets of a code point. -/
def utf8Octets (cp : Nat) : Array Nat :=
  if cp < 0x80 then #[cp]
  else if cp < 0x800 then #[0xC0 + cp / 64, 0x80 + cp % 64]
  else if cp < 0x10000 then #[0xE0 + cp / 4096, 0x80 + cp / 64 % 64, 0x80 + cp % 64]
  else #[0xF0 + cp / 262144, 0x80 + cp / 4096 % 64, 0x80 + cp / 64 % 64, 0x80 + cp % 64]

/-- Encode(string, extraUnescaped) (`reserved`: extraUnescaped is uriReserved and "#").
spec: https://tc39.es/ecma262/#sec-encode -/
def uriEncode (s : JSStr) (reserved : Bool) : M JSStr := do
  -- 1-5.
  let len := s.length
  let r ← M.repeatFrom (0, JSStr.empty) fun (k, R) => do
    -- 6.
    if k ≥ len then return .inr R
    -- a.
    let c := s.get k
    -- b.
    if isAlwaysUnescaped c || (reserved && isReservedOrHash c) then
      return .inl (k + 1, R.push c)
    -- c.
    let (cp, n, lone) := s.codePointAt k
    if lone then throwError .uriError "URI malformed"
    let R := (utf8Octets cp).foldl (fun R o => R.push 0x25 ++ hexByte o) R
    return .inl (k + n, R)
  pure r

/-- Decode(string, preserveEscapeSet) (`reserved`: preserveEscapeSet is uriReserved and "#").
spec: https://tc39.es/ecma262/#sec-decode -/
def uriDecode (s : JSStr) (reserved : Bool) : M JSStr := do
  -- 1-3.
  let len := s.length
  let bad {α} : M α := throwError .uriError "URI malformed"
  let parseHexOctet (k : Nat) : Option Nat := do
    let a ← hexVal (s.get k)
    let b ← hexVal (s.get (k + 1))
    pure (a * 16 + b)
  M.repeatFrom (0, JSStr.empty) fun (k, R) => do
    -- 4.
    if k ≥ len then return .inr R
    -- a.
    let c := s.get k
    -- b.
    if c != 0x25 then return .inl (k + 1, R.push c)
    -- c.i-iv.
    if k + 3 > len then bad
    let escape := s.slice k (k + 3)
    let some B := parseHexOctet (k + 1) | bad
    -- v.
    let k := k + 2
    -- vi.
    let n := if B < 0x80 then 0 else if B < 0xC0 then 1 else if B < 0xE0 then 2 else if B < 0xF0 then 3
      else if B < 0xF8 then 4 else 5
    -- vii.
    if n == 0 then
      let S := if reserved && isReservedOrHash B.toUInt16 then escape else JSStr.empty.push B.toUInt16
      return .inl (k + 1, R ++ S)
    -- viii.1.
    if n == 1 || n > 4 then bad
    -- 2-4.
    let (k, octets) ← M.repeatFrom (k, #[B]) fun (k, octets) => do
      if octets.size ≥ n then return .inr (k, octets)
      let k := k + 1
      if k + 3 > len then bad
      if s.get k != 0x25 then bad
      let some cb := parseHexOctet (k + 1) | bad
      if cb < 0x80 || cb ≥ 0xC0 then bad
      return .inl (k + 2, octets.push cb)
    -- 6-7.
    let V := (octets.extract 1 octets.size).foldl (fun acc o => acc * 64 + (o % 64)) (B % (2 ^ (7 - n)))
    let minV := if n == 2 then 0x80 else if n == 3 then 0x800 else 0x10000
    if V < minV || V > 0x10FFFF || (0xD800 ≤ V && V ≤ 0xDFFF) then bad
    -- 8.
    return .inl (k + 1, R.pushCodePoint V)

def encodeURIFn (reserved : Bool) : BuiltinFn := fun _ _ args _ => do
  pure (.str (← uriEncode (← toStr (arg args 0)) reserved))

def decodeURIFn (reserved : Bool) : BuiltinFn := fun _ _ args _ => do
  pure (.str (← uriDecode (← toStr (arg args 0)) reserved))

/-- escape(string) spec: https://tc39.es/ecma262/#sec-escape-string -/
def globalEscape : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let s ← toStr (arg args 0)
  -- 2-5.
  let ok (u : UInt16) : Bool :=
    (65 ≤ u && u ≤ 90) || (97 ≤ u && u ≤ 122) || (48 ≤ u && u ≤ 57) || "@*_+-./".any (·.toNat == u.toNat)
  let r := (Array.range s.length).foldl (fun (R : JSStr) k =>
    let c := s.get k
    if ok c then R.push c
    else if c < 256 then R.push 0x25 ++ hexByte c.toNat
    else (R.push 0x25).push 0x75 ++ hexByte (c.toNat / 256) ++ hexByte (c.toNat % 256)) JSStr.empty
  pure (.str r)

/-- unescape(string) spec: https://tc39.es/ecma262/#sec-unescape-string -/
def globalUnescape : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let s ← toStr (arg args 0)
  let len := s.length
  let hex (i n : Nat) : Option Nat :=
    (List.range n).foldl (fun acc j => acc.bind fun a => (hexVal (s.get (i + j))).map (a * 16 + ·)) (some 0)
  -- 2-6.
  let r ← M.repeatFrom (0, JSStr.empty) fun (k, R) => do
    if k ≥ len then return .inr R
    let c := s.get k
    if c == 0x25 then
      if k + 6 ≤ len && s.get (k + 1) == 0x75 then
        if let some v := hex (k + 2) 4 then return .inl (k + 6, R.push v.toUInt16)
      if k + 3 ≤ len then
        if let some v := hex (k + 1) 2 then return .inl (k + 3, R.push v.toUInt16)
    return .inl (k + 1, R.push c)
  pure (.str r)

/-! ## Math -/

/-- A one-argument Math function: ToNumber, then `f`. -/
def mathFn1 (f : F64 → F64) : BuiltinFn := fun _ _ args _ => do
  pure (.num (f (← toNum (arg args 0))))

/-- A two-argument Math function. -/
def mathFn2 (f : F64 → F64 → F64) : BuiltinFn := fun _ _ args _ => do
  let a ← toNum (arg args 0)
  let b ← toNum (arg args 1)
  pure (.num (f a b))

/-- A variadic Math function: every argument coerced first. -/
def mathFnN (f : Array F64 → F64) : BuiltinFn := fun _ _ args _ => do
  let xs ← M.mapArr args toNum
  pure (.num (f xs))

/-- Math.random spec: https://tc39.es/ecma262/#sec-math.random
(xorshift64*; the seed is kept in the engine's host data: an implementation-defined algorithm). -/
def mathRandom : BuiltinFn := fun _ _ _ _ => do
  let key := "Math.random seed"
  let seed ← readS fun s => match s.hostData.get? key with
    | some (.bigint i) => i.toNat
    | _ => 0x2545F4914F6CDD1D
  let m := 2 ^ 64
  let x := seed
  let x := (x ^^^ (x >>> 12)) % m
  let x := (x ^^^ (x <<< 25)) % m
  let x := (x ^^^ (x >>> 27)) % m
  modify fun s => { s with hostData := s.hostData.insert key (.bigint x) }
  let r := (x * 0x2545F4914F6CDD1D) % m
  -- (53 random bits as a fraction of 2^53)
  pure (.num (Num.ofNatExp false (r >>> 11) (-53)))

/-- Math.sumPrecise spec: https://tc39.es/ecma262/#sec-math.sumprecise -/
def mathSumPrecise : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let items ← requireObjectCoercible (arg args 0)
  -- 2.
  let r ← getIterator items
  -- 3-6.
  let xs ← M.repeatFrom (r, (#[] : Array F64)) fun (r, acc) => do
    let (r, v) ← iteratorStepValue r
    match v with
    | none => return .inr acc
    | some v =>
      if acc.size ≥ 9007199254740991 then
        iteratorCloseOnThrow r (← makeError .rangeError "Math.sumPrecise: too many values")
      match v with
      | .num x => return .inl (r, acc.push x)
      | _ => iteratorCloseOnThrow r (← makeError .typeError "Math.sumPrecise: value is not a Number")
  -- 7-.
  pure (.num (Num.sumPrecise xs))

/-! ## BigInt -/

/-- NumberToBigInt spec: https://tc39.es/ecma262/#sec-numbertobigint -/
def numberToBigInt (x : F64) : M Int := do
  match Num.toInt? x with
  | some i => pure i
  | none => throwRange "The number cannot be converted to a BigInt because it is not an integer"

/-- ToBigInt spec: https://tc39.es/ecma262/#sec-tobigint -/
def toBigInt (v : Value) : M Int := do
  -- 1.
  let prim ← toPrim v (some true)
  -- 2.
  match prim with
  | .undefined | .null => throwType "Cannot convert undefined or null to a BigInt"
  | .bool b => pure (if b then 1 else 0)
  | .bigint i => pure i
  | .num _ => throwType "Cannot convert a Number to a BigInt"
  | .str s => match Num.BigInt.stringToBigInt s with
    | some i => pure i
    | none => throwError .syntaxError s!"Cannot convert {s} to a BigInt"
  | .sym _ => throwType "Cannot convert a Symbol to a BigInt"
  | .obj _ => throwType "Cannot convert an object to a BigInt"

/-- BigInt(value) spec: https://tc39.es/ecma262/#sec-bigint-constructor-number-value -/
def bigintCtor : BuiltinFn := fun _ _ args nt => do
  -- 1.
  if !nt.isUndefined then throwType "BigInt is not a constructor"
  -- 2.
  let prim ← toPrim (arg args 0) (some true)
  -- 3.
  match prim with
  | .num x => pure (.bigint (← numberToBigInt x))
  -- 4.
  | _ => pure (.bigint (← toBigInt prim))

/-- ThisBigIntValue spec: https://tc39.es/ecma262/#sec-thisbigintvalue -/
def thisBigIntValue (v : Value) : M Int := do
  match v with
  | .bigint i => pure i
  | .obj o => match ← objKind o with
    | .primitive (.bigint i) => pure i
    | _ => throwType "BigInt.prototype method called on incompatible receiver"
  | _ => throwType "BigInt.prototype method called on incompatible receiver"

/-- BigInt.asIntN spec: https://tc39.es/ecma262/#sec-bigint.asintn -/
def bigintAsIntN : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let bits ← toIndex (arg args 0)
  -- 2.
  let x ← toBigInt (arg args 1)
  -- 3-4. (a BigInt that fits is its own result: no 2^bits for huge bits)
  if bits == 0 then return .bigint 0
  if Num.BigInt.bitLen x < bits then return .bigint x
  pure (.bigint (Num.BigInt.asIntN bits x))

/-- BigInt.asUintN spec: https://tc39.es/ecma262/#sec-bigint.asuintn -/
def bigintAsUintN : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let bits ← toIndex (arg args 0)
  -- 2.
  let x ← toBigInt (arg args 1)
  -- 3.
  if x ≥ 0 && Num.BigInt.bitLen x ≤ bits then return .bigint x
  if bits > Num.BigInt.maxBits then throwRange "Maximum BigInt size exceeded"
  pure (.bigint (Num.BigInt.asUintN bits x))

/-- BigInt.prototype.toString spec: https://tc39.es/ecma262/#sec-bigint.prototype.tostring -/
def bigintProtoToString : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  let x ← thisBigIntValue thisV
  -- 2-4.
  let radix := arg args 0
  let r ← if radix.isUndefined then pure 10 else do
    match Conv.toIntegerOrInf (← toNum radix) with
    | .inr i => if 2 ≤ i && i ≤ 36 then pure i.toNat else throwRange "toString() radix must be between 2 and 36"
    | .inl _ => throwRange "toString() radix must be between 2 and 36"
  -- 5.
  pure (.str (JSStr.ofString (Num.BigInt.toString x r)))

def bigintProtoToLocaleString : BuiltinFn := fun _ thisV _ _ => do
  pure (.str (JSStr.ofString (Num.BigInt.toString (← thisBigIntValue thisV))))

def bigintProtoValueOf : BuiltinFn := fun _ thisV _ _ => do pure (.bigint (← thisBigIntValue thisV))

/-! ## Behaviours and setup -/

def numberDefs : Array BuiltinDef := #[
  ⟨"Number.prototype.toString(radix)", numberProtoToString⟩,
  ⟨"Number.prototype.toLocaleString", numberProtoToLocaleString⟩,
  ⟨"Number.prototype.toFixed", numberProtoToFixed⟩,
  ⟨"Number.prototype.toExponential", numberProtoToExponential⟩,
  ⟨"Number.prototype.toPrecision", numberProtoToPrecision⟩,
  ⟨"Number.isFinite", numberIsFinite⟩, ⟨"Number.isInteger", numberIsInteger⟩,
  ⟨"Number.isNaN", numberIsNaN⟩, ⟨"Number.isSafeInteger", numberIsSafeInteger⟩,
  ⟨"isNaN", globalIsNaN⟩, ⟨"isFinite", globalIsFinite⟩, ⟨"parseFloat", globalParseFloat⟩,
  ⟨"parseInt", globalParseInt⟩,
  ⟨"encodeURI", encodeURIFn true⟩, ⟨"encodeURIComponent", encodeURIFn false⟩,
  ⟨"decodeURI", decodeURIFn true⟩, ⟨"decodeURIComponent", decodeURIFn false⟩,
  ⟨"escape", globalEscape⟩, ⟨"unescape", globalUnescape⟩,
  ⟨"Math.abs", mathFn1 Num.mathAbs⟩, ⟨"Math.acos", mathFn1 Num.acos⟩, ⟨"Math.acosh", mathFn1 Num.acosh⟩,
  ⟨"Math.asin", mathFn1 Num.asin⟩, ⟨"Math.asinh", mathFn1 Num.asinh⟩, ⟨"Math.atan", mathFn1 Num.atan⟩,
  ⟨"Math.atanh", mathFn1 Num.atanh⟩, ⟨"Math.atan2", mathFn2 Num.atan2⟩, ⟨"Math.cbrt", mathFn1 Num.cbrt⟩,
  ⟨"Math.ceil", mathFn1 Num.ceil⟩, ⟨"Math.clz32", mathFn1 (fun x => Num.ofNat (Num.clz32 x))⟩,
  ⟨"Math.cos", mathFn1 Num.cos⟩, ⟨"Math.cosh", mathFn1 Num.cosh⟩, ⟨"Math.exp", mathFn1 Num.exp⟩,
  ⟨"Math.expm1", mathFn1 Num.expm1⟩, ⟨"Math.floor", mathFn1 Num.floor⟩, ⟨"Math.fround", mathFn1 Num.fround⟩,
  ⟨"Math.f16round", mathFn1 Num.f16round⟩,
  ⟨"Math.hypot", mathFnN Num.hypot⟩, ⟨"Math.imul", mathFn2 Num.imul⟩, ⟨"Math.log", mathFn1 Num.log⟩,
  ⟨"Math.log1p", mathFn1 Num.log1p⟩, ⟨"Math.log10", mathFn1 Num.log10⟩, ⟨"Math.log2", mathFn1 Num.log2⟩,
  ⟨"Math.max", mathFnN Num.mathMax⟩, ⟨"Math.min", mathFnN Num.mathMin⟩, ⟨"Math.random", mathRandom⟩,
  ⟨"Math.round", mathFn1 Num.round⟩, ⟨"Math.sign", mathFn1 Num.sign⟩, ⟨"Math.sin", mathFn1 Num.sin⟩,
  ⟨"Math.sinh", mathFn1 Num.sinh⟩, ⟨"Math.sqrt", mathFn1 Num.sqrt⟩, ⟨"Math.tan", mathFn1 Num.tan⟩,
  ⟨"Math.tanh", mathFn1 Num.tanh⟩, ⟨"Math.trunc", mathFn1 Num.trunc⟩,
  ⟨"Math.sumPrecise", mathSumPrecise⟩,
  ⟨"BigInt", bigintCtor⟩, ⟨"BigInt.asIntN", bigintAsIntN⟩, ⟨"BigInt.asUintN", bigintAsUintN⟩,
  ⟨"BigInt.prototype.toString", bigintProtoToString⟩,
  ⟨"BigInt.prototype.toLocaleString", bigintProtoToLocaleString⟩,
  ⟨"BigInt.prototype.valueOf", bigintProtoValueOf⟩]

/-- Number's, Math's, BigInt's and the global functions' intrinsics. -/
def numberSetup : M Unit := do
  -- Number
  let nc ← intrinsic "%Number%"
  let np ← intrinsic "%Number.prototype%"
  let _ ← defMethod np (.str kToString) "Number.prototype.toString(radix)" 1
  defMethods np "Number.prototype" [("toLocaleString", 0), ("toFixed", 1), ("toExponential", 1),
    ("toPrecision", 1)]
  for (nm, v) in [("EPSILON", Num.ofNatExp false 1 (-52)),
      ("MAX_SAFE_INTEGER", Num.ofNat 9007199254740991),
      ("MAX_VALUE", Num.ofNatExp false (2 ^ 53 - 1) 971),
      ("MIN_SAFE_INTEGER", (Num.ofNat 9007199254740991).neg),
      ("MIN_VALUE", Num.ofNatExp false 1 (-1074)),
      ("NaN", F64.nan), ("NEGATIVE_INFINITY", F64.inf true), ("POSITIVE_INFINITY", F64.inf false)] do
    setOwn nc (.str (JSStr.ofString nm)) (.data (.num v) false false false)
  defMethods nc "Number" [("isFinite", 1), ("isInteger", 1), ("isNaN", 1), ("isSafeInteger", 1)]
  -- global functions
  let g ← readS (·.curRealm.globalObj)
  for (nm, len) in [("isNaN", 1), ("isFinite", 1), ("encodeURI", 1), ("encodeURIComponent", 1),
      ("decodeURI", 1), ("decodeURIComponent", 1), ("escape", 1), ("unescape", 1)] do
    let _ ← defMethod g (.str (JSStr.ofString nm)) nm len
  let pf ← defMethod g (.str "parseFloat") "parseFloat" 1
  let pi ← defMethod g (.str "parseInt") "parseInt" 2
  setOwn nc (.str "parseFloat") (.data (.obj pf) true false true)
  setOwn nc (.str "parseInt") (.data (.obj pi) true false true)
  -- Math
  let mo ← intrinsic "%Math%"
  for (nm, v) in [("E", "2.718281828459045"), ("LN10", "2.302585092994046"),
      ("LN2", "0.6931471805599453"), ("LOG10E", "0.4342944819032518"),
      ("LOG2E", "1.4426950408889634"), ("PI", "3.141592653589793"),
      ("SQRT1_2", "0.7071067811865476"), ("SQRT2", "1.4142135623730951")] do
    setOwn mo (.str (JSStr.ofString nm)) (.data (.num (numLit v)) false false false)
  defMethods mo "Math" [("abs", 1), ("acos", 1), ("acosh", 1), ("asin", 1), ("asinh", 1),
    ("atan", 1), ("atanh", 1), ("atan2", 2), ("cbrt", 1), ("ceil", 1), ("clz32", 1), ("cos", 1),
    ("cosh", 1), ("exp", 1), ("expm1", 1), ("floor", 1), ("fround", 1), ("f16round", 1),
    ("hypot", 2), ("imul", 2), ("log", 1), ("log1p", 1), ("log10", 1), ("log2", 1), ("max", 2),
    ("min", 2), ("random", 0), ("round", 1), ("sign", 1), ("sin", 1), ("sinh", 1), ("sqrt", 1),
    ("tan", 1), ("tanh", 1), ("trunc", 1), ("sumPrecise", 1)]
  -- BigInt
  let bp ← intrinsic "%BigInt.prototype%"
  let (bc, _) ← defConstructor "BigInt" 1 "BigInt" bp
  defMethods bc "BigInt" [("asIntN", 2), ("asUintN", 2)]
  defMethods bp "BigInt.prototype" [("toString", 0), ("toLocaleString", 0), ("valueOf", 0)]
  defTag bp "BigInt"

end ES.Builtins.Text
