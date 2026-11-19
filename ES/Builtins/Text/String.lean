import ES.Builtins.Text.RegExp
import ES.Unicode.Text

/-!
# String objects

String.fromCharCode/fromCodePoint/raw, every String.prototype method (with Annex B's substr,
trimLeft/trimRight and the HTML methods), and %StringIteratorPrototype%. Case conversion and
normalization are `ES/Unicode/Text.lean`'s.

spec: https://tc39.es/ecma262/#sec-string-objects
spec: https://tc39.es/ecma262/#sec-additional-properties-of-the-string.prototype-object
-/

namespace ES.Builtins.Text

open ES (F64)

/-- The longest String the engine makes (V8's limit, 2^29 - 24 code units): longer results are a
RangeError, as in engines: LIMITATION (docs/es.md L11)). -/
def maxStringLength : Nat := 536870888

def checkLength (n : Nat) : M Unit := do
  if n > maxStringLength then throwRange "Invalid string length"

/-- RequireObjectCoercible(this value) and ToString: the first steps of most String.prototype
methods. -/
def thisStr (thisV : Value) (what : String) : M JSStr := do
  if thisV.isNullish then throwType s!"String.prototype.{what} called on null or undefined"
  toStr thisV

/-- The value of ToIntegerOrInfinity clamped to [0, len]. -/
def clampIndex (v : Value) (len : Nat) : M Nat := do
  pure (← toIntClamp v 0 len).toNat

/-- A relative index (start/end of slice): negative counts from `len`. -/
def relIndex (v : Value) (len : Nat) : M Nat := do
  match ← toIntegerOrInfinity v with
  | .inl true => pure 0
  | .inl false => pure len
  | .inr i => pure (if i < 0 then (max 0 ((len : Int) + i)).toNat else min i.toNat len)

def strV (s : JSStr) : Value := .str s

/-- `s` repeated `n` times (by doubling: the result's length is checked by the callers). -/
def repeatStr (s : JSStr) (n : Nat) : JSStr := Id.run do
  let mut out := JSStr.empty
  let mut p := s
  let mut k := n
  -- (64 halvings exhaust any count below 2^64; counts are bounded by the String length limit)
  for _ in [0:64] do
    if k == 0 then break
    if k % 2 == 1 then out := out ++ p
    k := k / 2
    if k > 0 then p := p ++ p
  return out

/-- String.fromCharCode spec: https://tc39.es/ecma262/#sec-string.fromcharcode -/
def stringFromCharCode : BuiltinFn := fun _ _ args _ => do
  let us ← M.mapArr args fun v => do pure (Num.toUint16 (← toNum v)).toUInt16
  pure (.str (JSStr.ofUnits us))

/-- String.fromCodePoint spec: https://tc39.es/ecma262/#sec-string.fromcodepoint -/
def stringFromCodePoint : BuiltinFn := fun _ _ args _ => do
  let r ← M.foldArr args JSStr.empty fun acc v => do
    let n ← toNum v
    match Num.toInt? n with
    | some i =>
      if i < 0 || i > 0x10FFFF then throwRange s!"Invalid code point {numberToJSStr n}"
      pure (acc.pushCodePoint i.toNat)
    | none => throwRange s!"Invalid code point {numberToJSStr n}"
  pure (.str r)

/-- String.raw spec: https://tc39.es/ecma262/#sec-string.raw -/
def stringRaw : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let substitutions := args.extract 1 args.size
  let substitutionCount := substitutions.size
  -- 2-4.
  let cooked ← toObject (arg args 0)
  let literals ← toObject (← getProp cooked (.str "raw"))
  let literalCount ← lengthOf literals
  -- 5.
  if literalCount == 0 then return .str JSStr.empty
  -- 6-8.
  M.repeatFrom (0, JSStr.empty) fun (nextIndex, R) => do
    let nextLiteral ← toStr (← getProp literals (PropKey.ofNat nextIndex))
    let R := R ++ nextLiteral
    checkLength R.length
    if nextIndex + 1 == literalCount then return .inr (.str R)
    let R ← if nextIndex < substitutionCount then do pure (R ++ (← toStr substitutions[nextIndex]!)) else pure R
    return .inl (nextIndex + 1, R)

/-- String.prototype.at spec: https://tc39.es/ecma262/#sec-string.prototype.at -/
def stringProtoAt : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "at"
  let len := S.length
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr rel =>
    let k : Int := if rel ≥ 0 then rel else len + rel
    if k < 0 || k ≥ len then return .undefined
    pure (.str (S.slice k.toNat (k.toNat + 1)))
  | .inl _ => pure .undefined

/-- String.prototype.charAt spec: https://tc39.es/ecma262/#sec-string.prototype.charat -/
def stringProtoCharAt : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "charAt"
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr p => if p < 0 || p ≥ S.length then pure (.str JSStr.empty) else pure (.str (S.slice p.toNat (p.toNat + 1)))
  | .inl _ => pure (.str JSStr.empty)

/-- String.prototype.charCodeAt spec: https://tc39.es/ecma262/#sec-string.prototype.charcodeat -/
def stringProtoCharCodeAt : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "charCodeAt"
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr p => if p < 0 || p ≥ S.length then pure (.num .nan) else pure (numV (S.get p.toNat).toNat)
  | .inl _ => pure (.num .nan)

/-- String.prototype.codePointAt spec: https://tc39.es/ecma262/#sec-string.prototype.codepointat -/
def stringProtoCodePointAt : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "codePointAt"
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr p => if p < 0 || p ≥ S.length then pure .undefined else pure (numV (S.codePointAt p.toNat).1)
  | .inl _ => pure .undefined

/-- String.prototype.concat spec: https://tc39.es/ecma262/#sec-string.prototype.concat -/
def stringProtoConcat : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "concat"
  let r ← M.foldArr args S fun R v => do
    let R := R ++ (← toStr v)
    checkLength R.length
    pure R
  pure (.str r)

/-- The search string of endsWith/includes/startsWith (a RegExp is a TypeError). -/
def searchStringArg (v : Value) (what : String) : M JSStr := do
  if ← isRegExp v then throwType s!"First argument to String.prototype.{what} must not be a regular expression"
  toStr v

/-- String.prototype.endsWith spec: https://tc39.es/ecma262/#sec-string.prototype.endswith -/
def stringProtoEndsWith : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "endsWith"
  let searchStr ← searchStringArg (arg args 0) "endsWith"
  let len := S.length
  let e := arg args 1
  let endPos ← if e.isUndefined then pure len else clampIndex e len
  let searchLength := searchStr.length
  if searchLength == 0 then return .bool true
  if endPos < searchLength then return .bool false
  pure (.bool (S.matchesAt searchStr (endPos - searchLength)))

/-- String.prototype.includes spec: https://tc39.es/ecma262/#sec-string.prototype.includes -/
def stringProtoIncludes : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "includes"
  let searchStr ← searchStringArg (arg args 0) "includes"
  let start ← clampIndex (arg args 1) S.length
  pure (.bool (S.indexOf searchStr start).isSome)

/-- String.prototype.indexOf spec: https://tc39.es/ecma262/#sec-string.prototype.indexof -/
def stringProtoIndexOf : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "indexOf"
  let searchStr ← toStr (arg args 0)
  let start ← clampIndex (arg args 1) S.length
  match S.indexOf searchStr start with
  | some i => pure (numV i)
  | none => pure (intV (-1))

/-- IsStringWellFormedUnicode spec: https://tc39.es/ecma262/#sec-isstringwellformedunicode -/
def isWellFormedStr (s : JSStr) : Bool := Id.run do
  let mut k := 0
  for _ in [0:s.length] do
    if k ≥ s.length then break
    let (_, n, lone) := s.codePointAt k
    if lone then return false
    k := k + n
  return true

def stringProtoIsWellFormed : BuiltinFn := fun _ thisV _ _ => do
  pure (.bool (isWellFormedStr (← thisStr thisV "isWellFormed")))

/-- String.prototype.toWellFormed spec: https://tc39.es/ecma262/#sec-string.prototype.towellformed -/
def stringProtoToWellFormed : BuiltinFn := fun _ thisV _ _ => do
  let S ← thisStr thisV "toWellFormed"
  if isWellFormedStr S then return .str S
  let r := Id.run do
    let mut out := JSStr.empty
    let mut k := 0
    for _ in [0:S.length] do
      if k ≥ S.length then break
      let (cp, n, lone) := S.codePointAt k
      out := out.pushCodePoint (if lone then 0xFFFD else cp)
      k := k + n
    return out
  pure (.str r)

/-- String.prototype.lastIndexOf spec: https://tc39.es/ecma262/#sec-string.prototype.lastindexof -/
def stringProtoLastIndexOf : BuiltinFn := fun _ thisV args _ => do
  -- 1-3.
  let S ← thisStr thisV "lastIndexOf"
  let searchStr ← toStr (arg args 0)
  -- 4-6.
  let numPos ← toNum (arg args 1)
  let pos : Option Int := match numPos with
    | .nan => none
    | x => match Conv.toIntegerOrInf x with
      | .inl true => some 0
      | .inl false => none
      | .inr i => some i
  -- 7-9.
  let len := S.length
  let searchLen := searchStr.length
  if searchLen > len then return intV (-1)
  let hi := len - searchLen
  let start := match pos with | none => hi | some p => (max 0 (min p hi)).toNat
  -- 10.
  if searchLen == 0 then return numV start
  -- 11-12.
  let r := Id.run do
    for k in [0:start + 1] do
      if S.matchesAt searchStr (start - k) then return some (start - k)
    return none
  match r with
  | some i => pure (numV i)
  | none => pure (intV (-1))

/-- String.prototype.localeCompare spec: https://tc39.es/ecma262/#sec-string.prototype.localecompare
LIMITATION (docs/es.md L10): no locale collation: canonically equivalent Strings are equal (both
are compared in NFC), others compare by code points. -/
def stringProtoLocaleCompare : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "localeCompare"
  let That ← toStr (arg args 0)
  let a := Unicode.codePoints (Unicode.normalize S 0)
  let b := Unicode.codePoints (Unicode.normalize That 0)
  let n := min a.size b.size
  let r := Id.run do
    for i in [0:n] do
      if a[i]! < b[i]! then return -1
      if a[i]! > b[i]! then return 1
    return (if a.size < b.size then -1 else if a.size > b.size then 1 else (0 : Int))
  pure (intV r)

/-- String.prototype.match spec: https://tc39.es/ecma262/#sec-string.prototype.match -/
def stringProtoMatch : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  if thisV.isNullish then throwType "String.prototype.match called on null or undefined"
  let regexp := arg args 0
  -- 2.
  if regexp.isObject then
    if let some matcher ← getMethodOf regexp (.sym WK.match) then
      return ← call matcher regexp #[thisV]
  -- 3-5.
  let S ← toStr thisV
  let rx ← regexpCreate regexp .undefined
  invoke rx (.sym WK.match) #[.str S]

/-- String.prototype.matchAll spec: https://tc39.es/ecma262/#sec-string.prototype.matchall -/
def stringProtoMatchAll : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  if thisV.isNullish then throwType "String.prototype.matchAll called on null or undefined"
  let regexp := arg args 0
  -- 2.
  if let .obj ro := regexp then
    if ← isRegExp regexp then
      let flags ← getProp ro (.str kFlags)
      let _ ← requireObjectCoercible flags
      if !strHas (← toStr flags) 'g' then throwType "String.prototype.matchAll called with a non-global RegExp argument"
    if let some matcher ← getMethodOf regexp (.sym WK.matchAll) then
      return ← call matcher regexp #[thisV]
  -- 3-5.
  let S ← toStr thisV
  let rx ← regexpCreate regexp (.str "g")
  invoke rx (.sym WK.matchAll) #[.str S]

/-- String.prototype.normalize spec: https://tc39.es/ecma262/#sec-string.prototype.normalize -/
def stringProtoNormalize : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "normalize"
  let fv := arg args 0
  let f ← if fv.isUndefined then pure (JSStr.ofString "NFC") else toStr fv
  let form ← match f.toString with
    | "NFC" => pure 0 | "NFD" => pure 1 | "NFKC" => pure 2 | "NFKD" => pure 3
    | _ => throwRange "The normalization form should be one of NFC, NFD, NFKC, NFKD."
  pure (.str (Unicode.normalize S form))

/-- StringPaddingBuiltinsImpl spec: https://tc39.es/ecma262/#sec-stringpaddingbuiltinsimpl -/
def stringPad (atStart : Bool) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let S ← thisStr thisV (if atStart then "padStart" else "padEnd")
  -- 3.
  let intMaxLength ← toLen (arg args 0)
  -- 4-5.
  let stringLength := S.length
  if intMaxLength ≤ stringLength then return .str S
  -- 6-7.
  let fv := arg args 1
  let fill ← if fv.isUndefined then pure (JSStr.ofString " ") else toStr fv
  -- StringPad
  if fill.isEmpty then return .str S
  checkLength intMaxLength
  let fillLen := intMaxLength - stringLength
  let filler := (repeatStr fill (fillLen / fill.length + 1)).take fillLen
  pure (.str (if atStart then filler ++ S else S ++ filler))

/-- String.prototype.repeat spec: https://tc39.es/ecma262/#sec-string.prototype.repeat -/
def stringProtoRepeat : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "repeat"
  match ← toIntegerOrInfinity (arg args 0) with
  | .inr n =>
    if n < 0 then throwRange "Invalid count value"
    if n == 0 || S.isEmpty then return .str JSStr.empty
    checkLength (S.length * n.toNat)
    let r := repeatStr S n.toNat
    pure (.str r)
  | .inl _ => throwRange "Invalid count value"

/-- String.prototype.replace spec: https://tc39.es/ecma262/#sec-string.prototype.replace -/
def stringProtoReplace : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  if thisV.isNullish then throwType "String.prototype.replace called on null or undefined"
  let searchValue := arg args 0
  let replaceValue := arg args 1
  -- 2.
  if searchValue.isObject then
    if let some replacer ← getMethodOf searchValue (.sym WK.replace) then
      return ← call replacer searchValue #[thisV, replaceValue]
  -- 3-4.
  let string ← toStr thisV
  let searchString ← toStr searchValue
  -- 5-6.
  let functionalReplace ← isCallable replaceValue
  let replaceStr ← if functionalReplace then pure JSStr.empty else toStr replaceValue
  -- 7-9.
  let searchLength := searchString.length
  let some position := string.indexOf searchString 0 | return .str string
  -- 10-11.
  let preceding := string.slice 0 position
  let following := string.slice (position + searchLength) string.length
  -- 12-13.
  let replacement ← if functionalReplace then
      toStr (← call replaceValue .undefined #[.str searchString, numV position, .str string])
    else getSubstitution searchString string position #[] .undefined replaceStr
  -- 14.
  let r := preceding ++ replacement ++ following
  checkLength r.length
  pure (.str r)

/-- String.prototype.replaceAll spec: https://tc39.es/ecma262/#sec-string.prototype.replaceall -/
def stringProtoReplaceAll : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  if thisV.isNullish then throwType "String.prototype.replaceAll called on null or undefined"
  let searchValue := arg args 0
  let replaceValue := arg args 1
  -- 2.
  if let .obj so := searchValue then
    if ← isRegExp searchValue then
      let flags ← getProp so (.str kFlags)
      let _ ← requireObjectCoercible flags
      if !strHas (← toStr flags) 'g' then throwType "replaceAll must be called with a global RegExp"
    if let some replacer ← getMethodOf searchValue (.sym WK.replace) then
      return ← call replacer searchValue #[thisV, replaceValue]
  -- 3-6.
  let string ← toStr thisV
  let searchString ← toStr searchValue
  let functionalReplace ← isCallable replaceValue
  let replaceStr ← if functionalReplace then pure JSStr.empty else toStr replaceValue
  -- 7-11.
  let searchLength := searchString.length
  let advanceBy := max 1 searchLength
  let matchPositions := Id.run do
    let mut ps : Array Nat := #[]
    let mut p := string.indexOf searchString 0
    for _ in [0:string.length + 2] do
      match p with
      | some q =>
        ps := ps.push q
        p := string.indexOf searchString (q + advanceBy)
      | none => break
    return ps
  -- 12-14.
  let (result, endOfLastMatch) ← M.foldArr matchPositions (JSStr.empty, 0) fun (result, endOfLast) p => do
    let preserved := string.slice endOfLast p
    let replacement ← if functionalReplace then
        toStr (← call replaceValue .undefined #[.str searchString, numV p, .str string])
      else getSubstitution searchString string p #[] .undefined replaceStr
    let result := result ++ preserved ++ replacement
    checkLength result.length
    pure (result, p + searchLength)
  -- 15-16.
  if endOfLastMatch < string.length then return .str (result ++ string.slice endOfLastMatch string.length)
  pure (.str result)

/-- String.prototype.search spec: https://tc39.es/ecma262/#sec-string.prototype.search -/
def stringProtoSearch : BuiltinFn := fun _ thisV args _ => do
  if thisV.isNullish then throwType "String.prototype.search called on null or undefined"
  let regexp := arg args 0
  if regexp.isObject then
    if let some searcher ← getMethodOf regexp (.sym WK.search) then
      return ← call searcher regexp #[thisV]
  let S ← toStr thisV
  let rx ← regexpCreate regexp .undefined
  invoke rx (.sym WK.search) #[.str S]

/-- String.prototype.slice spec: https://tc39.es/ecma262/#sec-string.prototype.slice -/
def stringProtoSlice : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "slice"
  let len := S.length
  let fromI ← relIndex (arg args 0) len
  let e := arg args 1
  let toI ← if e.isUndefined then pure len else relIndex e len
  if fromI ≥ toI then return .str JSStr.empty
  pure (.str (S.slice fromI toI))

/-- String.prototype.split spec: https://tc39.es/ecma262/#sec-string.prototype.split -/
def stringProtoSplit : BuiltinFn := fun _ thisV args _ => do
  -- 1.
  if thisV.isNullish then throwType "String.prototype.split called on null or undefined"
  let separator := arg args 0
  let limit := arg args 1
  -- 2.
  if separator.isObject then
    if let some splitter ← getMethodOf separator (.sym WK.split) then
      return ← call splitter separator #[thisV, limit]
  -- 3.
  let S ← toStr thisV
  -- 4.
  let lim ← if limit.isUndefined then pure 4294967295 else toUint32 limit
  -- 5.
  let R ← toStr separator
  -- 6.
  if lim == 0 then return ← createArrayFromList #[]
  -- 7.
  if separator.isUndefined then return ← createArrayFromList #[.str S]
  -- 8-9.
  let separatorLength := R.length
  if separatorLength == 0 then
    let head := S.take lim
    return ← createArrayFromList ((Array.range head.length).map fun i => .str (head.slice i (i + 1)))
  -- 10.
  if S.isEmpty then return ← createArrayFromList #[.str S]
  -- 11-15.
  let parts := Id.run do
    let mut subs : Array Value := #[]
    let mut i := 0
    let mut j := S.indexOf R 0
    for _ in [0:S.length + 1] do
      match j with
      | some jj =>
        subs := subs.push (.str (S.slice i jj))
        if subs.size == lim then return subs
        i := jj + separatorLength
        j := S.indexOf R i
      | none => break
    return subs.push (.str (S.slice i S.length))
  createArrayFromList parts

/-- String.prototype.startsWith spec: https://tc39.es/ecma262/#sec-string.prototype.startswith -/
def stringProtoStartsWith : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "startsWith"
  let searchStr ← searchStringArg (arg args 0) "startsWith"
  let start ← clampIndex (arg args 1) S.length
  let searchLength := searchStr.length
  if searchLength == 0 then return .bool true
  if start + searchLength > S.length then return .bool false
  pure (.bool (S.matchesAt searchStr start))

/-- String.prototype.substring spec: https://tc39.es/ecma262/#sec-string.prototype.substring -/
def stringProtoSubstring : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "substring"
  let len := S.length
  let finalStart ← clampIndex (arg args 0) len
  let e := arg args 1
  let finalEnd ← if e.isUndefined then pure len else clampIndex e len
  pure (.str (S.slice (min finalStart finalEnd) (max finalStart finalEnd)))

/-- String.prototype.substr spec: https://tc39.es/ecma262/#sec-string.prototype.substr -/
def stringProtoSubstr : BuiltinFn := fun _ thisV args _ => do
  let S ← thisStr thisV "substr"
  let size := S.length
  let intStart ← relIndex (arg args 0) size
  let lv := arg args 1
  let intLength ← if lv.isUndefined then pure size else clampIndex lv size
  let intEnd := min (intStart + intLength) size
  if intStart ≥ intEnd then return .str JSStr.empty
  pure (.str (S.slice intStart intEnd))

/-- toLowerCase/toUpperCase (and the locale variants: LIMITATION (docs/es.md L10), no
language-sensitive mappings).
spec: https://tc39.es/ecma262/#sec-string.prototype.tolowercase -/
def stringCase (lower : Bool) (what : String) : BuiltinFn := fun _ thisV _ _ => do
  let S ← thisStr thisV what
  pure (.str (if lower then Unicode.toLower S else Unicode.toUpper S))

/-- TrimString (`where`: 0 start, 1 end, 2 both) spec: https://tc39.es/ecma262/#sec-trimstring -/
def trimString (s : JSStr) (where_ : Nat) : JSStr := Id.run do
  let n := s.length
  let mut i := 0
  if where_ != 1 then
    for _ in [0:n] do
      if i < n && Num.isStrWhiteSpace (s.get i) then i := i + 1 else break
  let mut j := n
  if where_ != 0 then
    for _ in [0:n] do
      if j > i && Num.isStrWhiteSpace (s.get (j - 1)) then j := j - 1 else break
  return s.slice i j

def stringTrim (where_ : Nat) (what : String) : BuiltinFn := fun _ thisV _ _ => do
  pure (.str (trimString (← thisStr thisV what) where_))

/-- CreateHTML spec: https://tc39.es/ecma262/#sec-createhtml -/
def createHTML (tag attr : String) : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let S ← thisStr thisV tag
  -- 3-4.
  let p1 := JSStr.ofString ("<" ++ tag)
  let p1 ← if attr.isEmpty then pure p1 else do
    let V ← toStr (arg args 0)
    let escapedV := (Array.range V.length).foldl (fun (acc : JSStr) i =>
      let c := V.get i
      if c == 0x22 then acc ++ JSStr.ofString "&quot;" else acc.push c) JSStr.empty
    pure (p1 ++ JSStr.ofString (" " ++ attr ++ "=\"") ++ escapedV ++ JSStr.ofString "\"")
  -- 5-7.
  pure (.str (p1 ++ JSStr.ofString ">" ++ S ++ JSStr.ofString ("</" ++ tag ++ ">")))

/-- String.prototype[@@iterator] spec: https://tc39.es/ecma262/#sec-string.prototype-%symbol.iterator% -/
def stringProtoIterator : BuiltinFn := fun _ thisV _ _ => do
  let s ← thisStr thisV "[Symbol.iterator]"
  let proto ← intrinsic "%StringIteratorPrototype%"
  let sl : Array Value := #[.str s, numV 0]
  let it ← alloc { proto := .obj proto, kind := .internal "String Iterator" sl }
  pure (.obj it)

/-- %StringIteratorPrototype%.next spec: https://tc39.es/ecma262/#sec-%stringiteratorprototype%.next -/
def stringIteratorNext : BuiltinFn := fun _ thisV _ _ => do
  let .obj it := thisV | throwType "next method called on incompatible receiver"
  let .internal "String Iterator" sl ← objKind it | throwType "next method called on incompatible receiver"
  let .str s := sl[0]! | createIterResult .undefined true
  let pos := match sl[1]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  if pos ≥ s.length then
    let sl' : Array Value := #[.undefined, numV pos]
    modifyObj it fun o => { o with kind := .internal "String Iterator" sl' }
    return ← createIterResult .undefined true
  let (_, n, _) := s.codePointAt pos
  let sl' : Array Value := #[.str s, numV (pos + n)]
  modifyObj it fun o => { o with kind := .internal "String Iterator" sl' }
  createIterResult (.str (s.slice pos (pos + n))) false

def stringDefs : Array BuiltinDef := #[
  ⟨"String.fromCharCode", stringFromCharCode⟩, ⟨"String.fromCodePoint", stringFromCodePoint⟩,
  ⟨"String.raw", stringRaw⟩,
  ⟨"String.prototype.at", stringProtoAt⟩, ⟨"String.prototype.charAt", stringProtoCharAt⟩,
  ⟨"String.prototype.charCodeAt", stringProtoCharCodeAt⟩,
  ⟨"String.prototype.codePointAt", stringProtoCodePointAt⟩,
  ⟨"String.prototype.concat", stringProtoConcat⟩, ⟨"String.prototype.endsWith", stringProtoEndsWith⟩,
  ⟨"String.prototype.includes", stringProtoIncludes⟩, ⟨"String.prototype.indexOf", stringProtoIndexOf⟩,
  ⟨"String.prototype.isWellFormed", stringProtoIsWellFormed⟩,
  ⟨"String.prototype.lastIndexOf", stringProtoLastIndexOf⟩,
  ⟨"String.prototype.localeCompare", stringProtoLocaleCompare⟩,
  ⟨"String.prototype.match", stringProtoMatch⟩, ⟨"String.prototype.matchAll", stringProtoMatchAll⟩,
  ⟨"String.prototype.normalize", stringProtoNormalize⟩,
  ⟨"String.prototype.padEnd", stringPad false⟩, ⟨"String.prototype.padStart", stringPad true⟩,
  ⟨"String.prototype.repeat", stringProtoRepeat⟩, ⟨"String.prototype.replace", stringProtoReplace⟩,
  ⟨"String.prototype.replaceAll", stringProtoReplaceAll⟩,
  ⟨"String.prototype.search", stringProtoSearch⟩, ⟨"String.prototype.slice", stringProtoSlice⟩,
  ⟨"String.prototype.split", stringProtoSplit⟩, ⟨"String.prototype.startsWith", stringProtoStartsWith⟩,
  ⟨"String.prototype.substring", stringProtoSubstring⟩, ⟨"String.prototype.substr", stringProtoSubstr⟩,
  ⟨"String.prototype.toLowerCase", stringCase true "toLowerCase"⟩,
  ⟨"String.prototype.toUpperCase", stringCase false "toUpperCase"⟩,
  ⟨"String.prototype.toLocaleLowerCase", stringCase true "toLocaleLowerCase"⟩,
  ⟨"String.prototype.toLocaleUpperCase", stringCase false "toLocaleUpperCase"⟩,
  ⟨"String.prototype.toWellFormed", stringProtoToWellFormed⟩,
  ⟨"String.prototype.trim", stringTrim 2 "trim"⟩, ⟨"String.prototype.trimStart", stringTrim 0 "trimStart"⟩,
  ⟨"String.prototype.trimEnd", stringTrim 1 "trimEnd"⟩,
  ⟨"String.prototype.anchor", createHTML "a" "name"⟩, ⟨"String.prototype.big", createHTML "big" ""⟩,
  ⟨"String.prototype.blink", createHTML "blink" ""⟩, ⟨"String.prototype.bold", createHTML "b" ""⟩,
  ⟨"String.prototype.fixed", createHTML "tt" ""⟩,
  ⟨"String.prototype.fontcolor", createHTML "font" "color"⟩,
  ⟨"String.prototype.fontsize", createHTML "font" "size"⟩,
  ⟨"String.prototype.italics", createHTML "i" ""⟩, ⟨"String.prototype.link", createHTML "a" "href"⟩,
  ⟨"String.prototype.small", createHTML "small" ""⟩, ⟨"String.prototype.strike", createHTML "strike" ""⟩,
  ⟨"String.prototype.sub", createHTML "sub" ""⟩, ⟨"String.prototype.sup", createHTML "sup" ""⟩,
  ⟨"String.prototype[Symbol.iterator]", stringProtoIterator⟩,
  ⟨"%StringIteratorPrototype%.next", stringIteratorNext⟩]

def stringSetup : M Unit := do
  let sc ← intrinsic "%String%"
  let sp ← intrinsic "%String.prototype%"
  defMethods sc "String" [("fromCharCode", 1), ("fromCodePoint", 1), ("raw", 1)]
  defMethods sp "String.prototype" [("at", 1), ("charAt", 1), ("charCodeAt", 1), ("codePointAt", 1),
    ("concat", 1), ("endsWith", 1), ("includes", 1), ("indexOf", 1), ("isWellFormed", 0),
    ("lastIndexOf", 1), ("localeCompare", 1), ("match", 1), ("matchAll", 1), ("normalize", 0),
    ("padEnd", 1), ("padStart", 1), ("repeat", 1), ("replace", 2), ("replaceAll", 2), ("search", 1),
    ("slice", 2), ("split", 2), ("startsWith", 1), ("substring", 2), ("substr", 2),
    ("toLowerCase", 0), ("toUpperCase", 0), ("toLocaleLowerCase", 0), ("toLocaleUpperCase", 0),
    ("toWellFormed", 0), ("trim", 0), ("anchor", 1), ("big", 0), ("blink", 0), ("bold", 0),
    ("fixed", 0), ("fontcolor", 1), ("fontsize", 1), ("italics", 0), ("link", 1), ("small", 0),
    ("strike", 0), ("sub", 0), ("sup", 0)]
  let ts ← defMethod sp (.str "trimStart") "String.prototype.trimStart" 0
  let te ← defMethod sp (.str "trimEnd") "String.prototype.trimEnd" 0
  setOwn sp (.str "trimLeft") (.data (.obj ts) true false true)
  setOwn sp (.str "trimRight") (.data (.obj te) true false true)
  let _ ← defMethod sp (.sym WK.iterator) "String.prototype[Symbol.iterator]" 0
  -- %StringIteratorPrototype%
  let ip ← intrinsic "%Iterator.prototype%"
  let sip ← newIntrinsicObject "%StringIteratorPrototype%" (some ip)
  let _ ← defMethod sip (.str kNext) "%StringIteratorPrototype%.next" 0
  defTag sip "String Iterator"

end ES.Builtins.Text
