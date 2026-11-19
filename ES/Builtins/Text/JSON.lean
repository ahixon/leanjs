import ES.Builtins.Text.Number

/-!
# The JSON object

JSON.parse (a JSON text parser over String values, the reviver's InternalizeJSONProperty with
the source text access of JSON Parse Records), JSON.stringify (SerializeJSONProperty and friends,
well-formed QuoteJSONString), JSON.rawJSON and JSON.isRawJSON.

spec: https://tc39.es/ecma262/#sec-json-object
spec: https://tc39.es/proposal-json-parse-with-source/ (JSON Parse Records, rawJSON, isRawJSON)
-/

namespace ES.Builtins.Text

open ES (F64)

/-- A parsed JSON value: primitives keep their source range [start, stop). -/
inductive JVal where
  | prim (v : Value) (start stop : Nat)
  | arr (xs : Array JVal)
  | obj (kvs : Array (JSStr × JVal))
  deriving Inhabited

/-- The nesting depth bound of JSON.parse (and its reviver walk) and JSON.stringify (deeper structures are a
RangeError, as the call stack's limit is in engines: LIMITATION (docs/es.md L11)). -/
def jsonDepth : Nat := 5000

/-- The message of a JSON text nested past `jsonDepth` (a RangeError). -/
def tooDeep : String := "JSON nesting too deep"

namespace JSONParse

@[inline] def isWS (u : UInt16) : Bool := u == 0x20 || u == 0x09 || u == 0x0A || u == 0x0D

def skipWS (s : JSStr) (i : Nat) : Nat := Id.run do
  let mut i := i
  for _ in [0:s.length] do
    if i < s.length && isWS (s.get i) then i := i + 1 else break
  return i

@[inline] def isDigit (u : UInt16) : Bool := 48 ≤ u && u ≤ 57

/-- A JSON string starting at the quote `i`: its value and the index after the closing quote. -/
def str (s : JSStr) (i : Nat) : Except String (JSStr × Nat) := Id.run do
  let n := s.length
  let mut out := JSStr.empty
  let mut k := i + 1
  for _ in [0:n + 1] do
    if k ≥ n then return .error "Unterminated string in JSON"
    let c := s.get k
    if c == 0x22 then return .ok (out, k + 1)
    if c < 0x20 then return .error "Bad control character in string literal in JSON"
    if c == 0x5C then
      if k + 1 ≥ n then return .error "Bad escaped character in JSON"
      let e := s.get (k + 1)
      if e == 0x75 then
        if k + 6 > n then return .error "Bad Unicode escape in JSON"
        let mut v := 0
        for j in [0:4] do
          match hexVal (s.get (k + 2 + j)) with
          | some d => v := v * 16 + d
          | none => return .error "Bad Unicode escape in JSON"
        out := out.push v.toUInt16
        k := k + 6
      else
        let r : Option UInt16 :=
          if e == 0x22 then some 0x22 else if e == 0x5C then some 0x5C else if e == 0x2F then some 0x2F
          else if e == 0x62 then some 8 else if e == 0x66 then some 12 else if e == 0x6E then some 10
          else if e == 0x72 then some 13 else if e == 0x74 then some 9 else none
        match r with
        | some u => out := out.push u; k := k + 2
        | none => return .error "Bad escaped character in JSON"
    else
      out := out.push c
      k := k + 1
  return .error "Unterminated string in JSON"

/-- A JSON number starting at `i`: its end index. -/
def number (s : JSStr) (i : Nat) : Except String Nat := Id.run do
  let n := s.length
  let digits (k : Nat) : Nat := Id.run do
    let mut k := k
    for _ in [0:n] do
      if k < n && isDigit (s.get k) then k := k + 1 else break
    return k
  let mut k := i
  if k < n && s.get k == 0x2D then k := k + 1
  if k ≥ n || !isDigit (s.get k) then return .error "No number after minus sign in JSON"
  if s.get k == 0x30 then k := k + 1 else k := digits k
  if k < n && s.get k == 0x2E then
    if k + 1 ≥ n || !isDigit (s.get (k + 1)) then return .error "Unterminated fractional number in JSON"
    k := digits (k + 1)
  if k < n && (s.get k == 0x65 || s.get k == 0x45) then
    k := k + 1
    if k < n && (s.get k == 0x2B || s.get k == 0x2D) then k := k + 1
    if k ≥ n || !isDigit (s.get k) then return .error "Exponent part is missing a number in JSON"
    k := digits k
  return .ok k

/-- A JSON value starting at `i` (after whitespace): the value and the index after it; `fuel`
bounds the nesting depth (`jsonDepth`: deeper texts are an engine limit). -/
def value (s : JSStr) : Nat → Nat → Except String (JVal × Nat)
  | 0, _ => .error tooDeep
  | fuel + 1, i => do
    let n := s.length
    let i := skipWS s i
    if i ≥ n then throw "Unexpected end of JSON input"
    let c := s.get i
    if c == 0x7B then
      -- object
      let mut k := skipWS s (i + 1)
      let mut kvs : Array (JSStr × JVal) := #[]
      if k < n && s.get k == 0x7D then return (.obj kvs, k + 1)
      for _ in [0:n] do
        if k ≥ n || s.get k != 0x22 then throw "Expected property name in JSON"
        let (key, k1) ← str s k
        let k2 := skipWS s k1
        if k2 ≥ n || s.get k2 != 0x3A then throw "Expected ':' after property name in JSON"
        let (v, k3) ← value s fuel (k2 + 1)
        kvs := kvs.push (key, v)
        let k4 := skipWS s k3
        if k4 < n && s.get k4 == 0x2C then k := skipWS s (k4 + 1)
        else if k4 < n && s.get k4 == 0x7D then return (.obj kvs, k4 + 1)
        else throw "Expected ',' or '}' after property value in JSON"
      throw "Unterminated object in JSON"
    else if c == 0x5B then
      let mut k := skipWS s (i + 1)
      let mut xs : Array JVal := #[]
      if k < n && s.get k == 0x5D then return (.arr xs, k + 1)
      for _ in [0:n] do
        let (v, k3) ← value s fuel k
        xs := xs.push v
        let k4 := skipWS s k3
        if k4 < n && s.get k4 == 0x2C then k := k4 + 1
        else if k4 < n && s.get k4 == 0x5D then return (.arr xs, k4 + 1)
        else throw "Expected ',' or ']' after array element in JSON"
      throw "Unterminated array in JSON"
    else if c == 0x22 then
      let (v, k) ← str s i
      return (.prim (.str v) i k, k)
    else if c == 0x2D || isDigit c then
      let k ← number s i
      return (.prim (.num (stringToNumber (s.slice i k))) i k, k)
    else if s.matchesAt (JSStr.ofString "true") i then return (.prim (.bool true) i (i + 4), i + 4)
    else if s.matchesAt (JSStr.ofString "false") i then return (.prim (.bool false) i (i + 5), i + 5)
    else if s.matchesAt (JSStr.ofString "null") i then return (.prim .null i (i + 4), i + 4)
    else throw "Unexpected token in JSON"

/-- Parses a whole JSON text. -/
def text (s : JSStr) : Except String JVal := do
  let (v, k) ← value s (jsonDepth + 1) 0
  if skipWS s k < s.length then throw "Unexpected non-whitespace character after JSON"
  return v

end JSONParse

/-- A JSON Parse Record: the value made from a parse node, and its elements' or entries' records;
primitives keep their source text.
spec: https://tc39.es/proposal-json-parse-with-source/#sec-json-parse-record -/
inductive PRec where
  | prim (v : Value) (src : JSStr)
  | arr (v : Value) (elems : Array PRec)
  | obj (v : Value) (entries : Array (JSStr × PRec))
  deriving Inhabited

def PRec.value : PRec → Value
  | .prim v _ | .arr v _ | .obj v _ => v

/-- Creates the values of a parsed JSON text (the evaluation of the JSON text as an expression,
JSON.parse step 9) with their JSON Parse Records (CreateJSONParseRecord). -/
def buildJSON (src : JSStr) : Nat → JVal → M PRec
  | 0, _ => throwRange "Maximum call stack size exceeded"
  | _ + 1, .prim v a b => pure (.prim v (src.slice a b))
  | n + 1, .arr xs => do
    let recs ← M.mapArr xs (buildJSON src n)
    let a ← createArrayFromList (recs.map (·.value))
    pure (.arr a recs)
  | n + 1, .obj kvs => do
    let o ← newObject
    let entries ← M.mapArr kvs fun (k, v) => do
      let r ← buildJSON src n v
      createDataPropertyOrThrow o (.str k) r.value
      pure (k, r)
    pure (.obj (.obj o) entries)


/-- InternalizeJSONProperty spec: https://tc39.es/proposal-json-parse-with-source/#sec-internalizejsonproperty -/
def internalize (reviver : Value) : Nat → ObjId → PropKey → Option PRec → M Value
  | 0, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, holder, name, rec => do
    -- 1.
    let val ← getProp holder name
    -- 2.
    let context ← newObject
    -- 3-4.
    let (elems, entries) ← match rec with
      | some r =>
        if sameValue r.value val then
          match r with
          | .prim _ src =>
            createDataPropertyOrThrow context (.str "source") (.str src)
            pure (#[], #[])
          | .arr _ es => pure (es, #[])
          | .obj _ ens => pure (#[], ens)
        else pure (#[], #[])
      | none => pure (#[], #[])
    -- 5.
    if let .obj o := val then
      if ← isArray val then
        let len ← lengthOf o
        M.repeatFrom 0 fun i => do
          if i ≥ len then return .inr ()
          M.tick
          let prop := PropKey.ofNat i
          let newElement ← internalize reviver n o prop elems[i]?
          if newElement.isUndefined then let _ ← Obj'.delete o prop
          else let _ ← createDataProperty o prop newElement
          return .inl (i + 1)
      else
        let keys ← enumerableOwnProperties o 0
        M.forArr keys fun pv => do
          let .str p := pv | pure ()
          let er := (entries.reverse.find? (·.1 == p)).map (·.2)
          let newElement ← internalize reviver n o (.str p) er
          if newElement.isUndefined then let _ ← Obj'.delete o (.str p)
          else let _ ← createDataProperty o (.str p) newElement
    -- 6.
    call reviver (.obj holder) #[keyToValue name, val, .obj context]

/-- JSON.parse spec: https://tc39.es/ecma262/#sec-json.parse -/
def jsonParse : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let jsonString ← toStr (arg args 0)
  -- 2-8.
  let jv ← match JSONParse.text jsonString with
    | .ok v => pure v
    | .error m => if m == tooDeep then throwRange m else throwError .syntaxError m
  -- 9-10.
  let rec_ ← buildJSON jsonString (jsonDepth + 2) jv
  let unfiltered := rec_.value
  -- 11.
  let reviver := arg args 1
  if ← isCallable reviver then
    let root ← newObject
    createDataPropertyOrThrow root (.str JSStr.empty) unfiltered
    return ← internalize reviver jsonDepth root (.str JSStr.empty) (some rec_)
  -- 12.
  pure unfiltered

/-- JSON.rawJSON spec: https://tc39.es/proposal-json-parse-with-source/#sec-json.rawjson -/
def jsonRawJSON : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let jsonString ← toStr (arg args 0)
  -- 2.
  let n := jsonString.length
  if n == 0 || JSONParse.isWS (jsonString.get 0) || JSONParse.isWS (jsonString.get (n - 1)) then
    throwError .syntaxError "Invalid value for JSON.rawJSON"
  -- 3.
  match JSONParse.text jsonString with
  | .ok (.prim ..) => pure ()
  | .ok _ => throwError .syntaxError "Invalid value for JSON.rawJSON"
  | .error m => throwError .syntaxError m
  -- 4-5.
  let o ← ordinaryObjectCreate .null (.internal "RawJSON" #[])
  -- 6-8.
  createDataPropertyOrThrow o (.str "rawJSON") (.str jsonString)
  let _ ← setIntegrityLevel o true
  pure (.obj o)

def isRawJSONObj (v : Value) : M Bool := do
  let .obj o := v | return false
  match ← objKind o with
  | .internal "RawJSON" _ => pure true
  | _ => pure false

/-- JSON.isRawJSON spec: https://tc39.es/proposal-json-parse-with-source/#sec-json.israwjson -/
def jsonIsRawJSON : BuiltinFn := fun _ _ args _ => do
  pure (.bool (← isRawJSONObj (arg args 0)))

/-- QuoteJSONString spec: https://tc39.es/ecma262/#sec-quotejsonstring -/
def quoteJSONString (s : JSStr) (out : JSStr) : JSStr := Id.run do
  let esc (o : JSStr) (c : Char) : JSStr := (o.push 0x5C).push c.toNat.toUInt16
  let mut out := out.push 0x22
  let mut k := 0
  for _ in [0:s.length] do
    if k ≥ s.length then break
    let (cp, n, lone) := s.codePointAt k
    out :=
      if cp == 8 then esc out 'b' else if cp == 9 then esc out 't' else if cp == 10 then esc out 'n'
      else if cp == 12 then esc out 'f' else if cp == 13 then esc out 'r'
      else if cp == 0x22 then esc out '"' else if cp == 0x5C then esc out '\\'
      else if cp < 0x20 || lone then (out.push 0x5C).push 0x75 ++ JSStr.ofString (Num.natDigits cp 16 4)
      else out.pushCodePoint cp
    k := k + n
  return out.push 0x22

/-- The JSON Serialization Record's fixed parts. -/
structure SerState where
  replacer : Option Value
  propertyList : Option (Array JSStr)
  gap : JSStr

/-- SerializeJSONProperty (with SerializeJSONObject and SerializeJSONArray); `stack` and `indent`
are the record's changing parts. `none` is undefined.
spec: https://tc39.es/ecma262/#sec-serializejsonproperty
spec: https://tc39.es/ecma262/#sec-serializejsonobject
spec: https://tc39.es/ecma262/#sec-serializejsonarray -/
def serialize (st : SerState) : Nat → Array ObjId → JSStr → PropKey → Value → M (Option JSStr)
  | 0, _, _, _, _ => throwRange "Maximum call stack size exceeded"
  | n + 1, stack, indent, key, holder => do
    -- 1.
    let value ← match holder with
      | .obj h => getProp h key
      | _ => pure .undefined
    -- 2.
    let value ← match value with
      | .obj _ | .bigint _ =>
        let toJSON ← getVProp value (.str "toJSON")
        if ← isCallable toJSON then call toJSON value #[keyToValue key] else pure value
      | _ => pure value
    -- 3.
    let value ← match st.replacer with
      | some f => call f holder #[keyToValue key, value]
      | none => pure value
    -- 4.
    let value ← match value with
      | .obj o =>
        match ← objKind o with
        | .internal "RawJSON" _ => return some (← toStr (← getProp o (.str "rawJSON")))
        | .primitive (.num _) => pure (Value.num (← toNum value))
        | .primitive (.str _) => pure (Value.str (← toStr value))
        | .primitive (.bool b) => pure (Value.bool b)
        | .primitive (.bigint i) => pure (Value.bigint i)
        | _ => pure value
      | _ => pure value
    -- 5-10.
    match value with
    | .null => return some (JSStr.ofString "null")
    | .bool true => return some (JSStr.ofString "true")
    | .bool false => return some (JSStr.ofString "false")
    | .str s => return some (quoteJSONString s JSStr.empty)
    | .num x => return some (if Num.isFinite x then numberToJSStr x else JSStr.ofString "null")
    | .bigint _ => throwType "Do not know how to serialize a BigInt"
    | .obj o =>
      -- 11.
      if ← isCallable value then return none
      -- (SerializeJSONObject/Array) 1-2.
      if stack.contains o then throwType "Converting circular structure to JSON"
      let stack := stack.push o
      -- 3-4.
      let stepback := indent
      let indent := indent ++ st.gap
      let isArr ← isArray value
      let partial_ ← if isArr then do
          let len ← lengthOf o
          M.repeatFrom (0, (#[] : Array JSStr)) fun (index, acc) => do
            if index ≥ len then return .inr acc
            M.tick
            let strP ← serialize st n stack indent (PropKey.ofNat index) value
            return .inl (index + 1, acc.push (strP.getD (JSStr.ofString "null")))
        else do
          let K ← match st.propertyList with
            | some pl => pure pl
            | none => do
              let ks ← enumerableOwnProperties o 0
              pure (ks.filterMap fun k => match k with | .str s => some s | _ => none)
          M.foldArr K #[] fun acc P => do
            let strP ← serialize st n stack indent (.str P) value
            match strP with
            | some sp =>
              let member := quoteJSONString P JSStr.empty
              let member := member.push 0x3A
              let member := if st.gap.isEmpty then member else member.push 0x20
              pure (acc.push (member ++ sp))
            | none => pure acc
      let (op, cl) : UInt16 × UInt16 := if isArr then (0x5B, 0x5D) else (0x7B, 0x7D)
      if partial_.isEmpty then return some ((JSStr.empty.push op).push cl)
      if st.gap.isEmpty then
        return some ((JSStr.join partial_ (JSStr.ofString ",")).push cl |> fun s => (JSStr.empty.push op) ++ s)
      let nl := JSStr.ofString "\n"
      let separator := JSStr.ofString ",\n" ++ indent
      return some ((JSStr.empty.push op) ++ nl ++ indent ++ JSStr.join partial_ separator ++ nl ++ stepback |>.push cl)
    | _ => return none

/-- JSON.stringify spec: https://tc39.es/ecma262/#sec-json.stringify -/
def jsonStringify : BuiltinFn := fun _ _ args _ => do
  let value := arg args 0
  let replacer := arg args 1
  let space := arg args 2
  -- 1-4.
  let (replacerFn, propertyList) ← match replacer with
    | .obj ro =>
      if ← isCallable replacer then pure (some replacer, none)
      else if ← isArray replacer then
        let len ← lengthOf ro
        let pl ← M.repeatFrom (0, (#[] : Array JSStr)) fun (k, pl) => do
          if k ≥ len then return .inr pl
          M.tick
          let v ← getProp ro (PropKey.ofNat k)
          let item ← match v with
            | .str s => pure (some s)
            | .num x => pure (some (numberToJSStr x))
            | .obj vo => match ← objKind vo with
              | .primitive (.str _) | .primitive (.num _) => some <$> toStr v
              | _ => pure none
            | _ => pure none
          match item with
          | some it => return .inl (k + 1, if pl.contains it then pl else pl.push it)
          | none => return .inl (k + 1, pl)
        pure (none, some pl)
      else pure (none, none)
    | _ => pure (none, none)
  -- 5.
  let space ← match space with
    | .obj so => match ← objKind so with
      | .primitive (.num _) => pure (Value.num (← toNum space))
      | .primitive (.str _) => pure (Value.str (← toStr space))
      | _ => pure space
    | _ => pure space
  -- 6-8.
  let gap : JSStr := match space with
    | .num x =>
      let k := (Num.toIntegerClamp x 0 10).toNat
      (List.range k).foldl (fun acc _ => acc.push 0x20) JSStr.empty
    | .str s => s.take 10
    | _ => JSStr.empty
  -- 9-10.
  let wrapper ← newObject
  createDataPropertyOrThrow wrapper (.str JSStr.empty) value
  -- 11-12.
  let st : SerState := { replacer := replacerFn, propertyList, gap }
  match ← serialize st jsonDepth #[] JSStr.empty (.str JSStr.empty) (.obj wrapper) with
  | some s => pure (.str s)
  | none => pure .undefined

def jsonDefs : Array BuiltinDef := #[
  ⟨"JSON.parse", jsonParse⟩, ⟨"JSON.stringify", jsonStringify⟩,
  ⟨"JSON.rawJSON", jsonRawJSON⟩, ⟨"JSON.isRawJSON", jsonIsRawJSON⟩]

def jsonSetup : M Unit := do
  let j ← newIntrinsicObject "%JSON%"
  defGlobal "JSON" (.obj j)
  defMethods j "JSON" [("parse", 2), ("stringify", 3), ("rawJSON", 1), ("isRawJSON", 1)]
  defTag j "JSON"

end ES.Builtins.Text
