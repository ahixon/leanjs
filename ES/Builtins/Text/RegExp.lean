import ES.Builtins.Text.Number

/-!
# RegExp objects

The constructor (IsRegExp, RegExpAlloc, RegExpInitialize), RegExp.escape, the prototype's exec,
test, toString, flag getters, source (EscapeRegExpPattern), the @@match/@@matchAll/@@replace/
@@search/@@split methods (with GetSubstitution, which String.prototype.replace shares),
Annex B's compile, and %RegExpStringIteratorPrototype%. Matching itself is `ES/Regex.lean`'s.

spec: https://tc39.es/ecma262/#sec-regexp-regular-expression-objects
-/

namespace ES.Builtins.Text

open ES (F64)

def kLastIndex : JSStr := "lastIndex"
def kIndex : JSStr := "index"
def kInput : JSStr := "input"
def kGroups : JSStr := "groups"
def kFlags : JSStr := "flags"
def kSource : JSStr := "source"

/-- The [[OriginalSource]], [[OriginalFlags]] and [[RegExpMatcher]] of an initialized RegExp. -/
def regexpParts? (v : Value) : M (Option (JSStr × JSStr × Regex.Program)) := do
  let .obj o := v | return none
  match ← objKind o with
  | .regexp src fl p => pure (some (src, fl, p))
  | _ => pure none

/-- Whether a String contains a code unit. -/
def strHas (s : JSStr) (c : Char) : Bool := (s.indexOf (JSStr.empty.push c.toNat.toUInt16)).isSome

/-- AdvanceStringIndex spec: https://tc39.es/ecma262/#sec-advancestringindex -/
def advanceStringIndex (s : JSStr) (index : Nat) (unicode : Bool) : Nat :=
  -- 2.
  if !unicode then index + 1
  -- 3-4.
  else if index + 1 ≥ s.length then index + 1
  -- 5-6.
  else index + (s.codePointAt index).2.1

/-- IsRegExp spec: https://tc39.es/ecma262/#sec-isregexp -/
def isRegExp (v : Value) : M Bool := do
  -- 1.
  let .obj o := v | return false
  -- 2-3.
  let m ← getProp o (.sym WK.match)
  if !m.isUndefined then return toBoolean m
  -- 4-5.
  pure (← regexpParts? v).isSome

/-- RegExpAlloc spec: https://tc39.es/ecma262/#sec-regexpalloc -/
def regexpAlloc (newTarget : Value) : M ObjId := do
  -- 1.
  let o ← ordinaryCreateFromConstructor newTarget "%RegExp.prototype%" (.internal "RegExpAlloc" #[])
  -- 2-3.
  definePropertyOrThrow o (.str kLastIndex) { writable := some true, enumerable := some false, configurable := some false }
  pure o

/-- RegExpInitialize spec: https://tc39.es/ecma262/#sec-regexpinitialize -/
def regexpInitialize (o : ObjId) (pattern flags : Value) : M Value := do
  -- 1-2.
  let P ← if pattern.isUndefined then pure JSStr.empty else toStr pattern
  let F ← if flags.isUndefined then pure JSStr.empty else toStr flags
  -- 3-12.
  match Regex.compile P F with
  | .error msg => throwError .syntaxError s!"Invalid regular expression: /{P}/{F}: {msg}"
  | .ok prog =>
    modifyObj o fun ob => { ob with kind := .regexp P F prog }
    -- 13.
    setProp o (.str kLastIndex) (numV 0)
    -- 14.
    pure (.obj o)

/-- RegExpCreate spec: https://tc39.es/ecma262/#sec-regexpcreate -/
def regexpCreate (P F : Value) : M Value := do
  -- 1.
  let o ← regexpAlloc (← intrinsicV "%RegExp%")
  -- 2.
  regexpInitialize o P F

/-- RegExp(pattern, flags) spec: https://tc39.es/ecma262/#sec-regexp-pattern-flags -/
def regexpCtor : BuiltinFn := fun self _ args nt => do
  let pattern := arg args 0
  let flags := arg args 1
  -- 1.
  let patternIsRegExp ← isRegExp pattern
  -- 2-3.
  let newTarget := if nt.isUndefined then Value.obj self else nt
  if nt.isUndefined && patternIsRegExp && flags.isUndefined then
    if let .obj po := pattern then
      let pc ← getProp po (.str kConstructor)
      if sameValue newTarget pc then return pattern
  -- 4-6.
  let (P, F) ← match ← regexpParts? pattern with
    | some (src, fl, _) => pure (Value.str src, if flags.isUndefined then Value.str fl else flags)
    | none =>
      if patternIsRegExp then
        let .obj po := pattern | pure (pattern, flags)
        let src ← getProp po (.str kSource)
        let F ← if flags.isUndefined then getProp po (.str kFlags) else pure flags
        pure (src, F)
      else pure (pattern, flags)
  -- 7.
  let o ← regexpAlloc newTarget
  -- 8.
  regexpInitialize o P F

/-- The digits of a code point in lowercase hexadecimal, at least `w` of them. -/
def hexLower (n w : Nat) : JSStr := JSStr.ofString (Num.natDigits n 16 w)

/-- EncodeForRegExpEscape spec: https://tc39.es/ecma262/#sec-encodeforregexpescape -/
def encodeForRegExpEscape (c : Nat) (lone : Bool) : JSStr :=
  let bs := JSStr.empty.push 0x5C
  -- 1.
  if "^$\\.*+?()[]{}|/".any (·.toNat == c) then bs.pushCodePoint c
  -- 2.
  else if c == 9 then bs.push 0x74 else if c == 10 then bs.push 0x6E
  else if c == 11 then bs.push 0x76 else if c == 12 then bs.push 0x66
  else if c == 13 then bs.push 0x72
  else
  -- 3-5.
  let isWS := c < 0x10000 && Num.isStrWhiteSpace c.toUInt16
  if ",-=<>#&!%:;@~'`\"".any (·.toNat == c) || isWS || lone then
    if c ≤ 0xFF then (bs.push 0x78) ++ hexLower c 2
    else
      let units := (JSStr.empty.pushCodePoint c).toUnits
      units.foldl (fun acc u => (acc.push 0x5C).push 0x75 ++ hexLower u.toNat 4) JSStr.empty
  -- 6.
  else JSStr.empty.pushCodePoint c

/-- RegExp.escape(S) spec: https://tc39.es/ecma262/#sec-regexp.escape -/
def regexpEscape : BuiltinFn := fun _ _ args _ => do
  -- 1.
  let .str s := arg args 0 | throwType "RegExp.escape requires a string"
  -- 2-4.
  let r := Id.run do
    let mut out := JSStr.empty
    let mut i := 0
    for _ in [0:s.length] do
      if i ≥ s.length then break
      let (cp, n, lone) := s.codePointAt i
      if out.isEmpty && ((48 ≤ cp && cp ≤ 57) || (65 ≤ cp && cp ≤ 90) || (97 ≤ cp && cp ≤ 122)) then
        out := (out.push 0x5C).push 0x78 ++ hexLower cp 2
      else out := out ++ encodeForRegExpEscape cp lone
      i := i + n
    return out
  pure (.str r)

/-- MakeMatchIndicesIndexPairArray spec: https://tc39.es/ecma262/#sec-makematchindicesindexpairarray -/
def makeMatchIndicesIndexPairArray (indices : Array (Option (Nat × Nat)))
    (groupNames : Array (Option JSStr)) (hasGroups : Bool) : M Value := do
  -- 1-4.
  let A ← arrayCreate 0
  -- 5-6.
  let groups ← if hasGroups then (Value.obj <$> ordinaryObjectCreate .null) else pure .undefined
  -- 7.
  createDataPropertyOrThrow A (.str kGroups) groups
  -- 8.
  M.forArr (Array.range indices.size) fun i => do
    let pair ← match indices[i]! with
      | some (s, e) => createArrayFromList #[numV s, numV e]
      | none => pure .undefined
    createDataPropertyOrThrow A (PropKey.ofNat i) pair
    if i > 0 then
      if let some (some nm) := groupNames[i - 1]? then
        let .obj g := groups | pure ()
        createDataPropertyOrThrow g (.str nm) pair
  pure (.obj A)

/-- RegExpBuiltinExec spec: https://tc39.es/ecma262/#sec-regexpbuiltinexec -/
def regexpBuiltinExec (R : ObjId) (S : JSStr) : M Value := do
  -- 1.
  let length := S.length
  -- 2.
  let lastIndex ← toLen (← getProp R (.str kLastIndex))
  -- 3-6.
  let some (_, _, prog) ← regexpParts? (.obj R) | throwType "RegExp exec called on incompatible receiver"
  let global := prog.global
  let sticky := prog.sticky
  let hasIndices := prog.hasIndices
  -- 7.
  let lastIndex := if !global && !sticky then 0 else lastIndex
  -- 8-12. (the matcher reads code points itself for u/v: `Regex.matchAt`)
  -- 13. (the loop: one match attempt when sticky, else `Regex.search` from lastIndex, which
  -- advances as AdvanceStringIndex does)
  let fail : M Value := do
    if global || sticky then setProp R (.str kLastIndex) (numV 0)
    pure .null
  if lastIndex > length then return ← fail
  let r := if sticky then Regex.matchAt prog S lastIndex else Regex.search prog S lastIndex
  let m ← match r with
    | .ok (some m) => pure m
    | .ok none => return ← fail
    | .error msg => throwRange s!"RegExp: {msg}"
  -- 14-15.
  let e := m.endIndex
  let start := match m.captures[0]? with | some (some (s, _)) => s | _ => lastIndex
  -- 16.
  if global || sticky then setProp R (.str kLastIndex) (numV e)
  -- 17-20.
  let n := prog.groupCount
  let vals : Array Value := (Array.range (n + 1)).map fun i =>
    match m.captures[i]? with
    | some (some (s, t)) => .str (S.slice s t)
    | _ => .undefined
  let vals := vals.set! 0 (.str (S.slice start e))
  let Av ← createArrayFromList vals
  let .obj A := Av | pure .null
  -- 21-22.
  createDataPropertyOrThrow A (.str kIndex) (numV start)
  createDataPropertyOrThrow A (.str kInput) (.str S)
  -- 28-30.
  let hasGroups := prog.hasGroupNames
  let groups ← if hasGroups then (Value.obj <$> ordinaryObjectCreate .null) else pure .undefined
  createDataPropertyOrThrow A (.str kGroups) groups
  -- 31-32. (named groups: a name's value is its participating group's capture)
  let (groupNames, _) ← M.foldArr (Array.range n) ((#[] : Array (Option JSStr)), (#[] : Array JSStr))
      fun (gn, matched) j => do
    let i := j + 1
    match prog.groupNames[i]? with
    | some (some s) =>
      if matched.contains s then return (gn.push none, matched)
      let cv := vals[i]!
      let matched := if cv.isUndefined then matched else matched.push s
      let .obj g := groups | return (gn.push (some s), matched)
      createDataPropertyOrThrow g (.str s) cv
      return (gn.push (some s), matched)
    | _ => return (gn.push none, matched)
  -- 33.
  if hasIndices then
    let indices := (Array.range (n + 1)).map fun i =>
      if i == 0 then some (start, e) else (m.captures[i]?).bind id
    let ia ← makeMatchIndicesIndexPairArray indices groupNames hasGroups
    createDataPropertyOrThrow A (.str "indices") ia
  -- 34.
  pure (.obj A)

/-- RegExpExec spec: https://tc39.es/ecma262/#sec-regexpexec -/
def regexpExec (R : ObjId) (S : JSStr) : M Value := do
  -- 1.
  let exec ← getProp R (.str "exec")
  -- 2.
  if ← isCallable exec then
    let result ← call exec (.obj R) #[.str S]
    match result with
    | .obj _ | .null => return result
    | _ => throwType "RegExp exec method returned something other than an Object or null"
  -- 3-4.
  if (← regexpParts? (.obj R)).isNone then throwType "RegExp.prototype.exec called on incompatible receiver"
  regexpBuiltinExec R S

/-- RegExp.prototype.exec spec: https://tc39.es/ecma262/#sec-regexp.prototype.exec -/
def regexpProtoExec : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj R := thisV | throwType "RegExp.prototype.exec called on incompatible receiver"
  if (← regexpParts? thisV).isNone then throwType "RegExp.prototype.exec called on incompatible receiver"
  -- 3.
  let S ← toStr (arg args 0)
  -- 4.
  regexpBuiltinExec R S

/-- RegExp.prototype.test spec: https://tc39.es/ecma262/#sec-regexp.prototype.test -/
def regexpProtoTest : BuiltinFn := fun _ thisV args _ => do
  let .obj R := thisV | throwType "RegExp.prototype.test called on incompatible receiver"
  let S ← toStr (arg args 0)
  let m ← regexpExec R S
  pure (.bool !(match m with | .null => true | _ => false))

/-- RegExp.prototype.toString spec: https://tc39.es/ecma262/#sec-regexp.prototype.tostring -/
def regexpProtoToString : BuiltinFn := fun _ thisV _ _ => do
  let .obj R := thisV | throwType "RegExp.prototype.toString called on incompatible receiver"
  let p ← toStr (← getProp R (.str kSource))
  let f ← toStr (← getProp R (.str kFlags))
  pure (.str ((JSStr.empty.push 0x2F) ++ p ++ (JSStr.empty.push 0x2F) ++ f))

/-- RegExpHasFlag spec: https://tc39.es/ecma262/#sec-regexphasflag -/
def regexpHasFlag (flag : Char) : BuiltinFn := fun _ thisV _ _ => do
  -- 1-2.
  let .obj _ := thisV | throwType s!"RegExp flag getter called on non-object"
  -- 3.
  match ← regexpParts? thisV with
  | none =>
    if sameValue thisV (← intrinsicV "%RegExp.prototype%") then return .undefined
    throwType "RegExp flag getter called on incompatible receiver"
  -- 4-6.
  | some (_, fl, _) => pure (.bool (strHas fl flag))

/-- get RegExp.prototype.flags spec: https://tc39.es/ecma262/#sec-get-regexp.prototype.flags -/
def regexpProtoFlags : BuiltinFn := fun _ thisV _ _ => do
  let .obj R := thisV | throwType "RegExp.prototype.flags getter called on non-object"
  let r ← M.foldArr #[("hasIndices", 'd'), ("global", 'g'), ("ignoreCase", 'i'), ("multiline", 'm'),
      ("dotAll", 's'), ("unicode", 'u'), ("unicodeSets", 'v'), ("sticky", 'y')] JSStr.empty
      fun acc (nm, c) => do
    let b := toBoolean (← getProp R (.str (JSStr.ofString nm)))
    pure (if b then acc.push c.toNat.toUInt16 else acc)
  pure (.str r)

/-- EscapeRegExpPattern spec: https://tc39.es/ecma262/#sec-escaperegexppattern
(the escaping V8 does: `/` outside classes, line terminators, `(?:)` for the empty pattern) -/
def escapeRegExpPattern (src : JSStr) : JSStr := Id.run do
  if src.isEmpty then return JSStr.ofString "(?:)"
  let mut out := JSStr.empty
  let mut inClass := false
  let mut escaped := false
  for i in [0:src.length] do
    let c := src.get i
    let lt : Option String :=
      if c == 10 then some "n" else if c == 13 then some "r" else if c == 0x2028 then some "u2028"
      else if c == 0x2029 then some "u2029" else none
    if escaped then
      escaped := false
      match lt with
      | some e => out := out ++ JSStr.ofString e
      | none => out := out.push c
    else if c == 0x5C then
      out := out.push c
      escaped := true
    else
      match lt with
      | some e => out := (out.push 0x5C) ++ JSStr.ofString e
      | none =>
        if c == 0x2F && !inClass then out := (out.push 0x5C).push c
        else
          if c == 0x5B then inClass := true
          else if c == 0x5D then inClass := false
          out := out.push c
  return out

/-- get RegExp.prototype.source spec: https://tc39.es/ecma262/#sec-get-regexp.prototype.source -/
def regexpProtoSource : BuiltinFn := fun _ thisV _ _ => do
  let .obj _ := thisV | throwType "RegExp.prototype.source getter called on non-object"
  match ← regexpParts? thisV with
  | none =>
    if sameValue thisV (← intrinsicV "%RegExp.prototype%") then return .str (JSStr.ofString "(?:)")
    throwType "RegExp.prototype.source getter called on incompatible receiver"
  | some (src, _, _) => pure (.str (escapeRegExpPattern src))

/-- GetSubstitution spec: https://tc39.es/ecma262/#sec-getsubstitution -/
def getSubstitution (matched str : JSStr) (position : Nat) (captures : Array Value)
    (namedCaptures : Value) (template : JSStr) : M JSStr := do
  -- 1-2.
  let stringLength := str.length
  let m := captures.size
  let tl := template.length
  let isDigit (u : UInt16) : Bool := 48 ≤ u && u ≤ 57
  -- 4-5.
  M.repeatFrom (0, JSStr.empty) fun (i, result) => do
    if i ≥ tl then return .inr result
    let c := template.get i
    let c1 := if i + 1 < tl then template.get (i + 1) else 0
    if c != 0x24 || i + 1 ≥ tl then return .inl (i + 1, result.push c)
    -- $$
    if c1 == 0x24 then return .inl (i + 2, result.push 0x24)
    -- $`
    if c1 == 0x60 then return .inl (i + 2, result ++ str.slice 0 position)
    -- $&
    if c1 == 0x26 then return .inl (i + 2, result ++ matched)
    -- $'
    if c1 == 0x27 then
      let tailPos := min (position + matched.length) stringLength
      return .inl (i + 2, result ++ str.slice tailPos stringLength)
    -- $n, $nn
    if isDigit c1 then
      let c2 := if i + 2 < tl then template.get (i + 2) else 0
      let (digitCount, index) :=
        if isDigit c2 then
          let idx := (c1.toNat - 48) * 10 + (c2.toNat - 48)
          if idx > m then (1, c1.toNat - 48) else (2, idx)
        else (1, c1.toNat - 48)
      let ref := template.slice i (i + 1 + digitCount)
      if 1 ≤ index && index ≤ m then
        let rep ← match captures[index - 1]! with
          | .undefined => pure JSStr.empty
          | v => toStr v
        return .inl (i + 1 + digitCount, result ++ rep)
      return .inl (i + 1 + digitCount, result ++ ref)
    -- $<
    if c1 == 0x3C then
      let gtPos := template.indexOf (JSStr.ofString ">") i
      match gtPos, namedCaptures with
      | some gt, .obj nc =>
        let groupName := template.slice (i + 2) gt
        let capture ← getProp nc (.str groupName)
        let rep ← if capture.isUndefined then pure JSStr.empty else toStr capture
        return .inl (gt + 1, result ++ rep)
      | _, _ => return .inl (i + 2, (result.push 0x24).push 0x3C)
    return .inl (i + 1, result.push c)

/-- RegExp.prototype[@@match] spec: https://tc39.es/ecma262/#sec-regexp.prototype-%symbol.match% -/
def regexpProtoMatch : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj rx := thisV | throwType "RegExp.prototype[Symbol.match] called on non-object"
  -- 3.
  let S ← toStr (arg args 0)
  -- 4.
  let flags ← toStr (← getProp rx (.str kFlags))
  -- 5.
  if !strHas flags 'g' then return ← regexpExec rx S
  -- 6.
  let fullUnicode := strHas flags 'u' || strHas flags 'v'
  setProp rx (.str kLastIndex) (numV 0)
  let A ← arrayCreate 0
  M.repeatFrom 0 fun n => do
    M.tick
    let result ← regexpExec rx S
    match result with
    | .obj res =>
      let matchStr ← toStr (← getProp res (PropKey.ofNat 0))
      createDataPropertyOrThrow A (PropKey.ofNat n) (.str matchStr)
      if matchStr.isEmpty then
        let thisIndex ← toLen (← getProp rx (.str kLastIndex))
        setProp rx (.str kLastIndex) (numV (advanceStringIndex S thisIndex fullUnicode))
      return .inl (n + 1)
    | _ => return .inr (if n == 0 then Value.null else .obj A)

/-- CreateRegExpStringIterator spec: https://tc39.es/ecma262/#sec-createregexpstringiterator -/
def createRegExpStringIterator (R : Value) (S : JSStr) (global fullUnicode : Bool) : M Value := do
  let proto ← intrinsic "%RegExpStringIteratorPrototype%"
  let sl : Array Value := #[R, .str S, .bool global, .bool fullUnicode, .bool false]
  let it ← alloc { proto := .obj proto, kind := .internal "RegExp String Iterator" sl }
  pure (.obj it)

/-- RegExp.prototype[@@matchAll] spec: https://tc39.es/ecma262/#sec-regexp-prototype-%symbol.matchall% -/
def regexpProtoMatchAll : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj R := thisV | throwType "RegExp.prototype[Symbol.matchAll] called on non-object"
  -- 3.
  let S ← toStr (arg args 0)
  -- 4.
  let C ← speciesConstructor R (← intrinsicV "%RegExp%")
  -- 5.
  let flags ← toStr (← getProp R (.str kFlags))
  -- 6.
  let matcher ← construct C #[.obj R, .str flags]
  let .obj mo := matcher | throwType "RegExp species constructor returned a non-object"
  -- 7-8.
  let lastIndex ← toLen (← getProp R (.str kLastIndex))
  setProp mo (.str kLastIndex) (numV lastIndex)
  -- 9-12.
  createRegExpStringIterator matcher S (strHas flags 'g') (strHas flags 'u' || strHas flags 'v')

/-- %RegExpStringIteratorPrototype%.next
spec: https://tc39.es/ecma262/#sec-%regexpstringiteratorprototype%.next -/
def regexpStringIteratorNext : BuiltinFn := fun _ thisV _ _ => do
  let .obj it := thisV | throwType "next method called on incompatible receiver"
  let .internal "RegExp String Iterator" sl ← objKind it | throwType "next method called on incompatible receiver"
  let done := match sl[4]? with | some (.bool b) => b | _ => true
  if done then return ← createIterResult .undefined true
  let .obj R := sl[0]! | createIterResult .undefined true
  let S := match sl[1]! with | .str s => s | _ => JSStr.empty
  let global := match sl[2]! with | .bool b => b | _ => false
  let fullUnicode := match sl[3]! with | .bool b => b | _ => false
  let setDone : M Unit := modifyObj it fun o => { o with kind := .internal "RegExp String Iterator" (sl.set! 4 (.bool true)) }
  let m ← regexpExec R S
  match m with
  | .obj mo =>
    if global then
      let matchStr ← toStr (← getProp mo (PropKey.ofNat 0))
      if matchStr.isEmpty then
        let thisIndex ← toLen (← getProp R (.str kLastIndex))
        setProp R (.str kLastIndex) (numV (advanceStringIndex S thisIndex fullUnicode))
      createIterResult m false
    else
      setDone
      createIterResult m false
  | _ =>
    setDone
    createIterResult .undefined true

/-- RegExp.prototype[@@replace] spec: https://tc39.es/ecma262/#sec-regexp.prototype-%symbol.replace% -/
def regexpProtoReplace : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj rx := thisV | throwType "RegExp.prototype[Symbol.replace] called on non-object"
  -- 3-4.
  let S ← toStr (arg args 0)
  let lengthS := S.length
  -- 5-6.
  let replaceValue := arg args 1
  let functionalReplace ← isCallable replaceValue
  let replaceStr ← if functionalReplace then pure JSStr.empty else toStr replaceValue
  -- 7-8.
  let flags ← toStr (← getProp rx (.str kFlags))
  let global := strHas flags 'g'
  -- 9.
  let fullUnicode := strHas flags 'u' || strHas flags 'v'
  if global then setProp rx (.str kLastIndex) (numV 0)
  -- 10-12.
  let results ← M.repeatFrom (#[] : Array ObjId) fun results => do
    M.tick
    let result ← regexpExec rx S
    match result with
    | .obj r =>
      let results := results.push r
      if !global then return .inr results
      let matchStr ← toStr (← getProp r (PropKey.ofNat 0))
      if matchStr.isEmpty then
        let thisIndex ← toLen (← getProp rx (.str kLastIndex))
        setProp rx (.str kLastIndex) (numV (advanceStringIndex S thisIndex fullUnicode))
      return .inl results
    | _ => return .inr results
  -- 13-14.
  let (acc, nextSourcePosition) ← M.foldArr results (JSStr.empty, 0) fun (acc, nextPos) result => do
    -- a-b.
    let resultLength ← lengthOf result
    let nCaptures := resultLength - 1
    -- c-d.
    let matched ← toStr (← getProp result (PropKey.ofNat 0))
    let matchLength := matched.length
    -- e-f.
    let position ← toIntClamp (← getProp result (.str kIndex)) 0 lengthS
    let position := position.toNat
    -- g-i.
    let captures ← M.mapArr (Array.range nCaptures) fun k => do
      let capN ← getProp result (PropKey.ofNat (k + 1))
      if capN.isUndefined then pure capN else pure (.str (← toStr capN))
    -- j.
    let namedCaptures ← getProp result (.str kGroups)
    -- k-l.
    let replacement ← if functionalReplace then do
        let mut replacerArgs := #[Value.str matched] ++ captures ++ #[numV position, .str S]
        if !namedCaptures.isUndefined then replacerArgs := replacerArgs.push namedCaptures
        let replValue ← call replaceValue .undefined replacerArgs
        toStr replValue
      else do
        let nc ← if namedCaptures.isUndefined then pure Value.undefined else (Value.obj <$> toObject namedCaptures)
        getSubstitution matched S position captures nc replaceStr
    -- m.
    if position ≥ nextPos then
      pure (acc ++ S.slice nextPos position ++ replacement, position + matchLength)
    else pure (acc, nextPos)
  -- 15-16.
  if nextSourcePosition ≥ lengthS then return .str acc
  pure (.str (acc ++ S.slice nextSourcePosition lengthS))

/-- RegExp.prototype[@@search] spec: https://tc39.es/ecma262/#sec-regexp.prototype-%symbol.search% -/
def regexpProtoSearch : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj rx := thisV | throwType "RegExp.prototype[Symbol.search] called on non-object"
  -- 3.
  let S ← toStr (arg args 0)
  -- 4-5.
  let previousLastIndex ← getProp rx (.str kLastIndex)
  if !sameValue previousLastIndex (numV 0) then setProp rx (.str kLastIndex) (numV 0)
  -- 6.
  let result ← regexpExec rx S
  -- 7-8.
  let currentLastIndex ← getProp rx (.str kLastIndex)
  if !sameValue currentLastIndex previousLastIndex then setProp rx (.str kLastIndex) previousLastIndex
  -- 9-10.
  match result with
  | .obj r => getProp r (.str kIndex)
  | _ => pure (intV (-1))

/-- RegExp.prototype[@@split] spec: https://tc39.es/ecma262/#sec-regexp.prototype-%symbol.split% -/
def regexpProtoSplit : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj rx := thisV | throwType "RegExp.prototype[Symbol.split] called on non-object"
  -- 3.
  let S ← toStr (arg args 0)
  -- 4.
  let C ← speciesConstructor rx (← intrinsicV "%RegExp%")
  -- 5-7.
  let flags ← toStr (← getProp rx (.str kFlags))
  let unicodeMatching := strHas flags 'u' || strHas flags 'v'
  let newFlags := if strHas flags 'y' then flags else flags.push 0x79
  -- 8.
  let splitter ← construct C #[.obj rx, .str newFlags]
  let .obj sp := splitter | throwType "RegExp species constructor returned a non-object"
  -- 9-10.
  let A ← arrayCreate 0
  -- 11-12.
  let limit := arg args 1
  let lim ← if limit.isUndefined then pure 4294967295 else toUint32 limit
  -- 13.
  if lim == 0 then return .obj A
  -- 14-15.
  let size := S.length
  if size == 0 then
    let z ← regexpExec sp S
    if !(match z with | .null => true | _ => false) then return .obj A
    createDataPropertyOrThrow A (PropKey.ofNat 0) (.str S)
    return .obj A
  -- 16-19.
  let r ← M.repeatFrom (0, 0, 0) fun (p, q, lengthA) => do
    M.tick
    if q ≥ size then return .inr (Sum.inl (p, lengthA))
    setProp sp (.str kLastIndex) (numV q)
    let z ← regexpExec sp S
    match z with
    | .obj zo =>
      let e ← toLen (← getProp sp (.str kLastIndex))
      let e := min e size
      if e == p then return .inl (p, advanceStringIndex S q unicodeMatching, lengthA)
      createDataPropertyOrThrow A (PropKey.ofNat lengthA) (.str (S.slice p q))
      let lengthA := lengthA + 1
      if lengthA == lim then return .inr (Sum.inr ())
      let p := e
      let numberOfCaptures ← lengthOf zo
      let numberOfCaptures := numberOfCaptures - 1
      let r ← M.repeatFrom (1, lengthA) fun (i, lengthA) => do
        if i > numberOfCaptures then return .inr (some lengthA)
        let nextCapture ← getProp zo (PropKey.ofNat i)
        createDataPropertyOrThrow A (PropKey.ofNat lengthA) nextCapture
        let lengthA := lengthA + 1
        if lengthA == lim then return .inr none
        return .inl (i + 1, lengthA)
      match r with
      | none => return .inr (Sum.inr ())
      | some lengthA => return .inl (p, p, lengthA)
    | _ => return .inl (p, advanceStringIndex S q unicodeMatching, lengthA)
  match r with
  | .inr () => pure (.obj A)
  | .inl (p, lengthA) =>
    -- 20-22.
    createDataPropertyOrThrow A (PropKey.ofNat lengthA) (.str (S.slice p size))
    pure (.obj A)

/-- RegExp.prototype.compile spec: https://tc39.es/ecma262/#sec-regexp.prototype.compile -/
def regexpProtoCompile : BuiltinFn := fun _ thisV args _ => do
  -- 1-2.
  let .obj O := thisV | throwType "RegExp.prototype.compile called on incompatible receiver"
  if (← regexpParts? thisV).isNone then throwType "RegExp.prototype.compile called on incompatible receiver"
  let pattern := arg args 0
  let flags := arg args 1
  -- 3-4.
  let (P, F) ← match ← regexpParts? pattern with
    | some (src, fl, _) =>
      if !flags.isUndefined then throwType "Cannot supply flags when constructing one RegExp from another"
      pure (Value.str src, Value.str fl)
    | none => pure (pattern, flags)
  -- 5.
  regexpInitialize O P F

def regexpDefs : Array BuiltinDef := #[
  ⟨"RegExp", regexpCtor⟩, ⟨"RegExp.escape", regexpEscape⟩,
  ⟨"RegExp.prototype.exec", regexpProtoExec⟩, ⟨"RegExp.prototype.test", regexpProtoTest⟩,
  ⟨"RegExp.prototype.toString", regexpProtoToString⟩,
  ⟨"RegExp.prototype.compile", regexpProtoCompile⟩,
  ⟨"get RegExp.prototype.flags", regexpProtoFlags⟩,
  ⟨"get RegExp.prototype.source", regexpProtoSource⟩,
  ⟨"get RegExp.prototype.hasIndices", regexpHasFlag 'd'⟩,
  ⟨"get RegExp.prototype.global", regexpHasFlag 'g'⟩,
  ⟨"get RegExp.prototype.ignoreCase", regexpHasFlag 'i'⟩,
  ⟨"get RegExp.prototype.multiline", regexpHasFlag 'm'⟩,
  ⟨"get RegExp.prototype.dotAll", regexpHasFlag 's'⟩,
  ⟨"get RegExp.prototype.unicode", regexpHasFlag 'u'⟩,
  ⟨"get RegExp.prototype.unicodeSets", regexpHasFlag 'v'⟩,
  ⟨"get RegExp.prototype.sticky", regexpHasFlag 'y'⟩,
  ⟨"RegExp.prototype[Symbol.match]", regexpProtoMatch⟩,
  ⟨"RegExp.prototype[Symbol.matchAll]", regexpProtoMatchAll⟩,
  ⟨"RegExp.prototype[Symbol.replace]", regexpProtoReplace⟩,
  ⟨"RegExp.prototype[Symbol.search]", regexpProtoSearch⟩,
  ⟨"RegExp.prototype[Symbol.split]", regexpProtoSplit⟩,
  ⟨"%RegExpStringIteratorPrototype%.next", regexpStringIteratorNext⟩]

def regexpSetup : M Unit := do
  let rp ← newIntrinsicObject "%RegExp.prototype%"
  let (rc, _) ← defConstructor "RegExp" 2 "RegExp" rp
  defSpecies rc
  let _ ← defMethod rc (.str "escape") "RegExp.escape" 1
  defMethods rp "RegExp.prototype" [("exec", 1), ("test", 1), ("toString", 0), ("compile", 2)]
  for nm in ["flags", "source", "hasIndices", "global", "ignoreCase", "multiline", "dotAll",
      "unicode", "unicodeSets", "sticky"] do
    defGetter rp (.str (JSStr.ofString nm)) s!"get RegExp.prototype.{nm}"
  for (sym, nm, len) in [(WK.match, "match", 1), (WK.matchAll, "matchAll", 1),
      (WK.replace, "replace", 2), (WK.search, "search", 1), (WK.split, "split", 2)] do
    let _ ← defMethod rp (.sym sym) s!"RegExp.prototype[Symbol.{nm}]" len
  -- %RegExpStringIteratorPrototype%
  let ip ← intrinsic "%Iterator.prototype%"
  let rsip ← newIntrinsicObject "%RegExpStringIteratorPrototype%" (some ip)
  let _ ← defMethod rsip (.str kNext) "%RegExpStringIteratorPrototype%.next" 0
  defTag rsip "RegExp String Iterator"

end ES.Builtins.Text
