import ES.AST
import ES.Unicode.Ident
import Std.Data.HashMap

/-!
# ECMAScript lexical grammar

spec: https://tc39.es/ecma262/#sec-ecmascript-language-lexical-grammar

The lexer is driven by the parser: `lex` scans one token at a byte position of the UTF-8 source
with the InputElementDiv goal; where the syntactic grammar allows a RegularExpressionLiteral or a
TemplateMiddle/TemplateTail instead (InputElementRegExp, InputElementTemplateTail), the parser
re-scans the `/`, `/=` or `}` token with `lexRegex` / `lexTemplate`. Tokens carry what the
parser's early errors need (legacy octal literals and escapes, escaped identifiers, invalid
template escapes); whether those are errors depends on strictness, which only the parser knows.
-/

namespace ES.Lex

open ES (F64)

/-! ## Character classes -/

namespace Unicode

/-- Decodes a range table (`a-b,c,…` in hex) into sorted `(lo, hi)` pairs. -/
def decodeRanges (s : String) : Array (Nat × Nat) :=
  (s.splitOn ",").foldl (init := #[]) fun acc item =>
    let hex (t : String) : Nat := t.foldl (fun n c =>
      n * 16 + (if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87)) 0
    match item.splitOn "-" with
    | [a, b] => acc.push (hex a, hex b)
    | [a] => if a.isEmpty then acc else acc.push (hex a, hex a)
    | _ => acc

def idStartTable : Array (Nat × Nat) := decodeRanges ES.Unicode.idStartEnc
def idContinueTable : Array (Nat × Nat) := decodeRanges ES.Unicode.idContinueEnc

/-- Binary search for `c` in sorted disjoint ranges (at most 64 halvings: tables are far smaller
than 2^64). -/
def inRanges (t : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := t.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b) := t[mid]!
    if c < a then hi := mid
    else if c > b then lo := mid + 1
    else return true
  return false

end Unicode

/-- IdentifierStartChar: UnicodeIDStart, `$`, `_`.
spec: https://tc39.es/ecma262/#prod-IdentifierStartChar -/
@[inline] def isIdStart (c : Nat) : Bool :=
  if c < 128 then (c ≥ 97 && c ≤ 122) || (c ≥ 65 && c ≤ 90) || c == 36 || c == 95
  else Unicode.inRanges Unicode.idStartTable c

/-- IdentifierPartChar: UnicodeIDContinue, `$`, ZWNJ, ZWJ.
spec: https://tc39.es/ecma262/#prod-IdentifierPartChar -/
@[inline] def isIdPart (c : Nat) : Bool :=
  if c < 128 then (c ≥ 97 && c ≤ 122) || (c ≥ 65 && c ≤ 90) || (c ≥ 48 && c ≤ 57) || c == 36 || c == 95
  else c == 0x200C || c == 0x200D || Unicode.inRanges Unicode.idContinueTable c

/-- LineTerminator. spec: https://tc39.es/ecma262/#sec-line-terminators -/
@[inline] def isLineTerm (c : Nat) : Bool := c == 10 || c == 13 || c == 0x2028 || c == 0x2029

/-- WhiteSpace (TAB, VT, FF, ZWNBSP, and the Zs category).
spec: https://tc39.es/ecma262/#sec-white-space -/
@[inline] def isWhiteSpace (c : Nat) : Bool :=
  c == 9 || c == 11 || c == 12 || c == 32 || c == 0xA0 || c == 0xFEFF ||
  (c ≥ 0x1680 && (c == 0x1680 || (c ≥ 0x2000 && c ≤ 0x200A) || c == 0x202F || c == 0x205F || c == 0x3000))

@[inline] def isDigit (c : Nat) : Bool := c ≥ 48 && c ≤ 57
@[inline] def hexVal (c : Nat) : Option Nat :=
  if c ≥ 48 && c ≤ 57 then some (c - 48)
  else if c ≥ 97 && c ≤ 102 then some (c - 87)
  else if c ≥ 65 && c ≤ 70 then some (c - 55)
  else none

/-! ## Tokens -/

/-- Token kinds: the punctuators, and the classes of other tokens. -/
inductive T where
  | eof | name | priv | num | bigint | str | tmpl | regex
  | lbrace | rbrace | lparen | rparen | lbracket | rbracket
  | dot | ellipsis | semi | comma | lt | gt | le | ge | eq2 | ne | eq3 | ne3
  | plus | minus | star | slash | percent | star2 | inc | dec
  | shl | sar | shr | amp | pipe | caret | bang | tilde | and2 | or2 | nullish
  | question | qdot | colon | assign | arrow | at
  | plusEq | minusEq | starEq | slashEq | percentEq | star2Eq
  | shlEq | sarEq | shrEq | ampEq | pipeEq | caretEq | and2Eq | or2Eq | nullishEq
  deriving BEq, Inhabited, Repr

/-- Reserved words and the contextual words the parser asks about (`.none` for other names). -/
inductive Kw where
  | none
  | kAwait | kBreak | kCase | kCatch | kClass | kConst | kContinue | kDebugger | kDefault
  | kDelete | kDo | kElse | kEnum | kExport | kExtends | kFalse | kFinally | kFor | kFunction
  | kIf | kImport | kIn | kInstanceof | kNew | kNull | kReturn | kSuper | kSwitch | kThis
  | kThrow | kTrue | kTry | kTypeof | kVar | kVoid | kWhile | kWith | kYield
  | kLet | kStatic | kImplements | kInterface | kPackage | kPrivate | kProtected | kPublic
  | kAs | kAsync | kFrom | kGet | kSet | kOf | kTarget | kMeta | kUsing | kAccessor
  | kArguments | kEval | kConstructor | kPrototype | kSource | kDefer | kProto
  deriving BEq, Inhabited, Repr

def kwList : List (String × Kw) := [
  ("await", .kAwait), ("break", .kBreak), ("case", .kCase), ("catch", .kCatch),
  ("class", .kClass), ("const", .kConst), ("continue", .kContinue), ("debugger", .kDebugger),
  ("default", .kDefault), ("delete", .kDelete), ("do", .kDo), ("else", .kElse),
  ("enum", .kEnum), ("export", .kExport), ("extends", .kExtends), ("false", .kFalse),
  ("finally", .kFinally), ("for", .kFor), ("function", .kFunction), ("if", .kIf),
  ("import", .kImport), ("in", .kIn), ("instanceof", .kInstanceof), ("new", .kNew),
  ("null", .kNull), ("return", .kReturn), ("super", .kSuper), ("switch", .kSwitch),
  ("this", .kThis), ("throw", .kThrow), ("true", .kTrue), ("try", .kTry),
  ("typeof", .kTypeof), ("var", .kVar), ("void", .kVoid), ("while", .kWhile),
  ("with", .kWith), ("yield", .kYield), ("let", .kLet), ("static", .kStatic),
  ("implements", .kImplements), ("interface", .kInterface), ("package", .kPackage),
  ("private", .kPrivate), ("protected", .kProtected), ("public", .kPublic),
  ("as", .kAs), ("async", .kAsync), ("from", .kFrom), ("get", .kGet), ("set", .kSet),
  ("of", .kOf), ("target", .kTarget), ("meta", .kMeta), ("using", .kUsing),
  ("accessor", .kAccessor), ("arguments", .kArguments), ("eval", .kEval),
  ("constructor", .kConstructor), ("prototype", .kPrototype), ("source", .kSource),
  ("defer", .kDefer), ("__proto__", .kProto)]

def kwTable : Std.HashMap JSStr Kw :=
  kwList.foldl (fun m (s, k) => m.insert (JSStr.ofString s) k) {}

/-- ReservedWord (always, outside strict-only and contextual cases).
spec: https://tc39.es/ecma262/#prod-ReservedWord -/
def Kw.isReserved : Kw → Bool
  | .kBreak | .kCase | .kCatch | .kClass | .kConst | .kContinue | .kDebugger | .kDefault
  | .kDelete | .kDo | .kElse | .kEnum | .kExport | .kExtends | .kFalse | .kFinally | .kFor
  | .kFunction | .kIf | .kImport | .kIn | .kInstanceof | .kNew | .kNull | .kReturn | .kSuper
  | .kSwitch | .kThis | .kThrow | .kTrue | .kTry | .kTypeof | .kVar | .kVoid | .kWhile
  | .kWith => true
  | _ => false

/-- The words reserved in strict mode code only (besides `yield`).
spec: https://tc39.es/ecma262/#sec-identifiers-static-semantics-early-errors -/
def Kw.isStrictReserved : Kw → Bool
  | .kLet | .kStatic | .kImplements | .kInterface | .kPackage | .kPrivate | .kProtected
  | .kPublic | .kYield => true
  | _ => false

structure Token where
  kind : T := .eof
  start : Nat := 0
  stop : Nat := 0
  /-- A LineTerminator (or a multi-line comment containing one) precedes the token. -/
  nl : Bool := false
  /-- Names: the StringValue (escapes decoded); strings: the SV; templates: the TV (cooked);
  regular expressions: the body; private names: without `#`. -/
  val : JSStr := JSStr.empty
  /-- Templates: the TRV (raw); regular expressions: the flags. -/
  raw : JSStr := JSStr.empty
  kw : Kw := .none
  /-- Names: contains a Unicode escape. -/
  escaped : Bool := false
  num : F64 := F64.zero
  big : Int := 0
  /-- Numbers: a LegacyOctalIntegerLiteral or NonOctalDecimalIntegerLiteral; strings: a
  LegacyOctalEscapeSequence or NonOctalDecimalEscapeSequence — as position + 1 (0: none). -/
  octal : Nat := 0
  /-- Templates: the cooked value is undefined (a NotEscapeSequence). -/
  badEscape : Bool := false
  /-- Templates: ends with the backtick (NoSubstitutionTemplate / TemplateTail). -/
  tail : Bool := false
  deriving Inhabited

abbrev LexM := Except SyntaxError

@[inline] def lexErr {α : Type} (msg : String) (pos : Nat) : LexM α := .error { msg, pos }

/-! ## Source access -/

/-- The code point starting at byte `i` of valid UTF-8 `src` and its length in bytes (0, 0 at
the end). -/
@[inline] def decodeAt (src : ByteArray) (i : Nat) : Nat × Nat :=
  if i ≥ src.size then (0, 0) else
  let b0 := (src.get! i).toNat
  if b0 < 0x80 then (b0, 1)
  else if b0 < 0xE0 then (((b0 &&& 0x1F) <<< 6) ||| ((src.get! (i+1)).toNat &&& 0x3F), 2)
  else if b0 < 0xF0 then
    (((b0 &&& 0x0F) <<< 12) ||| (((src.get! (i+1)).toNat &&& 0x3F) <<< 6) |||
      ((src.get! (i+2)).toNat &&& 0x3F), 3)
  else
    (((b0 &&& 0x07) <<< 18) ||| (((src.get! (i+1)).toNat &&& 0x3F) <<< 12) |||
      (((src.get! (i+2)).toNat &&& 0x3F) <<< 6) ||| ((src.get! (i+3)).toNat &&& 0x3F), 4)

/-- The byte at `i` (0 past the end; source text bytes 0 are NUL characters, which no token
check below accepts where it matters). -/
@[inline] def byteAt (src : ByteArray) (i : Nat) : Nat :=
  if i < src.size then (src.get! i).toNat else 0

/-- Whether `i` is at the end (byte 0 can also be a NUL in the text). -/
@[inline] def atEnd (src : ByteArray) (i : Nat) : Bool := i ≥ src.size

/-- The UTF-16 encoding of source text `[a, b)`. -/
def sliceStr (src : ByteArray) (a b : Nat) : JSStr := Id.run do
  let mut out : JSStr := ⟨ByteArray.emptyWithCapacity (2 * (b - a))⟩
  let mut i := a
  for _ in [0:b - a] do
    if i ≥ b then break
    let (c, n) := decodeAt src i
    out := out.pushCodePoint c
    i := i + max n 1
  return out

/-! ## White space and comments -/

/-- Skips WhiteSpace, LineTerminators, and Comments (with Annex B's HTML-like comments in
scripts) from `pos`; returns the next token's start and whether a line terminator was crossed.
`lineStart`: the position is the start of the input (an HTMLCloseComment may start there).
Each iteration consumes at least one byte, so `src.size` iterations suffice.
spec: https://tc39.es/ecma262/#sec-comments
spec: https://tc39.es/ecma262/#sec-html-like-comments -/
def skipTrivia (src : ByteArray) (pos : Nat) (isModule : Bool) (lineStart : Bool) :
    LexM (Nat × Bool) := do
  let mut i := pos
  let mut nl := lineStart
  let mut sawNl := false
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let b := byteAt src i
    if b == 10 || b == 13 then i := i + 1; nl := true; sawNl := true
    else if b == 32 || b == 9 || b == 11 || b == 12 then i := i + 1
    else if b == 47 then -- '/'
      let b1 := byteAt src (i + 1)
      if b1 == 47 then i := skipLine src (i + 2)
      else if b1 == 42 then
        let (j, hadNl, closed) := skipBlock src (i + 2)
        if !closed then lexErr "unterminated comment" i
        i := j
        if hadNl then nl := true; sawNl := true
      else break
    else if b == 60 && !isModule && byteAt src (i+1) == 33 && byteAt src (i+2) == 45 &&
        byteAt src (i+3) == 45 then -- '<!--'
      i := skipLine src (i + 4)
    else if b == 45 && !isModule && nl && byteAt src (i+1) == 45 && byteAt src (i+2) == 62 then
      i := skipLine src (i + 3) -- '-->' at the start of a line
    else if b < 128 then break
    else
      let (c, n) := decodeAt src i
      if c == 0x2028 || c == 0x2029 then i := i + n; nl := true; sawNl := true
      else if isWhiteSpace c then i := i + n
      else break
  return (i, sawNl)
where
  /-- The end of a single-line comment: the next line terminator (not consumed). -/
  skipLine (src : ByteArray) (i : Nat) : Nat := Id.run do
    let mut j := i
    for _ in [0:src.size + 1] do
      if j ≥ src.size then break
      let b := byteAt src j
      if b == 10 || b == 13 then break
      if b == 0xE2 then
        let (c, _) := decodeAt src j
        if c == 0x2028 || c == 0x2029 then break
      j := j + 1
    return j
  /-- After `/*`: the end of the comment, whether it contains a line terminator, and whether
  it was closed. -/
  skipBlock (src : ByteArray) (i : Nat) : Nat × Bool × Bool := Id.run do
    let mut j := i
    let mut hadNl := false
    for _ in [0:src.size + 1] do
      if j ≥ src.size then return (j, hadNl, false)
      let b := byteAt src j
      if b == 42 && byteAt src (j+1) == 47 then return (j + 2, hadNl, true)
      if b == 10 || b == 13 then hadNl := true
      if b == 0xE2 then
        let (c, _) := decodeAt src j
        if c == 0x2028 || c == 0x2029 then hadNl := true
      j := j + 1
    return (j, hadNl, false)

/-! ## Identifiers -/

/-- `\u` escapes in identifiers: after the backslash at `i`, the code point and the next
position. spec: https://tc39.es/ecma262/#prod-UnicodeEscapeSequence -/
def scanUnicodeEscape (src : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run do
  if byteAt src i != 92 || byteAt src (i+1) != 117 then return none
  let j := i + 2
  if byteAt src j == 123 then -- '{'
    let mut v := 0
    let mut k := j + 1
    let mut digits := 0
    for _ in [0:src.size + 1] do
      match hexVal (byteAt src k) with
      | some d =>
        v := v * 16 + d; k := k + 1; digits := digits + 1
        if v > 0x10FFFF then return none
      | none => break
    if digits == 0 || byteAt src k != 125 then return none
    return some (v, k + 1)
  else
    let mut v := 0
    for t in [0:4] do
      match hexVal (byteAt src (j + t)) with
      | some d => v := v * 16 + d
      | none => return none
    return some (v, j + 4)

/-- IdentifierName from `i` (whose first character the caller checked can start one): the
StringValue, whether an escape occurred, and the end.
spec: https://tc39.es/ecma262/#sec-names-and-keywords -/
def scanIdentName (src : ByteArray) (i : Nat) : LexM (JSStr × Bool × Nat) := do
  let mut out : JSStr := JSStr.empty
  let mut j := i
  let mut escaped := false
  let mut first := true
  for _ in [0:src.size + 1] do
    let b := byteAt src j
    if j ≥ src.size then break
    if b < 128 && b != 92 then
      if (b ≥ 97 && b ≤ 122) || (b ≥ 65 && b ≤ 90) || b == 36 || b == 95 || (!first && isDigit b) then
        out := out.push b.toUInt16; j := j + 1
      else break
    else if b == 92 then
      match scanUnicodeEscape src j with
      | some (c, k) =>
        if (first && !isIdStart c) || (!first && !isIdPart c) then
          lexErr "invalid Unicode escape in identifier" j
        out := out.pushCodePoint c; j := k; escaped := true
      | none => lexErr "invalid Unicode escape in identifier" j
    else
      let (c, n) := decodeAt src j
      if (first && isIdStart c) || (!first && isIdPart c) then
        out := out.pushCodePoint c; j := j + n
      else break
    first := false
  return (out, escaped, j)

/-! ## Numeric literals -/

/-- Digits of `radix` from `i`, with NumericLiteralSeparators between digits when `sep`: the
value, the digit count, and the end. A separator not between two digits is an error.
spec: https://tc39.es/ecma262/#sec-literals-numeric-literals -/
def scanDigits (src : ByteArray) (i : Nat) (radix : Nat) (sep : Bool) : LexM (Nat × Nat × Nat) := do
  let mut v := 0
  let mut n := 0
  let mut j := i
  let mut lastSep := false
  for _ in [0:src.size + 1] do
    let b := byteAt src j
    if b == 95 && sep then
      if n == 0 || lastSep then lexErr "invalid numeric separator" j
      lastSep := true; j := j + 1
    else
      let d := match hexVal b with | some d => d | none => 99
      if d < radix then v := v * radix + d; n := n + 1; j := j + 1; lastSep := false
      else break
  if lastSep then lexErr "invalid numeric separator" (j - 1)
  return (v, n, j)

/-- The Number value of `m × 10^e` (RoundMVResult), exact; values far outside the finite range
are decided without building huge powers of ten. -/
def decimalValue (m : Nat) (digits : Nat) (e : Int) : F64 :=
  if m == 0 then F64.zero
  else if e + digits > 311 then .inf false
  else if e + digits < -330 then F64.zero
  else if e ≥ 0 then F64.ofRat false (m * 10 ^ e.toNat) 1
  else F64.ofRat false m (10 ^ (-e).toNat)

/-- The SourceCharacter after a NumericLiteral must not be an IdentifierStart or a digit.
spec: https://tc39.es/ecma262/#sec-literals-numeric-literals -/
def checkAfterNumber (src : ByteArray) (j : Nat) : LexM Unit := do
  if j ≥ src.size then return
  let (c, _) := decodeAt src j
  if isDigit c || isIdStart c || c == 92 then
    lexErr "identifier starts immediately after numeric literal" j

/-- NumericLiteral from `i` (a digit, or `.` followed by one).
spec: https://tc39.es/ecma262/#sec-literals-numeric-literals -/
def scanNumber (src : ByteArray) (i : Nat) : LexM Token := do
  let b0 := byteAt src i
  let b1 := byteAt src (i + 1)
  let tok : Token := { kind := .num, start := i }
  -- NonDecimalIntegerLiteral
  if b0 == 48 && (b1 == 120 || b1 == 88 || b1 == 111 || b1 == 79 || b1 == 98 || b1 == 66) then
    let radix := if b1 == 120 || b1 == 88 then 16 else if b1 == 111 || b1 == 79 then 8 else 2
    let (v, n, j) ← scanDigits src (i + 2) radix true
    if n == 0 then lexErr "missing digits in numeric literal" (i + 2)
    if byteAt src j == 110 then
      checkAfterNumber src (j + 1)
      return { tok with kind := .bigint, big := v, stop := j + 1 }
    checkAfterNumber src j
    return { tok with num := F64.ofRat false v 1, stop := j }
  -- LegacyOctalLikeDecimalIntegerLiteral / NonOctalDecimalIntegerLiteral (Annex B)
  if b0 == 48 && isDigit b1 then
    let (v8, n8, j8) ← scanDigits src (i + 1) 8 false
    let next := byteAt src j8
    if !isDigit next then
      if next == 95 then lexErr "invalid numeric separator" j8
      if next == 110 then lexErr "invalid BigInt literal" j8
      checkAfterNumber src j8
      let _ := n8
      return { tok with num := F64.ofRat false v8 1, stop := j8, octal := i + 1 }
    -- NonOctalDecimalIntegerLiteral: decimal digits, no separators
    let (vi, ni, ji) ← scanDigits src (i + 1) 10 false
    if byteAt src ji == 95 then lexErr "invalid numeric separator" ji
    if byteAt src ji == 110 then lexErr "invalid BigInt literal" ji
    let r ← fracExp src ji vi ni
    let (val, j) := r
    checkAfterNumber src j
    return { tok with num := val, stop := j, octal := i + 1 }
  if b0 == 48 && b1 == 95 then lexErr "invalid numeric separator" (i + 1)
  -- DecimalLiteral / DecimalBigIntegerLiteral
  let (vi, ni, ji) ← if b0 == 46 then pure (0, 0, i) else scanDigits src i 10 true
  if b0 != 46 && byteAt src ji == 110 then
    checkAfterNumber src (ji + 1)
    return { tok with kind := .bigint, big := vi, stop := ji + 1 }
  let (val, j) ← fracExp src ji vi ni
  checkAfterNumber src j
  return { tok with num := val, stop := j }
where
  /-- The optional `.digits` and ExponentPart after integer digits (value `vi`, `ni` digits). -/
  fracExp (src : ByteArray) (j : Nat) (vi ni : Nat) : LexM (F64 × Nat) := do
    let mut m := vi
    let mut digits := ni
    let mut scale : Int := 0
    let mut j := j
    if byteAt src j == 46 then
      if byteAt src (j + 1) == 95 then lexErr "invalid numeric separator" (j + 1)
      let (vf, nf, jf) ← scanDigits src (j + 1) 10 true
      if ni == 0 && nf == 0 then lexErr "invalid number" j
      m := m * 10 ^ nf + vf; digits := digits + nf; scale := -(nf : Int); j := jf
    let e := byteAt src j
    if e == 101 || e == 69 then
      let s := byteAt src (j + 1)
      let (neg, k) := if s == 43 then (false, j + 2) else if s == 45 then (true, j + 2) else (false, j + 1)
      if byteAt src k == 95 then lexErr "invalid numeric separator" k
      let (ve, ne, je) ← scanDigits src k 10 true
      if ne == 0 then lexErr "missing exponent" k
      -- (huge exponents saturate: the value is then 0 or infinite anyway)
      let ve := min ve 100000
      scale := scale + (if neg then -(ve : Int) else ve)
      j := je
    -- (a lower bound on the number of decimal digits of m, at most one below it)
    let _ := digits
    let sig := if m == 0 then 0 else (Nat.log2 m * 30103) / 100000 + 1
    return (decimalValue m sig scale, j)

/-! ## String literals and escapes -/

/-- The result of one escape sequence: the code point appended (none: line continuation),
the end, whether it is a legacy octal / non-octal-decimal escape, and whether it is invalid
(a NotEscapeSequence in templates). -/
structure Esc where
  cp : Option Nat
  stop : Nat
  octal : Bool := false
  bad : Bool := false

/-- The EscapeSequence (or LineContinuation) after the backslash at `i`.
spec: https://tc39.es/ecma262/#prod-EscapeSequence
spec: https://tc39.es/ecma262/#sec-additional-syntax-string-literals (legacy octal escapes) -/
def scanEscape (src : ByteArray) (i : Nat) (template : Bool) : Esc :=
  let j := i + 1
  let (c, n) := decodeAt src j
  if c == 13 then { cp := none, stop := if byteAt src (j + 1) == 10 then j + 2 else j + 1 }
  else if c == 10 || c == 0x2028 || c == 0x2029 then { cp := none, stop := j + n }
  else if c == 110 then { cp := some 10, stop := j + 1 }
  else if c == 116 then { cp := some 9, stop := j + 1 }
  else if c == 114 then { cp := some 13, stop := j + 1 }
  else if c == 98 then { cp := some 8, stop := j + 1 }
  else if c == 102 then { cp := some 12, stop := j + 1 }
  else if c == 118 then { cp := some 11, stop := j + 1 }
  else if c == 48 && !isDigit (byteAt src (j + 1)) then { cp := some 0, stop := j + 1 }
  else if c ≥ 48 && c ≤ 55 then
    if template then { cp := none, stop := j + 1, bad := true } else
    -- LegacyOctalEscapeSequence
    let d1 := byteAt src (j + 1)
    let d2 := byteAt src (j + 2)
    if c ≤ 51 && d1 ≥ 48 && d1 ≤ 55 && d2 ≥ 48 && d2 ≤ 55 then
      { cp := some ((c - 48) * 64 + (d1 - 48) * 8 + (d2 - 48)), stop := j + 3, octal := true }
    else if d1 ≥ 48 && d1 ≤ 55 then
      { cp := some ((c - 48) * 8 + (d1 - 48)), stop := j + 2, octal := true }
    else { cp := some (c - 48), stop := j + 1, octal := true }
  else if c == 56 || c == 57 then
    if template then { cp := none, stop := j + 1, bad := true }
    else { cp := some c, stop := j + 1, octal := true }
  else if c == 120 then
    match hexVal (byteAt src (j + 1)), hexVal (byteAt src (j + 2)) with
    | some a, some b => { cp := some (a * 16 + b), stop := j + 3 }
    | _, _ => { cp := none, stop := j + 1, bad := true }
  else if c == 117 then
    match scanUnicodeEscape src i with
    | some (v, k) => { cp := some v, stop := k }
    | none => { cp := none, stop := j + 1, bad := true }
  else { cp := some c, stop := j + n }

/-- StringLiteral from the quote at `i`.
spec: https://tc39.es/ecma262/#sec-literals-string-literals -/
def scanString (src : ByteArray) (i : Nat) : LexM Token := do
  let q := byteAt src i
  let mut out : JSStr := JSStr.empty
  let mut j := i + 1
  let mut octal := 0
  for _ in [0:src.size + 1] do
    if j ≥ src.size then lexErr "unterminated string literal" i
    let b := byteAt src j
    if b == q then
      return { kind := .str, start := i, stop := j + 1, val := out, octal }
    if b == 92 then
      let e := scanEscape src j false
      if e.bad then lexErr "invalid escape sequence" j
      if e.octal && octal == 0 then octal := j + 1
      match e.cp with
      | some c => out := out.pushCodePoint c
      | none => pure ()
      j := e.stop
    else if b == 10 || b == 13 then lexErr "unterminated string literal" i
    else if b < 128 then out := out.push b.toUInt16; j := j + 1
    else
      let (c, n) := decodeAt src j
      out := out.pushCodePoint c; j := j + n
  lexErr "unterminated string literal" i

/-- A template's characters after the "`" or "}" at `i`, up to and including "`" or "${":
cooked (TV) and raw (TRV) values.
spec: https://tc39.es/ecma262/#sec-template-literal-lexical-components -/
def lexTemplate (src : ByteArray) (i : Nat) : LexM Token := do
  let mut cooked : JSStr := JSStr.empty
  let mut raw : JSStr := JSStr.empty
  let mut bad := false
  let mut j := i + 1
  for _ in [0:src.size + 1] do
    if j ≥ src.size then lexErr "unterminated template literal" i
    let b := byteAt src j
    if b == 96 then
      return { kind := .tmpl, start := i, stop := j + 1, val := cooked, raw, badEscape := bad, tail := true }
    if b == 36 && byteAt src (j + 1) == 123 then
      return { kind := .tmpl, start := i, stop := j + 2, val := cooked, raw, badEscape := bad, tail := false }
    if b == 92 then
      let e := scanEscape src j true
      if e.bad then bad := true
      match e.cp with
      | some c => cooked := cooked.pushCodePoint c
      | none => pure ()
      -- raw: the source text, line terminator sequences normalized
      let mut k := j
      for _ in [0:e.stop - j] do
        if k ≥ e.stop then break
        let bk := byteAt src k
        if bk == 13 then
          raw := raw.push 10
          k := if byteAt src (k + 1) == 10 && k + 1 < e.stop then k + 2 else k + 1
        else
          let (c, n) := decodeAt src k
          raw := raw.pushCodePoint c; k := k + max n 1
      j := e.stop
    else if b == 13 then
      cooked := cooked.push 10; raw := raw.push 10
      j := if byteAt src (j + 1) == 10 then j + 2 else j + 1
    else if b < 128 then
      cooked := cooked.push b.toUInt16; raw := raw.push b.toUInt16; j := j + 1
    else
      let (c, n) := decodeAt src j
      cooked := cooked.pushCodePoint c; raw := raw.pushCodePoint c; j := j + n
  lexErr "unterminated template literal" i

/-- RegularExpressionLiteral from the `/` at `i`: body and flags (validated by the parser via
`Regex.compile`).
spec: https://tc39.es/ecma262/#sec-literals-regular-expression-literals -/
def lexRegex (src : ByteArray) (i : Nat) : LexM Token := do
  let mut j := i + 1
  let mut inClass := false
  let mut closed := false
  for _ in [0:src.size + 1] do
    if j ≥ src.size then break
    let (c, n) := decodeAt src j
    if isLineTerm c then break
    if c == 92 then
      let (c2, n2) := decodeAt src (j + 1)
      if j + 1 ≥ src.size || isLineTerm c2 then break
      j := j + 1 + n2
    else if c == 91 then inClass := true; j := j + 1
    else if c == 93 then inClass := false; j := j + 1
    else if c == 47 && !inClass then closed := true; break
    else j := j + n
  if !closed then lexErr "unterminated regular expression" i
  let body := sliceStr src (i + 1) j
  let fstart := j + 1
  let mut k := fstart
  for _ in [0:src.size + 1] do
    if k ≥ src.size then break
    let (c, n) := decodeAt src k
    if c == 92 then lexErr "invalid regular expression flags" k
    if isIdPart c then k := k + n else break
  return { kind := .regex, start := i, stop := k, val := body, raw := sliceStr src fstart k }

/-! ## Tokens -/

@[inline] def punct (k : T) (i n : Nat) : LexM Token := pure { kind := k, start := i, stop := i + n }

/-- The token starting at `i` (after trivia) with the InputElementDiv goal.
spec: https://tc39.es/ecma262/#sec-ecmascript-language-lexical-grammar -/
def lexAt (src : ByteArray) (i : Nat) : LexM Token := do
  if i ≥ src.size then return { kind := .eof, start := src.size, stop := src.size }
  let b := byteAt src i
  let b1 := byteAt src (i + 1)
  let b2 := byteAt src (i + 2)
  let b3 := byteAt src (i + 3)
  if (b ≥ 97 && b ≤ 122) || (b ≥ 65 && b ≤ 90) || b == 36 || b == 95 || b == 92 || b ≥ 128 then
    if b ≥ 128 then
      let (c, _) := decodeAt src i
      if !isIdStart c then lexErr s!"unexpected character U+{String.ofList (Nat.toDigits 16 c)}" i
    let (name, esc, j) ← scanIdentName src i
    if j == i then lexErr "unexpected character" i
    let kw := kwTable.getD name .none
    return { kind := .name, start := i, stop := j, val := name, escaped := esc, kw }
  if isDigit b || (b == 46 && isDigit b1) then return ← scanNumber src i
  match b with
  | 34 | 39 => scanString src i
  | 96 => lexTemplate src i
  | 35 => -- '#'
    let (name, esc, j) ← scanIdentName src (i + 1)
    if j == i + 1 then lexErr "invalid private name" i
    return { kind := .priv, start := i, stop := j, val := name, escaped := esc }
  | 123 => punct .lbrace i 1
  | 125 => punct .rbrace i 1
  | 40 => punct .lparen i 1
  | 41 => punct .rparen i 1
  | 91 => punct .lbracket i 1
  | 93 => punct .rbracket i 1
  | 59 => punct .semi i 1
  | 44 => punct .comma i 1
  | 126 => punct .tilde i 1
  | 58 => punct .colon i 1
  | 64 => punct .at i 1
  | 46 => if b1 == 46 && b2 == 46 then punct .ellipsis i 3 else punct .dot i 1
  | 63 => -- '?'
    if b1 == 63 then (if b2 == 61 then punct .nullishEq i 3 else punct .nullish i 2)
    else if b1 == 46 && !isDigit b2 then punct .qdot i 2
    else punct .question i 1
  | 60 => -- '<'
    if b1 == 60 then (if b2 == 61 then punct .shlEq i 3 else punct .shl i 2)
    else if b1 == 61 then punct .le i 2 else punct .lt i 1
  | 62 => -- '>'
    if b1 == 62 then
      if b2 == 62 then (if b3 == 61 then punct .shrEq i 4 else punct .shr i 3)
      else if b2 == 61 then punct .sarEq i 3 else punct .sar i 2
    else if b1 == 61 then punct .ge i 2 else punct .gt i 1
  | 61 => -- '='
    if b1 == 61 then (if b2 == 61 then punct .eq3 i 3 else punct .eq2 i 2)
    else if b1 == 62 then punct .arrow i 2 else punct .assign i 1
  | 33 => if b1 == 61 then (if b2 == 61 then punct .ne3 i 3 else punct .ne i 2) else punct .bang i 1
  | 43 => if b1 == 43 then punct .inc i 2 else if b1 == 61 then punct .plusEq i 2 else punct .plus i 1
  | 45 => if b1 == 45 then punct .dec i 2 else if b1 == 61 then punct .minusEq i 2 else punct .minus i 1
  | 42 =>
    if b1 == 42 then (if b2 == 61 then punct .star2Eq i 3 else punct .star2 i 2)
    else if b1 == 61 then punct .starEq i 2 else punct .star i 1
  | 47 => if b1 == 61 then punct .slashEq i 2 else punct .slash i 1
  | 37 => if b1 == 61 then punct .percentEq i 2 else punct .percent i 1
  | 38 =>
    if b1 == 38 then (if b2 == 61 then punct .and2Eq i 3 else punct .and2 i 2)
    else if b1 == 61 then punct .ampEq i 2 else punct .amp i 1
  | 124 =>
    if b1 == 124 then (if b2 == 61 then punct .or2Eq i 3 else punct .or2 i 2)
    else if b1 == 61 then punct .pipeEq i 2 else punct .pipe i 1
  | 94 => if b1 == 61 then punct .caretEq i 2 else punct .caret i 1
  | _ => lexErr "unexpected character" i

/-- The next token after `pos`: trivia skipped, `nl` set. `lineStart`: `pos` is the start of
the input (or right after the hashbang). -/
def lex (src : ByteArray) (pos : Nat) (isModule : Bool) (lineStart : Bool := false) : LexM Token := do
  let (i, nl) ← skipTrivia src pos isModule lineStart
  let t ← lexAt src i
  return { t with nl }

/-- The end of a HashbangComment at the start of the source (0 if there is none).
spec: https://tc39.es/ecma262/#sec-hashbang -/
def skipHashbang (src : ByteArray) : Nat :=
  if byteAt src 0 == 35 && byteAt src 1 == 33 then skipTrivia.skipLine src 2 else 0

end ES.Lex
