import ES.Str
import ES.Regex.Unicode

/-!
# RegExp patterns: syntax trees, the parser, and early errors

The pattern grammar of 22.2.1 with its parameters [UnicodeMode], [UnicodeSetsMode],
[NamedCaptureGroups], and Annex B.1.2's grammar for BMP patterns (no `u`/`v` flag). The parser
works on the pattern's characters (code points for Unicode patterns, code units otherwise: the
patternText of RegExpInitialize step 10) and builds an arena of `Node`s. The characters sets of
atoms are computed while parsing, with the RegExp Record in effect there (modifiers included):
CompileToCharSet, MaybeSimpleCaseFolding, CharacterComplement.

spec: https://tc39.es/ecma262/#sec-patterns
spec: https://tc39.es/ecma262/#sec-regular-expressions-patterns
-/

namespace ES.Regex

/-- A pattern syntax node; children are ids in the arena (`Pattern.nodes`). Characters sets are
those of CompileToCharSet (not yet canonicalized); `ic`/`ml`/`da` are the RegExp Record's
[[IgnoreCase]]/[[Multiline]]/[[DotAll]] in effect at the node (after modifiers). -/
inductive Node where
  | empty
  /-- A single character (PatternCharacter, CharacterEscape). -/
  | char (c : Nat) (ic : Bool)
  /-- A CharacterSetMatcher: `invert` for BMP/`u` patterns' `[^…]`. -/
  | set (s : CharSet) (invert : Bool) (ic : Bool)
  | seq (kids : Array Nat)
  | alt (kids : Array Nat)
  /-- A capturing group with its number (≥ 1). -/
  | group (idx : Nat) (body : Nat)
  | look (behind neg : Bool) (body : Nat)
  /-- `parenIndex`/`parenCount` as in Term :: Atom Quantifier. `max = none` is +∞. -/
  | quant (body : Nat) (min : Nat) (max : Option Nat) (greedy : Bool) (parenIndex parenCount : Nat)
  | bol (ml : Bool)
  | eol (ml : Bool)
  | wordB (neg : Bool) (ic : Bool)
  | backref (groups : Array Nat) (ic : Bool)
  /-- `\k<name>`, resolved to the groups with that name after parsing. -/
  | namedRef (name : JSStr) (ic : Bool)
  deriving Inhabited

/-- A parsed pattern. -/
structure Pattern where
  nodes : Array Node
  root : Nat
  groupCount : Nat
  /-- Index 0 unused. -/
  groupNames : Array (Option JSStr)
  deriving Inhabited

/-! ## Character sets of the RegExp Record -/

/-- The flags of a RegExp Record that character sets depend on. -/
structure Rer where
  ic : Bool
  ml : Bool
  da : Bool
  u : Bool
  v : Bool

namespace Rer
@[inline] def eitherUnicode (r : Rer) : Bool := r.u || r.v
@[inline] def maxChar (r : Rer) : Nat := if r.eitherUnicode then 0x10FFFF else 0xFFFF
end Rer

/-- AllCharacters(rer).
spec: https://tc39.es/ecma262/#sec-allcharacters -/
def allCharacters (r : Rer) : CharSet :=
  -- 1.
  if r.v && r.ic then scfKeys.complement 0x10FFFF
  -- 2.
  else if r.eitherUnicode then CharSet.range 0 0x10FFFF
  -- 3.
  else CharSet.range 0 0xFFFF

/-- CharacterComplement(rer, S).
spec: https://tc39.es/ecma262/#sec-charactercomplement -/
def characterComplement (r : Rer) (s : CharSet) : CharSet := (allCharacters r).diff s

/-- The ASCII word characters. -/
def basicWordChars : CharSet := #[48, 57, 65, 90, 95, 95, 97, 122]

/-- WordCharacters(rer).
spec: https://tc39.es/ecma262/#sec-wordcharacters -/
def wordCharacters (r : Rer) : CharSet :=
  -- 1.
  let basic := basicWordChars
  -- 2. (Canonicalize only maps non-ASCII to ASCII with either unicode flag and ignoreCase:
  -- scf's keys whose folding is a basic word character)
  if r.eitherUnicode && r.ic then
    let extra := Id.run do
      let mut out : Array Nat := #[]
      for i in [0:scfMap.size / 2] do
        let k := scfMap[2 * i]!
        if !basic.contains k && basic.contains scfMap[2 * i + 1]! then out := out.push k
      return out
    -- 4.
    basic.union (CharSet.ofChars extra)
  else basic

/-- WhiteSpace and LineTerminator (`\s`): TAB, LF, VT, FF, CR, SP, NBSP, ZWNBSP, the other Zs
characters (Unicode 17: U+1680, U+2000–U+200A, U+202F, U+205F, U+3000), LS, PS.
spec: https://tc39.es/ecma262/#sec-white-space -/
def whiteSpaceChars : CharSet :=
  #[9, 13, 32, 32, 0xA0, 0xA0, 0x1680, 0x1680, 0x2000, 0x200A, 0x2028, 0x2029, 0x202F, 0x202F,
    0x205F, 0x205F, 0x3000, 0x3000, 0xFEFF, 0xFEFF]

/-- LineTerminator: LF, CR, LS, PS. -/
def lineTerminators : CharSet := #[10, 10, 13, 13, 0x2028, 0x2029]

@[inline] def isLineTerminator (c : Nat) : Bool := c == 10 || c == 13 || c == 0x2028 || c == 0x2029

/-! ## Class sets with strings (UnicodeSets mode) -/

/-- Lexicographic order on code point sequences. -/
def seqLt (a b : Array Nat) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

/-- Sorted, without duplicates. -/
def sortSeqs (xs : Array (Array Nat)) : Array (Array Nat) :=
  let s := xs.qsort seqLt
  s.foldl (fun acc x => if acc.size > 0 && acc[acc.size - 1]! == x then acc else acc.push x) #[]

/-- A CharSet of UnicodeSets mode: single characters, and the other strings (length ≠ 1,
sorted, unique). -/
structure CSet where
  chars : CharSet := #[]
  strs : Array (Array Nat) := #[]
  deriving Inhabited

namespace CSet
def ofChars (s : CharSet) : CSet := { chars := s }
/-- Adds strings (length-1 ones become characters). -/
def ofSeqs (xs : Array (Array Nat)) : CSet :=
  let singles := (xs.filter (·.size == 1)).map (·[0]!)
  { chars := CharSet.ofChars singles, strs := sortSeqs (xs.filter (·.size != 1)) }
def union (a b : CSet) : CSet := { chars := a.chars.union b.chars, strs := sortSeqs (a.strs ++ b.strs) }
def inter (a b : CSet) : CSet := { chars := a.chars.inter b.chars, strs := a.strs.filter (b.strs.contains ·) }
def diff (a b : CSet) : CSet := { chars := a.chars.diff b.chars, strs := a.strs.filter (!b.strs.contains ·) }
end CSet

/-- MaybeSimpleCaseFolding(rer, A) on single characters.
spec: https://tc39.es/ecma262/#sec-maybesimplecasefolding -/
def maybeScfChars (r : Rer) (s : CharSet) : CharSet :=
  -- 1.
  if !r.v || !r.ic then s
  -- 2-4. (scf's image of a set: canonImage with unicode Canonicalize)
  else canonImage true s

/-- MaybeSimpleCaseFolding(rer, A) on a set with strings. -/
def maybeScf (r : Rer) (s : CSet) : CSet :=
  if !r.v || !r.ic then s
  else { chars := maybeScfChars r s.chars, strs := sortSeqs (s.strs.map (·.map scf)) }

/-! ## The parser -/

/-- What the parser reads and never changes: the pattern's characters and the grammar's
parameters ([UnicodeMode] for `u` or `v`, [UnicodeSetsMode], [NamedCaptureGroups]). -/
structure PCtx where
  src : Array Nat
  u : Bool
  v : Bool
  named : Bool
  totalGroups : Nat

/-- The parser's state. Functions never keep the whole state across a change of it (that would
share its arrays and turn every push into a copy). -/
structure PState where
  pos : Nat := 0
  ic : Bool
  ml : Bool
  da : Bool
  nodes : Array Node := #[]
  groups : Nat := 0
  names : Array (Option JSStr) := #[none]
  /-- Each named group: its name, and its path of (disjunction id, alternative index). -/
  namePaths : Array (JSStr × Array (Nat × Nat)) := #[]
  path : Array (Nat × Nat) := #[]
  disjCount : Nat := 0
  refNames : Array JSStr := #[]

abbrev PM := ReaderT PCtx (StateT PState (Except String))

namespace P

@[inline] def ch (c : Char) : Nat := c.toNat

def rer : PM Rer := do
  let cx ← read
  let s ← get
  return { ic := s.ic, ml := s.ml, da := s.da, u := cx.u, v := cx.v }

@[inline] def getPos : PM Nat := do return (← get).pos
@[inline] def setPos (p : Nat) : PM Unit := modify fun s => { s with pos := p }

@[inline] def peekAt (k : Nat) : PM (Option Nat) := do
  let cx ← read
  let p ← getPos
  return cx.src[p + k]?

@[inline] def peek : PM (Option Nat) := peekAt 0

@[inline] def isAt (k : Nat) (c : Char) : PM Bool := do
  return (← peekAt k) == some c.toNat

@[inline] def adv (n : Nat := 1) : PM Unit := modify fun s => { s with pos := s.pos + n }

def eat (c : Char) : PM Bool := do
  if ← isAt 0 c then adv; return true
  return false

def push (n : Node) : PM Nat :=
  modifyGet fun s => (s.nodes.size, { s with nodes := s.nodes.push n })

def fail {α} (msg : String) : PM α := throw msg

@[inline] def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
@[inline] def isHex (c : Nat) : Bool := isDigit c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
@[inline] def hexVal (c : Nat) : Nat := if isDigit c then c - 48 else if c ≥ 97 then c - 87 else c - 55
@[inline] def isAsciiLetter (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
@[inline] def isSyntaxChar (c : Nat) : Bool :=
  c == ch '^' || c == ch '$' || c == ch '\\' || c == ch '.' || c == ch '*' || c == ch '+' ||
  c == ch '?' || c == ch '(' || c == ch ')' || c == ch '[' || c == ch ']' || c == ch '{' ||
  c == ch '}' || c == ch '|'

/-- Reads `k` hex digits at the current position (none consumed on failure). -/
def hexDigits (k : Nat) : PM (Option Nat) := do
  let s ← read
  let p0 ← getPos
  let mut v := 0
  for i in [0:k] do
    match s.src[p0 + i]? with
    | some c => if isHex c then v := v * 16 + hexVal c else return none
    | none => return none
  adv k
  return some v

/-- DecimalDigits[~Sep] at the current position (its MV), if any. -/
def decimalDigits : PM (Option Nat) := do
  let s ← read
  let p0 ← getPos
  let mut v := 0
  let mut n := 0
  for i in [0:s.src.size - p0] do
    match s.src[p0 + i]? with
    | some c => if isDigit c then v := v * 10 + (c - 48); n := n + 1 else break
    | none => break
  if n == 0 then return none
  adv n
  return some v

/-- RegExpUnicodeEscapeSequence after `\u` was consumed (`umode`: [+UnicodeMode]); `none` (nothing
consumed) when there is none.
spec: https://tc39.es/ecma262/#prod-RegExpUnicodeEscapeSequence -/
def unicodeEscape (umode : Bool) : PM (Option Nat) := do
  if umode && (← isAt 0 '{') then
    let save ← getPos
    adv
    let s ← read
    let p0 ← getPos
    let mut v := 0
    let mut n := 0
    for i in [0:s.src.size - p0] do
      match s.src[p0 + i]? with
      | some c =>
        if isHex c then
          v := v * 16 + hexVal c
          n := n + 1
          if v > 0x10FFFF then break
        else break
      | none => break
    if n == 0 || v > 0x10FFFF then setPos save; return none
    adv n
    if !(← eat '}') then setPos save; return none
    return some v
  match ← hexDigits 4 with
  | none => return none
  | some lead =>
    -- `u` HexLeadSurrogate `\u` HexTrailSurrogate ([+UnicodeMode]; the nearest-lead rule)
    if umode && 0xD800 ≤ lead && lead ≤ 0xDBFF && (← isAt 0 '\\') && (← isAt 1 'u') then
      let save ← getPos
      adv 2
      match ← hexDigits 4 with
      | some trail =>
        if 0xDC00 ≤ trail && trail ≤ 0xDFFF then
          return some ((lead - 0xD800) * 0x400 + (trail - 0xDC00) + 0x10000)
        setPos save
        return some lead
      | none => setPos save; return some lead
    return some lead

/-- RegExpIdentifierName in a GroupName (after `<`, through `>`); CapturingGroupName.
spec: https://tc39.es/ecma262/#sec-static-semantics-capturinggroupname -/
def groupName : PM JSStr := do
  let s0 ← read
  let mut out := JSStr.empty
  let mut first := true
  for _ in [0:s0.src.size + 1] do
    let s ← read
    let p0 ← getPos
    match s.src[p0]? with
    | none => fail "Invalid capture group name"
    | some c =>
      if c == ch '>' then
        if first then fail "Invalid capture group name"
        adv
        return out
      let mut cp := c
      if c == ch '\\' then
        adv
        if !(← eat 'u') then fail "Invalid Unicode escape in group name"
        match ← unicodeEscape true with
        | some v => cp := v
        | none => fail "Invalid Unicode escape in group name"
      else
        adv
        -- [~UnicodeMode] UnicodeLeadSurrogate UnicodeTrailSurrogate
        if !s.u && 0xD800 ≤ c && c ≤ 0xDBFF then
          match s.src[p0 + 1]? with
          | some t =>
            if 0xDC00 ≤ t && t ≤ 0xDFFF then
              adv
              cp := (c - 0xD800) * 0x400 + (t - 0xDC00) + 0x10000
          | none => pure ()
      let ok :=
        if first then cp == ch '$' || cp == ch '_' || idStartSet.contains cp
        else cp == ch '$' || cp == 0x200C || cp == 0x200D || idContinueSet.contains cp
      if !ok then fail "Invalid capture group name"
      out := out.pushCodePoint cp
      first := false
  fail "Invalid capture group name"

/-- `\p{…}`/`\P{…}` after `p{`/`P{`: UnicodePropertyValueExpression through `}`: the set and
whether it may contain strings (MayContainStrings).
spec: https://tc39.es/ecma262/#sec-compiletocharset (UnicodePropertyValueExpression) -/
def propertyEscape : PM (CSet × Bool) := do
  let s ← read
  let p0 ← getPos
  let mut name := ""
  let mut value : Option String := none
  let mut closed := false
  for i in [0:s.src.size - p0] do
    let c := s.src[p0 + i]!
    if c == ch '}' then
      adv (i + 1)
      closed := true
      break
    if c == ch '=' then
      if value.isSome then fail "Invalid property name"
      value := some ""
    else if isAsciiLetter c || c == ch '_' || isDigit c then
      match value with
      | some v => value := some (v.push (Char.ofNat c))
      | none => name := name.push (Char.ofNat c)
    else fail "Invalid property name"
  if !closed then fail "Invalid property name"
  let r ← rer
  match value with
  | some v =>
    -- UnicodePropertyName `=` UnicodePropertyValue
    if name.any Char.isDigit then fail "Invalid property name"
    let key? :=
      if name == "General_Category" || name == "gc" then (gcValue? v).map ("gc=" ++ ·)
      else if name == "Script" || name == "sc" then (scValue? v).map ("sc=" ++ ·)
      else if name == "Script_Extensions" || name == "scx" then (scValue? v).map ("scx=" ++ ·)
      else none
    match key?.bind propTable with
    | some cs => return (CSet.ofChars (maybeScfChars r cs), false)
    | none => fail "Invalid property name"
  | none =>
    -- LoneUnicodePropertyNameOrValue
    match gcValue? name with
    | some g =>
      match propTable ("gc=" ++ g) with
      | some cs => return (CSet.ofChars cs, false)
      | none => fail "Invalid property name"
    | none =>
      match binProp? name with
      | some b =>
        match propTable ("bin=" ++ b) with
        | some cs => return (CSet.ofChars (maybeScfChars r cs), false)
        | none => fail "Invalid property name"
      | none =>
        if isStrProp name && s.v then
          let (singles, seqs) := strProp name
          return (maybeScf r { chars := singles, strs := sortSeqs seqs }, true)
        fail "Invalid property name"

/-- CharacterClassEscape after `\` (d D s S w W, and p{ P{ in Unicode mode): its set and
MayContainStrings; `none` (nothing consumed) if the next character starts none.
spec: https://tc39.es/ecma262/#sec-compiletocharset (CharacterClassEscape) -/
def classEscape? : PM (Option (CSet × Bool)) := do
  let r ← rer
  match ← peek with
  | none => return none
  | some c =>
    if c == ch 'd' then adv; return some (CSet.ofChars (CharSet.range 48 57), false)
    if c == ch 'D' then adv; return some (CSet.ofChars (characterComplement r (CharSet.range 48 57)), false)
    if c == ch 's' then adv; return some (CSet.ofChars whiteSpaceChars, false)
    if c == ch 'S' then adv; return some (CSet.ofChars (characterComplement r whiteSpaceChars), false)
    if c == ch 'w' then adv; return some (CSet.ofChars (maybeScfChars r (wordCharacters r)), false)
    if c == ch 'W' then
      adv; return some (CSet.ofChars (characterComplement r (maybeScfChars r (wordCharacters r))), false)
    if r.eitherUnicode && (c == ch 'p' || c == ch 'P') then
      if !(← isAt 1 '{') then fail "Invalid property name"
      adv 2
      let (cs, strs) ← propertyEscape
      if c == ch 'P' then
        if strs then fail "Invalid property name"
        return some (CSet.ofChars (characterComplement r cs.chars), false)
      return some (cs, strs)
    return none

/-- LegacyOctalEscapeSequence at the current position (an octal digit is next).
spec: https://tc39.es/ecma262/#prod-LegacyOctalEscapeSequence -/
def legacyOctal : PM Nat := do
  let d1 := (← peek).getD 48 - 48
  adv
  let isOct (c : Option Nat) : Bool := match c with | some c => 48 ≤ c && c ≤ 55 | none => false
  if !isOct (← peek) then return d1
  let d2 := (← peek).getD 48 - 48
  adv
  if d1 ≥ 4 || !isOct (← peek) then return d1 * 8 + d2
  let d3 := (← peek).getD 48 - 48
  adv
  return d1 * 64 + d2 * 8 + d3

/-- CharacterEscape after `\` (with Annex B's extensions for BMP patterns): the character value,
or `none` (nothing consumed) when no CharacterEscape starts here; `inClass`: in a ClassEscape.
spec: https://tc39.es/ecma262/#sec-patterns-static-semantics-character-value -/
def characterEscape? (inClass : Bool) : PM (Option Nat) := do
  let s ← read
  match ← peek with
  | none => fail "\\ at end of pattern"
  | some c =>
    -- ControlEscape
    if c == ch 't' then adv; return some 9
    if c == ch 'n' then adv; return some 10
    if c == ch 'v' then adv; return some 11
    if c == ch 'f' then adv; return some 12
    if c == ch 'r' then adv; return some 13
    -- `c` AsciiLetter
    if c == ch 'c' then
      match ← peekAt 1 with
      | some l =>
        if isAsciiLetter l then adv 2; return some (l % 32)
        -- Annex B: ClassEscape :: `c` ClassControlLetter
        if !s.u && inClass && (isDigit l || l == ch '_') then adv 2; return some (l % 32)
      | none => pure ()
      if s.u then fail "Invalid unicode escape"
      -- Annex B: `\` [lookahead = c] is a backslash
      return none
    -- `0` [lookahead ∉ DecimalDigit]
    if c == ch '0' then
      match ← peekAt 1 with
      | some d =>
        if isDigit d then
          if s.u then fail "Invalid decimal escape"
          if d ≤ ch '7' then return some (← legacyOctal)
          adv; return some 0
      | none => pure ()
      adv; return some 0
    -- HexEscapeSequence
    if c == ch 'x' then
      adv
      match ← hexDigits 2 with
      | some v => return some v
      | none => if s.u then fail "Invalid escape" else return some (ch 'x')
    -- RegExpUnicodeEscapeSequence
    if c == ch 'u' then
      adv
      match ← unicodeEscape s.u with
      | some v => return some v
      | none => if s.u then fail "Invalid Unicode escape" else return some (ch 'u')
    if s.u then
      -- IdentityEscape[+UnicodeMode]: SyntaxCharacter or `/`
      if isSyntaxChar c || c == ch '/' then adv; return some c
      return none
    -- Annex B: LegacyOctalEscapeSequence (1-7: DecimalEscape is tried before, by the caller)
    if ch '1' ≤ c && c ≤ ch '7' then return some (← legacyOctal)
    -- Annex B: SourceCharacterIdentityEscape: not `c`, nor `k` with [NamedCaptureGroups]
    if c == ch 'k' && s.named then return none
    adv
    return some c

/-! ### Character classes -/

/-- A ClassAtom of a BMP/`u` pattern: a character, or a class escape's set. -/
inductive ClassAtom where
  | ch (c : Nat)
  | cls (s : CharSet)

/-- ClassAtom (non-UnicodeSets mode).
spec: https://tc39.es/ecma262/#prod-ClassAtom -/
def classAtom : PM ClassAtom := do
  let s ← read
  match ← peek with
  | none => fail "Unterminated character class"
  | some c =>
    if c != ch '\\' then adv; return .ch c
    adv
    match ← peek with
    | none => fail "\\ at end of pattern"
    | some e =>
      if e == ch 'b' then adv; return .ch 8
      if s.u && e == ch '-' then adv; return .ch (ch '-')
      match ← classEscape? with
      | some (cs, _) => return .cls cs.chars
      | none =>
        -- Annex B: `\8`, `\9` are identity escapes; `\c` without a control letter is `\`
        match ← characterEscape? true with
        | some v => return .ch v
        | none =>
          if !s.u && e == ch 'c' then return .ch (ch '\\')
          fail "Invalid class escape"

/-- ClassContents in non-UnicodeSets mode (NonemptyClassRanges), through the closing `]`.
spec: https://tc39.es/ecma262/#sec-compiletocharset (NonemptyClassRanges) -/
def classRanges : PM CharSet := do
  let s0 ← read
  let mut acc : CharSet := #[]
  for _ in [0:s0.src.size + 1] do
    match ← peek with
    | none => fail "Unterminated character class"
    | some c =>
      if c == ch ']' then adv; return acc
      let a ← classAtom
      if (← isAt 0 '-') && !(← isAt 1 ']') && (← peekAt 1).isSome then
        adv
        let b ← classAtom
        match a, b with
        | .ch x, .ch y =>
          if x > y then fail "Range out of order in character class"
          acc := acc.union (CharSet.range x y)
        | _, _ =>
          if s0.u then fail "Invalid character class"
          -- Annex B: CharacterRangeOrUnion
          let sa := match a with | .ch x => CharSet.single x | .cls s => s
          let sb := match b with | .ch x => CharSet.single x | .cls s => s
          acc := (acc.union sa).union (sb.union (CharSet.single (ch '-')))
      else
        acc := acc.union (match a with | .ch x => CharSet.single x | .cls s => s)
  fail "Unterminated character class"

/-- ClassSetReservedDoublePunctuator's characters. -/
def isDoublePunct (c : Nat) : Bool :=
  "&!#$%*+,.:;<=>?@^`~".any (·.toNat == c)

/-- ClassSetSyntaxCharacter. -/
def isClassSetSyntax (c : Nat) : Bool := "()[]{}/-\\|".any (·.toNat == c)

/-- ClassSetReservedPunctuator. -/
def isClassSetReservedPunct (c : Nat) : Bool := "&-!#%,:;<=>@`~".any (·.toNat == c)

/-- ClassSetCharacter: its character value, or `none` (nothing consumed) when none starts here.
spec: https://tc39.es/ecma262/#prod-ClassSetCharacter -/
def classSetCharacter? : PM (Option Nat) := do
  match ← peek with
  | none => return none
  | some c =>
    if c == ch '\\' then
      match ← peekAt 1 with
      | none => fail "\\ at end of pattern"
      | some e =>
        if e == ch 'b' then adv 2; return some 8
        if isClassSetReservedPunct e then adv 2; return some e
        if e == ch 'd' || e == ch 'D' || e == ch 's' || e == ch 'S' || e == ch 'w' || e == ch 'W' ||
           e == ch 'p' || e == ch 'P' || e == ch 'q' then return none
        adv
        match ← characterEscape? true with
        | some v => return some v
        | none => fail "Invalid escape"
    if isClassSetSyntax c then return none
    if isDoublePunct c && (← peekAt 1) == some c then fail "Invalid set operation in character class"
    adv
    return some c

mutual

/-- NestedClass / ClassContents in UnicodeSets mode after `[` (or `[^`), through `]`: the set
(not yet complemented) and MayContainStrings.
spec: https://tc39.es/ecma262/#sec-compiletocharset (ClassSetExpression) -/
def classSetExpression (d : Nat) : PM (CSet × Bool) := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  if ← eat ']' then return ({}, false)
  let s0 ← read
  -- the first operand (or range)
  let (first, firstStrs, isRange) ← classSetOperandOrRange d
  if (← isAt 0 '&') && (← isAt 1 '&') then
    if isRange then fail "Invalid set operation in character class"
    -- ClassIntersection
    let mut acc := first
    let mut strs := firstStrs
    for _ in [0:s0.src.size + 1] do
      if ← eat ']' then return (acc, strs)
      if !((← isAt 0 '&') && (← isAt 1 '&')) then fail "Invalid set operation in character class"
      adv 2
      if ← isAt 0 '&' then fail "Invalid character in character class"
      let (o, os, r) ← classSetOperandOrRange d
      if r then fail "Invalid set operation in character class"
      acc := acc.inter o
      strs := strs && os
    fail "Unterminated character class"
  if (← isAt 0 '-') && (← isAt 1 '-') then
    if isRange then fail "Invalid set operation in character class"
    -- ClassSubtraction
    let mut acc := first
    for _ in [0:s0.src.size + 1] do
      if ← eat ']' then return (acc, firstStrs)
      if !((← isAt 0 '-') && (← isAt 1 '-')) then fail "Invalid set operation in character class"
      adv 2
      let (o, _, r) ← classSetOperandOrRange d
      if r then fail "Invalid set operation in character class"
      acc := acc.diff o
    fail "Unterminated character class"
  -- ClassUnion
  let mut acc := first
  let mut strs := firstStrs
  for _ in [0:s0.src.size + 1] do
    if ← eat ']' then return (acc, strs)
    if (← isAt 0 '-') && (← isAt 1 '-') then fail "Invalid set operation in character class"
    if (← isAt 0 '&') && (← isAt 1 '&') then fail "Invalid set operation in character class"
    let (o, os, _) ← classSetOperandOrRange d
    acc := acc.union o
    strs := strs || os
  fail "Unterminated character class"

/-- ClassSetOperand or ClassSetRange: the set, MayContainStrings, and whether it was a range.
spec: https://tc39.es/ecma262/#prod-ClassSetOperand -/
def classSetOperandOrRange (d : Nat) : PM (CSet × Bool × Bool) := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  let r ← rer
  match ← peek with
  | none => fail "Unterminated character class"
  | some c =>
    -- NestedClass
    if c == ch '[' then
      adv
      if ← eat '^' then
        let (cs, strs) ← classSetExpression d
        if strs then fail "Negated character class may contain strings"
        return (CSet.ofChars (characterComplement r cs.chars), false, false)
      let (cs, strs) ← classSetExpression d
      return (cs, strs, false)
    if c == ch '\\' then
      -- ClassStringDisjunction
      if (← isAt 1 'q') then
        if !(← isAt 2 '{') then fail "Invalid escape"
        adv 3
        let s0 ← read
        let mut seqs : Array (Array Nat) := #[]
        let mut cur : Array Nat := #[]
        let mut strs := false
        for _ in [0:s0.src.size + 1] do
          if ← eat '}' then
            seqs := seqs.push cur
            if cur.size != 1 then strs := true
            return (maybeScf r (CSet.ofSeqs seqs), strs, false)
          if ← eat '|' then
            seqs := seqs.push cur
            if cur.size != 1 then strs := true
            cur := #[]
          else
            match ← classSetCharacter? with
            | some v => cur := cur.push v
            | none => fail "Invalid escape"
        fail "Unterminated character class"
      -- `\` CharacterClassEscape
      let save ← getPos
      adv
      match ← classEscape? with
      | some (cs, strs) => return (cs, strs, false)
      | none => setPos save
    -- ClassSetCharacter, or a ClassSetRange
    match ← classSetCharacter? with
    | none => fail "Invalid character in character class"
    | some a =>
      if (← isAt 0 '-') && !(← isAt 1 '-') then
        adv
        match ← classSetCharacter? with
        | none => fail "Invalid character class"
        | some b =>
          if a > b then fail "Range out of order in character class"
          return (CSet.ofChars (maybeScfChars r (CharSet.range a b)), false, true)
      return (CSet.ofChars (maybeScfChars r (CharSet.single a)), false, false)

end

/-- Groups strings (sorted) that are longer than `k` by their character at `k`. -/
def groupAt (strs : Array (Array Nat)) (k : Nat) : Array (Nat × Array (Array Nat)) :=
  strs.foldl (fun acc sq =>
    if sq.size ≤ k then acc else
    let c := sq[k]!
    if acc.size > 0 && acc[acc.size - 1]!.1 == c then
      acc.modify (acc.size - 1) fun (c, g) => (c, g.push sq)
    else acc.push (c, #[sq])) #[]

/-- The strings (sorted, all longer than `k - 1`, sharing their first `k` characters) after
their common prefix, as a trie of alternatives: longer strings first, then the one ending here.
`fuel`: the longest string's length. -/
def trieNode (ic : Bool) : Nat → Array (Array Nat) → Nat → PM Nat
  | 0, _, _ => push .empty
  | fuel + 1, strs, k => do
    let mut alts : Array Nat := #[]
    for (c, g) in groupAt strs k do
      let ch ← push (.char c ic)
      let rest ← trieNode ic fuel g (k + 1)
      alts := alts.push (← push (.seq #[ch, rest]))
    if strs.any (·.size == k) then alts := alts.push (← push .empty)
    if alts.size == 1 then return alts[0]!
    push (.alt alts)

/-- The node for a class set in UnicodeSets mode (CompileAtom's CharacterClass/CharacterClassEscape
steps 3-12: strings longest first, then the single characters, then the empty string). The
strings become a trie: at one position only strings that are prefixes of one another can match,
so trying deeper trie nodes first is trying longer strings first.
spec: https://tc39.es/ecma262/#sec-compileatom -/
def csetNode (cs : CSet) : PM Nat := do
  let r ← rer
  -- 2.
  if cs.strs.isEmpty then return ← push (.set cs.chars false r.ic)
  -- 5-6.
  let multi := cs.strs.filter (·.size > 1)
  let longest := multi.foldl (fun m sq => max m sq.size) 0
  let mut alts : Array Nat := #[]
  for (c, g) in groupAt multi 0 do
    let ch ← push (.char c r.ic)
    let rest ← trieNode r.ic longest g 1
    alts := alts.push (← push (.seq #[ch, rest]))
  -- 7-8.
  alts := alts.push (← push (.set cs.chars false r.ic))
  -- 9.
  if cs.strs.any (·.size == 0) then alts := alts.push (← push .empty)
  push (.alt alts)

/-- QuantifierPrefix and an optional `?`, if one starts here (nothing consumed otherwise):
min, max (`none` = +∞), greedy.
spec: https://tc39.es/ecma262/#sec-compilequantifier -/
def quantifier? : PM (Option (Nat × Option Nat × Bool)) := do
  let q ← do
    match ← peek with
    | none => pure none
    | some c =>
      if c == ch '*' then adv; pure (some (0, none))
      else if c == ch '+' then adv; pure (some (1, none))
      else if c == ch '?' then adv; pure (some (0, some 1))
      else if c == ch '{' then
        let save ← getPos
        adv
        match ← decimalDigits with
        | none => setPos save; pure none
        | some i =>
          if ← eat '}' then pure (some (i, some i))
          else if ← eat ',' then
            if ← eat '}' then pure (some (i, none))
            else match ← decimalDigits with
              | some j =>
                if ← eat '}' then
                  if i > j then fail "numbers out of order in {} quantifier"
                  pure (some (i, some j))
                else setPos save; pure none
              | none => setPos save; pure none
          else setPos save; pure none
      else pure none
  match q with
  | none => return none
  | some (mn, mx) =>
    let lazy ← eat '?'
    return some (mn, mx, !lazy)

/-- RegularExpressionModifiers: the flags (`i`, `m`, `s`) read; duplicates are an error. -/
def modifiers : PM (Bool × Bool × Bool × Nat) := do
  let s0 ← read
  let mut i := false
  let mut m := false
  let mut sflag := false
  let mut n := 0
  for _ in [0:s0.src.size] do
    match ← peek with
    | some c =>
      if c == ch 'i' then
        if i then fail "Repeated flag in modifiers"
        i := true
      else if c == ch 'm' then
        if m then fail "Repeated flag in modifiers"
        m := true
      else if c == ch 's' then
        if sflag then fail "Repeated flag in modifiers"
        sflag := true
      else break
      adv
      n := n + 1
    | none => break
  return (i, m, sflag, n)

mutual

/-- Disjunction, up to (not including) `)` or the end.
spec: https://tc39.es/ecma262/#prod-Disjunction -/
def disjunction (d : Nat) : PM Nat := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  let s0 ← read
  let did ← modifyGet fun s => (s.disjCount, { s with disjCount := s.disjCount + 1 })
  let outer := (← get).path
  let mut alts : Array Nat := #[]
  for k in [0:s0.src.size + 1] do
    modify fun s => { s with path := outer.push (did, k) }
    alts := alts.push (← alternative d)
    if !(← eat '|') then break
  modify fun s => { s with path := outer }
  if alts.size == 1 then return alts[0]!
  push (.alt alts)

/-- Alternative: Terms up to `|`, `)` or the end.
spec: https://tc39.es/ecma262/#prod-Alternative -/
def alternative (d : Nat) : PM Nat := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  let s0 ← read
  let mut kids : Array Nat := #[]
  for _ in [0:s0.src.size + 1] do
    match ← peek with
    | none => break
    | some c =>
      if c == ch '|' || c == ch ')' then break
      kids := kids.push (← term d)
  if kids.size == 1 then return kids[0]!
  if kids.isEmpty then push .empty else push (.seq kids)

/-- Term (with Annex B's QuantifiableAssertion and ExtendedAtom for BMP patterns).
spec: https://tc39.es/ecma262/#prod-Term -/
def term (d : Nat) : PM Nat := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  let s ← read
  let r ← rer
  let c := (← peek).getD 0
  -- Assertions
  if c == ch '^' then adv; return ← push (.bol r.ml)
  if c == ch '$' then adv; return ← push (.eol r.ml)
  if c == ch '\\' && ((← isAt 1 'b') || (← isAt 1 'B')) then
    let neg ← isAt 1 'B'
    adv 2
    return ← push (.wordB neg r.ic)
  let parenBefore := (← get).groups
  let mut quantifiable := true
  let mut atom := 0
  if c == ch '(' && (← isAt 1 '?') && ((← isAt 2 '=') || (← isAt 2 '!') ||
      ((← isAt 2 '<') && ((← isAt 3 '=') || (← isAt 3 '!')))) then
    -- lookaround
    let behind ← isAt 2 '<'
    let neg ← if behind then isAt 3 '!' else isAt 2 '!'
    adv (if behind then 4 else 3)
    let body ← disjunction d
    if !(← eat ')') then fail "Unterminated group"
    atom ← push (.look behind neg body)
    -- Annex B: `(?=`/`(?!` are QuantifiableAssertions in BMP patterns
    quantifiable := !behind && !s.u
    if !quantifiable then return atom
  else
    atom ← atomP d
  match ← quantifier? with
  | none => return atom
  | some (mn, mx, greedy) =>
    let parenAfter := (← get).groups
    push (.quant atom mn mx greedy parenBefore (parenAfter - parenBefore))

/-- Atom (Annex B: ExtendedAtom for BMP patterns).
spec: https://tc39.es/ecma262/#prod-Atom -/
def atomP (d : Nat) : PM Nat := do
  match d with
  | 0 => fail "Pattern too deeply nested"
  | d + 1 =>
  let s ← read
  let r ← rer
  match ← peek with
  | none => fail "Unexpected end of pattern"
  | some c =>
  if c == ch '.' then
    adv
    let all := allCharacters r
    return ← push (.set (if r.da then all else all.diff lineTerminators) false r.ic)
  if c == ch '(' then
    adv
    if ← eat '?' then
      if ← isAt 0 '<' then
        -- `(` GroupSpecifier Disjunction `)`
        adv
        let name ← groupName
        let idx := (← get).groups + 1
        modify fun st => { st with groups := idx, names := st.names.push (some name),
                                   namePaths := st.namePaths.push (name, st.path) }
        let body ← disjunction d
        if !(← eat ')') then fail "Unterminated group"
        return ← push (.group idx body)
      -- `(?` RegularExpressionModifiers [`-` RegularExpressionModifiers] `:`
      let (ai, am, as_, an) ← modifiers
      let mut rem := (false, false, false)
      if ← eat '-' then
        let (ri, rm, rs, rn) ← modifiers
        if an == 0 && rn == 0 then fail "Invalid group"
        if (ai && ri) || (am && rm) || (as_ && rs) then fail "Repeated flag in modifiers"
        rem := (ri, rm, rs)
      if !(← eat ':') then fail "Invalid group"
      -- UpdateModifiers
      let (ri, rm, rs) := rem
      modify fun st => { st with
        ic := if ri then false else if ai then true else st.ic
        ml := if rm then false else if am then true else st.ml
        da := if rs then false else if as_ then true else st.da }
      let body ← disjunction d
      modify fun st => { st with ic := r.ic, ml := r.ml, da := r.da }
      if !(← eat ')') then fail "Unterminated group"
      return body
    -- `(` Disjunction `)`
    let idx := (← get).groups + 1
    modify fun st => { st with groups := idx, names := st.names.push none }
    let body ← disjunction d
    if !(← eat ')') then fail "Unterminated group"
    return ← push (.group idx body)
  if c == ch '[' then
    adv
    let neg ← eat '^'
    if s.v then
      let (cs, strs) ← classSetExpression (2 * s.src.size + 4)
      if neg then
        if strs then fail "Negated character class may contain strings"
        return ← push (.set (characterComplement r cs.chars) false r.ic)
      return ← csetNode cs
    let cs ← classRanges
    return ← push (.set cs neg r.ic)
  if c == ch '\\' then
    adv
    let e := (← peek).getD 0
    if (← peek).isNone then fail "\\ at end of pattern"
    -- DecimalEscape
    if ch '1' ≤ e && e ≤ ch '9' then
      let save ← getPos
      let n := (← decimalDigits).getD 0
      if n ≤ s.totalGroups then return ← push (.backref #[n] r.ic)
      if s.u then fail "Invalid escape"
      setPos save
    -- `k` GroupName
    if e == ch 'k' && s.named then
      adv
      if !(← eat '<') then fail "Invalid named reference"
      let name ← groupName
      modify fun st => { st with refNames := st.refNames.push name }
      return ← push (.namedRef name r.ic)
    match ← classEscape? with
    | some (cs, _) => return ← csetNode cs
    | none =>
    match ← characterEscape? false with
    | some v => return ← push (.char v r.ic)
    | none =>
      if !s.u && e == ch 'c' then return ← push (.char (ch '\\') r.ic)
      fail "Invalid escape"
  if c == ch '*' || c == ch '+' || c == ch '?' then fail "Nothing to repeat"
  if c == ch '{' then
    if s.u then fail "Lone quantifier brackets"
    -- Annex B: InvalidBracedQuantifier is an error; otherwise a literal `{`
    if (← quantifier?).isSome then fail "Nothing to repeat"
  if s.u && (c == ch '}' || c == ch ']') then fail "Lone quantifier brackets"
  if c == ch ')' || c == ch '|' then fail "Unexpected character"
  adv
  push (.char c r.ic)

end

/-- Pre-scan: the number of left-capturing parentheses and whether there is a GroupName
(CountLeftCapturingParensWithin, needed before parsing DecimalEscapes; ParsePattern's Annex B
step choosing [NamedCaptureGroups]). Escapes and classes are skipped (nested classes in
UnicodeSets mode). -/
def prescan (src : Array Nat) (v : Bool) : Nat × Bool := Id.run do
  let mut i := 0
  let mut n := 0
  let mut named := false
  let mut depth := 0
  for _ in [0:src.size] do
    if i ≥ src.size then break
    let c := src[i]!
    if c == ch '\\' then i := i + 2; continue
    if depth > 0 then
      if c == ch ']' then depth := depth - 1
      else if c == ch '[' && v then depth := depth + 1
      i := i + 1
      continue
    if c == ch '[' then depth := 1; i := i + 1; continue
    if c == ch '(' then
      if src[i + 1]? != some (ch '?') then n := n + 1
      else if src[i + 2]? == some (ch '<') && src[i + 3]? != some (ch '=') &&
          src[i + 3]? != some (ch '!') then
        n := n + 1
        named := true
    i := i + 1
  return (n, named)

end P

/-- MightBothParticipate for two groups given their paths of (disjunction, alternative): false
iff some disjunction has them in different alternatives.
spec: https://tc39.es/ecma262/#sec-mightbothparticipate -/
def mightBothParticipate (x y : Array (Nat × Nat)) : Bool :=
  !(x.any fun (d, a) => y.any fun (d', a') => d == d' && a != a')

/-- ParsePattern (with Annex B's re-parse rule) and the early errors.
spec: https://tc39.es/ecma262/#sec-parsepattern
spec: https://tc39.es/ecma262/#sec-patterns-static-semantics-early-errors -/
def parsePattern (src : Array Nat) (u v ic ml da : Bool) : Except String Pattern := do
  -- 1.
  if u && v then throw "Invalid flags"
  let (total, hasNames) := P.prescan src v
  -- CountLeftCapturingParensWithin(Pattern) ≥ 2³² - 1
  if total ≥ 4294967295 then throw "Too many capture groups"
  let cx : PCtx := { src, u := u || v, v, named := u || v || hasNames, totalGroups := total }
  let st : PState := { ic, ml, da }
  let (root, s) ← (do
      -- (each nesting level of the grammar takes at most 4 calls, and one pattern character)
      let r ← P.disjunction (4 * src.size + 8)
      if (← P.peek).isSome then P.fail "Unmatched ')'"
      return r).run cx |>.run st
  -- duplicate group names that might both participate
  for i in [0:s.namePaths.size] do
    for j in [i + 1:s.namePaths.size] do
      let (a, pa) := s.namePaths[i]!
      let (b, pb) := s.namePaths[j]!
      if a == b && mightBothParticipate pa pb then throw "Duplicate capture group name"
  -- `\k<name>` with no such group
  for r in s.refNames do
    if !(s.namePaths.any (·.1 == r)) then throw "Invalid named capture referenced"
  return { nodes := s.nodes, root, groupCount := s.groups, groupNames := s.names }

end ES.Regex
