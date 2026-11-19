import ES.Unicode.RegexData

/-!
# Character sets and Unicode data for regular expressions

`CharSet`: sets of characters (code points, or code units for BMP patterns) as sorted, disjoint,
non-adjacent inclusive ranges, flattened (`#[lo₀, hi₀, lo₁, hi₁, …]`). Also the decoders of the
generated tables (`ES/Unicode/RegexData.lean`), Unicode property lookup, and Canonicalize.

spec: https://tc39.es/ecma262/#sec-pattern-semantics
-/

namespace ES.Regex

/-- A set of characters: flattened sorted, disjoint, non-adjacent inclusive ranges. -/
abbrev CharSet := Array Nat

namespace CharSet

def empty : CharSet := #[]

def single (c : Nat) : CharSet := #[c, c]

def range (lo hi : Nat) : CharSet := if lo ≤ hi then #[lo, hi] else #[]

/-- The number of ranges. -/
@[inline] def nRanges (s : CharSet) : Nat := s.size / 2

/-- Appends a range that starts at or after the last range's start (merging when overlapping or
adjacent). -/
@[inline] def pushRange (s : CharSet) (lo hi : Nat) : CharSet :=
  let n := s.size
  if n ≥ 2 && lo ≤ s[n - 1]! + 1 then
    let last := s[n - 1]!
    if hi > last then s.set! (n - 1) hi else s
  else (s.push lo).push hi

/-- Normalizes arbitrary `(lo, hi)` pairs. -/
def ofPairs (ps : Array (Nat × Nat)) : CharSet :=
  let sorted := (ps.filter (fun p => p.1 ≤ p.2)).qsort (fun a b => a.1 < b.1)
  sorted.foldl (fun acc p => acc.pushRange p.1 p.2) #[]

def ofChars (cs : Array Nat) : CharSet := ofPairs (cs.map fun c => (c, c))

/-- Whether `c` is in the set (binary search over the ranges; 64 halvings exceed any set's
size). -/
def contains (s : CharSet) (c : Nat) : Bool := go 0 s.nRanges 64
where
  go (lo hi : Nat) : Nat → Bool
    | 0 => false
    | f + 1 =>
      if lo ≥ hi then false else
      let mid := (lo + hi) / 2
      if c < s[2 * mid]! then go lo mid f
      else if c > s[2 * mid + 1]! then go (mid + 1) hi f
      else true

/-- Union (merge of two sorted range lists). -/
def union (a b : CharSet) : CharSet := Id.run do
  let mut out : CharSet := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  for _ in [0:a.nRanges + b.nRanges] do
    if i < a.nRanges && (j ≥ b.nRanges || a[2 * i]! ≤ b[2 * j]!) then
      out := out.pushRange a[2 * i]! a[2 * i + 1]!
      i := i + 1
    else if j < b.nRanges then
      out := out.pushRange b[2 * j]! b[2 * j + 1]!
      j := j + 1
  return out

/-- The complement within `[0, maxChar]`. -/
def complement (s : CharSet) (maxChar : Nat) : CharSet := Id.run do
  let mut out : CharSet := #[]
  let mut prev := 0
  for k in [0:s.nRanges] do
    let lo := s[2 * k]!
    let hi := s[2 * k + 1]!
    if lo > maxChar then break
    if lo > prev then out := (out.push prev).push (lo - 1)
    prev := hi + 1
  if prev ≤ maxChar then out := (out.push prev).push maxChar
  return out

/-- Intersection. -/
def inter (a b : CharSet) : CharSet := Id.run do
  let mut out : CharSet := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:a.nRanges + b.nRanges] do
    if i ≥ a.nRanges || j ≥ b.nRanges then break
    let alo := a[2 * i]!
    let ahi := a[2 * i + 1]!
    let blo := b[2 * j]!
    let bhi := b[2 * j + 1]!
    let lo := max alo blo
    let hi := min ahi bhi
    if lo ≤ hi then out := out.pushRange lo hi
    if ahi < bhi then i := i + 1 else j := j + 1
  return out

/-- Difference `a \ b`. -/
def diff (a b : CharSet) : CharSet :=
  let top := max (if a.size > 0 then a[a.size - 1]! else 0) (if b.size > 0 then b[b.size - 1]! else 0)
  inter a (complement b top)

/-- Whether the set has exactly one character, and which. -/
def single? (s : CharSet) : Option Nat :=
  if s.size == 2 && s[0]! == s[1]! then some s[0]! else none

/-- The number of characters. -/
def card (s : CharSet) : Nat := Id.run do
  let mut n := 0
  for k in [0:s.nRanges] do n := n + (s[2 * k + 1]! - s[2 * k]! + 1)
  return n

end CharSet

/-! ## Decoding the generated tables -/

/-- Decodes a list of naturals (base-64 digits `A-Za-z0-9+/`; big-endian 5-bit groups, all but
the last offset by 32). -/
def decodeNats (s : String) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (s.utf8ByteSize / 2)
  let mut acc := 0
  for c in s.toList do
    let n := c.toNat
    let v :=
      if 65 ≤ n && n ≤ 90 then n - 65
      else if 97 ≤ n && n ≤ 122 then n - 97 + 26
      else if 48 ≤ n && n ≤ 57 then n - 48 + 52
      else if n == 43 then 62 else 63
    if v ≥ 32 then acc := acc * 32 + (v - 32)
    else
      out := out.push (acc * 32 + v)
      acc := 0
  return out

/-- Decodes a range list (gap, length - 1 pairs) into a `CharSet`. -/
def decodeRanges (s : String) : CharSet := Id.run do
  let ns := decodeNats s
  let mut out : CharSet := Array.mkEmpty ns.size
  let mut next := 0
  for k in [0:ns.size / 2] do
    let lo := next + ns[2 * k]!
    let hi := lo + ns[2 * k + 1]!
    out := (out.push lo).push hi
    next := hi + 1
  return out

/-- Decodes a mapping (key delta, zigzag value delta pairs) into flattened sorted
`#[k₀, v₀, k₁, v₁, …]`. -/
def decodeMap (s : String) : Array Nat := Id.run do
  let ns := decodeNats s
  let mut out : Array Nat := Array.mkEmpty ns.size
  let mut k := 0
  for i in [0:ns.size / 2] do
    k := k + ns[2 * i]!
    let z := ns[2 * i + 1]!
    let v : Int := if z % 2 == 0 then (k : Int) + (z / 2 : Nat) else (k : Int) - ((z + 1) / 2 : Nat)
    out := (out.push k).push v.toNat
  return out

/-- Looks a key up in a flattened sorted mapping (64 halvings exceed any table's size). -/
def mapLookup (m : Array Nat) (c : Nat) : Option Nat := go 0 (m.size / 2) 64
where
  go (lo hi : Nat) : Nat → Option Nat
    | 0 => none
    | f + 1 =>
      if lo ≥ hi then none else
      let mid := (lo + hi) / 2
      let k := m[2 * mid]!
      if c < k then go lo mid f
      else if c > k then go (mid + 1) hi f
      else some m[2 * mid + 1]!

/-- The mapping's value for `c`, or `c` (`mapLookup` without the `Option`). -/
def mapGet (m : Array Nat) (c : Nat) : Nat := go 0 (m.size / 2) 64
where
  go (lo hi : Nat) : Nat → Nat
    | 0 => c
    | f + 1 =>
      if lo ≥ hi then c else
      let mid := (lo + hi) / 2
      let k := m[2 * mid]!
      if c < k then go lo mid f
      else if c > k then go (mid + 1) hi f
      else m[2 * mid + 1]!

/-- The keys of a flattened mapping as a set. -/
def mapKeys (m : Array Nat) : CharSet := Id.run do
  let mut out : CharSet := #[]
  for i in [0:m.size / 2] do
    let k := m[2 * i]!
    out := out.pushRange k k
  return out

/-! ## Canonicalize -/

/-- Simple case folding (CaseFolding.txt C + S). -/
def scfMap : Array Nat := decodeMap ES.Unicode.RegexData.scf
/-- The non-unicode Canonicalize's uppercase table. -/
def upperMap : Array Nat := decodeMap ES.Unicode.RegexData.upper
def scfKeys : CharSet := mapKeys scfMap
def upperKeys : CharSet := mapKeys upperMap

/-- scf(c): simple case folding. -/
@[inline] def scf (c : Nat) : Nat :=
  if c < 128 then (if 65 ≤ c && c ≤ 90 then c + 32 else c)
  else mapGet scfMap c

/-- Canonicalize for a BMP pattern with ignoreCase (toUppercase of a code unit, single-unit
results only, never from non-ASCII to ASCII). -/
@[inline] def upperCanon (c : Nat) : Nat :=
  if c < 128 then (if 97 ≤ c && c ≤ 122 then c - 32 else c)
  else mapGet upperMap c

/-- Canonicalize(rer, ch), given whether the pattern has either unicode flag and ignoreCase.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-canonicalize-ch -/
@[inline] def canonicalize (unicode ignoreCase : Bool) (ch : Nat) : Nat :=
  -- 1.
  if unicode && ignoreCase then scf ch
  -- 2.
  else if !ignoreCase then ch
  -- 3-8.
  else upperCanon ch

/-- The image of a set under Canonicalize: characters that are not keys of the mapping stay,
keys map to their canonical character. Matching `Canonicalize(ch) ∈ canonImage A` is
CharacterSetMatcher's "exists a ∈ A with Canonicalize(a) = Canonicalize(ch)". -/
def canonImage (unicode : Bool) (s : CharSet) : CharSet :=
  let (m, keys) := if unicode then (scfMap, scfKeys) else (upperMap, upperKeys)
  let kept := s.diff keys
  let hit := s.inter keys
  let imgs := Id.run do
    let mut out : Array Nat := #[]
    for r in [0:hit.nRanges] do
      for c in [hit[2 * r]!:hit[2 * r + 1]! + 1] do
        out := out.push ((mapLookup m c).getD c)
    return out
  kept.union (CharSet.ofChars imgs)

/-! ## Unicode properties -/

/-- Looks up `name` in an `;alias=Canonical;` table. -/
def aliasLookup (table name : String) : Option String :=
  if name.isEmpty then none else
  let key := ";" ++ name ++ "="
  match table.splitOn key with
  | [_, rest] => some ((rest.splitOn ";").headD "")
  | _ => none

/-- The range table with the given key. -/
def propTable (key : String) : Option CharSet :=
  (ES.Unicode.RegexData.tables.find? (·.1 == key)).map fun p => decodeRanges p.2

/-- The canonical General_Category value of a value or alias. -/
def gcValue? (v : String) : Option String := aliasLookup ES.Unicode.RegexData.gcAliases v
/-- The canonical Script value of a value or alias. -/
def scValue? (v : String) : Option String := aliasLookup ES.Unicode.RegexData.scAliases v
/-- The canonical binary property of a name or alias. -/
def binProp? (v : String) : Option String := aliasLookup ES.Unicode.RegexData.binAliases v
/-- Whether `v` names a property of strings. -/
def isStrProp (v : String) : Bool :=
  !v.isEmpty && (ES.Unicode.RegexData.strProps.splitOn (";" ++ v ++ ";")).length == 2

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0

/-- A property of strings: its single code points and its longer strings (code point lists). -/
def strProp (name : String) : CharSet × Array (Array Nat) :=
  match ES.Unicode.RegexData.strTables.find? (·.1 == name) with
  | some (_, singles, seqs) =>
    (decodeRanges singles,
      ((seqs.splitOn ",").filter (!·.isEmpty)).toArray.map fun s =>
        ((s.splitOn " ").map hexVal).toArray)
  | none => (#[], #[])

/-- ID_Start and ID_Continue (for group names' IdentifierStartChar/IdentifierPartChar). -/
def idStartSet : CharSet := (propTable "bin=ID_Start").getD #[]
def idContinueSet : CharSet := (propTable "bin=ID_Continue").getD #[]

end ES.Regex
