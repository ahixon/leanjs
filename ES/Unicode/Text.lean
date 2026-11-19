import Std.Data.HashMap
import ES.Str
import ES.Regex.Unicode
import ES.Unicode.TextData

/-!
# Case conversion and normalization of String values

Full case mappings with Final_Sigma (`toLower`, `toUpper`) and the Unicode normalization forms
(`normalize`) over `JSStr`, from the generated tables of `ES/Unicode/TextData.lean`. Strings are
read as code points (StringToCodePoints: a lone surrogate is a code point of its own, which maps
to itself and has combining class 0).

spec: https://tc39.es/ecma262/#sec-string.prototype.tolowercase
spec: https://tc39.es/ecma262/#sec-string.prototype.normalize
spec: https://unicode.org/reports/tr15/ (decomposition, canonical ordering, composition)
-/

namespace ES.Unicode

open Std (HashMap)

/-! ## Decoding the tables -/

/-- Decodes a sequence map: (key delta, count, values…) entries. -/
def decodeSeqMap (s : String) : HashMap Nat (Array Nat) := Id.run do
  let ns := Regex.decodeNats s
  let mut m : HashMap Nat (Array Nat) := {}
  let mut i := 0
  let mut k := 0
  -- (each entry takes at least two numbers: fewer iterations than numbers suffice)
  for _ in [0:ns.size] do
    if i + 1 ≥ ns.size then break
    k := k + ns[i]!
    let n := ns[i + 1]!
    m := m.insert k (ns.extract (i + 2) (i + 2 + n))
    i := i + 2 + n
  return m

/-- Decodes a value map: (key delta, value) pairs. -/
def decodeValMap (s : String) : HashMap Nat Nat := Id.run do
  let ns := Regex.decodeNats s
  let mut m : HashMap Nat Nat := {}
  let mut k := 0
  for j in [0:ns.size / 2] do
    k := k + ns[2 * j]!
    m := m.insert k ns[2 * j + 1]!
  return m

/-- The key of a pair of code points in the composition map. -/
@[inline] def pairKey (a b : Nat) : Nat := a * 0x110000 + b

/-- Decodes the composition triples: (first delta, second, composite). -/
def decodeComps (s : String) : HashMap Nat Nat := Id.run do
  let ns := Regex.decodeNats s
  let mut m : HashMap Nat Nat := {}
  let mut a := 0
  for j in [0:ns.size / 3] do
    a := a + ns[3 * j]!
    m := m.insert (pairKey a ns[3 * j + 1]!) ns[3 * j + 2]!
  return m

def lowerMap : HashMap Nat (Array Nat) := decodeSeqMap TextData.lowerMap
def upperMap : HashMap Nat (Array Nat) := decodeSeqMap TextData.upperMap
def casedSet : Regex.CharSet := Regex.decodeRanges TextData.casedRanges
def caseIgnorableSet : Regex.CharSet := Regex.decodeRanges TextData.caseIgnorableRanges
def cccMap : HashMap Nat Nat := decodeValMap TextData.cccMap
def nfdMap : HashMap Nat (Array Nat) := decodeSeqMap TextData.nfdMap
def nfkdMap : HashMap Nat (Array Nat) := decodeSeqMap TextData.nfkdMap
def compMap : HashMap Nat Nat := decodeComps TextData.compositions

/-! ## Code points of a String -/

/-- The code points of a String (StringToCodePoints).
spec: https://tc39.es/ecma262/#sec-stringtocodepoints -/
def codePoints (s : JSStr) : Array Nat := Id.run do
  let mut out := Array.mkEmpty s.length
  let mut i := 0
  for _ in [0:s.length] do
    if i ≥ s.length then break
    let (cp, n, _) := s.codePointAt i
    out := out.push cp
    i := i + n
  return out

/-- CodePointsToString spec: https://tc39.es/ecma262/#sec-codepointstostring -/
def ofCodePoints (cps : Array Nat) : JSStr :=
  cps.foldl JSStr.pushCodePoint ⟨ByteArray.emptyWithCapacity (2 * cps.size)⟩

/-! ## Case conversion -/

/-- The code point ending just before code unit index `j` (and its start). -/
def cpBefore (s : JSStr) (j : Nat) : Nat × Nat :=
  if j ≥ 2 && JSStr.isLowSurrogate (s.get (j - 1)) && JSStr.isHighSurrogate (s.get (j - 2)) then
    let (cp, _, _) := s.codePointAt (j - 2)
    (cp, j - 2)
  else ((s.get (j - 1)).toNat, j - 1)

/-- Final_Sigma at the code unit index `i` (a U+03A3 code unit): preceded by a cased letter and
case-ignorable characters, and not followed by case-ignorable characters and a cased letter (a
character that is both case-ignorable and cased is skipped as case-ignorable, as ICU does).
spec: https://www.unicode.org/versions/latest/core-spec/chapter-3/#G54277 (Table 3-17) -/
def isFinalSigma (s : JSStr) (i : Nat) : Bool := Id.run do
  -- before
  let mut j := i
  let mut before := false
  for _ in [0:i] do
    if j == 0 then break
    let (cp, st) := cpBefore s j
    j := st
    if caseIgnorableSet.contains cp then continue
    if casedSet.contains cp then before := true
    break
  if !before then return false
  -- after
  let mut k := i + 1
  for _ in [0:s.length] do
    if k ≥ s.length then break
    let (cp, n, _) := s.codePointAt k
    k := k + n
    if caseIgnorableSet.contains cp then continue
    if casedSet.contains cp then return false
    break
  return true

/-- Maps every code point with a full case mapping (`lower`: toLowercase with Final_Sigma). -/
def caseMap (s : JSStr) (lower : Bool) : JSStr := Id.run do
  -- (ASCII fast path)
  if s.isAscii then
    let mut out := ⟨ByteArray.emptyWithCapacity s.b.size⟩
    for k in [0:s.length] do
      let u := s.get k
      let u := if lower then (if 65 ≤ u && u ≤ 90 then u + 32 else u)
        else (if 97 ≤ u && u ≤ 122 then u - 32 else u)
      out := out.push u
    return out
  let m := if lower then lowerMap else upperMap
  let mut out := ⟨ByteArray.emptyWithCapacity s.b.size⟩
  let mut i := 0
  for _ in [0:s.length] do
    if i ≥ s.length then break
    let (cp, n, _) := s.codePointAt i
    if lower && cp == 0x3A3 then
      out := out.pushCodePoint (if isFinalSigma s i then 0x3C2 else 0x3C3)
    else match m.get? cp with
      | some cps => out := cps.foldl JSStr.pushCodePoint out
      | none => out := out.pushCodePoint cp
    i := i + n
  return out

/-- toLowercase of a String (full mappings, Final_Sigma; no language-sensitive mappings). -/
def toLower (s : JSStr) : JSStr := caseMap s true
/-- toUppercase of a String (full mappings). -/
def toUpper (s : JSStr) : JSStr := caseMap s false

/-! ## Normalization -/

def sBase : Nat := 0xAC00
def lBase : Nat := 0x1100
def vBase : Nat := 0x1161
def tBase : Nat := 0x11A7
def lCount : Nat := 19
def vCount : Nat := 21
def tCount : Nat := 28
def nCount : Nat := vCount * tCount
def sCount : Nat := lCount * nCount

@[inline] def ccc (c : Nat) : Nat := cccMap.getD c 0

/-- Appends the full decomposition of `c` (canonical, or compatibility when `compat`). -/
def pushDecomposed (out : Array Nat) (c : Nat) (compat : Bool) : Array Nat :=
  if sBase ≤ c && c < sBase + sCount then
    -- (Hangul syllables: algorithmic)
    let si := c - sBase
    let out := (out.push (lBase + si / nCount)).push (vBase + (si % nCount) / tCount)
    if si % tCount == 0 then out else out.push (tBase + si % tCount)
  else
    let d := if compat then (nfkdMap.get? c).orElse (fun _ => nfdMap.get? c) else nfdMap.get? c
    match d with
    | some cps => out ++ cps
    | none => out.push c

/-- The Canonical Ordering Algorithm: stable sort of each run of non-starters by combining class. -/
def canonicalOrder (cps : Array Nat) : Array Nat := Id.run do
  let mut out := cps
  let mut i := 0
  for _ in [0:cps.size] do
    if i ≥ cps.size then break
    if ccc cps[i]! == 0 then i := i + 1; continue
    let mut j := i
    for _ in [0:cps.size] do
      if j < cps.size && ccc cps[j]! != 0 then j := j + 1 else break
    if j - i > 1 then
      let run := (cps.extract i j).insertionSort (fun a b => ccc a < ccc b)
      for k in [0:run.size] do out := out.set! (i + k) run[k]!
    i := j
  return out

/-- The primary composite of a pair, if any (Hangul LV and LVT algorithmically). -/
def composePair (a b : Nat) : Option Nat :=
  if lBase ≤ a && a < lBase + lCount && vBase ≤ b && b < vBase + vCount then
    some (sBase + ((a - lBase) * vCount + (b - vBase)) * tCount)
  else if sBase ≤ a && a < sBase + sCount && (a - sBase) % tCount == 0 && tBase < b && b < tBase + tCount then
    some (a + (b - tBase))
  else compMap.get? (pairKey a b)

/-- The Canonical Composition Algorithm. -/
def compose (cps : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty cps.size
  let mut starter : Option Nat := none
  -- (the combining class of the last character after the starter; none: the starter is last)
  let mut last : Option Nat := none
  for c in cps do
    let cc := ccc c
    if let some s := starter then
      let blocked := match last with
        | some l => l == 0 || l ≥ cc
        | none => false
      if !blocked then
        if let some x := composePair out[s]! c then
          out := out.set! s x
          continue
    if cc == 0 then
      starter := some out.size
      last := none
    else last := some cc
    out := out.push c
  return out

/-- The normalization forms: 0 NFC, 1 NFD, 2 NFKC, 3 NFKD. -/
def normalize (s : JSStr) (form : Nat) : JSStr := Id.run do
  -- (ASCII is in every normalization form)
  if s.isAscii then return s
  let compat := form ≥ 2
  let d := (codePoints s).foldl (fun out c => pushDecomposed out c compat) #[]
  let d := canonicalOrder d
  let r := if form % 2 == 0 then compose d else d
  return ofCodePoints r

end ES.Unicode
