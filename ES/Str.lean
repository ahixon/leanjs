/-!
# ECMAScript String values

spec: https://tc39.es/ecma262/#sec-ecmascript-language-types-string-type

A String value is a finite sequence of 16-bit code units (any sequence: lone surrogates are
allowed). `JSStr` keeps them in a `ByteArray`, little-endian, two bytes per unit, so that strings
are compact, appends are copies of bytes, and hashing is native. Lean `String`s (which cannot hold
lone surrogates) convert in with UTF-16 encoding and out with lone surrogates replaced by U+FFFD.
-/

namespace ES

/-- A String value: UTF-16 code units, little-endian, in `b` (`b.size` is even). -/
structure JSStr where
  b : ByteArray
  deriving Inhabited

namespace JSStr

/-- The number of code units. -/
@[inline] def length (s : JSStr) : Nat := s.b.size / 2

/-- The code unit at `i` (0 past the end). -/
@[inline] def get (s : JSStr) (i : Nat) : UInt16 :=
  (s.b.get! (2 * i)).toUInt16 ||| ((s.b.get! (2 * i + 1)).toUInt16 <<< 8)

def empty : JSStr := ⟨ByteArray.empty⟩

@[inline] def isEmpty (s : JSStr) : Bool := s.b.size == 0

@[inline] def push (s : JSStr) (u : UInt16) : JSStr :=
  ⟨(s.b.push u.toUInt8).push (u >>> 8).toUInt8⟩

/-- Appends a code point (two units past U+FFFF). -/
def pushCodePoint (s : JSStr) (c : Nat) : JSStr :=
  if c < 0x10000 then s.push c.toUInt16 else
  let c' := c - 0x10000
  (s.push (0xD800 + c' / 0x400).toUInt16).push (0xDC00 + c' % 0x400).toUInt16

@[inline] def append (s t : JSStr) : JSStr := ⟨s.b ++ t.b⟩
instance : Append JSStr := ⟨append⟩

/-- Code units `[i, j)` (clamped). -/
def slice (s : JSStr) (i j : Nat) : JSStr :=
  let n := s.length
  let j := min j n
  let i := min i j
  ⟨s.b.extract (2 * i) (2 * j)⟩

def drop (s : JSStr) (i : Nat) : JSStr := s.slice i s.length
def take (s : JSStr) (i : Nat) : JSStr := s.slice 0 i

def ofUnits (us : Array UInt16) : JSStr := us.foldl push ⟨ByteArray.emptyWithCapacity (2 * us.size)⟩

def toUnits (s : JSStr) : Array UInt16 := Id.run do
  let mut a := Array.mkEmpty s.length
  for i in [0:s.length] do a := a.push (s.get i)
  return a

/-- A list of characters, UTF-16 encoded. -/
def ofList (cs : List Char) : JSStr := cs.foldl (fun acc c => acc.pushCodePoint c.toNat) empty

/-- A Lean string, UTF-16 encoded. (Through `String.toList` and `List.foldl`, so that it unfolds
definitionally on string literals: proofs can decide equalities of JSStr literals.) -/
def ofString (str : String) : JSStr := ofList str.toList

instance : Coe String JSStr := ⟨ofString⟩

@[inline] def isHighSurrogate (u : UInt16) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF
@[inline] def isLowSurrogate (u : UInt16) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- CodePointAt: the code point at `i`, its length in units, and whether it is a lone surrogate.
spec: https://tc39.es/ecma262/#sec-codepointat -/
def codePointAt (s : JSStr) (i : Nat) : Nat × Nat × Bool :=
  -- 1-3.
  let first := s.get i
  let cp := first.toNat
  -- 4.
  if !(isHighSurrogate first) && !(isLowSurrogate first) then (cp, 1, false)
  -- 5.
  else if isLowSurrogate first || i + 1 = s.length then (cp, 1, true)
  else
  -- 6-7.
  let second := s.get (i + 1)
  if !(isLowSurrogate second) then (cp, 1, true)
  -- 8.
  else ((first.toNat - 0xD800) * 0x400 + (second.toNat - 0xDC00) + 0x10000, 2, false)

/-- Converts to a Lean `String`, lone surrogates as U+FFFD. -/
def toString (s : JSStr) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for _ in [0:s.length] do
    if i ≥ s.length then break
    let (cp, n, lone) := s.codePointAt i
    out := out.push (if lone then '�' else Char.ofNat cp)
    i := i + n
  return out

instance : ToString JSStr := ⟨toString⟩
instance : Repr JSStr := ⟨fun s _ => repr s.toString⟩

/-- Code-unit equality: equality of the bytes (lawful, so proofs can use hash map lemmas). -/
def beq (s t : JSStr) : Bool := s.b == t.b

instance : BEq JSStr := ⟨beq⟩

instance : LawfulBEq JSStr where
  eq_of_beq {a b} h := by
    cases a; cases b
    have h' : _ = _ := eq_of_beq (α := ByteArray) h
    subst h'; rfl
  rfl {a} := by cases a; exact beq_self_eq_true (α := ByteArray) _

instance : DecidableEq JSStr := fun a b =>
  if h : a.b = b.b then .isTrue (by cases a; cases b; simp_all) else .isFalse (by intro e; cases e; exact h rfl)

instance : Hashable JSStr := ⟨fun s => s.b.hash⟩

instance : LawfulHashable JSStr where
  hash_eq {a b} h := by rw [eq_of_beq h]

/-- Code-unit order (IsLessThan for strings).
spec: https://tc39.es/ecma262/#sec-islessthan (step 3) -/
def lt (s t : JSStr) : Bool := Id.run do
  let n := min s.length t.length
  for i in [0:n] do
    let a := s.get i
    let b := t.get i
    if a < b then return true
    if a > b then return false
  return s.length < t.length

instance : LT JSStr := ⟨fun s t => lt s t = true⟩
instance (s t : JSStr) : Decidable (s < t) := inferInstanceAs (Decidable (lt s t = true))

/-- Whether `t` occurs at `i` in `s`. -/
def matchesAt (s t : JSStr) (i : Nat) : Bool :=
  i + t.length ≤ s.length && Id.run do
    for j in [0:t.length] do
      if s.get (i + j) != t.get j then return false
    return true

/-- StringIndexOf: the first index ≥ `from` where `t` occurs.
spec: https://tc39.es/ecma262/#sec-stringindexof -/
def indexOf (s t : JSStr) (fromIdx : Nat := 0) : Option Nat := Id.run do
  let len := s.length
  if t.length == 0 && fromIdx ≤ len then return some fromIdx
  if t.length > len then return none
  for i in [fromIdx:len - t.length + 1] do
    if s.matchesAt t i then return some i
  return none

def startsWith (s t : JSStr) : Bool := s.matchesAt t 0

/-- The ASCII string of a Lean string literal (no conversion work at use sites beyond once). -/
def lit (str : String) : JSStr := ofString str

/-- CanonicalNumericIndexString's and array indices' first step: the value of a string of
decimal digits without leading zeros (`"0"` alone allowed), if it is one. -/
def toIndex? (s : JSStr) : Option Nat := Id.run do
  let n := s.length
  if n == 0 || n > 16 then return none
  if n > 1 && s.get 0 == 48 then return none
  let mut v := 0
  for i in [0:n] do
    let u := s.get i
    if u < 48 || u > 57 then return none
    v := v * 10 + (u.toNat - 48)
  return some v

/-- An array index: an integer index below 2^32 - 1.
spec: https://tc39.es/ecma262/#array-index -/
def toArrayIndex? (s : JSStr) : Option Nat :=
  match s.toIndex? with
  | some v => if v < 4294967295 then some v else none
  | none => none

def ofNat (n : Nat) : JSStr := ofString (Nat.repr n)

/-- Whether every code unit is ASCII. -/
def isAscii (s : JSStr) : Bool := Id.run do
  for i in [0:s.length] do
    if s.get i ≥ 128 then return false
  return true

/-- Concatenates an array of strings. -/
def join (parts : Array JSStr) (sep : JSStr := empty) : JSStr := Id.run do
  let mut out := empty
  let mut first := true
  for p in parts do
    if !first then out := out ++ sep
    out := out ++ p
    first := false
  return out

end JSStr
end ES
