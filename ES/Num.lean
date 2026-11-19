import ES.Number
import ES.Str

/-!
# Number and BigInt algorithms

The numeric algorithms of ECMA-262 over the exact binary64 model `ES.F64` (no `Float`) and
Lean's `Int` (BigInt values):

- rounding of exact values (`ofNatExp`, `ofRatExp`), Number::toString (shortest round-trip digits
  for radix 10, V8's digit generation for other radices), StringToNumber, `parseFloat`/`parseInt`,
  `toFixed`/`toExponential`/`toPrecision`;
- the Number:: operations (`**`, `%`, shifts, bitwise, comparisons) and ToInt32 & co.;
- `Math`: exact or correctly rounded. Algebraic functions (`sqrt`, `cbrt`, `hypot`, integral
  powers) are computed exactly; transcendental ones with Ziv's strategy: an approximation with a
  proven-by-construction error bound (fixed-point arithmetic at a working precision plus 64 guard
  bits), rounded once; if the two ends of the error interval round differently, again at twice
  the precision;
- binary32/binary16 rounding and encodings (`fround`, `f16round`, typed arrays);
- BigInt: two's complement bitwise operations, `asIntN`/`asUintN`, StringToBigInt, ToString,
  exact conversions and comparisons with Numbers;
- Date: the time-value arithmetic of 21.4.1, the string formats and `Date.parse`.

Errors (RangeError, SyntaxError) are `Option`/`Except` results for the caller to throw.
-/

namespace ES.Num

open ES (F64)

/-! ## Exact rounding -/

def posZero : F64 := .fin false 0 (-1074)
def negZero : F64 := .fin true 0 (-1074)
def one : F64 := .fin false (2 ^ 52) (-52)
def negOne : F64 := .fin true (2 ^ 52) (-52)

/-- `n` halved `k` times, rounded to nearest, ties to even (by shifts). -/
@[inline] def shiftRoundEven (n k : Nat) : Nat :=
  if k == 0 then n else
  let q := n >>> k
  let r := n - (q <<< k)
  let half := 1 <<< (k - 1)
  if r > half || (r == half && q % 2 == 1) then q + 1 else q

/-- The Number nearest to (-1)^neg · v · 2^s (ties to even; ±∞ from 2^1024 − 2^970 on), exact
when representable. Only shifts: no division.
spec: https://tc39.es/ecma262/#number-value -/
def ofNatExp (neg : Bool) (v : Nat) (s : Int) : F64 :=
  if v == 0 then .fin neg 0 (-1074) else
  -- (v · 2^s ∈ [2^top, 2^(top+1)))
  let top : Int := s + (Nat.log2 v : Int)
  if top ≥ 1024 then .inf neg
  else if top < -1076 then .fin neg 0 (-1074)
  else
  let e := max (-1074) (top - 52)
  let (m, e) := if e ≤ s then (v <<< (s - e).toNat, e) else
    let m := shiftRoundEven v (e - s).toNat
    if m == 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)
  if e > 971 then .inf neg else .fin neg m e

/-- `ofNatExp` of a signed integer (+0 for 0). -/
@[inline] def ofIntExp (v : Int) (s : Int) : F64 := ofNatExp (v < 0) v.natAbs s

/-- An integer as a Number (rounded). -/
@[inline] def ofInt (i : Int) : F64 := ofIntExp i 0

@[inline] def ofNat (n : Nat) : F64 := ofNatExp false n 0

/-- The Number nearest to (-1)^neg · a / b · 2^s (b > 0); never materialises a power of two past
what the result can need. -/
def ofRatExp (neg : Bool) (a b : Nat) (s : Int) : F64 :=
  if a == 0 then .fin neg 0 (-1074) else
  -- (a / b ∈ (2^(la-lb-1), 2^(la-lb+1)))
  let lg : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int) + s
  if lg > 1025 then .inf neg else if lg < -1080 then .fin neg 0 (-1074) else
  if b &&& (b - 1) == 0 then ofNatExp neg a (s - (Nat.log2 b : Int)) else
  if s ≥ 0 then F64.ofRat neg (a <<< s.toNat) b else F64.ofRat neg a (b <<< (-s).toNat)

/-! ## Classification and integral values -/

@[inline] def isNaN (x : F64) : Bool := match x with | .nan => true | _ => false
@[inline] def isFinite (x : F64) : Bool := match x with | .fin .. => true | _ => false
@[inline] def isZero (x : F64) : Bool := match x with | .fin _ 0 _ => true | _ => false
/-- The sign bit (−0 and −∞ included; NaN: false). -/
@[inline] def signBit (x : F64) : Bool := match x with | .fin n _ _ | .inf n => n | .nan => false

def abs : F64 → F64
  | .nan => .nan
  | .inf _ => .inf false
  | .fin _ m e => .fin false m e

/-- ⌊log2 |x|⌋ of a finite nonzero x = m·2^e. -/
@[inline] def ilog2 (m : Nat) (e : Int) : Int := (Nat.log2 m : Int) + e

/-- Whether m·2^e is an integer. -/
@[inline] def intMag (m : Nat) (e : Int) : Bool :=
  e ≥ 0 || ((m >>> (-e).toNat) <<< (-e).toNat) == m

/-- Whether a Number is an integral Number (finite, no fractional part).
spec: https://tc39.es/ecma262/#sec-isintegralnumber -/
def isIntegral : F64 → Bool
  | .fin _ m e => intMag m e
  | _ => false

/-- |m·2^e| truncated toward zero. -/
@[inline] def truncMag (m : Nat) (e : Int) : Nat :=
  if e ≥ 0 then m <<< e.toNat else m >>> (-e).toNat

/-- The mathematical value truncated toward zero, of a finite Number (0 for NaN and ±∞). -/
def truncInt : F64 → Int
  | .fin n m e => if n then -(truncMag m e : Int) else truncMag m e
  | _ => 0

/-- Whether x is an odd integral Number. -/
def isOddInt : F64 → Bool
  | .fin _ m e => intMag m e && (if e > 0 then false else (m >>> (-e).toNat) % 2 == 1)
  | _ => false

/-- The exact integer value of an integral Number (`none` otherwise). -/
def toInt? (x : F64) : Option Int := if isIntegral x then some (truncInt x) else none

/-- truncate(ℝ(x)) as a Number: −0 for x in (−1, 0), sign kept; NaN and ±∞ unchanged. -/
def trunc (x : F64) : F64 :=
  match x with
  | .fin n m e => if intMag m e then x else ofNatExp n (truncMag m e) 0
  | _ => x

/-- ToIntegerOrInfinity's numeric part: NaN and ±0 → +0, ±∞ kept, else truncated (+0 for
results in (−1, 1)).
spec: https://tc39.es/ecma262/#sec-tointegerorinfinity -/
def toIntegerOrInfinity (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => posZero
  -- 3.
  | .inf _ => x
  | .fin n m e =>
    -- 4-5.
    let t := truncMag m e
    if t == 0 then posZero else if intMag m e then x else ofNatExp n t 0

/-- ToIntegerOrInfinity clamped to [lo, hi] as an integer (the common use: relative indices). -/
def toIntegerClamp (x : F64) (lo hi : Int) : Int :=
  match x with
  | .nan => max lo (min hi 0)
  | .inf n => if n then lo else hi
  | _ => max lo (min hi (truncInt x))

/-! ## Comparison and equality -/

/-- Compares two finite magnitudes m·2^e and n·2^f exactly. -/
def cmpMag (m : Nat) (e : Int) (n : Nat) (f : Int) : Ordering :=
  if m == 0 then (if n == 0 then .eq else .lt) else if n == 0 then .gt else
  let a := ilog2 m e
  let b := ilog2 n f
  if a < b then .lt else if a > b then .gt else
  let g := min e f
  compare (m <<< (e - g).toNat) (n <<< (f - g).toNat)

/-- Compares two non-NaN Numbers (−0 = +0); `none` if either is NaN. -/
def cmp (x y : F64) : Option Ordering :=
  match x, y with
  | .nan, _ | _, .nan => none
  | .inf a, .inf b => some (if a == b then .eq else if a then .lt else .gt)
  | .inf a, _ => some (if a then .lt else .gt)
  | _, .inf b => some (if b then .gt else .lt)
  | .fin a m e, .fin b n f =>
    if m == 0 && n == 0 then some .eq
    else if (a && m != 0) != (b && n != 0) then
      -- (different signs, zeros counted as positive)
      some (if a && m != 0 then .lt else .gt)
    else
      let c := cmpMag m e n f
      some (if a && m != 0 then c.swap else c)

/-- Number::lessThan: `none` stands for undefined (a NaN operand).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-lessThan -/
def lessThan (x y : F64) : Option Bool := (cmp x y).map (· == .lt)

/-- Number::equal.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-equal -/
def equal (x y : F64) : Bool := cmp x y == some .eq

/-- Number::sameValue (NaN is NaN; +0 is not −0): values are canonical, so structural equality.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-sameValue -/
def sameValue (x y : F64) : Bool := x == y

/-- Number::sameValueZero.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-sameValueZero -/
def sameValueZero (x y : F64) : Bool := (isZero x && isZero y) || x == y

/-- Number::unaryMinus.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-unaryMinus -/
def unaryMinus (x : F64) : F64 := x.neg

/-! ## Integer conversions -/

/-- ℝ(truncate(x)) modulo 2^bits for a Number (0 for NaN, ±∞). -/
def toUintMod (bits : Nat) : F64 → Nat
  | .fin n m e =>
    let i : Nat := if e ≥ 0 then (if e ≥ (bits : Int) then 0 else (m <<< e.toNat) % (1 <<< bits))
      else (m >>> (-e).toNat) % (1 <<< bits)
    if n && i != 0 then (1 <<< bits) - i else i
  | _ => 0

/-- The signed view of an unsigned `bits`-bit integer. -/
@[inline] def signedOf (bits : Nat) (u : Nat) : Int :=
  if u ≥ 1 <<< (bits - 1) then (u : Int) - (1 <<< bits : Nat) else u

/-- spec: https://tc39.es/ecma262/#sec-toint32 -/
def toInt32 (x : F64) : Int := signedOf 32 (toUintMod 32 x)
/-- spec: https://tc39.es/ecma262/#sec-touint32 -/
def toUint32 (x : F64) : Nat := toUintMod 32 x
/-- spec: https://tc39.es/ecma262/#sec-toint16 -/
def toInt16 (x : F64) : Int := signedOf 16 (toUintMod 16 x)
/-- spec: https://tc39.es/ecma262/#sec-touint16 -/
def toUint16 (x : F64) : Nat := toUintMod 16 x
/-- spec: https://tc39.es/ecma262/#sec-toint8 -/
def toInt8 (x : F64) : Int := signedOf 8 (toUintMod 8 x)
/-- spec: https://tc39.es/ecma262/#sec-touint8 -/
def toUint8 (x : F64) : Nat := toUintMod 8 x

/-- ToUint8Clamp: round half to even into [0, 255].
spec: https://tc39.es/ecma262/#sec-touint8clamp -/
def toUint8Clamp (x : F64) : Nat :=
  match x with
  -- 2.
  | .nan => 0
  | .inf n => if n then 0 else 255
  | .fin n m e =>
    -- 3-4.
    if n || m == 0 then 0 else
    if cmpMag m e 255 0 != .lt then 255 else
    -- 5-10. (f = floor(x); round half to even)
    let f := truncMag m e
    if e ≥ 0 then f else
    let k := (-e).toNat
    let r := m - (f <<< k)
    let half := 1 <<< (k - 1)
    if r > half then f + 1 else if r < half then f else if f % 2 == 0 then f else f + 1

/-! ## Bitwise operators and shifts -/

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-bitwiseNOT -/
def bitwiseNOT (x : F64) : F64 := ofInt (signedOf 32 (0xFFFFFFFF - toUint32 x))

/-- spec: https://tc39.es/ecma262/#sec-numberbitwiseop -/
def bitwiseAND (x y : F64) : F64 := ofInt (signedOf 32 (toUint32 x &&& toUint32 y))
/-- spec: https://tc39.es/ecma262/#sec-numberbitwiseop -/
def bitwiseOR (x y : F64) : F64 := ofInt (signedOf 32 (toUint32 x ||| toUint32 y))
/-- spec: https://tc39.es/ecma262/#sec-numberbitwiseop -/
def bitwiseXOR (x y : F64) : F64 := ofInt (signedOf 32 (toUint32 x ^^^ toUint32 y))

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-leftShift -/
def leftShift (x y : F64) : F64 :=
  -- 1-4.
  let shift := toUint32 y % 32
  -- 5.
  ofInt (signedOf 32 ((toUint32 x <<< shift) % (1 <<< 32)))

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-signedRightShift -/
def signedRightShift (x y : F64) : F64 :=
  let shift := toUint32 y % 32
  ofInt (toInt32 x >>> shift)

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-unsignedRightShift -/
def unsignedRightShift (x y : F64) : F64 :=
  let shift := toUint32 y % 32
  ofNat (toUint32 x >>> shift)

/-! ## Arithmetic -/

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-add -/
def add (x y : F64) : F64 := F64.add x y
/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-subtract -/
def sub (x y : F64) : F64 := F64.sub x y
/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-multiply -/
def mul (x y : F64) : F64 := F64.mul x y
/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-divide -/
def div (x y : F64) : F64 := F64.div x y

/-- Number::remainder: exact (the result is always representable).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-remainder -/
def remainder (n d : F64) : F64 :=
  match n, d with
  -- 1.
  | .nan, _ | _, .nan => .nan
  -- 2.
  | .inf _, _ => .nan
  -- 3.
  | _, .inf _ => n
  -- 4.
  | _, .fin _ 0 _ => .nan
  -- 5.
  | .fin _ 0 _, _ => n
  | .fin sn m e, .fin _ k f =>
    -- 7-9. (r = n − d·truncate(n/d), over the smaller exponent's power of two)
    if cmpMag m e k f == .lt then n else
    let g := min e f
    let r := (m <<< (e - g).toNat) % (k <<< (f - g).toNat)
    -- 10-11.
    ofNatExp sn r g

/-! ## Rounding to integers (Math.floor, ceil, trunc, round) -/

/-- spec: https://tc39.es/ecma262/#sec-math.floor -/
def floor (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    -- 2-3.
    if m == 0 || intMag m e then x
    -- 4.
    else if !n then ofNatExp false (truncMag m e) 0
    -- 5.
    else ofNatExp true (truncMag m e + 1) 0
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.ceil -/
def ceil (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    if m == 0 || intMag m e then x
    -- (−0 for x in (−1, 0))
    else if n then ofNatExp true (truncMag m e) 0
    else ofNatExp false (truncMag m e + 1) 0
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.round -/
def round (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    -- 2.
    if m == 0 || intMag m e then x else
    let k := (-e).toNat
    -- (|x| = m / 2^k with k ≥ 1; floor(x + 1/2))
    if !n then
      -- 3, 5.
      ofNatExp false ((m + (1 <<< (k - 1))) >>> k) 0
    else
      -- 4, 5. (−floor(−|x| + 1/2) = ceil(|x| − 1/2): ties toward +∞; −0 for x in [−0.5, 0))
      let t := (m + (1 <<< (k - 1)) - 1) >>> k
      ofNatExp true t 0
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.sign -/
def sign (x : F64) : F64 :=
  match x with
  | .nan => .nan
  | .fin _ 0 _ => x
  | .fin n _ _ | .inf n => if n then negOne else one

/-! ## Number::toString -/

def digitChars : Array Char := "0123456789abcdefghijklmnopqrstuvwxyz".toList.toArray

@[inline] def digitChar (d : Nat) : Char := digitChars[d]?.getD '?'

/-- The digits of `n` in `radix` (2–36), most significant first, at least `width` digits
(zero-padded). Divide and conquer over radix^(c·2^i) for large values (quadratic only in the
chunk size).
Fuel: level `lvl` handles n < P_lvl = radix^(c·2^lvl); the top level is the first whose bound
exceeds n, found by squaring (at most log2 of n's bit length + 1 levels). -/
def natDigits (n : Nat) (radix : Nat := 10) (width : Nat := 0) : String :=
  let radix := if radix < 2 then 10 else radix
  -- (the chunk: c digits with radix^c < 2^60)
  let c := 60 / (Nat.log2 radix + 1)
  let p0 := radix ^ c
  -- (powers P_i = p0^(2^i) while P_i ≤ n)
  let rec pows (fuel : Nat) (acc : Array Nat) (p : Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | f + 1 => if p > n then acc.push p else pows f (acc.push p) (p * p)
  let ps := pows 64 #[] p0
  let small (v : Nat) (w : Nat) : String := Id.run do
    let mut v := v
    let mut cs : Array Char := #[]
    while v > 0 do
      cs := cs.push (digitChar (v % radix))
      v := v / radix
    while cs.size < w do cs := cs.push '0'
    return String.ofList cs.toList.reverse
  -- (level i: n < ps[i]; split by ps[i-1])
  let rec go : Nat → Nat → Nat → String
    | 0, v, w => small v w
    | lvl + 1, v, w =>
      let d := ps[lvl]!
      let hi := v / d
      let lo := v % d
      let half := c * 2 ^ lvl
      if hi == 0 then go lvl lo w
      else go lvl hi (w - min w half) ++ go lvl lo half
  let s := go (ps.size - 1) n width
  if s.isEmpty then "0" else s

/-- Number::toString's digits for radix 10: `n` and the k-digit `s` with s·10^(n−k) = x, k as
small as possible, and among those the s closest to x (the even one on a tie), for a finite
positive x = m·2^e.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring (step 5 and Note 2) -/
def shortestDigits (m : Nat) (e : Int) : Nat × Int :=
  -- (the values that round to x: [L, H] · 2^(e−2), ends included iff m is even; the gap below
  -- a power of two is half as wide)
  let lowerHalf := m == 2 ^ 52 && e > -1074
  let V := 4 * m
  let L := if lowerHalf then 4 * m - 1 else 4 * m - 2
  let H := 4 * m + 2
  let incl := m % 2 == 0
  let E := e - 2
  -- (X · 2^E / 10^p = X · A / B)
  let scale (p : Int) : Nat × Nat :=
    ((1 <<< (max E 0).toNat) * 10 ^ (max (-p) 0).toNat, (1 <<< (max (-E) 0).toNat) * 10 ^ (max p 0).toNat)
  -- (the integers s with s · 10^p in the interval)
  let range (p : Int) : Nat × Nat × Nat × Nat :=
    let (A, B) := scale p
    let lo := L * A
    let hi := H * A
    let sLo := if lo % B == 0 then (if incl then lo / B else lo / B + 1) else lo / B + 1
    let sHi := if hi % B == 0 then (if incl then hi / B else hi / B - 1) else hi / B
    (sLo, sHi, A, B)
  let works (p : Int) : Bool := let (a, b, _, _) := range p; a ≤ b
  let b := ilog2 m e
  -- (⌊b · log10 2⌋ within one: 78913 / 2^18 ≈ log10 2)
  let lg (t : Int) : Int := (t * 78913) >>> 18
  let loP := lg b - 18
  let hiP := lg (b + 1) + 2
  -- (the largest p that works: `works` is monotone, `loP` works since 17 digits always suffice)
  let rec search : Nat → Int → Int → Int
    | 0, lo, _ => lo
    | f + 1, lo, hi =>
      if lo ≥ hi then lo else
      let mid := (lo + hi + 1) / 2
      if works mid then search f mid hi else search f lo (mid - 1)
  let p := search 64 loP hiP
  let (sLo, sHi, A, B) := range p
  -- (the closest: V·A/B rounded half to even, within [sLo, sHi])
  let num := V * A
  let q := num / B
  let r := num - q * B
  let s0 := if 2 * r > B || (2 * r == B && q % 2 == 1) then q + 1 else q
  let s := max sLo (min sHi s0)
  let k := (toString s).length
  (s, p + k)

/-- Formats a decimal s·10^(n−k) (k = digits of s) as Number::toString steps 6-12 do.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring -/
def formatDecimal (neg : Bool) (s : Nat) (n : Int) : String :=
  let ds := toString s
  let k : Int := ds.length
  let sign := if neg then "-" else ""
  let zeros (c : Nat) : String := String.ofList (List.replicate c '0')
  let expPart (x : Int) : String := "e" ++ (if x ≥ 0 then "+" else "-") ++ toString x.natAbs
  -- 6.
  if k ≤ n && n ≤ 21 then sign ++ ds ++ zeros (n - k).toNat
  -- 7.
  else if 0 < n && n ≤ 21 then
    sign ++ String.ofList (ds.toList.take n.toNat) ++ "." ++ String.ofList (ds.toList.drop n.toNat)
  -- 8.
  else if -6 < n && n ≤ 0 then sign ++ "0." ++ zeros (-n).toNat ++ ds
  -- 9-10.
  else if k == 1 then sign ++ ds ++ expPart (n - 1)
  else sign ++ String.ofList (ds.toList.take 1) ++ "." ++ String.ofList (ds.toList.drop 1) ++ expPart (n - 1)

/-- Number::toString(x, 10).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring -/
def toStringDec (x : F64) : String :=
  match x with
  -- 2.
  | .nan => "NaN"
  -- 3.
  | .fin _ 0 _ => "0"
  -- 5.
  | .inf n => if n then "-Infinity" else "Infinity"
  | .fin n m e =>
    -- (integers below 2^53: their own digits)
    if e == 0 then (if n then "-" else "") ++ toString m
    else if e < 0 && e > -53 && intMag m e then (if n then "-" else "") ++ toString (m >>> (-e).toNat)
    else
      -- 4, 6-12.
      let (s, k) := shortestDigits m e
      formatDecimal n s k

/-! ### Other radices

Number::toString leaves the digits for radices other than 10 implementation-defined beyond
"a generalization of" the radix-10 algorithm; browsers agree with V8's `DoubleToRadixCString`:
fractional digits until the value is uniquely identified (delta = half the gap to the next Number,
scaled with each digit), rounded half to even, and the integer part from repeated division. Its
double arithmetic is reproduced here with the exactly rounded `F64` operations. -/

/-- The next Number above a finite positive one. -/
def nextUp (x : F64) : F64 :=
  match x with
  | .fin false m e =>
    if m + 1 == 2 ^ 53 then (if e + 1 > 971 then .inf false else .fin false (2 ^ 52) (e + 1))
    else .fin false (m + 1) e
  | _ => x

/-- V8's `Double::Exponent` (canonical forms already carry it). -/
@[inline] def v8Exponent : F64 → Int
  | .fin _ _ e => e
  | _ => 0

/-- Number::toString(x, radix) for radix ≠ 10, finite nonzero x (V8's `DoubleToRadixCString`).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring -/
def toStringRadixV8 (x : F64) (radix : Nat) : String :=
  let negative := signBit x
  let value := abs x
  let rdx := ofNat radix
  let integer := floor value
  let fraction := F64.sub value integer
  let delta0 := F64.mul (.fin false (2 ^ 52) (-53)) (F64.sub (nextUp value) value)
  let delta0 := F64.max delta0 (.fin false 1 (-1074))
  -- (fraction digits; `carry`: whether the integer part gets one more)
  -- Fuel: delta grows by radix ≥ 2 each step from ≥ 2^-1074 and the loop stops once
  -- delta > fraction (< 1), so 1100 steps suffice.
  let rec carryBack : Nat → Array Nat → Array Nat × Bool
    | 0, ds => (ds, true)
    | f + 1, ds =>
      match ds.back? with
      | none => (ds, true)
      | some d => if d + 1 < radix then (ds.pop.push (d + 1), false) else carryBack f ds.pop
  let rec fracLoop : Nat → F64 → F64 → Array Nat → Array Nat × Bool
    | 0, _, _, ds => (ds, false)
    | f + 1, fraction, delta, ds =>
      let fraction := F64.mul fraction rdx
      let delta := F64.mul delta rdx
      let digit := truncMag' fraction
      let ds := ds.push digit
      let fraction := F64.sub fraction (ofNat digit)
      let half : F64 := .fin false (2 ^ 52) (-53)
      let up := F64.lt half fraction || (fraction == half && digit % 2 == 1)
      if up && F64.lt one (F64.add fraction delta) then carryBack (ds.size + 1) ds
      else if F64.lt fraction delta then (ds, false)
      else fracLoop f fraction delta ds
  let (fds, carry) := if F64.lt fraction delta0 then (#[], false)
    else fracLoop 1100 fraction delta0 #[]
  let integer := if carry then F64.add integer one else integer
  -- (integer digits; below the top 53 bits, zeros)
  -- Fuel: each step divides by radix ≥ 2 a value below 2^1024.
  let rec zeroLoop : Nat → F64 → Nat → F64 × Nat
    | 0, i, z => (i, z)
    | f + 1, i, z =>
      if v8Exponent (F64.div i rdx) > 0 then zeroLoop f (F64.div i rdx) (z + 1) else (i, z)
  let (integer, nz) := zeroLoop 1100 integer 0
  let rec intLoop : Nat → F64 → List Char → List Char
    | 0, _, acc => acc
    | f + 1, i, acc =>
      let r := remainder i rdx
      let acc := digitChar (truncMag' r) :: acc
      let i := F64.div (F64.sub i r) rdx
      if F64.lt posZero i then intLoop f i acc else acc
  let ids := intLoop 1100 integer []
  let s := String.ofList ids ++ String.ofList (List.replicate nz '0')
  let s := if fds.isEmpty then s else s ++ "." ++ String.ofList (fds.toList.map digitChar)
  if negative then "-" ++ s else s
where
  truncMag' : F64 → Nat
    | .fin _ m e => truncMag m e
    | _ => 0

/-- Number::toString(x, radix), radix in 2..36.
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring -/
def toStringRadix (x : F64) (radix : Nat := 10) : String :=
  if radix == 10 then toStringDec x else
  match x with
  | .nan => "NaN"
  | .fin _ 0 _ => "0"
  | .inf n => if n then "-Infinity" else "Infinity"
  | .fin n m e =>
    -- (integers below 2^53: exact digits, as V8's algorithm gives them too)
    if intMag m e && e ≤ 0 then (if n then "-" else "") ++ natDigits (truncMag m e) radix
    else toStringRadixV8 x radix

/-- Number::toString(x, radix) as a String value. -/
def toJSStr (x : F64) (radix : Nat := 10) : JSStr := JSStr.ofString (toStringRadix x radix)

/-! ## StringToNumber, parseFloat, parseInt -/

/-- StrWhiteSpaceChar: WhiteSpace (incl. every Zs code point and U+FEFF) or LineTerminator.
spec: https://tc39.es/ecma262/#prod-StrWhiteSpaceChar -/
def isStrWhiteSpace (u : UInt16) : Bool :=
  u == 0x20 || (0x09 ≤ u && u ≤ 0x0D) || u == 0xA0 || u == 0x1680 || (0x2000 ≤ u && u ≤ 0x200A) ||
  u == 0x2028 || u == 0x2029 || u == 0x202F || u == 0x205F || u == 0x3000 || u == 0xFEFF

/-- The value of a digit code unit in radices up to 36 (99 for a non-digit). -/
@[inline] def digitVal (u : UInt16) : Nat :=
  if 0x30 ≤ u && u ≤ 0x39 then (u - 0x30).toNat
  else if 0x61 ≤ u && u ≤ 0x7A then (u - 0x61).toNat + 10
  else if 0x41 ≤ u && u ≤ 0x5A then (u - 0x41).toNat + 10
  else 99

/-- The Number value for mant · 10^exp10 (correctly rounded; the parser's numeric literals and
StringToNumber's decimal forms).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-mv-s (the MV, then RoundMVResult) -/
def ofDecimalLiteral (mant : Nat) (exp10 : Int) (neg : Bool := false) : F64 :=
  if mant == 0 then .fin neg 0 (-1074) else
  let lb : Int := Nat.log2 mant
  -- (mant · 10^exp10 ≥ 10^(0.30102·lb + exp10), < 10^(0.30103·(lb+1) + exp10))
  if lb * 30102 / 100000 + exp10 > 309 then .inf neg
  else if (lb + 1) * 30103 / 100000 + 1 + exp10 < -324 then .fin neg 0 (-1074)
  else if exp10 ≥ 0 then ofNatExp neg (mant * 10 ^ exp10.toNat) 0
  else F64.ofRat neg mant (10 ^ (-exp10).toNat)

/-- A scanned decimal: value mant · 10^exp10, the literal ending before `stop`. -/
structure DecScan where
  mant : Nat
  exp10 : Int
  stop : Nat

/-- Significant digits kept from a decimal literal: more never change the rounding
(binary64 needs at most 767), the rest only as a sticky nonzero digit. -/
def maxSigDigits : Nat := 800

/-- Scans StrUnsignedDecimalLiteral (without `Infinity`) from `i` up to `j`: the longest prefix
that is one. `none` if there is none.
spec: https://tc39.es/ecma262/#prod-StrUnsignedDecimalLiteral -/
def scanUnsignedDecimal (s : JSStr) (i j : Nat) : Option DecScan := Id.run do
  let mut pos := i
  let mut mant := 0
  let mut nsig := 0
  let mut exp10 : Int := 0
  let mut sticky := false
  let mut nd := 0
  -- (DecimalDigits)
  while pos < j && digitVal (s.get pos) < 10 do
    let d := digitVal (s.get pos)
    if nsig < maxSigDigits then
      mant := mant * 10 + d
      if mant != 0 then nsig := nsig + 1
    else
      exp10 := exp10 + 1
      if d != 0 then sticky := true
    pos := pos + 1
    nd := nd + 1
  -- (. DecimalDigits_opt)
  if pos < j && s.get pos == 0x2E then
    let save := pos
    pos := pos + 1
    let mut fd := 0
    while pos < j && digitVal (s.get pos) < 10 do
      let d := digitVal (s.get pos)
      if nsig < maxSigDigits then
        mant := mant * 10 + d
        if mant != 0 then nsig := nsig + 1
        exp10 := exp10 - 1
      else if d != 0 then sticky := true
      pos := pos + 1
      fd := fd + 1
    if nd == 0 && fd == 0 then pos := save
    nd := nd + fd
  if nd == 0 then return none
  -- (ExponentPart_opt: only with digits)
  if pos < j && (s.get pos == 0x65 || s.get pos == 0x45) then
    let mut q := pos + 1
    let mut eneg := false
    if q < j && (s.get q == 0x2B || s.get q == 0x2D) then
      eneg := s.get q == 0x2D
      q := q + 1
    if q < j && digitVal (s.get q) < 10 then
      let mut ev : Nat := 0
      while q < j && digitVal (s.get q) < 10 do
        -- (capped: past 10^10 the result is 0 or ∞ whatever the digits)
        ev := min (ev * 10 + digitVal (s.get q)) 10000000000
        q := q + 1
      exp10 := exp10 + (if eneg then -(ev : Int) else ev)
      pos := q
  if sticky then
    mant := mant * 10 + 1
    exp10 := exp10 - 1
  return some { mant, exp10, stop := pos }

/-- The index of the first unit at or after `i` that is not StrWhiteSpaceChar. -/
def skipWS (s : JSStr) (i : Nat) : Nat := Id.run do
  let mut i := i
  while i < s.length && isStrWhiteSpace (s.get i) do i := i + 1
  return i

/-- The index after the last unit before `j` that is not StrWhiteSpaceChar (≥ i). -/
def trimEnd (s : JSStr) (i j : Nat) : Nat := Id.run do
  let mut j := j
  while j > i && isStrWhiteSpace (s.get (j - 1)) do j := j - 1
  return j

/-- Whether s[i, i+8) is `Infinity`. -/
def isInfinityAt (s : JSStr) (i : Nat) : Bool :=
  s.matchesAt "Infinity" i

/-- The value of digits s[i, j) in a power-of-two-or-any radix, exactly; `none` if one is not a
digit of the radix (or there are none). -/
def radixDigits (s : JSStr) (i j : Nat) (radix : Nat) : Option Nat := Id.run do
  if i ≥ j then return none
  let mut v := 0
  for k in [i:j] do
    let d := digitVal (s.get k)
    if d ≥ radix then return none
    v := v * radix + d
  return some v

/-- StringToNumber: the StringNumericLiteral grammar over String values, correctly rounded.
spec: https://tc39.es/ecma262/#sec-stringtonumber -/
def stringToNumber (str : JSStr) : F64 := Id.run do
  -- 1-2. (StrWhiteSpace_opt StrNumericLiteral StrWhiteSpace_opt)
  let i := skipWS str 0
  let j := trimEnd str i str.length
  -- (StrWhiteSpace_opt alone: 0)
  if i == j then return posZero
  -- (NonDecimalIntegerLiteral)
  if j - i > 2 && str.get i == 0x30 then
    let c := str.get (i + 1)
    let radix := if c == 0x78 || c == 0x58 then 16 else if c == 0x6F || c == 0x4F then 8
      else if c == 0x62 || c == 0x42 then 2 else 0
    if radix != 0 then
      return match radixDigits str (i + 2) j radix with
        | some v => ofNat v
        | none => .nan
  -- (StrDecimalLiteral)
  let (neg, k) := if str.get i == 0x2D then (true, i + 1)
    else if str.get i == 0x2B then (false, i + 1) else (false, i)
  if j - k == 8 && isInfinityAt str k then return .inf neg
  match scanUnsignedDecimal str k j with
  | some d => if d.stop == j then ofDecimalLiteral d.mant d.exp10 neg else .nan
  | none => .nan

/-- `parseFloat(string)` after ToString: the longest prefix that is a StrDecimalLiteral.
spec: https://tc39.es/ecma262/#sec-parsefloat-string -/
def parseFloat (str : JSStr) : F64 :=
  -- 2.
  let i := skipWS str 0
  let n := str.length
  let (neg, k) := if i < n && str.get i == 0x2D then (true, i + 1)
    else if i < n && str.get i == 0x2B then (false, i + 1) else (false, i)
  -- 3-4.
  if isInfinityAt str k then .inf neg else
  match scanUnsignedDecimal str k n with
  -- 5.
  | some d => ofDecimalLiteral d.mant d.exp10 neg
  | none => .nan

/-- V8's accumulation for parseInt in radices other than 2, 4, 8, 10, 16, 32 (which the spec
leaves implementation-approximated): chunks of digits whose multiplier stays within
0xFFFFFFFF / 36, folded into the result by result · multiplier + part in double arithmetic.
spec: https://tc39.es/ecma262/#sec-parseint-string-radix (step 14's approximation) -/
def parseIntGeneric (s : JSStr) (i j : Nat) (radix : Nat) : F64 := Id.run do
  let maxMul := 0xFFFFFFFF / 36
  let mut res := posZero
  let mut part := 0
  let mut mult := 1
  for k in [i:j] do
    let d := digitVal (s.get k)
    if mult * radix > maxMul then
      res := fma res mult part
      part := 0
      mult := 1
    part := part * radix + d
    mult := mult * radix
  res := fma res mult part
  return res
where
  /-- r · m + p rounded once (V8's compiled `result * multiplier + part` is a fused
  multiply-add on arm64; r is a nonnegative integer or 0). -/
  fma (r : F64) (m p : Nat) : F64 :=
    match r with
    | .fin _ rm re => ofNatExp false (truncMag rm re * m + p) 0
    | _ => r

/-- `parseInt(string, radix)` after ToString(string) and ToInt32(radix).
spec: https://tc39.es/ecma262/#sec-parseint-string-radix -/
def parseInt (str : JSStr) (radix : Int) : F64 := Id.run do
  let n := str.length
  -- 2.
  let i := skipWS str 0
  -- 3-5.
  let neg := i < n && str.get i == 0x2D
  let i := if i < n && (str.get i == 0x2D || str.get i == 0x2B) then i + 1 else i
  -- 6-9.
  let mut R : Nat := 10
  let mut stripPrefix := true
  if radix != 0 then
    if radix < 2 || radix > 36 then return .nan
    R := radix.toNat
    if R != 16 then stripPrefix := false
  -- 10.
  let mut i := i
  if stripPrefix && i + 2 ≤ n && str.get i == 0x30 && (str.get (i + 1) == 0x78 || str.get (i + 1) == 0x58) then
    i := i + 2
    R := 16
  -- 11-12.
  let mut j := i
  while j < n && digitVal (str.get j) < R do j := j + 1
  -- 13.
  if j == i then return .nan
  -- 14-16.
  let v := if R == 10 || R == 2 || R == 4 || R == 8 || R == 16 || R == 32 then
      ofNat ((radixDigits str i j R).getD 0)
    else parseIntGeneric str i j R
  return if neg then v.neg else v

/-! ## High-precision evaluation

Fixed-point values: an `Int` y stands for y / 2^q at precision q. The constants are computed
once, to `constBits` bits; the series below truncate each term (errors of a unit or two per term)
and are evaluated with 64 guard bits (`approx`), far more than their accumulated error. -/

/-- Bits of the precomputed constants (π, ln 2, ln 10): the largest working precision is
`80 · 2^5` + 64 guard bits + at most 1100 bits for results near zero or 1025 bits of argument
reduction (never both) + small margins, below 4000. -/
def constBits : Nat := 4400

/-- 2^p · Σ_k (±1)^k / ((2k+1)·x^(2k+1)): atan(1/x) (alternating) or atanh(1/x), each term
rounded down (error < 2 per term).
Fuel: the power 2^p / x^(2k+1) shrinks by x² ≥ 4 per term, so it is 0 after p/2 + 1 terms. -/
def arcSeries (x : Nat) (alt : Bool) (p : Nat) : Int :=
  let rec go : Nat → Nat → Nat → Int → Int
    | 0, _, _, acc => acc
    | f + 1, k, pw, acc =>
      if pw == 0 then acc else
      let t : Int := (pw / (2 * k + 1) : Nat)
      go f (k + 1) (pw / (x * x)) (if alt && k % 2 == 1 then acc - t else acc + t)
  go (p / 2 + 1) 0 ((1 <<< p) / x) 0

/-- π · 2^constBits (Machin: π = 16 atan(1/5) − 4 atan(1/239)), within 1. -/
def piBig : Nat :=
  (16 * arcSeries 5 true (constBits + 32) - 4 * arcSeries 239 true (constBits + 32)).toNat >>> 32
/-- ln 2 · 2^constBits (2 atanh(1/3)), within 1. -/
def ln2Big : Nat := (2 * arcSeries 3 false (constBits + 32)).toNat >>> 32
/-- ln 10 · 2^constBits (3 ln 2 + 2 atanh(1/9)), within 1. -/
def ln10Big : Nat :=
  (6 * arcSeries 3 false (constBits + 32) + 2 * arcSeries 9 false (constBits + 32)).toNat >>> 32

@[inline] def scaledConst (big : Nat) (q : Nat) : Int :=
  if q ≤ constBits then ((big >>> (constBits - q) : Nat) : Int) else ((big <<< (q - constBits) : Nat) : Int)
/-- π at precision q. -/
def piQ (q : Nat) : Int := scaledConst piBig q
/-- ln 2 at precision q. -/
def ln2Q (q : Nat) : Int := scaledConst ln2Big q
/-- ln 10 at precision q. -/
def ln10Q (q : Nat) : Int := scaledConst ln10Big q

/-- z · 2^k. -/
@[inline] def shl (z : Int) (k : Nat) : Int :=
  if z ≥ 0 then ((z.toNat <<< k : Nat) : Int) else -(((-z).toNat <<< k : Nat) : Int)

/-- z · 2^k for an integer k (floor when k < 0). -/
@[inline] def shiftI (z : Int) (k : Int) : Int := if k ≥ 0 then shl z k.toNat else z >>> (-k).toNat

/-- a / (2^q · d), truncated toward zero. -/
@[inline] def divT (a : Int) (q : Nat) (d : Nat) : Int :=
  if a ≥ 0 then (((a.toNat >>> q) / d : Nat) : Int) else -((((-a).toNat >>> q) / d : Nat) : Int)

/-- trunc(x · 2^q) for x = (−1)^n · m · 2^e. -/
def fixOf (n : Bool) (m : Nat) (e : Int) (q : Nat) : Int :=
  let v : Nat := truncMag m (e + q)
  if n then -(v : Int) else v

/-- The exact value m·2^e as a fraction a / b (b a power of two). -/
@[inline] def ratOf (m : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (m <<< e.toNat, 1) else (m, 1 <<< (-e).toNat)

/-- exp(r) · 2^q for |r| ≤ 1: r / 2^8 by the Taylor series, then squared 8 times.
Fuel: the terms shrink by 2^-8/i, so they vanish after q/8 + 1 steps. -/
def expFix (q : Nat) (r : Int) : Int :=
  let r' := divT r 8 1
  let rec taylor : Nat → Nat → Int → Int → Int
    | 0, _, _, acc => acc
    | f + 1, i, term, acc =>
      let t := divT (term * r') q i
      if t == 0 then acc else taylor f (i + 1) t (acc + t)
  let one : Int := ((1 <<< q : Nat) : Int)
  let rec sq : Nat → Int → Int
    | 0, y => y
    | f + 1, y => sq f ((y * y) >>> q)
  sq 8 (taylor (q + 2) 1 one one)

/-- (sin r, cos r) · 2^q for |r| ≤ 1 (Taylor series).
Fuel: the terms shrink by r²/((k+1)(k+2)) ≤ 1/2, so they vanish within q + 1 steps. -/
def sinCosFix (q : Nat) (r : Int) : Int × Int :=
  let r2 := (r * r) >>> q
  let rec ser : Nat → Nat → Int → Int → Int
    | 0, _, _, acc => acc
    | f + 1, k, term, acc =>
      let t := -(divT (term * r2) q ((k + 1) * (k + 2)))
      if t == 0 then acc else ser f (k + 2) t (acc + t)
  let one : Int := ((1 <<< q : Nat) : Int)
  (ser (q + 2) 1 r r, ser (q + 2) 0 one one)

/-- atan(z) · 2^q for |z| ≤ 1: three halvings z ↦ z / (1 + √(1 + z²)) (to |z| ≤ 0.1), then the
series Σ (−1)^k z^(2k+1) / (2k+1), times 8.
Fuel: the powers shrink by z² ≤ 0.01 per term, so they vanish within q/6 + 1 steps. -/
def atanFix (q : Nat) (z : Int) : Int :=
  let one : Nat := 1 <<< q
  let red (z : Int) : Int :=
    let s := Nat.sqrt ((one * one) + (z * z).toNat)
    (shl z q).tdiv ((one + s : Nat) : Int)
  let z := red (red (red z))
  let z2 := (z * z) >>> q
  let rec ser : Nat → Nat → Int → Int → Int
    | 0, _, _, acc => acc
    | f + 1, k, pw, acc =>
      if pw == 0 then acc else
      ser f (k + 1) (-(divT (pw * z2) q 1)) (acc + pw.tdiv ((2 * k + 1 : Nat) : Int))
  8 * ser (q + 2) 0 z 0

/-- log(a / b) · 2^q for a, b > 0: a/b = f · 2^t with f ∈ [0.7, 1.4), log f = 2 atanh((f−1)/(f+1))
(|z| ≤ 0.18) by its series, plus t · ln 2.
Fuel: the powers shrink by z² ≤ 0.031 per term, so they vanish within q/5 + 1 steps. -/
def logRatFix (q : Nat) (a b : Nat) : Int :=
  let t0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
  let (A, B) := if t0 ≥ 0 then (a, b <<< t0.toNat) else (a <<< (-t0).toNat, b)
  -- (A/B ∈ (1/2, 2) → [0.7, 1.4))
  let (A, B, t) := if 5 * A ≥ 7 * B then (A, 2 * B, t0 + 1)
    else if 10 * A < 7 * B then (2 * A, B, t0 - 1) else (A, B, t0)
  let z : Int := (shl ((A : Int) - (B : Int)) q).tdiv ((A + B : Nat) : Int)
  let z2 := (z * z) >>> q
  let rec ser : Nat → Nat → Int → Int → Int
    | 0, _, _, acc => acc
    | f + 1, k, pw, acc =>
      if pw == 0 then acc else
      ser f (k + 1) (divT (pw * z2) q 1) (acc + pw.tdiv ((2 * k + 1 : Nat) : Int))
  2 * ser (q + 2) 0 z 0 + ((t * ln2Q (q + 16)) >>> 16)

/-- e^(X / 2^q) ≈ E · 2^(k − q) with E ≈ e^r · 2^q, r = X/2^q − k ln 2 ∈ [−0.35, 0.35]
(|X| / 2^q at most a few thousand). -/
def expScaled (q : Nat) (X : Int) : Int × Int :=
  let L := ln2Q (q + 16)
  let XS := shl X 16
  -- (k = round(X / ln 2))
  let k := (2 * XS + L) / (2 * L)
  let r := X - ((k * L) >>> 16)
  (expFix q r, k)

/-- An approximation of a real: within err · 2^sc of v · 2^sc. -/
structure Approx where
  v : Int
  err : Nat
  sc : Int

/-- y · 2^sc, within e units of y, kept to all but `g` guard bits: truncating adds a unit, and
the error left is e / 2^g + 1. -/
@[inline] def approx (y : Int) (sc : Int) (g : Nat := 64) (e : Nat := 0) : Approx :=
  ⟨y >>> g, (e >>> g) + 2, sc + g⟩

/-- Of two adjacent Numbers, the one with an even significand (ties to even); else `mid`. -/
def tieEven (lo hi mid : F64) : F64 :=
  match lo, hi with
  | .fin _ m _, _ => if m % 2 == 0 then lo else
      match hi with | .fin _ n _ => if n % 2 == 0 then hi else mid | _ => mid
  | _, _ => mid

/-- The correctly rounded value of a real given by approximations at a requested precision
(Ziv's strategy): the first precision at which both ends of the error interval round to the
same Number; after the last, the interval holds a rounding boundary to 2^-2600 relative, which
for the algebraic and transcendental values here means the value is that boundary (an exact
midpoint, e.g. a power with a dyadic exponent): ties to even.
Fuel: precisions p0, 2·p0, …, 32·p0. -/
def ziv (f : Nat → Approx) (p0 : Nat := 80) : F64 :=
  go 6 p0
where
  go : Nat → Nat → F64
    | 0, p => let a := f p; ofIntExp a.v a.sc
    | n + 1, p =>
      let a := f p
      let lo := ofIntExp (a.v - a.err) a.sc
      let hi := ofIntExp (a.v + a.err) a.sc
      if lo == hi then lo
      else if n == 0 then tieEven lo hi (ofIntExp a.v a.sc)
      else go n (2 * p)

/-- π · 2^k, rounded, with a sign. -/
def piTimes2Pow (neg : Bool) (k : Int) (mul : Nat := 1) : F64 :=
  let y := (mul : Int) * piQ 256
  ofIntExp (if neg then -y else y) (k - 256)

/-! ## Math -/

/-- The bits of precision lost to a result near 0: ⌈−log2 |x|⌉ for |x| < 1. -/
@[inline] def lzOf (m : Nat) (e : Int) : Nat := (max 0 (-(ilog2 m e))).toNat + 1

/-- spec: https://tc39.es/ecma262/#sec-math.abs -/
def mathAbs (x : F64) : F64 := abs x

/-- spec: https://tc39.es/ecma262/#sec-math.exp -/
def exp (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  -- 3.
  | .fin _ 0 _ => one
  -- 4-5.
  | .inf n => if n then posZero else x
  | .fin n m e =>
    -- (|x| < 2^-54: within half an ulp of 1; past 710 / −746: overflow / underflow)
    if ilog2 m e < -54 then one
    else if !n && cmpMag m e 710 0 != .lt then .inf false
    else if n && cmpMag m e 746 0 != .lt then posZero
    else ziv fun p =>
      let q := p + 64
      let (E, k) := expScaled q (fixOf n m e q)
      approx E (k - q)

/-- spec: https://tc39.es/ecma262/#sec-math.expm1 -/
def expm1 (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  | .fin _ 0 _ => x
  | .inf n => if n then negOne else x
  | .fin n m e =>
    -- (|x| < 2^-54: e^x − 1 = x(1 + x/2 + …) rounds to x; below −40 to −1)
    if ilog2 m e < -54 then x
    else if !n && cmpMag m e 710 0 != .lt then .inf false
    else if n && cmpMag m e 40 0 != .lt then negOne
    else ziv fun p =>
      let q := p + 64 + lzOf m e
      let (E, k) := expScaled q (fixOf n m e q)
      -- (e^x − 1 = (E − 2^(q−k)) · 2^(k−q); past 2^q the 1 is within a unit)
      let sh : Int := (q : Int) - k
      if sh ≥ 0 then approx (E - ((1 <<< sh.toNat : Nat) : Int)) (k - q)
      else approx E (k - q) 64 1

/-- log(a/b) for a fraction a/b ≠ 1 near 1: precision lost to the result's smallness. -/
def nearOne (a b : Nat) : Nat :=
  let d : Nat := if a ≥ b then a - b else b - a
  if d == 0 then 0 else (max 0 ((Nat.log2 b : Int) - (Nat.log2 d : Int))).toNat + 1

/-- log(a/b) (a, b > 0, a ≠ b) correctly rounded, divided by ln 2 or ln 10 (`base` 2, 10) or
not (`base` 0). -/
def logOfRat (a b : Nat) (base : Nat := 0) (lz : Nat := nearOne a b) : F64 :=
  ziv fun p =>
    let q := p + 64 + lz
    let y := logRatFix q a b
    if base == 0 then approx y (-(q : Int))
    else
      let L := if base == 2 then ln2Q q else ln10Q q
      approx ((shl y q).tdiv L) (-(q : Int))

/-- The shared special cases of log, log2, log10.
spec: https://tc39.es/ecma262/#sec-math.log -/
def logBase (base : Nat) (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  | .inf n => if n then .nan else x
  | .fin n m e =>
    -- 4.
    if m == 0 then .inf true
    -- 5.
    else if n then .nan
    -- 3.
    else if m == 2 ^ 52 && e == -52 then posZero
    else let (a, b) := ratOf m e; logOfRat a b base

/-- spec: https://tc39.es/ecma262/#sec-math.log -/
def log (x : F64) : F64 := logBase 0 x
/-- spec: https://tc39.es/ecma262/#sec-math.log2 -/
def log2 (x : F64) : F64 := logBase 2 x
/-- spec: https://tc39.es/ecma262/#sec-math.log10 -/
def log10 (x : F64) : F64 := logBase 10 x

/-- spec: https://tc39.es/ecma262/#sec-math.log1p -/
def log1p (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  | .inf n => if n then .nan else x
  | .fin n m e =>
    if m == 0 then x
    else match n, cmpMag m e 1 0 with
      -- 3.
      | true, .eq => .inf true
      -- 4.
      | true, .gt => .nan
      | _, _ =>
        -- (|x| < 2^-54: log(1 + x) = x(1 − x/2 + …) rounds to x)
        if ilog2 m e < -54 then x else
        let (a, b) := ratOf m e
        logOfRat (if n then b - a else b + a) b 0 (lzOf m e)

/-- The correctly rounded √(v · 2^s) for v > 0 and an even s: the root of v · 4^t (≥ 2^120) to
the nearest integer below, with a sticky bit for the remainder.
spec: https://tc39.es/ecma262/#sec-math.sqrt -/
def sqrtExact (neg : Bool) (v : Nat) (s : Int) : F64 :=
  let lv := Nat.log2 v
  let t : Nat := if lv ≥ 121 then 0 else (122 - lv) / 2 + 1
  let V := v <<< (2 * t)
  let r := Nat.sqrt V
  let sticky := if r * r == V then 0 else 1
  ofNatExp neg (2 * r + sticky) (s / 2 - t - 1)

/-- spec: https://tc39.es/ecma262/#sec-math.sqrt -/
def sqrt (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  | .inf n => if n then .nan else x
  | .fin n m e =>
    if m == 0 then x
    -- 3.
    else if n then .nan
    else if e % 2 == 0 then sqrtExact false m e else sqrtExact false (2 * m) (e - 1)

/-- ⌊∛n⌋ by Newton's iteration from above (decreasing until it stops).
Fuel: from 2^(⌊log2 n / 3⌋ + 1) the iteration converges quadratically once within a factor of 2,
so log2 of n's bit length + a few steps; 200 is far more. -/
def icbrt (n : Nat) : Nat :=
  if n < 8 then (if n == 0 then 0 else 1) else
  let rec go : Nat → Nat → Nat
    | 0, y => y
    | f + 1, y =>
      let y' := (2 * y + n / (y * y)) / 3
      if y' < y then go f y' else y
  go 200 (1 <<< (Nat.log2 n / 3 + 1))

/-- spec: https://tc39.es/ecma262/#sec-math.cbrt -/
def cbrt (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    if m == 0 then x else
    -- (an exponent divisible by 3, and a significand of ≥ 180 bits)
    let r := e % 3
    let m := m <<< r.toNat
    let e := e - r
    let lm := Nat.log2 m
    let t : Nat := if lm ≥ 180 then 0 else (183 - lm) / 3 + 1
    let V := m <<< (3 * t)
    let c := icbrt V
    let sticky := if c * c * c == V then 0 else 1
    ofNatExp n (2 * c + sticky) (e / 3 - t - 1)
  -- 2.
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.hypot -/
def hypot (xs : Array F64) : F64 :=
  -- 4.
  if xs.any (fun x => match x with | .inf _ => true | _ => false) then .inf false
  -- 5.
  else if xs.any isNaN then .nan
  -- 6.
  else if xs.all isZero then posZero
  else
    -- 7. (exactly: Σ m² · 2^(2e − g) over the smallest 2e, then the square root)
    let g := xs.foldl (fun g x => match x with | .fin _ m e => if m == 0 then g else min g (2 * e) | _ => g) 4000
    let S := xs.foldl (fun S x => match x with | .fin _ m e => S + ((m * m) <<< (2 * e - g).toNat) | _ => S) 0
    sqrtExact false S g

/-- x = k · π/2 + r (r at precision q): (k mod 4, sin r, cos r). -/
def trigReduce (n : Bool) (m : Nat) (e : Int) (q : Nat) : Int × Int × Int :=
  let xb := (max 0 (ilog2 m e + 1)).toNat
  let q2 := q + xb + 16
  let X := fixOf n m e q2
  -- (π/2 at q2, within a unit: k of them within 2^xb units, below a unit at q)
  let H := piQ (q2 - 1)
  let k := (2 * X + H) / (2 * H)
  let r := (X - k * H) >>> (xb + 16)
  let (s, c) := sinCosFix q r
  (k % 4, s, c)

/-- spec: https://tc39.es/ecma262/#sec-math.sin -/
def sin (x : F64) : F64 :=
  match x with
  -- 2-3.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    -- (|x| < 2^-26: sin x = x(1 − x²/6 + …) rounds to x)
    if m == 0 || ilog2 m e < -26 then x else
    ziv fun p =>
      let q := p + 64 + lzOf m e
      let (k, s, c) := trigReduce n m e q
      approx (if k == 0 then s else if k == 1 then c else if k == 2 then -s else -c) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.cos -/
def cos (x : F64) : F64 :=
  match x with
  -- 2-3.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    -- (|x| < 2^-27: cos x = 1 − x²/2 + … rounds to 1)
    if m == 0 || ilog2 m e < -27 then one else
    ziv fun p =>
      let q := p + 64
      let (k, s, c) := trigReduce n m e q
      approx (if k == 0 then c else if k == 1 then -s else if k == 2 then -c else s) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.tan -/
def tan (x : F64) : F64 :=
  match x with
  -- 2-3.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    -- (|x| < 2^-27: tan x = x(1 + x²/3 + …) rounds to x)
    if m == 0 || ilog2 m e < -27 then x else
    ziv fun p =>
      let q := p + 64 + lzOf m e
      let (k, s, c) := trigReduce n m e q
      let (num, den) := if k % 2 == 0 then (s, c) else (-c, s)
      if den == 0 then ⟨0, 1 <<< (q + 8), -(q : Int)⟩ else
      -- (s and c within 2^10 units: the quotient within ee/|d| + |n|·ee/d² of n/d)
      let ee : Nat := 1 <<< 10
      let dn := den.natAbs
      let err := ((ee <<< q) / dn) + ((num.natAbs * ee) <<< q) / (dn * dn) + 2
      approx ((shl num q).tdiv den) (-(q : Int)) 64 err

/-- atan(a / b) · 2^q for a, b ≥ 0, not both 0. -/
def angleFix (q : Nat) (a b : Nat) : Int :=
  if a ≤ b then atanFix q (((a <<< q) / b : Nat) : Int)
  else piQ (q - 1) - atanFix q (((b <<< q) / a : Nat) : Int)

/-- spec: https://tc39.es/ecma262/#sec-math.atan -/
def atan (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  -- 3-4.
  | .inf n => piTimes2Pow n (-1)
  | .fin n m e =>
    -- (|x| < 2^-27: atan x = x(1 − x²/3 + …) rounds to x)
    if m == 0 || ilog2 m e < -27 then x else
    let (a, b) := ratOf m e
    ziv fun p =>
      let q := p + 64 + lzOf m e
      let y := angleFix q a b
      approx (if n then -y else y) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.atan2 -/
def atan2 (y x : F64) : F64 :=
  let isPosOrPosZero (x : F64) : Bool := match x with | .fin false .. | .inf false => true | _ => false
  match y, x with
  -- 3.
  | .nan, _ | _, .nan => .nan
  -- 4-5.
  | .inf yn, .inf xn => if xn then piTimes2Pow yn (-2) 3 else piTimes2Pow yn (-2)
  | .inf yn, _ => piTimes2Pow yn (-1)
  -- 6-7.
  | .fin yn 0 _, _ => if isPosOrPosZero x then y else piTimes2Pow yn 0
  -- 8-9.
  | .fin yn _ _, .inf xn => if xn then piTimes2Pow yn 0 else .fin yn 0 (-1074)
  | .fin yn _ _, .fin _ 0 _ => piTimes2Pow yn (-1)
  | .fin yn my ey, .fin xn mx ex =>
    -- 10-13. (|y/x| = a/b exactly)
    let d := ey - ex
    let (a, b) := if d ≥ 0 then (my <<< d.toNat, mx) else (my, mx <<< (-d).toNat)
    let lt : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
    if !xn then
      -- (below 2^-1100 the result rounds to 0)
      if lt < -1100 then .fin yn 0 (-1074) else
      ziv fun p =>
        let q := p + 64 + (max 0 (-lt)).toNat + 1
        let r := angleFix q a b
        approx (if yn then -r else r) (-(q : Int))
    else
      ziv fun p =>
        let q := p + 64
        let r := piQ q - angleFix q a b
        approx (if yn then -r else r) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.asin -/
def asin (x : F64) : F64 :=
  match x with
  -- 2-3.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    if m == 0 then x else
    match cmpMag m e 1 0 with
    | .gt => .nan
    | .eq => piTimes2Pow n (-1)
    | .lt =>
      -- (|x| < 2^-26: asin x = x(1 + x²/6 + …) rounds to x)
      if ilog2 m e < -26 then x else
      let (a, b) := ratOf m e
      ziv fun p =>
        let q := p + 64 + lzOf m e
        let xs := (a <<< q) / b
        let cs := Nat.sqrt ((b * b - a * a) <<< (2 * q)) / b
        let y := angleFix q xs cs
        approx (if n then -y else y) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.acos -/
def acos (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    if m == 0 then piTimes2Pow false (-1) else
    match cmpMag m e 1 0 with
    | .gt => .nan
    -- 3.
    | .eq => if n then piTimes2Pow false 0 else posZero
    | .lt =>
      let (a, b) := ratOf m e
      ziv fun p =>
        let q := p + 64 + 32
        let xs := (a <<< q) / b
        let cs := Nat.sqrt ((b * b - a * a) <<< (2 * q)) / b
        let y := if n then piQ q - angleFix q cs xs else angleFix q cs xs
        approx y (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.asinh -/
def asinh (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    -- 2. (|x| < 2^-26: asinh x = x(1 − x²/6 + …) rounds to x)
    if m == 0 || ilog2 m e < -26 then x else
    let (a, b) := ratOf m e
    ziv fun p =>
      let q := p + 64 + lzOf m e
      -- (log(|x| + √(x² + 1)))
      let xs := (a <<< q) / b
      let w := Nat.sqrt ((a * a + b * b) <<< (2 * q)) / b
      let y := logRatFix q (xs + w) (1 <<< q)
      approx (if n then -y else y) (-(q : Int))
  -- 2.
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.acosh -/
def acosh (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  | .inf n => if n then .nan else x
  | .fin n m e =>
    -- 4.
    if n || m == 0 then .nan else
    match cmpMag m e 1 0 with
    | .lt => .nan
    -- 3.
    | .eq => posZero
    | .gt =>
      let (a, b) := ratOf m e
      ziv fun p =>
        let q := p + 64 + 32
        let xs := (a <<< q) / b
        let w := Nat.sqrt ((a * a - b * b) <<< (2 * q)) / b
        approx (logRatFix q (xs + w) (1 <<< q)) (-(q : Int))

/-- spec: https://tc39.es/ecma262/#sec-math.atanh -/
def atanh (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan | .inf _ => .nan
  | .fin n m e =>
    if m == 0 then x else
    match cmpMag m e 1 0 with
    -- 3.
    | .gt => .nan
    -- 4-5.
    | .eq => .inf n
    | .lt =>
      -- (|x| < 2^-27: atanh x = x(1 + x²/3 + …) rounds to x)
      if ilog2 m e < -27 then x else
      let (a, b) := ratOf m e
      -- (½ log((1 + x)/(1 − x)))
      ziv fun p =>
        let q := p + 64 + lzOf m e
        let y := logRatFix q (b + a) (b - a)
        approx (if n then -y else y) (-(q : Int) - 1)

/-- e^|x| ≈ E · 2^(k−q) and e^−|x| ≈ D · 2^(k−q) at precision q (D = 0 past it). -/
def expPair (m : Nat) (e : Int) (q : Nat) : Int × Int × Int :=
  let (E, k) := expScaled q (fixOf false m e q)
  let sh : Int := 2 * ((q : Int) - k)
  let D : Int := if sh ≥ 0 then (((1 <<< sh.toNat : Nat) : Int)) / E else 0
  (E, D, k)

/-- spec: https://tc39.es/ecma262/#sec-math.sinh -/
def sinh (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    -- 2. (|x| < 2^-26: sinh x = x(1 + x²/6 + …) rounds to x)
    if m == 0 || ilog2 m e < -26 then x
    else if cmpMag m e 711 0 != .lt then .inf n
    else ziv fun p =>
      let q := p + 64 + lzOf m e
      let (E, D, k) := expPair m e q
      approx (if n then D - E else E - D) (k - q - 1)
  -- 2.
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.cosh -/
def cosh (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  -- 3.
  | .inf _ => .inf false
  | .fin _ m e =>
    -- 4. (|x| < 2^-27: cosh x = 1 + x²/2 + … rounds to 1)
    if m == 0 || ilog2 m e < -27 then one
    else if cmpMag m e 711 0 != .lt then .inf false
    else ziv fun p =>
      let q := p + 64
      let (E, D, k) := expPair m e q
      approx (E + D) (k - q - 1)

/-- spec: https://tc39.es/ecma262/#sec-math.tanh -/
def tanh (x : F64) : F64 :=
  match x with
  -- 2.
  | .nan => .nan
  -- 3-4.
  | .inf n => if n then negOne else one
  | .fin n m e =>
    -- 2. (|x| < 2^-27: tanh x = x(1 − x²/3 + …) rounds to x; past 22, within 2^-60 of ±1)
    if m == 0 || ilog2 m e < -27 then x
    else if cmpMag m e 22 0 != .lt then (if n then negOne else one)
    else ziv fun p =>
      let q := p + 64 + lzOf m e
      let (E, D, _) := expPair m e q
      let y := (shl (E - D) q).tdiv (E + D)
      approx (if n then -y else y) (-(q : Int))

/-- The number of trailing zero bits of a positive n < 2^64 (0 for 0). -/
def trailingZeros (n : Nat) : Nat :=
  if n == 0 then 0 else ((List.range 64).find? (fun i => (n >>> i) % 2 == 1)).getD 0

/-- |b|^y for a finite nonzero base magnitude bm·2^be and a finite nonzero exponent
(−1)^yn · ym · 2^ye, with the result's sign `neg`: exact for integral exponents (when the exact
power is at most a few thousand bits), else e^(y · ln|b|) correctly rounded. -/
def powFinite (neg : Bool) (bm : Nat) (be : Int) (yn : Bool) (ym : Nat) (ye : Int) : F64 :=
  -- (|b| = o · 2^t with o odd)
  let tz := trailingZeros bm
  let o := bm >>> tz
  let t : Int := be + tz
  let yInt := intMag ym ye
  let yMag := truncMag ym ye
  if yInt && o == 1 then
    -- (a power of two to an integral power)
    ofNatExp neg 1 (t * (if yn then -(yMag : Int) else yMag))
  else if yInt && yMag * (Nat.log2 o + 1) ≤ 4000 then
    -- (exactly: o^n · 2^(t·n))
    let R := o ^ yMag
    let T := t * yMag
    if yn then ofRatExp neg 1 R (-T) else ofNatExp neg R T
  else
    let (a, b) := ratOf bm be
    -- (λ = y · ln|b| to 2^-64, for overflow and underflow)
    let yb := (max 0 (ilog2 ym ye + 1)).toNat
    let l0 := shiftI (logRatFix (64 + yb) a b * ym) (ye - yb)
    let l0 := if yn then -l0 else l0
    if l0 > 710 * (1 <<< 64 : Nat) then .inf neg
    else if l0 < -(746 * (1 <<< 64 : Nat) : Int) then .fin neg 0 (-1074)
    else ziv fun p =>
      let q := p + 64
      let q2 := q + yb + 4
      let L := shiftI (logRatFix q2 a b * ym) (ye - yb - 4)
      let (E, k) := expScaled q (if yn then -L else L)
      approx (if neg then -E else E) (k - q)

/-- Number::exponentiate (`**` and Math.pow).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-exponentiate -/
def exponentiate (base exponent : F64) : F64 :=
  match exponent with
  -- 1.
  | .nan => .nan
  -- 2.
  | .fin _ 0 _ => one
  | _ =>
  let expPos := !signBit exponent
  let odd := isOddInt exponent
  match base with
  -- 3.
  | .nan => .nan
  -- 4.
  | .inf false => if expPos then .inf false else posZero
  -- 5.
  | .inf true => if expPos then .inf odd else .fin odd 0 (-1074)
  -- 6.
  | .fin false 0 _ => if expPos then posZero else .inf false
  -- 7.
  | .fin true 0 _ => if expPos then .fin odd 0 (-1074) else .inf odd
  | .fin bn bm be =>
    match exponent with
    -- 9-10.
    | .inf xn =>
      match cmpMag bm be 1 0 with
      | .gt => if xn then posZero else .inf false
      | .eq => .nan
      | .lt => if xn then .inf false else posZero
    | .fin yn ym ye =>
      -- 12.
      if bn && !intMag ym ye then .nan
      -- 13.
      else powFinite (bn && odd) bm be yn ym ye
    | .nan => .nan

/-- spec: https://tc39.es/ecma262/#sec-math.pow -/
def pow (base exponent : F64) : F64 := exponentiate base exponent

/-- spec: https://tc39.es/ecma262/#sec-math.clz32 -/
def clz32 (x : F64) : Nat :=
  let n := toUint32 x
  if n == 0 then 32 else 31 - Nat.log2 n

/-- spec: https://tc39.es/ecma262/#sec-math.imul -/
def imul (x y : F64) : F64 := ofInt (signedOf 32 ((toUint32 x * toUint32 y) % (1 <<< 32)))

/-- Math.max over the coerced arguments (NaN wins; +0 above −0).
spec: https://tc39.es/ecma262/#sec-math.max -/
def mathMax (xs : Array F64) : F64 := xs.foldl F64.max (.inf true)

/-- Math.min over the coerced arguments (NaN wins; −0 below +0).
spec: https://tc39.es/ecma262/#sec-math.min -/
def mathMin (xs : Array F64) : F64 := xs.foldl F64.min (.inf false)

/-- Math.sumPrecise's result for the Numbers of the iterable (after its TypeError checks): the
exact sum, rounded once.
spec: https://tc39.es/ecma262/#sec-math.sumprecise -/
def sumPrecise (xs : Array F64) : F64 := Id.run do
  -- (state: 0 minus-zero, 1 finite, 2 plus-infinity, 3 minus-infinity, 4 not-a-number)
  let mut state := 0
  -- (the sum, in units of 2^-1074)
  let mut sum : Int := 0
  for x in xs do
    if state != 4 then
      match x with
      | .nan => state := 4
      | .inf false => state := if state == 3 then 4 else 2
      | .inf true => state := if state == 2 then 4 else 3
      | .fin n m e =>
        if !(n && m == 0) && (state == 0 || state == 1) then
          state := 1
          let v : Int := ((m <<< (e + 1074).toNat : Nat) : Int)
          sum := if n then sum - v else sum + v
  return match state with
    | 4 => .nan
    | 2 => .inf false
    | 3 => .inf true
    | 0 => negZero
    | _ => if sum == 0 then posZero else ofIntExp sum (-1074)

/-! ## binary32 and binary16 -/

/-- x = m · 2^e rounded to `prec` significant bits with the least exponent eMin (subnormals),
ties to even: (m', e'), or `none` past 2^ovf (overflow to ∞). -/
def roundBin (prec : Nat) (eMin : Int) (ovf : Int) (m : Nat) (e : Int) : Option (Nat × Int) :=
  if m == 0 then some (0, eMin) else
  let te := max eMin (ilog2 m e - (prec - 1 : Nat))
  let (m', te) := if te ≤ e then (m <<< (e - te).toNat, te) else
    let r := shiftRoundEven m (te - e).toNat
    if r == 1 <<< prec then (1 <<< (prec - 1), te + 1) else (r, te)
  if m' == 0 then some (0, eMin)
  else if ilog2 m' te ≥ ovf then none else some (m', te)

/-- spec: https://tc39.es/ecma262/#sec-math.fround -/
def fround (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    match roundBin 24 (-149) 128 m e with
    | some (m', e') => ofNatExp n m' e'
    | none => .inf n
  | _ => x

/-- spec: https://tc39.es/ecma262/#sec-math.f16round -/
def f16round (x : F64) : F64 :=
  match x with
  | .fin n m e =>
    match roundBin 11 (-24) 16 m e with
    | some (m', e') => ofNatExp n m' e'
    | none => .inf n
  | _ => x

/-- The encoding of x rounded to a binary format with `fracBits` fraction bits and
`expBits` exponent bits (NaN: the quiet NaN with only the top fraction bit set, as browsers
write it).
spec: https://tc39.es/ecma262/#sec-numerictorawbytes -/
def encodeBin (fracBits expBits : Nat) (x : F64) : Nat :=
  let bias : Nat := (1 <<< (expBits - 1)) - 1
  let expAll : Nat := (1 <<< expBits) - 1
  let signBitV : Nat := 1 <<< (fracBits + expBits)
  match x with
  | .nan => (expAll <<< fracBits) ||| (1 <<< (fracBits - 1))
  | .inf n => (if n then signBitV else 0) ||| (expAll <<< fracBits)
  | .fin n m e =>
    let s := if n then signBitV else 0
    let eMin : Int := 1 - (bias : Int) - fracBits
    match roundBin (fracBits + 1) eMin (bias + 1 : Nat) m e with
    | none => s ||| (expAll <<< fracBits)
    | some (m', te) =>
      if m' < 1 <<< fracBits then s ||| m'
      else s ||| ((te - eMin + 1).toNat <<< fracBits) ||| (m' - (1 <<< fracBits))

/-- The Number a binary format's encoding stands for (exact; every NaN is NaN).
spec: https://tc39.es/ecma262/#sec-rawbytestonumeric -/
def decodeBin (fracBits expBits : Nat) (bits : Nat) : F64 :=
  let bias : Nat := (1 <<< (expBits - 1)) - 1
  let expAll : Nat := (1 <<< expBits) - 1
  let neg := (bits >>> (fracBits + expBits)) % 2 == 1
  let ex := (bits >>> fracBits) &&& expAll
  let fr := bits &&& ((1 <<< fracBits) - 1)
  let eMin : Int := 1 - (bias : Int) - fracBits
  if ex == expAll then (if fr == 0 then .inf neg else .nan)
  else if ex == 0 then ofNatExp neg fr eMin
  else ofNatExp neg (fr + (1 <<< fracBits)) (eMin + ex - 1)

def toFloat32Bits (x : F64) : UInt32 := (encodeBin 23 8 x).toUInt32
def ofFloat32Bits (b : UInt32) : F64 := decodeBin 23 8 b.toNat
def toFloat16Bits (x : F64) : UInt16 := (encodeBin 10 5 x).toUInt16
def ofFloat16Bits (b : UInt16) : F64 := decodeBin 10 5 b.toNat
def toFloat64Bits (x : F64) : UInt64 := F64.toBits x
def ofFloat64Bits (b : UInt64) : F64 := decodeBin 52 11 b.toNat


/-! ## Number.prototype.toFixed, toExponential, toPrecision -/

/-- ⌊log10(a / b)⌋ for a, b > 0.
Fuel: the estimate from the binary logarithms is within 2 of the answer. -/
def floorLog10 (a b : Nat) : Int :=
  -- (10^e ≤ a/b)
  let le (e : Int) : Bool := if e ≥ 0 then 10 ^ e.toNat * b ≤ a else b ≤ a * 10 ^ (-e).toNat
  let est : Int := (((Nat.log2 a : Int) - (Nat.log2 b : Int)) * 78913) >>> 18
  let rec down : Nat → Int → Int
    | 0, e => e
    | f + 1, e => if le e then e else down f (e - 1)
  let rec up : Nat → Int → Int
    | 0, e => e
    | f + 1, e => if le (e + 1) then up f (e + 1) else e
  up 8 (down 8 (est + 1))

/-- round(a/b · 10^k), ties up (the larger n). -/
def roundHalfUpScaled (a b : Nat) (k : Int) : Nat :=
  let (num, den) := if k ≥ 0 then (a * 10 ^ k.toNat, b) else (a, b * 10 ^ (-k).toNat)
  (2 * num + den) / (2 * den)

/-- The value of a ToIntegerOrInfinity result as an integer in [lo, hi] (`none`: out of range or
infinite, a RangeError). -/
def intInRange (f : F64) (lo hi : Int) : Option Int :=
  match f with
  | .fin .. => let i := truncInt f; if lo ≤ i && i ≤ hi then some i else none
  | _ => none

/-- Number.prototype.toFixed after ThisNumberValue and ToIntegerOrInfinity(fractionDigits) = f
(`none`: RangeError).
spec: https://tc39.es/ecma262/#sec-number.prototype.tofixed -/
def toFixed (x : F64) (f : F64) : Option String := do
  -- 4-5.
  let f ← intInRange f 0 100
  let f := f.toNat
  match x with
  -- 6.
  | .nan | .inf _ => return toStringDec x
  | .fin neg m e =>
    -- 8-9.
    let s := if neg && m != 0 then "-" else ""
    let (a, b) := ratOf m e
    -- 10.
    if a ≥ 10 ^ 21 * b then return s ++ toStringDec (abs x)
    -- 11.a.
    let n := roundHalfUpScaled a b f
    -- 11.b.
    let md := toString n
    -- 11.c.
    if f == 0 then return s ++ md
    let md := if md.length ≤ f then String.ofList (List.replicate (f + 1 - md.length) '0') ++ md else md
    let k := md.length
    return s ++ String.ofList (md.toList.take (k - f)) ++ "." ++ String.ofList (md.toList.drop (k - f))

/-- "e+d" / "e-d" for an exponent. -/
def expSuffix (e : Int) : String := "e" ++ (if e ≥ 0 then "+" else "-") ++ toString e.natAbs

/-- Number.prototype.toExponential after ThisNumberValue and ToIntegerOrInfinity(fractionDigits)
(`none` for undefined; result `none`: RangeError).
spec: https://tc39.es/ecma262/#sec-number.prototype.toexponential -/
def toExponential (x : F64) (fd : Option F64) : Option String := do
  match x with
  -- 4.
  | .nan | .inf _ => return toStringDec x
  | .fin neg m e =>
    -- 5.
    let f? ← match fd with
      | none => pure none
      | some f => (intInRange f 0 100).map (some ·.toNat)
    -- 7-8.
    let s := if neg && m != 0 then "-" else ""
    -- 9-10.
    let (digits, ex) : String × Int :=
      if m == 0 then (String.ofList (List.replicate (f?.getD 0 + 1) '0'), 0) else
      match f? with
      | some f =>
        let (a, b) := ratOf m e
        let e0 := floorLog10 a b
        let n := roundHalfUpScaled a b (f - e0)
        if n == 10 ^ (f + 1) then (toString (n / 10), e0 + 1) else (toString n, e0)
      | none =>
        let (sd, nn) := shortestDigits m e
        (toString sd, nn - 1)
    -- 11.
    let mstr := if digits.length > 1 then
      String.ofList (digits.toList.take 1) ++ "." ++ String.ofList (digits.toList.drop 1) else digits
    -- 12-14.
    return s ++ mstr ++ expSuffix ex

/-- Number.prototype.toPrecision after ThisNumberValue and, unless `precision` is undefined
(`none`), ToIntegerOrInfinity(precision) (result `none`: RangeError).
spec: https://tc39.es/ecma262/#sec-number.prototype.toprecision -/
def toPrecision (x : F64) (precision : Option F64) : Option String := do
  match precision with
  -- 2.
  | none => return toStringDec x
  | some pv =>
  match x with
  -- 4.
  | .nan | .inf _ => return toStringDec x
  | .fin neg m e =>
    -- 5.
    let p ← intInRange pv 1 100
    let p := p.toNat
    -- 7-8.
    let s := if neg && m != 0 then "-" else ""
    -- 9-10.
    let (md, ex) : String × Int :=
      if m == 0 then (String.ofList (List.replicate p '0'), 0) else
      let (a, b) := ratOf m e
      let e0 := floorLog10 a b
      let n := roundHalfUpScaled a b ((p : Int) - 1 - e0)
      if n == 10 ^ p then (toString (n / 10), e0 + 1) else (toString n, e0)
    -- 10.c.
    if ex < -6 || ex ≥ p then
      let mstr := if p != 1 then
        String.ofList (md.toList.take 1) ++ "." ++ String.ofList (md.toList.drop 1) else md
      return s ++ mstr ++ expSuffix ex
    -- 11.
    if ex == (p : Int) - 1 then return s ++ md
    -- 12.
    if ex ≥ 0 then
      let k := (ex + 1).toNat
      return s ++ String.ofList (md.toList.take k) ++ "." ++ String.ofList (md.toList.drop k)
    -- 13.
    return s ++ "0." ++ String.ofList (List.replicate (-(ex + 1)).toNat '0') ++ md

/-! ## BigInt -/

namespace BigInt

/-- The most bits a BigInt may have (V8's limit, 2^30): larger results are RangeErrors. -/
def maxBits : Nat := 1 <<< 30

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-tostring -/
def toString (x : Int) (radix : Nat := 10) : String :=
  (if x < 0 then "-" else "") ++ natDigits x.natAbs radix

/-- StringToBigInt (`none`: undefined, the string is not a StringIntegerLiteral).
spec: https://tc39.es/ecma262/#sec-stringtobigint -/
def stringToBigInt (str : JSStr) : Option Int := Id.run do
  let i := skipWS str 0
  let j := trimEnd str i str.length
  -- (StrWhiteSpace_opt)
  if i == j then return some 0
  -- (NonDecimalIntegerLiteral)
  if j - i > 2 && str.get i == 0x30 then
    let c := str.get (i + 1)
    let radix := if c == 0x78 || c == 0x58 then 16 else if c == 0x6F || c == 0x4F then 8
      else if c == 0x62 || c == 0x42 then 2 else 0
    if radix != 0 then return (radixDigits str (i + 2) j radix).map (fun (v : Nat) => (v : Int))
  -- (SignedInteger)
  let (neg, k) := if str.get i == 0x2D then (true, i + 1)
    else if str.get i == 0x2B then (false, i + 1) else (false, i)
  match radixDigits str k j 10 with
  | some v => return some (if neg then -(v : Int) else v)
  | none => return none

/-- The bit length of |x|. -/
@[inline] def bitLen (x : Int) : Nat := if x == 0 then 0 else Nat.log2 x.natAbs + 1

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-unaryMinus -/
def unaryMinus (x : Int) : Int := -x

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-bitwiseNOT -/
def bitwiseNOT (x : Int) : Int := -x - 1

/-- BigInt::exponentiate (`.error` messages are RangeErrors).
spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-exponentiate -/
def exponentiate (base exponent : Int) : Except String Int :=
  -- 1.
  if exponent < 0 then .error "Exponent must be non-negative" else
  -- 2.
  if base == 0 && exponent == 0 then .ok 1 else
  let n := exponent.toNat
  if base == 0 || base == 1 then .ok base
  else if base == -1 then .ok (if n % 2 == 0 then 1 else -1)
  else if (bitLen base - 1) * n ≥ maxBits then .error "Maximum BigInt size exceeded"
  -- 3.
  else .ok (base ^ n)

/-- BigInt::divide: truncating.
spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-divide -/
def divide (x y : Int) : Except String Int :=
  -- 1.
  if y == 0 then .error "Division by zero" else
  -- 2-3.
  .ok (x.tdiv y)

/-- BigInt::remainder: the sign of the dividend.
spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-remainder -/
def remainder (n d : Int) : Except String Int :=
  -- 1.
  if d == 0 then .error "Division by zero" else
  -- 2-5.
  .ok (n.tmod d)

/-- BigInt::leftShift (a negative count shifts right, rounding toward −∞).
spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-leftShift -/
def leftShift (x y : Int) : Except String Int :=
  if y < 0 then
    let k := (-y).toNat
    .ok (if k > bitLen x then (if x < 0 then -1 else 0) else x >>> k)
  else if x == 0 then .ok 0
  else if bitLen x + y.toNat > maxBits then .error "Maximum BigInt size exceeded"
  else .ok (shl x y.toNat)

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-signedRightShift -/
def signedRightShift (x y : Int) : Except String Int := leftShift x (-y)

/-- x & y on two's complement integers of unbounded width (a negative x is ~a for a = −x − 1).
spec: https://tc39.es/ecma262/#sec-bigintbitwiseop -/
def bitwiseAND (x y : Int) : Int :=
  match decide (x < 0), decide (y < 0) with
  | false, false => (x.toNat &&& y.toNat : Nat)
  | false, true => let a := x.toNat; let b := (-y - 1).toNat; (a ^^^ (a &&& b) : Nat)
  | true, false => let b := y.toNat; let a := (-x - 1).toNat; (b ^^^ (a &&& b) : Nat)
  | true, true => -(((-x - 1).toNat ||| (-y - 1).toNat : Nat) : Int) - 1

/-- spec: https://tc39.es/ecma262/#sec-bigintbitwiseop -/
def bitwiseOR (x y : Int) : Int :=
  match decide (x < 0), decide (y < 0) with
  | false, false => (x.toNat ||| y.toNat : Nat)
  | false, true => let a := x.toNat; let b := (-y - 1).toNat; -((b ^^^ (a &&& b) : Nat) : Int) - 1
  | true, false => let b := y.toNat; let a := (-x - 1).toNat; -((a ^^^ (a &&& b) : Nat) : Int) - 1
  | true, true => -(((-x - 1).toNat &&& (-y - 1).toNat : Nat) : Int) - 1

/-- spec: https://tc39.es/ecma262/#sec-bigintbitwiseop -/
def bitwiseXOR (x y : Int) : Int :=
  match decide (x < 0), decide (y < 0) with
  | false, false => (x.toNat ^^^ y.toNat : Nat)
  | false, true => -((x.toNat ^^^ (-y - 1).toNat : Nat) : Int) - 1
  | true, false => -(((-x - 1).toNat ^^^ y.toNat : Nat) : Int) - 1
  | true, true => (((-x - 1).toNat ^^^ (-y - 1).toNat : Nat) : Int)

/-- BigInt.asUintN: x modulo 2^bits.
spec: https://tc39.es/ecma262/#sec-bigint.asuintn -/
def asUintN (bits : Nat) (x : Int) : Int := x % ((1 <<< bits : Nat) : Int)

/-- BigInt.asIntN: x modulo 2^bits, as a signed value.
spec: https://tc39.es/ecma262/#sec-bigint.asintn -/
def asIntN (bits : Nat) (x : Int) : Int :=
  if bits == 0 then 0 else
  let mod := asUintN bits x
  if mod ≥ ((1 <<< (bits - 1) : Nat) : Int) then mod - ((1 <<< bits : Nat) : Int) else mod

/-- ToBigInt64's numeric part. spec: https://tc39.es/ecma262/#sec-tobigint64 -/
def toBigInt64 (x : Int) : Int := asIntN 64 x
/-- ToBigUint64's numeric part. spec: https://tc39.es/ecma262/#sec-tobiguint64 -/
def toBigUint64 (x : Int) : Int := asUintN 64 x

/-- NumberToBigInt (`none`: RangeError, x is not integral).
spec: https://tc39.es/ecma262/#sec-numbertobigint -/
def ofNumber (x : F64) : Option Int := toInt? x

/-- 𝔽(ℝ(x)): the Number value for a BigInt (Number(x)), correctly rounded.
spec: https://tc39.es/ecma262/#sec-number-constructor-number-value -/
def toNumber (x : Int) : F64 := ofInt x

/-- Compares a BigInt with a Number exactly (`none` if the Number is NaN).
spec: https://tc39.es/ecma262/#sec-islessthan -/
def compareNumber (x : Int) (y : F64) : Option Ordering :=
  match y with
  | .nan => none
  | .inf n => some (if n then .gt else .lt)
  | .fin n m e =>
    let xs := x < 0
    let ys := n && m != 0
    if x == 0 && m == 0 then some .eq
    else if xs != ys then some (if xs then .lt else .gt)
    else if x == 0 then some (if ys then .gt else .lt)
    else if m == 0 then some (if xs then .lt else .gt)
    else
      let c := cmpMag x.natAbs 0 m e
      some (if xs then c.swap else c)

/-- BigInt == Number (IsLooselyEqual's numeric step). -/
def equalNumber (x : Int) (y : F64) : Bool := compareNumber x y == some .eq

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-lessThan -/
def lessThan (x y : Int) : Bool := x < y
/-- spec: https://tc39.es/ecma262/#sec-numeric-types-bigint-equal -/
def equal (x y : Int) : Bool := x == y

end BigInt

/-! ## Date: time values

Time values are integral Numbers of milliseconds (or NaN); the calendar arithmetic of
21.4.1 is done on their exact integers. -/

namespace Date

def msPerDay : Int := 86400000
def msPerHour : Int := 3600000
def msPerMinute : Int := 60000
def msPerSecond : Int := 1000

/-- The integer of a finite time value (truncated; NaN and ±∞: `none`). -/
def tv? (t : F64) : Option Int := if isFinite t then some (truncInt t) else none

/-- spec: https://tc39.es/ecma262/#sec-day -/
def day (t : Int) : Int := t / msPerDay
/-- spec: https://tc39.es/ecma262/#sec-timewithinday -/
def timeWithinDay (t : Int) : Int := t % msPerDay

/-- spec: https://tc39.es/ecma262/#sec-daysinyear -/
def daysInYear (y : Int) : Int :=
  if y % 4 != 0 then 365 else if y % 100 != 0 then 366 else if y % 400 != 0 then 365 else 366

/-- spec: https://tc39.es/ecma262/#sec-dayfromyear -/
def dayFromYear (y : Int) : Int :=
  365 * (y - 1970) + (y - 1969) / 4 - (y - 1901) / 100 + (y - 1601) / 400

/-- spec: https://tc39.es/ecma262/#sec-timefromyear -/
def timeFromYear (y : Int) : Int := msPerDay * dayFromYear y

/-- The proleptic Gregorian (year, month 1–12, day 1–31) of a day number (days since the epoch).
(The standard era-based conversion: exact for every integer.) -/
def civilOfDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

/-- The day number of a proleptic Gregorian date (month 1–12). -/
def daysOfCivil (y : Int) (m : Nat) (d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mi : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy := (153 * mi + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- spec: https://tc39.es/ecma262/#sec-yearfromtime -/
def yearFromTime (t : Int) : Int := (civilOfDays (day t)).1
/-- spec: https://tc39.es/ecma262/#sec-inleapyear -/
def inLeapYear (t : Int) : Bool := daysInYear (yearFromTime t) == 366
/-- spec: https://tc39.es/ecma262/#sec-daywithinyear -/
def dayWithinYear (t : Int) : Int := day t - dayFromYear (yearFromTime t)
/-- MonthFromTime: 0–11. spec: https://tc39.es/ecma262/#sec-monthfromtime -/
def monthFromTime (t : Int) : Nat := (civilOfDays (day t)).2.1 - 1
/-- DateFromTime: 1–31. spec: https://tc39.es/ecma262/#sec-datefromtime -/
def dateFromTime (t : Int) : Nat := (civilOfDays (day t)).2.2
/-- spec: https://tc39.es/ecma262/#sec-weekday -/
def weekDay (t : Int) : Nat := ((day t + 4) % 7).toNat
/-- spec: https://tc39.es/ecma262/#sec-hourfromtime -/
def hourFromTime (t : Int) : Nat := ((t / msPerHour) % 24).toNat
/-- spec: https://tc39.es/ecma262/#sec-minfromtime -/
def minFromTime (t : Int) : Nat := ((t / msPerMinute) % 60).toNat
/-- spec: https://tc39.es/ecma262/#sec-secfromtime -/
def secFromTime (t : Int) : Nat := ((t / msPerSecond) % 60).toNat
/-- spec: https://tc39.es/ecma262/#sec-msfromtime -/
def msFromTime (t : Int) : Nat := (t % msPerSecond).toNat

/-- spec: https://tc39.es/ecma262/#sec-maketime -/
def makeTime (hour min sec ms : F64) : F64 :=
  -- 1.
  if !(isFinite hour && isFinite min && isFinite sec && isFinite ms) then .nan else
  -- 2-5.
  let h := toIntegerOrInfinity hour
  let m := toIntegerOrInfinity min
  let s := toIntegerOrInfinity sec
  let milli := toIntegerOrInfinity ms
  -- 6. (IEEE 754-2019 arithmetic, as the operators * and + do)
  F64.add (F64.add (F64.add (F64.mul h (ofInt msPerHour)) (F64.mul m (ofInt msPerMinute)))
    (F64.mul s (ofInt msPerSecond))) milli

/-- MakeDay. Step 8 ("if not possible") follows browsers: years beyond ±1,000,000 or months
beyond ±10,000,000 give NaN (V8's bounds; any representable result lies far inside them once
TimeClip applies).
spec: https://tc39.es/ecma262/#sec-makeday -/
def makeDay (year month date : F64) : F64 :=
  -- 1.
  if !(isFinite year && isFinite month && isFinite date) then .nan else
  -- 2-4.
  let y := toIntegerOrInfinity year
  let m := toIntegerOrInfinity month
  let dt := toIntegerOrInfinity date
  let yi := truncInt y
  let mi := truncInt m
  if yi < -1000000 || yi > 1000000 || mi < -10000000 || mi > 10000000 then .nan else
  -- 5-7.
  let ym := yi + mi / 12
  let mn := (mi % 12).toNat
  -- 8-9.
  F64.sub (F64.add (ofInt (daysOfCivil ym (mn + 1) 1)) dt) one

/-- spec: https://tc39.es/ecma262/#sec-makedate -/
def makeDate (day time : F64) : F64 :=
  -- 1.
  if !(isFinite day && isFinite time) then .nan else
  -- 2.
  let tv := F64.add (F64.mul day (ofInt msPerDay)) time
  -- 3-4.
  if isFinite tv then tv else .nan

/-- spec: https://tc39.es/ecma262/#sec-makefullyear -/
def makeFullYear (year : F64) : F64 :=
  match year with
  -- 1.
  | .nan => .nan
  | _ =>
    -- 2.
    let truncated := toIntegerOrInfinity year
    -- 3.
    match truncated with
    | .fin false _ _ =>
      let i := truncInt truncated
      if i ≤ 99 then ofInt (1900 + i) else truncated
    | _ => truncated

/-- spec: https://tc39.es/ecma262/#sec-timeclip -/
def timeClip (time : F64) : F64 :=
  -- 1.
  if !isFinite time then .nan
  -- 2.
  else if cmpMag (match time with | .fin _ m _ => m | _ => 0) (match time with | .fin _ _ e => e | _ => 0)
      8640000000000000 0 == .gt then .nan
  -- 3.
  else toIntegerOrInfinity time

def weekDayNames : Array String := #["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
def monthNames : Array String := #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- ToZeroPaddedDecimalString. spec: https://tc39.es/ecma262/#sec-tozeropaddeddecimalstring -/
def pad (n : Nat) (w : Nat) : String :=
  let s := Nat.repr n
  String.ofList (List.replicate (w - min w s.length) '0') ++ s

/-- spec: https://tc39.es/ecma262/#sec-timestring -/
def timeString (tv : Int) : String :=
  pad (hourFromTime tv) 2 ++ ":" ++ pad (minFromTime tv) 2 ++ ":" ++ pad (secFromTime tv) 2 ++ " GMT"

/-- spec: https://tc39.es/ecma262/#sec-datestring -/
def dateString (tv : Int) : String :=
  let yv := yearFromTime tv
  weekDayNames[weekDay tv]! ++ " " ++ monthNames[monthFromTime tv]! ++ " " ++ pad (dateFromTime tv) 2 ++
    " " ++ (if yv < 0 then "-" else "") ++ pad yv.natAbs 4

/-- TimeZoneString for a UTC offset in milliseconds and the zone's name (empty: none).
spec: https://tc39.es/ecma262/#sec-timezoneestring -/
def timeZoneString (offset : Int) (tzName : String := "Coordinated Universal Time") : String :=
  -- 4.
  let (sign, absOffset) := if offset ≥ 0 then ("+", offset) else ("-", -offset)
  -- 5-8.
  sign ++ pad (hourFromTime absOffset) 2 ++ pad (minFromTime absOffset) 2 ++
    (if tzName.isEmpty then "" else " (" ++ tzName ++ ")")

/-- Date.prototype.toString's result: ToDateString(tv) for a zone at a fixed UTC offset (ms).
spec: https://tc39.es/ecma262/#sec-todatestring -/
def toDateString (tv : F64) (offset : Int := 0) (tzName : String := "Coordinated Universal Time") : String :=
  match tv? tv with
  -- 2.
  | none => "Invalid Date"
  | some u =>
    -- 3-4.
    let t := u + offset
    dateString t ++ " " ++ timeString t ++ timeZoneString offset tzName

/-- Date.prototype.toDateString's result.
spec: https://tc39.es/ecma262/#sec-date.prototype.todatestring -/
def toDateOnlyString (tv : F64) (offset : Int := 0) : String :=
  match tv? tv with
  | none => "Invalid Date"
  | some u => dateString (u + offset)

/-- Date.prototype.toTimeString's result.
spec: https://tc39.es/ecma262/#sec-date.prototype.totimestring -/
def toTimeString (tv : F64) (offset : Int := 0) (tzName : String := "Coordinated Universal Time") : String :=
  match tv? tv with
  | none => "Invalid Date"
  | some u => timeString (u + offset) ++ timeZoneString offset tzName

/-- Date.prototype.toUTCString's result.
spec: https://tc39.es/ecma262/#sec-date.prototype.toutcstring -/
def toUTCString (tv : F64) : String :=
  match tv? tv with
  -- 3.
  | none => "Invalid Date"
  | some t =>
    -- 4-8.
    let yv := yearFromTime t
    weekDayNames[weekDay t]! ++ ", " ++ pad (dateFromTime t) 2 ++ " " ++ monthNames[monthFromTime t]! ++ " " ++
      (if yv < 0 then "-" else "") ++ pad yv.natAbs 4 ++ " " ++ timeString t

/-- Date.prototype.toISOString's result (`none`: RangeError for an invalid date): the Date Time
String Format in UTC, with an expanded year outside 0–9999.
spec: https://tc39.es/ecma262/#sec-date.prototype.toisostring -/
def toISOString (tv : F64) : Option String := do
  let t ← tv? tv
  let y := yearFromTime t
  let ys := if 0 ≤ y && y ≤ 9999 then pad y.toNat 4 else (if y < 0 then "-" else "+") ++ pad y.natAbs 6
  return ys ++ "-" ++ pad (monthFromTime t + 1) 2 ++ "-" ++ pad (dateFromTime t) 2 ++ "T" ++
    pad (hourFromTime t) 2 ++ ":" ++ pad (minFromTime t) 2 ++ ":" ++ pad (secFromTime t) 2 ++ "." ++
    pad (msFromTime t) 3 ++ "Z"

/-- The days in month m (1–12) of year y. -/
def daysInMonth (y : Int) (m : Nat) : Nat :=
  if m == 2 then (if daysInYear y == 366 then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- The time value of a UTC date and time (all fields validated), TimeClipped. -/
def utcOf (y : Int) (mon : Nat) (d : Nat) (h mi s ms : Nat) (offset : Int) : F64 :=
  let days := daysOfCivil y mon d
  timeClip (ofInt (days * msPerDay + h * msPerHour + mi * msPerMinute + s * msPerSecond + ms - offset))

/-- Parses the Date Time String Format (incl. expanded years); date-only forms are UTC,
date-times without an offset local (`localOffset` ms). `none` if `str` is not in the format.
spec: https://tc39.es/ecma262/#sec-date-time-string-format -/
def parseISO (str : String) (localOffset : Int) : Option F64 := do
  let cs := str.toList.toArray
  let n := cs.size
  let digit (i : Nat) : Option Nat := do
    let c ← cs[i]?
    if c.isDigit then some (c.toNat - 48) else none
  let num (i k : Nat) : Option Nat :=
    (List.range k).foldlM (fun acc j => do let d ← digit (i + j); pure (acc * 10 + d)) 0
  let atC (i : Nat) (c : Char) : Bool := cs[i]? == some c
  -- (year: YYYY or ±YYYYYY, −000000 not allowed)
  let (y, i) ← if atC 0 '+' || atC 0 '-' then do
      let v ← num 1 6
      if atC 0 '-' && v == 0 then none
      pure ((if atC 0 '-' then -(v : Int) else v), 7)
    else do pure (((← num 0 4) : Int), 4)
  let (mon, i) ← if atC i '-' then do pure ((← num (i + 1) 2), i + 3) else pure (1, i)
  let (d, i) ← if i > 4 && atC i '-' && (i == 7 || i == 10) then do pure ((← num (i + 1) 2), i + 3) else pure (1, i)
  if mon < 1 || mon > 12 || d < 1 || d > daysInMonth y mon then none
  if i == n then return utcOf y mon d 0 0 0 0 0
  -- (THH:mm[:ss[.sss]] and Z or ±HH:mm)
  if !atC i 'T' then none
  let h ← num (i + 1) 2
  if !atC (i + 3) ':' then none
  let mi ← num (i + 4) 2
  let mut i := i + 6
  let mut s := 0
  let mut ms := 0
  if atC i ':' then
    s ← num (i + 1) 2
    i := i + 3
    if atC i '.' then
      -- (one or more digits; the first three count)
      let mut k := i + 1
      let mut v := 0
      let mut cnt := 0
      while k < n && (digit k).isSome do
        if cnt < 3 then v := v * 10 + (digit k).get!
        cnt := cnt + 1
        k := k + 1
      if cnt == 0 then none
      ms := v * 10 ^ (3 - min 3 cnt)
      i := k
  if h > 24 || mi > 59 || s > 59 || (h == 24 && (mi != 0 || s != 0 || ms != 0)) then none
  let mut off := localOffset
  if i < n then
    if atC i 'Z' && i + 1 == n then off := 0
    else if (atC i '+' || atC i '-') && i + 6 == n && atC (i + 3) ':' then
      let oh ← num (i + 1) 2
      let om ← num (i + 4) 2
      if oh > 23 || om > 59 then none
      let o : Int := oh * msPerHour + om * msPerMinute
      off := if atC i '-' then -o else o
    else none
  return utcOf y mon d h mi s ms off

/-- Parses the formats Date.prototype.toString and toUTCString produce (and their variants:
weekday optional, time optional, `GMT`/`UTC`/`Z` with an optional ±hhmm offset, comments in
parentheses ignored); without a zone, local time.
spec: https://tc39.es/ecma262/#sec-date.parse -/
def parseLegacy (str : String) (localOffset : Int) : Option F64 := do
  -- (tokens: words, numbers with their separators, signs)
  let cs := str.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut year : Option Int := none
  let mut mon : Option Nat := none
  let mut d : Option Nat := none
  let mut time : Option (Nat × Nat × Nat) := none
  let mut off : Option Int := none
  let mut negNext := false
  let mut afterZone := false
  let mut fuel := n + 1
  while i < n && fuel > 0 do
    fuel := fuel - 1
    let c := cs[i]!
    if c == '(' then
      -- (a comment, to its closing parenthesis)
      while i < n && cs[i]! != ')' do i := i + 1
      i := i + 1
    else if c.isAlpha then
      let mut j := i
      while j < n && cs[j]!.isAlpha do j := j + 1
      let w := (String.ofList (cs.extract i j).toList).toLower
      i := j
      if w == "gmt" || w == "utc" || w == "z" then
        off := some 0
        afterZone := true
      else
        match monthNames.findIdx? (fun mn => mn.toLower == (w.take 3).toString) with
        | some k => if w.length ≥ 3 then mon := some (k + 1) else none
        | none =>
          if !(weekDayNames.any (fun wd => wd.toLower == (w.take 3).toString) && w.length ≥ 3) then none
    else if c.isDigit then
      let mut j := i
      let mut v := 0
      while j < n && cs[j]!.isDigit do
        v := v * 10 + (cs[j]!.toNat - 48)
        j := j + 1
      let len := j - i
      if j < n && cs[j]! == ':' && !afterZone then
        -- (hh:mm[:ss])
        let mm ← (if j + 2 < n + 0 && cs[j+1]!.isDigit && cs[j+2]!.isDigit then
          some ((cs[j+1]!.toNat - 48) * 10 + (cs[j+2]!.toNat - 48)) else none)
        let mut k := j + 3
        let mut ss := 0
        if k < n && cs[k]! == ':' then
          if k + 2 < n + 0 && cs[k+1]!.isDigit && cs[k+2]!.isDigit then
            ss := (cs[k+1]!.toNat - 48) * 10 + (cs[k+2]!.toNat - 48)
            k := k + 3
          else none
        if v > 24 || mm > 59 || ss > 59 then none
        time := some (v, mm, ss)
        i := k
      else if afterZone && (negNext || (i > 0 && cs[i-1]! == '+')) && len == 4 then
        let o : Int := (v / 100) * msPerHour + (v % 100) * msPerMinute
        off := some (if negNext then -o else o)
        negNext := false
        afterZone := false
        i := j
      else
        if d.isNone && mon.isSome && year.isNone && len ≤ 2 then d := some v
        else if d.isNone && mon.isNone && len ≤ 2 then d := some v
        else if year.isNone then year := some (if negNext then -(v : Int) else v)
        else none
        negNext := false
        i := j
    else if c == '-' then
      negNext := true
      i := i + 1
    else if c == '+' || c == ' ' || c == ',' then
      i := i + 1
    else none
  let y ← year
  let m ← mon
  let dd ← d
  if dd < 1 || dd > daysInMonth y m then none
  let (h, mi, s) := time.getD (0, 0, 0)
  return utcOf y m dd h mi s 0 (off.getD localOffset)

/-- Date.parse: the Date Time String Format, then the toString / toUTCString formats; NaN for
anything else. `localOffset`: the local zone's UTC offset in ms.
spec: https://tc39.es/ecma262/#sec-date.parse -/
def parse (str : JSStr) (localOffset : Int := 0) : F64 :=
  let s := str.toString.trimAscii.toString
  match parseISO s localOffset with
  | some t => t
  | none => (parseLegacy s localOffset).getD .nan

end Date

end ES.Num
