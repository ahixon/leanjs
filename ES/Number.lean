/-!
# ECMAScript Number values

The Number type's values are IEEE 754-2019 binary64 values (spec:
https://tc39.es/ecma262/#sec-ecmascript-language-types-number-type), modelled exactly without
`Float`: a finite value is a sign, an integer significand, and a binary exponent; results of
operations are the exact result rounded to the nearest value, ties to even (spec:
https://tc39.es/ecma262/#number-value). Values cross to and from the engine as decimal strings:
the engine's `ToString` (the shortest decimal that rounds back to the value) in, the exact
decimal out (which the engine's `StringToNumber` rounds back to the same value).
-/

namespace ES

/-- A Number value: NaN, an infinity, or (-1)^neg · m · 2^e (zero: m = 0, signed). Finite
values are kept in their canonical form (`F64.round`): m < 2^53, e ≥ -1074, and m ≥ 2^52
unless e = -1074 (a subnormal, or zero). -/
inductive F64 where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)
  deriving DecidableEq, Repr, Inhabited

namespace F64

def zero : F64 := .fin false 0 (-1074)

/-- `n` halved `k` times, rounded to nearest, ties to even. -/
def shiftRound (n : Nat) (k : Nat) : Nat :=
  if k == 0 then n else
  let q := n / 2 ^ k
  let r := n % 2 ^ k
  let half := 2 ^ (k - 1)
  if r > half || (r == half && q % 2 == 1) then q + 1 else q

/-- The Number value nearest to (-1)^neg · num / den (den > 0), ties to even; infinite past the
largest finite value.
spec: https://tc39.es/ecma262/#number-value (round to nearest, ties to even) -/
def ofRat (neg : Bool) (num den : Nat) : F64 :=
  if num == 0 then .fin neg 0 (-1074) else
  -- (the exponent e with 2^52 ≤ num / den / 2^e < 2^53, at least -1074)
  let lg := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  let e0 := max (-1074) (lg - 52 - 1)
  -- (scaled: num / den / 2^e as an integer part with 2 extra bits, then rounded)
  let quo (e : Int) : Nat × Bool :=
    -- (num / (den · 2^e), with whether a remainder is left: exact rounding needs it)
    if e ≥ 0 then (num / (den * 2 ^ e.toNat), num % (den * 2 ^ e.toNat) != 0)
    else (num * 2 ^ (-e).toNat / den, num * 2 ^ (-e).toNat % den != 0)
  -- (the first exponent from e0 whose quotient is below 2^53 (two steps at most past e0))
  let e := if (quo e0).1 < 2 ^ 53 then e0 else if (quo (e0 + 1)).1 < 2 ^ 53 then e0 + 1 else e0 + 2
  -- (round: the quotient at one more bit of precision, the remainder deciding ties)
  let (q2, rest) := quo (e - 1)
  let m := if q2 % 2 == 0 then q2 / 2
    else if rest || (q2 / 2) % 2 == 1 then q2 / 2 + 1 else q2 / 2
  let (m, e) := if m == 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)
  if e > 971 then .inf neg else .fin neg m e

/-- The exact value of a finite Number as a fraction (num, den), den a power of two. -/
def toRat : F64 → Option (Bool × Nat × Nat)
  | .fin neg m e => some (neg, if e ≥ 0 then m * 2 ^ e.toNat else m, if e ≥ 0 then 1 else 2 ^ (-e).toNat)
  | _ => none

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-add -/
def add : F64 → F64 → F64
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => if a == b then .inf a else .nan
  | .inf a, _ | _, .inf a => .inf a
  | x@(.fin a m e), y@(.fin b n f) =>
    if m == 0 && n == 0 then .fin (a && b) 0 (-1074)
    else if m == 0 then y else if n == 0 then x else
    -- (exactly, over the smaller exponent's power of two)
    let g := min e f
    let mx := m * 2 ^ (e - g).toNat
    let ny := n * 2 ^ (f - g).toNat
    let (neg, s) := if a == b then (a, mx + ny) else if mx ≥ ny then (a, mx - ny) else (b, ny - mx)
    -- (an exact zero sum is +0 when rounding to nearest)
    if s == 0 then .fin false 0 (-1074)
    else if g ≥ 0 then ofRat neg (s * 2 ^ g.toNat) 1 else ofRat neg s (2 ^ (-g).toNat)

/-- `<` on Number values (NaN: false).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-lessThan -/
def lt (x y : F64) : Bool :=
  match x, y with
  | .nan, _ | _, .nan => false
  | .inf a, .inf b => a && !b
  | .inf a, _ => a
  | _, .inf b => !b
  | .fin a m e, .fin b n f =>
    if m == 0 && n == 0 then false else
    let g := min e f
    let vx : Int := (if a then -1 else 1) * (m * 2 ^ (e - g).toNat : Nat)
    let vy : Int := (if b then -1 else 1) * (n * 2 ^ (f - g).toNat : Nat)
    vx < vy

def neg : F64 → F64
  | .nan => .nan
  | .inf n => .inf (!n)
  | .fin n m e => .fin (!n) m e

def isNeg (x : F64) : Bool := match x with | .fin n _ _ | .inf n => n | .nan => false
def isZero (x : F64) : Bool := match x with | .fin _ 0 _ => true | _ => false

/-- `Math.min` of two values (NaN if either is; -0 below +0).
spec: https://tc39.es/ecma262/#sec-math.min -/
def min (x y : F64) : F64 :=
  if x == .nan || y == .nan then .nan
  else if x.isZero && y.isZero then (if x.isNeg then x else y)
  else if lt y x then y else x

/-- `Math.max` of two values (NaN if either is; +0 above -0).
spec: https://tc39.es/ecma262/#sec-math.max -/
def max (x y : F64) : F64 :=
  if x == .nan || y == .nan then .nan
  else if x.isZero && y.isZero then (if x.isNeg then y else x)
  else if lt x y then y else x

/-- The digits of a natural number. -/
def digits (n : Nat) : String := toString n

/-- The exact decimal of a Number value (`NaN`, `Infinity`, `-0`, …), which `StringToNumber`
reads back as the same value. -/
def toDecimal : F64 → String
  | .nan => "NaN"
  | .inf n => if n then "-Infinity" else "Infinity"
  | .fin n m e =>
    let sign := if n then "-" else ""
    if m == 0 then sign ++ "0" else
    if e ≥ 0 then sign ++ digits (m * 2 ^ e.toNat) else
    -- (m / 2^k = m · 5^k / 10^k)
    let k := (-e).toNat
    let ds := digits (m * 5 ^ k)
    let ds := String.ofList (List.replicate (k + 1 - Nat.min (k + 1) ds.length) (Char.ofNat 48)) ++ ds
    let intPart := String.ofList (ds.toList.take (ds.length - k))
    let frac := String.ofList ((ds.toList.drop (ds.length - k)).reverse.dropWhile (· == '0')).reverse
    sign ++ intPart ++ (if frac.isEmpty then "" else "." ++ frac)

/-- A Number from a decimal string as the engine's `ToString` writes one (an integer, a decimal,
an exponent, `Infinity`, `NaN`); `none` for anything else.
spec: https://tc39.es/ecma262/#sec-stringtonumber (the StrDecimalLiteral forms) -/
def ofDecimal (s : String) : Option F64 := do
  let s := s.trimAscii.toString
  if s == "NaN" then return .nan
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString) else (false, s)
  if body == "Infinity" then return .inf neg
  let (mant, ex) := match body.splitOn "e" with
    | [m, x] => (m, x)
    | _ => match body.splitOn "E" with
      | [m, x] => (m, x)
      | _ => (body, "0")
  let exp : Int ← if ex.startsWith "+" then (ex.drop 1).toString.toInt? else ex.toInt?
  let (ip, fp) := match mant.splitOn "." with
    | [i, f] => (i, f)
    | _ => (mant, "")
  if ip.isEmpty && fp.isEmpty then none
  if !(ip.all Char.isDigit && fp.all Char.isDigit) then none
  let n := (ip ++ fp).foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0
  let e10 := exp - fp.length
  if e10 ≥ 0 then return ofRat neg (n * 10 ^ e10.toNat) 1
  return ofRat neg n (10 ^ (-e10).toNat)

/-- An integer as a Number. -/
def ofInt (i : Int) : F64 := ofRat (i < 0) i.natAbs 1

def one : F64 := ofInt 1

def isFinite (x : F64) : Bool := match x with | .fin .. => true | _ => false

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-subtract -/
def sub (x y : F64) : F64 := add x (neg y)

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-multiply -/
def mul : F64 → F64 → F64
  | .nan, _ | _, .nan => .nan
  | .inf a, .fin b m _ | .fin b m _, .inf a => if m == 0 then .nan else .inf (a != b)
  | .inf a, .inf b => .inf (a != b)
  | .fin a m e, .fin b n f =>
    let g := e + f
    if g ≥ 0 then ofRat (a != b) (m * n * 2 ^ g.toNat) 1 else ofRat (a != b) (m * n) (2 ^ (-g).toNat)

/-- spec: https://tc39.es/ecma262/#sec-numeric-types-number-divide -/
def div : F64 → F64 → F64
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .inf a, .fin b _ _ => .inf (a != b)
  | .fin a _ _, .inf b => .fin (a != b) 0 (-1074)
  | .fin a m e, .fin b n f =>
    if n == 0 then (if m == 0 then .nan else .inf (a != b)) else
    -- (m·2^e / (n·2^f))
    let g := e - f
    if g ≥ 0 then ofRat (a != b) (m * 2 ^ g.toNat) n else ofRat (a != b) m (n * 2 ^ (-g).toNat)

/-- The IEEE 754 binary64 encoding (sign, biased exponent, fraction), as the host reads numbers
(`Paint.DisplayList`'s canvas items). -/
def toBits : F64 → UInt64
  | .nan => 0x7FF8000000000000
  | .inf n => if n then 0xFFF0000000000000 else 0x7FF0000000000000
  | .fin n m e =>
    let s : UInt64 := if n then 0x8000000000000000 else 0
    -- (subnormal or zero: exponent field 0; else m ≥ 2^52 and the field is e + 1075)
    if m < 2 ^ 52 then s ||| UInt64.ofNat m
    else s ||| (UInt64.ofNat (e + 1075).toNat <<< 52) ||| UInt64.ofNat (m - 2 ^ 52)

/-! ### `sin` and `cos`

`Math.sin` and `Math.cos` are implementation-approximated (spec:
https://tc39.es/ecma262/#sec-math.sin); here the exact value is approximated with dyadic
rationals of 2^-`prec` precision (argument reduction against π to 2^-`prec`, then Taylor series)
and rounded to the nearest Number. -/

/-- The precision of the intermediate values: 2^-120 (far below a Number's 2^-53 relative
precision for arguments up to 2^60; larger arguments are reduced with an error there). -/
def prec : Nat := 120

/-- π to 2^-`prec` (π · 2^prec, rounded down), from its decimal expansion to 60 digits. -/
def piScaled : Nat :=
  314159265358979323846264338327950288419716939937510582097494 * 2 ^ prec / 10 ^ 59

/-- A Taylor series' terms, `x^(k+2)/(k+1)(k+2)` from `x^k/k!`, scaled by 2^prec (`x` too),
alternating; `n` terms. Fuel: the terms fall below 2^-prec after 40 for |x| ≤ π. -/
def taylor (x : Int) : Nat → Nat → Int → Int → Int
  | 0, _, _, acc => acc
  | f + 1, k, term, acc =>
    let next := -(term * x / 2 ^ prec * x / 2 ^ prec) / ((k + 1) * (k + 2) : Nat)
    taylor x f (k + 2) next (acc + next)

/-- (sin x, cos x) · 2^prec for x · 2^prec with |x| ≤ π. -/
def sinCosScaled (x : Int) : Int × Int :=
  (taylor x 40 1 x x, taylor x 40 0 (2 ^ prec) (2 ^ prec))

/-- `x` reduced to [-π, π] (scaled by 2^prec), for a finite `x`. -/
def reduce (x : F64) : Int :=
  match x.toRat with
  | none => 0
  | some (neg, num, den) =>
    let v : Int := (if neg then -1 else 1) * (num * 2 ^ prec / den : Nat)
    let twoPi : Int := 2 * piScaled
    let r := v - twoPi * ((v + piScaled) / twoPi)
    r

def ofScaled (v : Int) : F64 := ofRat (v < 0) v.natAbs (2 ^ prec)

/-- spec: https://tc39.es/ecma262/#sec-math.sin -/
def sin (x : F64) : F64 :=
  match x with
  | .fin _ 0 _ => x
  | .fin .. => ofScaled (sinCosScaled (reduce x)).1
  | _ => .nan

/-- spec: https://tc39.es/ecma262/#sec-math.cos -/
def cos (x : F64) : F64 :=
  match x with
  | .fin .. => ofScaled (sinCosScaled (reduce x)).2
  | _ => .nan

end F64

end ES
