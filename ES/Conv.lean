import ES.Str
import ES.Number

/-!
# Numeric conversions the object model needs

Integer views of Number values (exact), and the bridge to `ES/Num.lean`'s Number::toString and
StringToNumber.
-/

namespace ES

open ES (F64)

namespace Conv

/-- The integer part (truncated toward zero) of a finite Number. -/
def truncInt : F64 → Option Int
  | .fin neg m e =>
    let mag : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    some (if neg then -(mag : Int) else mag)
  | _ => none

/-- Whether a Number is an integral value (finite, no fraction). -/
def isIntegral : F64 → Bool
  | .fin _ m e => e ≥ 0 || m % 2 ^ (-e).toNat == 0
  | _ => false

/-- The value of a Number that is a non-negative integer (incl. -0), if it is one. -/
def toNat? (x : F64) : Option Nat :=
  if isIntegral x then match truncInt x with
    | some i => if i ≥ 0 then some i.toNat else none
    | none => none
  else none

def ofNat (n : Nat) : F64 := F64.ofInt n

/-- ToUint32's numeric part. spec: https://tc39.es/ecma262/#sec-touint32 -/
def toUint32 (x : F64) : Nat :=
  match truncInt x with
  | some i => (i % 4294967296).toNat
  | none => 0

/-- ToInt32's numeric part. spec: https://tc39.es/ecma262/#sec-toint32 -/
def toInt32 (x : F64) : Int :=
  let u := toUint32 x
  if u ≥ 2147483648 then (u : Int) - 4294967296 else u

/-- ToIntegerOrInfinity's numeric part: `none` for ±∞ with the sign (true: -∞).
spec: https://tc39.es/ecma262/#sec-tointegerorinfinity -/
def toIntegerOrInf : F64 → Sum Bool Int
  | .nan => .inr 0
  | .inf neg => .inl neg
  | x => .inr ((truncInt x).getD 0)

end Conv

end ES

namespace ES.Conv

open ES (F64)

/-- The value of a Number that is an integer of magnitude below 2^53 (not ±0), if it is one. -/
@[inline] def smallInt? : F64 → Option Int
  | .fin neg m e =>
    if m == 0 then none else
    if e ≥ 0 then
      if e ≤ 0 then some (if neg then -(m : Int) else m) else none
    else
      let k := (-e).toNat
      if k > 52 then none else
      let q := m >>> k
      if q <<< k != m then none else some (if neg then -(q : Int) else q)
  | _ => none

/-- An integer of magnitude at most 2^53 as a Number (exact; no division). -/
@[inline] def ofSmallInt (i : Int) : F64 :=
  if i == 0 then .fin false 0 (-1074) else
  let a := i.natAbs
  let b := Nat.log2 a
  if b ≤ 52 then .fin (i < 0) (a <<< (52 - b)) ((b : Int) - 52)
  else .fin (i < 0) (a >>> (b - 52)) ((b : Int) - 52)

/-- Exact Number addition with a fast path for small integers (`F64.add` otherwise). -/
def addF (x y : F64) : F64 :=
  match smallInt? x, smallInt? y with
  | some a, some b =>
    let r := a + b
    if r.natAbs ≤ 9007199254740992 then ofSmallInt r else x.add y
  | _, _ => x.add y

def subF (x y : F64) : F64 :=
  match smallInt? x, smallInt? y with
  | some a, some b =>
    let r := a - b
    if r.natAbs ≤ 9007199254740992 then ofSmallInt r else x.sub y
  | _, _ => x.sub y

def mulF (x y : F64) : F64 :=
  match smallInt? x, smallInt? y with
  | some a, some b =>
    let r := a * b
    if r != 0 && r.natAbs ≤ 9007199254740992 then ofSmallInt r else x.mul y
  | _, _ => x.mul y

/-- `<` with a fast path for small integers. -/
def ltF (x y : F64) : Bool :=
  match smallInt? x, smallInt? y with
  | some a, some b => a < b
  | _, _ => x.lt y

/-- Bitwise operations on (infinite two's complement) integers. -/
def intNot (a : Int) : Int := -a - 1

def intAnd (a b : Int) : Int :=
  match a, b with
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .ofNat x, .negSucc y => .ofNat (x - (x &&& y))          -- x & ~y
  | .negSucc x, .ofNat y => .ofNat (y - (y &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)            -- ~(~a | ~b)

def intOr (a b : Int) : Int := intNot (intAnd (intNot a) (intNot b))

def intXor (a b : Int) : Int := intAnd (intOr a b) (intNot (intAnd a b))

end ES.Conv
