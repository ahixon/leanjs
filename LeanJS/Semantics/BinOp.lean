/-
  Binary and unary operator evaluation for IR semantics.
-/
import LeanJS.Semantics.Value

namespace LeanJS.Semantics

open LeanJS.IR

/-- NaN value (0/0) -/
private def nan : Float := 0.0 / 0.0

/-- Float modulo via UInt32 for integer-like values, otherwise approximate -/
private def floatMod (a b : Float) : Float :=
  let bi := b.toUInt32.toNat
  if bi == 0 then nan
  else Float.ofNat (a.toUInt32.toNat % bi)

/-- Bitwise ops work on UInt32 -/
private def bitAnd (a b : Float) : Float :=
  Float.ofNat (a.toUInt32 &&& b.toUInt32).toNat
private def bitOr (a b : Float) : Float :=
  Float.ofNat (a.toUInt32 ||| b.toUInt32).toNat
private def bitXor (a b : Float) : Float :=
  Float.ofNat (a.toUInt32 ^^^ b.toUInt32).toNat
private def bitShl (a b : Float) : Float :=
  Float.ofNat (a.toUInt32 <<< b.toUInt32).toNat
private def bitShr (a b : Float) : Float :=
  Float.ofNat (a.toUInt32 >>> b.toUInt32).toNat
private def bitNot (n : Float) : Float :=
  -- Complement within 32 bits: xor with 0xFFFFFFFF
  Float.ofNat (n.toUInt32 ^^^ 0xFFFFFFFF).toNat

/-- Evaluate a binary operator on two values -/
def evalBinOp (op : IRBinOp) (l r : IRValue) (store : Store) : EvalResult :=
  match op, l, r with
  -- Arithmetic on numbers
  | .add, .number a, .number b => .val (.number (a + b)) store
  | .sub, .number a, .number b => .val (.number (a - b)) store
  | .mul, .number a, .number b => .val (.number (a * b)) store
  | .div, .number a, .number b => .val (.number (a / b)) store
  | .mod, .number a, .number b => .val (.number (floatMod a b)) store
  | .exp, .number a, .number b => .val (.number (a ^ b)) store
  -- String concat
  | .add, .string a, .string b => .val (.string (a ++ b)) store
  | .strConcat, .string a, .string b => .val (.string (a ++ b)) store
  -- String + number coercion (JS-like)
  | .add, .string a, .number b => .val (.string (a ++ toString b)) store
  | .add, .number a, .string b => .val (.string (toString a ++ b)) store
  -- Comparison on numbers
  | .lt, .number a, .number b => .val (.bool (a < b)) store
  | .lte, .number a, .number b => .val (.bool (a <= b)) store
  | .gt, .number a, .number b => .val (.bool (a > b)) store
  | .gte, .number a, .number b => .val (.bool (a >= b)) store
  -- Equality (structural)
  | .eq, .number a, .number b => .val (.bool (a == b)) store
  | .eq, .string a, .string b => .val (.bool (a == b)) store
  | .eq, .bool a, .bool b => .val (.bool (a == b)) store
  | .eq, .unit, .unit => .val (.bool true) store
  | .eq, .undefined, .undefined => .val (.bool true) store
  | .eq, .undefined, .unit => .val (.bool true) store
  | .eq, .unit, .undefined => .val (.bool true) store
  -- Inequality
  | .neq, .number a, .number b => .val (.bool (a != b)) store
  | .neq, .string a, .string b => .val (.bool (a != b)) store
  | .neq, .bool a, .bool b => .val (.bool (a != b)) store
  | .neq, .unit, .unit => .val (.bool false) store
  | .neq, .undefined, .undefined => .val (.bool false) store
  -- Logical operators (short-circuit semantics handled in eval, these are fallback)
  | .and, _, _ =>
    if isTruthy l then .val r store else .val l store
  | .or, _, _ =>
    if isTruthy l then .val l store else .val r store
  -- Bitwise
  | .bitAnd, .number a, .number b => .val (.number (bitAnd a b)) store
  | .bitOr, .number a, .number b => .val (.number (bitOr a b)) store
  | .bitXor, .number a, .number b => .val (.number (bitXor a b)) store
  | .shl, .number a, .number b => .val (.number (bitShl a b)) store
  | .shr, .number a, .number b => .val (.number (bitShr a b)) store
  | .ushr, .number a, .number b => .val (.number (bitShr a b)) store
  -- String comparison
  | .lt, .string a, .string b => .val (.bool (a < b)) store
  | .lte, .string a, .string b => .val (.bool (a ≤ b)) store
  | .gt, .string a, .string b => .val (.bool (b < a)) store
  | .gte, .string a, .string b => .val (.bool (b ≤ a)) store
  -- Type mismatch
  | _, _, _ => .error s!"binOp type mismatch: {repr op}"

/-- Evaluate a unary operator -/
def evalUnaryOp (op : IRUnaryOp) (v : IRValue) (store : Store) : EvalResult :=
  match op, v with
  | .neg, .number n => .val (.number (-n)) store
  | .not, _ => .val (.bool (!isTruthy v)) store
  | .bitNot, .number n => .val (.number (bitNot n)) store
  | .typeof, .number _ => .val (.string "number") store
  | .typeof, .string _ => .val (.string "string") store
  | .typeof, .bool _ => .val (.string "boolean") store
  | .typeof, .undefined => .val (.string "undefined") store
  | .typeof, .unit => .val (.string "undefined") store
  | .typeof, .closure .. => .val (.string "function") store
  | .typeof, .record _ => .val (.string "object") store
  | .typeof, .array _ => .val (.string "object") store
  | .typeof, .ref _ => .val (.string "object") store
  | .typeof, .constructed .. => .val (.string "object") store
  | _, _ => .error s!"unaryOp type mismatch: {repr op}"

end LeanJS.Semantics
