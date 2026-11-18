/-
  Runtime for executable Lean output.

  The verified IR → Lean translator produces an *untyped* Lean expression:
  its meaning is given by the model semantics in `LeanJS.Semantics.LeanEval`,
  where a variable can hold a number in one place and a function in another.
  Such a term is not well-typed Lean. `LeanJS.Lean.EmitExec` therefore prints
  it as real Lean code over the dynamic value type `Val` defined here, so the
  output can be compiled and run.

  The runtime mirrors `LeanEval` clause by clause:
  * evaluation is left to right in the `Except Sig` monad (`Sig.throw` is a
    Lean-level `throw`, `Sig.error` a "stuck" evaluation);
  * primitive operators call the very same `evalBinOp` / `evalUnaryOp` as
    the model semantics, so the operator semantics is shared, not copied;
  * functions are curried closures of one argument.

  `Val` has a constructor with a function argument that mentions `Val`
  negatively, so it is an `unsafe inductive`; nothing in the verified
  development depends on this module.
-/
import LeanJS.Semantics.BinOp

namespace LeanJS.Runtime

open LeanJS.IR
open LeanJS.Semantics

mutual

/-- Dynamic values of the Lean core fragment -/
unsafe inductive Val where
  /-- Numbers, strings, booleans, `()` (as `IRValue`s) -/
  | prim (v : IRValue)
  | fn (f : Val → Except Sig Val)
  | record (fields : List (String × Val))
  | array (elems : List Val)

/-- Abrupt completion -/
unsafe inductive Sig where
  /-- An uncaught `throw v` -/
  | throw (v : Val)
  /-- The model semantics has no derivation here (a runtime type error) -/
  | error (msg : String)

end

/-- A computation producing a value -/
unsafe abbrev R := Except Sig Val

namespace Val

unsafe def num (n : Float) : Val := .prim (.number n)
unsafe def str (s : String) : Val := .prim (.string s)
unsafe def bool (b : Bool) : Val := .prim (.bool b)
unsafe def unit : Val := .prim .unit

/-- The `IRValue` an operator sees. Non-primitive values are replaced by a
    representative of the same kind; `evalBinOp` / `evalUnaryOp` only inspect
    primitives (and truthiness, which is `true` for every non-primitive). -/
unsafe def toIR : Val → IRValue
  | .prim v => v
  | .fn _ => .closure .nil none [] .undefined
  | .record _ => .record []
  | .array _ => .array []

unsafe def truthy (v : Val) : Bool := isTruthy v.toIR

unsafe def ofResult : EvalResult → R
  | .val v _ => pure (.prim v)
  | .error msg => throw (.error msg)
  | _ => throw (.error "unexpected signal from operator")

/-- `l op r` for every operator except `&&` / `||` -/
unsafe def binop (op : IRBinOp) (l r : Val) : R :=
  ofResult (evalBinOp op l.toIR r.toIR Store.empty)

/-- `l && r`: the right operand is evaluated only if `l` is truthy -/
unsafe def and (l : Val) (r : Unit → R) : R :=
  if l.truthy then r () else pure l

/-- `l || r`: the right operand is evaluated only if `l` is falsy -/
unsafe def or (l : Val) (r : Unit → R) : R :=
  if l.truthy then pure l else r ()

unsafe def unop (op : IRUnaryOp) (v : Val) : R :=
  ofResult (evalUnaryOp op v.toIR Store.empty)

unsafe def call (f a : Val) : R :=
  match f with
  | .fn g => g a
  | _ => throw (.error "application of non-function")

unsafe def proj (v : Val) (k : String) : R :=
  match v with
  | .record fs =>
    match fs.lookup k with
    | some x => pure x
    | none => throw (.error s!"missing field {k}")
  | _ => throw (.error s!"projection .{k} of a non-record")

/-! ## Output, in the format of JavaScript's `JSON.stringify` -/

def jsonString (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.toNat < 0x20 then
        "\\u" ++ String.mk ((Nat.toDigits 16 c.toNat).leftpad 4 '0') else c.toString
  "\"" ++ body ++ "\""

/-- The shortest decimal `m / 10^k` (k ≤ 17) that reads back as `n`, for
    `0 < n < 2^53`. -/
def shortestDecimal (n : Float) : Option String :=
  (List.range 18).findSome? fun k =>
    let scale := (10 : Float) ^ k.toFloat
    let m := (n * scale).round
    if m < 9007199254740992.0 && m / scale == n then
      let digits := toString m.toUInt64.toNat
      let digits := String.mk (List.replicate (k + 1 - min (k + 1) digits.length) '0') ++ digits
      let intPart := digits.take (digits.length - k)
      let frac := digits.drop (digits.length - k)
      some (if k == 0 then intPart else intPart ++ "." ++ frac)
    else none

/-- Numbers as JavaScript prints them: exact for integers below 2^53 and for
    decimals with at most 17 fractional digits; other finite numbers fall
    back to Lean's `Float` formatting, which can differ from JS. -/
def jsonNumber (n : Float) : String :=
  if n.isNaN || n.isInf then "null"
  else if n == 0 then "0"
  else
    let sign := if n < 0 then "-" else ""
    match shortestDecimal n.abs with
    | some s => sign ++ s
    | none => toString n

/-- `none` for values that `JSON.stringify` omits (functions and `()`,
    which is JavaScript's `undefined`). -/
unsafe def toJSON? : Val → Option String
  | .prim (.number n) => some (jsonNumber n)
  | .prim (.string s) => some (jsonString s)
  | .prim (.bool b) => some (toString b)
  | .prim _ => none
  | .fn _ => none
  | .array vs => some ("[" ++ ",".intercalate (vs.map fun v => (toJSON? v).getD "null") ++ "]")
  | .record fs =>
    some ("{" ++ ",".intercalate (fs.filterMap fun (k, v) =>
      (toJSON? v).map (jsonString k ++ ":" ++ ·)) ++ "}")

unsafe def toJSON (v : Val) : String := (toJSON? v).getD "undefined"

end Val

/-- Print the outcome of a program -/
unsafe def report (r : R) : IO Unit :=
  match r with
  | .ok v => IO.println v.toJSON
  | .error (.throw v) => IO.println s!"uncaught exception: {v.toJSON}"
  | .error (.error msg) => IO.println s!"runtime error: {msg}"

end LeanJS.Runtime
