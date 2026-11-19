import ES.Conv
import ES.Num

/-!
# Number ↔ String (bridge to `ES/Num.lean`)

Number::toString and StringToNumber as the object model calls them.
-/

namespace ES

open ES (F64)

/-- Number::toString(x, 10).
spec: https://tc39.es/ecma262/#sec-numeric-types-number-tostring -/
def numberToJSStr (x : F64) : JSStr := Num.toJSStr x

/-- StringToNumber.
spec: https://tc39.es/ecma262/#sec-stringtonumber -/
def stringToNumber (s : JSStr) : F64 := Num.stringToNumber s

end ES

namespace ES.NumOps

open ES (F64)

/-- Number::remainder spec: https://tc39.es/ecma262/#sec-numeric-types-number-remainder -/
def rem (n d : F64) : F64 := Num.remainder n d

def ofBool (b : Bool) : F64 := if b then F64.one else F64.zero

/-- Number::exponentiate spec: https://tc39.es/ecma262/#sec-numeric-types-number-exponentiate -/
def pow (b e : F64) : F64 := Num.exponentiate b e

end ES.NumOps
