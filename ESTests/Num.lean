import ES.Num

/-!
# Tests for `ES/Num.lean`

`lake build es-num-test && .lake/build/bin/es-num-test` runs the fixed checks below (expected
values from V8 / the spec). `es-num-test cross FILE` evaluates the operations listed in FILE (one
per line, Numbers as 16 hex digits of their binary64 encoding) and prints one result per line;
`tools/es-num-cross.mjs` (scratch) compares those with node and with mpmath.
-/

open ES ES.Num

def num (s : String) : F64 := stringToNumber (JSStr.ofString s)
def hex (x : F64) : String :=
  let s := String.ofList (Nat.toDigits 16 (toFloat64Bits x).toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s
def ofHex (s : String) : F64 :=
  ofFloat64Bits (s.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87)) 0).toUInt64

/-- Checks: (description, got, expected). -/
def ordStr : Option Ordering → String
  | some .lt => "(some lt)" | some .eq => "(some eq)" | some .gt => "(some gt)" | none => "none"

def checks : List (String × String × String) :=
  let ts (x : F64) := toStringDec x
  let tsr (x : F64) (r : Nat) := toStringRadix x r
  [ -- Number::toString
    ("0.1+0.2", ts (F64.add (num "0.1") (num "0.2")), "0.30000000000000004"),
    ("1e21", ts (num "1e21"), "1e+21"),
    ("1e20", ts (num "1e20"), "100000000000000000000"),
    ("123e-20", ts (num "123e-20"), "1.23e-18"),
    ("5e-324", ts (num "5e-324"), "5e-324"),
    ("max", ts (num "1.7976931348623157e308"), "1.7976931348623157e+308"),
    ("1e-7", ts (num "1e-7"), "1e-7"),
    ("1e-6", ts (num "0.000001"), "0.000001"),
    ("-0", ts (num "-0"), "0"),
    ("2^60", ts (num "1152921504606846976"), "1152921504606847000"),
    ("tie even", ts (num "1125899906842624.25"), "1125899906842624.2"),
    ("NaN", ts .nan, "NaN"), ("-Inf", ts (.inf true), "-Infinity"),
    ("(255).toString(16)", tsr (num "255") 16, "ff"),
    ("(0.5).toString(2)", tsr (num "0.5") 2, "0.1"),
    ("(-255.5).toString(16)", tsr (num "-255.5") 16, "-ff.8"),
    ("(0.1).toString(3)", tsr (num "0.1") 3, "0.0022002200220022002200220022002201"),
    ("(1e21).toString(36)", tsr (num "1e21") 36, "5v1j4f4ds7c000"),
    ("(3.14159).toString(7)", tsr (num "3.14159") 7, "3.066364631133534554"),
    -- StringToNumber
    ("ws", ts (num " 　  12.5e1 ﻿"), "125"),
    ("hex", ts (num "0x1F"), "31"), ("bin", ts (num "0b101"), "5"), ("oct", ts (num "0O17"), "15"),
    ("-hex", ts (num "-0x10"), "NaN"), ("0x", ts (num "0x"), "NaN"), ("empty", ts (num "  "), "0"),
    ("+.5", ts (num "+.5"), "0.5"), ("5.", ts (num "5."), "5"), (".", ts (num "."), "NaN"),
    ("1e", ts (num "1e"), "NaN"), ("Infinity", ts (num "-Infinity"), "-Infinity"),
    ("infinity", ts (num "infinity"), "NaN"), ("1_0", ts (num "1_0"), "NaN"),
    ("1e400", ts (num "1e400"), "Infinity"), ("1e-400", ts (num "-1e-400"), "0"),
    ("-1e-400 sign", hex (num "-1e-400"), "8000000000000000"),
    ("halfway min subnormal", hex (num "2.4703282292062328e-324"), "0000000000000001"),
    ("below halfway", hex (num "2.4703282292062327e-324"), "0000000000000000"),
    ("long", ts (num "9007199254740993.0000000000000000000000000000000000000001"), "9007199254740994"),
    ("long tie", ts (num "9007199254740993"), "9007199254740992"),
    -- parseFloat / parseInt
    ("parseFloat", ts (parseFloat "  -0.5e3xyz"), "-500"),
    ("parseFloat -0", hex (parseFloat "-0"), "8000000000000000"),
    ("parseFloat Inf", ts (parseFloat "Infinityx"), "Infinity"),
    ("parseFloat 1e", ts (parseFloat "1e"), "1"), ("parseFloat .e1", ts (parseFloat ".e1"), "NaN"),
    ("parseInt 0x", ts (parseInt "  0x1fz" 0), "31"), ("parseInt -12px", ts (parseInt "-12px" 10), "-12"),
    ("parseInt zz", ts (parseInt "zz" 36), "1295"), ("parseInt radix 1", ts (parseInt "1" 1), "NaN"),
    ("parseInt 0x radix 16", ts (parseInt "0x10" 16), "16"), ("parseInt 0x radix 10", ts (parseInt "0x10" 10), "0"),
    ("parseInt -0", hex (parseInt "-0" 10), "8000000000000000"),
    ("parseInt big36", ts (parseInt "123456789abcdefghijklmnopqrstuvwxyz" 36), "8.684682361119716e+52"),
    ("parseInt 1e21", ts (parseInt "1e21" 10), "1"),
    -- toFixed / toExponential / toPrecision
    ("1.005.toFixed(2)", (toFixed (num "1.005") (num "2")).getD "?", "1.00"),
    ("1.45.toFixed(1)", (toFixed (num "1.45") (num "1")).getD "?", "1.4"),
    ("0.5.toFixed(0)", (toFixed (num "0.5") (num "0")).getD "?", "1"),
    ("-0.0000001.toFixed(2)", (toFixed (num "-0.0000001") (num "2")).getD "?", "-0.00"),
    ("1e21.toFixed(2)", (toFixed (num "1e21") (num "2")).getD "?", "1e+21"),
    ("1000000000000000128.toFixed(0)", (toFixed (num "1000000000000000128") (num "0")).getD "?", "1000000000000000128"),
    ("toFixed(101)", (toFixed (num "1") (num "101")).getD "RangeError", "RangeError"),
    ("toExponential()", (toExponential (num "123456") none).getD "?", "1.23456e+5"),
    ("toExponential(2)", (toExponential (num "123456") (some (num "2"))).getD "?", "1.23e+5"),
    ("toExponential 0", (toExponential (num "0") (some (num "2"))).getD "?", "0.00e+0"),
    ("toExponential neg", (toExponential (num "-0.00015") (some (num "1"))).getD "?", "-1.5e-4"),
    ("toExponential carry", (toExponential (num "9.99") (some (num "1"))).getD "?", "1.0e+1"),
    ("toPrecision(4)", (toPrecision (num "123.456") (some (num "4"))).getD "?", "123.5"),
    ("toPrecision(2) exp", (toPrecision (num "123456") (some (num "2"))).getD "?", "1.2e+5"),
    ("toPrecision small", (toPrecision (num "0.000123") (some (num "2"))).getD "?", "0.00012"),
    ("toPrecision e-6", (toPrecision (num "0.00000123") (some (num "2"))).getD "?", "0.0000012"),
    ("toPrecision 0", (toPrecision (num "0") (some (num "3"))).getD "?", "0.00"),
    ("toPrecision 1", (toPrecision (num "5e-7") (some (num "1"))).getD "?", "5e-7"),
    -- operations
    ("2**10", ts (exponentiate (num "2") (num "10")), "1024"),
    ("(-8)**(1/3)", ts (exponentiate (num "-8") (F64.div one (num "3"))), "NaN"),
    ("(-0)**-3", ts (exponentiate negZero (num "-3")), "-Infinity"),
    ("(-0)**-2", ts (exponentiate negZero (num "-2")), "Infinity"),
    ("(-Inf)**3", ts (exponentiate (.inf true) (num "3")), "-Infinity"),
    ("(-Inf)**-3 sign", hex (exponentiate (.inf true) (num "-3")), "8000000000000000"),
    ("1**Inf", ts (exponentiate one (.inf false)), "NaN"),
    ("(-1)**-Inf", ts (exponentiate negOne (.inf true)), "NaN"),
    ("0.5**-Inf", ts (exponentiate (num "0.5") (.inf true)), "Infinity"),
    ("NaN**0", ts (exponentiate .nan posZero), "1"),
    ("4**0.5", ts (exponentiate (num "4") (num "0.5")), "2"),
    ("10**308", ts (exponentiate (num "10") (num "308")), "1e+308"),
    ("10**-5", ts (exponentiate (num "10") (num "-5")), "0.00001"),
    ("2**-1074", ts (exponentiate (num "2") (num "-1074")), "5e-324"),
    ("2**-1075", ts (exponentiate (num "2") (num "-1075")), "0"),
    ("(1+2^-52)**2^52", ts (exponentiate (num "1.0000000000000002") (num "4503599627370496")), "2.718281828459045"),
    ("5.5 % 2", ts (remainder (num "5.5") (num "2")), "1.5"),
    ("-5.5 % 2", ts (remainder (num "-5.5") (num "2")), "-1.5"),
    ("-4 % 2", hex (remainder (num "-4") (num "2")), "8000000000000000"),
    ("1e308 % 3", ts (remainder (num "1e308") (num "3")), "2"),
    ("5e-324 % Inf", ts (remainder (num "5e-324") (.inf false)), "5e-324"),
    ("ToInt32(2^32+5)", toString (toInt32 (num "4294967301")), "5"),
    ("ToInt32(-1.5)", toString (toInt32 (num "-1.5")), "-1"),
    ("ToInt32(2^31)", toString (toInt32 (num "2147483648")), "-2147483648"),
    ("ToUint32(-1)", toString (toUint32 (num "-1")), "4294967295"),
    ("ToInt32(1e300)", toString (toInt32 (num "1e300")), "0"),
    ("ToInt8(255)", toString (toInt8 (num "255")), "-1"),
    ("ToUint8Clamp(2.5)", toString (toUint8Clamp (num "2.5")), "2"),
    ("ToUint8Clamp(3.5)", toString (toUint8Clamp (num "3.5")), "4"),
    ("ToUint8Clamp(254.6)", toString (toUint8Clamp (num "254.6")), "255"),
    ("1<<31", ts (leftShift one (num "31")), "-2147483648"),
    ("-1>>>0", ts (unsignedRightShift negOne posZero), "4294967295"),
    ("-16>>2", ts (signedRightShift (num "-16") (num "2")), "-4"),
    ("~5", ts (bitwiseNOT (num "5")), "-6"),
    ("5&-2", ts (bitwiseAND (num "5") (num "-2")), "4"),
    ("lessThan NaN", toString (lessThan .nan one), "none"),
    ("-0 == 0", toString (equal negZero posZero), "true"),
    ("sameValue -0 0", toString (sameValue negZero posZero), "false"),
    ("sameValueZero NaN", toString (sameValueZero .nan .nan), "true"),
    -- Math
    ("round(-2.5)", ts (round (num "-2.5")), "-2"),
    ("round(2.5)", ts (round (num "2.5")), "3"),
    ("round(-0.5)", hex (round (num "-0.5")), "8000000000000000"),
    ("round(0.49999999999999994)", ts (round (num "0.49999999999999994")), "0"),
    ("round(-0.2)", hex (round (num "-0.2")), "8000000000000000"),
    ("round(2^52+0.5)?", ts (round (num "4503599627370495.5")), "4503599627370496"),
    ("floor(-0.5)", ts (floor (num "-0.5")), "-1"),
    ("ceil(-0.5)", hex (ceil (num "-0.5")), "8000000000000000"),
    ("trunc(-0.5)", hex (trunc (num "-0.5")), "8000000000000000"),
    ("sqrt(2)", ts (sqrt (num "2")), "1.4142135623730951"),
    ("sqrt(-0)", hex (sqrt negZero), "8000000000000000"),
    ("sqrt(5e-324)", ts (sqrt (num "5e-324")), "2.2227587494850775e-162"),
    ("cbrt(27)", ts (cbrt (num "27")), "3"), ("cbrt(-8)", ts (cbrt (num "-8")), "-2"),
    ("hypot(3,4)", ts (hypot #[num "3", num "4"]), "5"),
    ("hypot(NaN,Inf)", ts (hypot #[.nan, .inf true]), "Infinity"),
    ("hypot()", ts (hypot #[]), "0"),
    ("hypot(1e308,1e308)", ts (hypot #[num "1e308", num "1e308"]), "1.4142135623730951e+308"),
    ("exp(1)", ts (exp one), "2.718281828459045"),
    ("exp(-Inf)", ts (exp (.inf true)), "0"),
    ("exp(709.7)", ts (exp (num "709.7")), "1.6549840276802644e+308"),
    ("exp(-745)", ts (exp (num "-745")), "5e-324"),
    ("expm1(1e-10)", ts (expm1 (num "1e-10")), "1.00000000005e-10"),
    ("log(10)", ts (log (num "10")), "2.302585092994046"),
    ("log(-0)", ts (log negZero), "-Infinity"),
    ("log2(8)", ts (log2 (num "8")), "3"),
    ("log10(1000)", ts (log10 (num "1000")), "3"),
    ("log10(1e-300)", ts (log10 (num "1e-300")), "-300"),
    ("log1p(-1)", ts (log1p negOne), "-Infinity"),
    ("log1p(1e-20)", ts (log1p (num "1e-20")), "1e-20"),
    ("sin(pi)", ts (sin (num "3.141592653589793")), "1.2246467991473532e-16"),
    ("cos(pi)", ts (cos (num "3.141592653589793")), "-1"),
    ("sin(1e300)", ts (sin (num "1e300")), "-0.8178819121159085"),
    ("tan(pi/4)", ts (tan (num "0.7853981633974483")), "0.9999999999999999"),
    ("tan(pi/2)", ts (tan (num "1.5707963267948966")), "16331239353195370"),
    ("atan(Inf)", ts (atan (.inf false)), "1.5707963267948966"),
    ("atan2(1,1)", ts (atan2 one one), "0.7853981633974483"),
    ("atan2(-0,-1)", ts (atan2 negZero negOne), "-3.141592653589793"),
    ("atan2(0,-0)", ts (atan2 posZero negZero), "3.141592653589793"),
    ("atan2(-Inf,-Inf)", ts (atan2 (.inf true) (.inf true)), "-2.356194490192345"),
    ("atan2(1e-300,-1e300)", ts (atan2 (num "1e-300") (num "-1e300")), "3.141592653589793"),
    ("atan2(1e-300,1e300)", ts (atan2 (num "1e-300") (num "1e300")), "0"),
    ("asin(1)", ts (asin one), "1.5707963267948966"),
    ("acos(-1)", ts (acos negOne), "3.141592653589793"),
    ("acos(0.5)", ts (acos (num "0.5")), "1.0471975511965979"),
    ("asinh(1)", ts (asinh one), "0.881373587019543"),
    ("acosh(1)", ts (acosh one), "0"), ("acosh(2) (V8: …166)", ts (acosh (num "2")), "1.3169578969248168"),
    ("atanh(0.5) (V8: …548)", ts (atanh (num "0.5")), "0.5493061443340549"),
    ("sinh(1)", ts (sinh one), "1.1752011936438014"),
    ("cosh(1)", ts (cosh one), "1.5430806348152437"),
    ("tanh(0.5)", ts (tanh (num "0.5")), "0.46211715726000974"),
    ("pow(2,0.5)", ts (pow (num "2") (num "0.5")), "1.4142135623730951"),
    ("clz32(1)", toString (clz32 one), "31"), ("clz32(0)", toString (clz32 posZero), "32"),
    ("imul(0xffffffff,5)", ts (imul (num "4294967295") (num "5")), "-5"),
    ("max()", ts (mathMax #[]), "-Infinity"),
    ("max(-0,0)", hex (mathMax #[negZero, posZero]), "0000000000000000"),
    ("min(0,-0)", hex (mathMin #[posZero, negZero]), "8000000000000000"),
    ("max(NaN,1)", ts (mathMax #[.nan, one]), "NaN"),
    ("sign(-3)", ts (sign (num "-3")), "-1"),
    ("fround(5.5)", ts (fround (num "5.5")), "5.5"),
    ("fround(5.05)", ts (fround (num "5.05")), "5.050000190734863"),
    ("fround(1e40)", ts (fround (num "1e40")), "Infinity"),
    ("fround(1e-46)", ts (fround (num "1e-46")), "0"),
    ("fround(2^-149)", ts (fround (num "1.401298464324817e-45")), "1.401298464324817e-45"),
    ("f16round(5.05)", ts (f16round (num "5.05")), "5.05078125"),
    ("f16round(65520)", ts (f16round (num "65520")), "Infinity"),
    ("f16round(65519)", ts (f16round (num "65519")), "65504"),
    ("f16round(2^-25)", ts (f16round (num "2.9802322387695312e-8")), "0"),
    ("f16round(2^-24*1.5)", ts (f16round (num "8.940696716308594e-8")), "1.1920928955078125e-7"),
    ("sumPrecise([])", hex (sumPrecise #[]), "8000000000000000"),
    ("sumPrecise([1e308,1e308,-1e308])", ts (sumPrecise #[num "1e308", num "1e308", num "-1e308"]), "1e+308"),
    ("sumPrecise([0.1,0.2])", ts (sumPrecise #[num "0.1", num "0.2"]), "0.30000000000000004"),
    ("sumPrecise([1e30,0.1,-1e30])", ts (sumPrecise #[num "1e30", num "0.1", num "-1e30"]), "0.1"),
    ("sumPrecise([-0,-0])", hex (sumPrecise #[negZero, negZero]), "8000000000000000"),
    ("sumPrecise([-0,0])", hex (sumPrecise #[negZero, posZero]), "0000000000000000"),
    ("sumPrecise([Inf,-Inf])", ts (sumPrecise #[.inf false, .inf true]), "NaN"),
    -- encodings
    ("f32 bits 1.5", toString (toFloat32Bits (num "1.5")), toString (0x3FC00000 : Nat)),
    ("f32 bits NaN", toString (toFloat32Bits .nan), toString (0x7FC00000 : Nat)),
    ("f32 bits -0", toString (toFloat32Bits negZero), toString (0x80000000 : Nat)),
    ("f32 bits sub", toString (toFloat32Bits (num "1.401298464324817e-45")), "1"),
    ("f32 decode", ts (ofFloat32Bits 0x3F800001), "1.0000001192092896"),
    ("f16 bits 1", toString (toFloat16Bits one), toString (0x3C00 : Nat)),
    ("f16 decode max", ts (ofFloat16Bits 0x7BFF), "65504"),
    ("f16 decode inf", ts (ofFloat16Bits 0xFC00), "-Infinity"),
    ("f64 roundtrip", ts (ofFloat64Bits (toFloat64Bits (num "0.1"))), "0.1"),
    ("f64 subnormal", ts (ofFloat64Bits 1), "5e-324"),
    -- BigInt
    ("2n**64n toString", BigInt.toString (2 ^ 64), "18446744073709551616"),
    ("(-255n).toString(16)", BigInt.toString (-255) 16, "-ff"),
    ("big radix 36", BigInt.toString (36 ^ 40 - 1) 36, String.ofList (List.replicate 40 'z')),
    ("big decimal", BigInt.toString (10 ^ 100) 10, "1" ++ String.ofList (List.replicate 100 '0')),
    ("StringToBigInt", toString (BigInt.stringToBigInt " -123 "), "(some -123)"),
    ("StringToBigInt hex", toString (BigInt.stringToBigInt "0xff"), "(some 255)"),
    ("StringToBigInt -hex", toString (BigInt.stringToBigInt "-0xff"), "none"),
    ("StringToBigInt 1e3", toString (BigInt.stringToBigInt "1e3"), "none"),
    ("StringToBigInt empty", toString (BigInt.stringToBigInt ""), "(some 0)"),
    ("StringToBigInt 1.", toString (BigInt.stringToBigInt "1."), "none"),
    ("-7n/2n", toString (BigInt.divide (-7) 2 |>.toOption), "(some -3)"),
    ("-7n%2n", toString (BigInt.remainder (-7) 2 |>.toOption), "(some -1)"),
    ("1n/0n", toString (BigInt.divide 1 0 |>.toOption), "none"),
    ("-5n>>1n", toString (BigInt.signedRightShift (-5) 1 |>.toOption), "(some -3)"),
    ("-5n<<-1n", toString (BigInt.leftShift (-5) (-1) |>.toOption), "(some -3)"),
    ("-5n>>1000n", toString (BigInt.signedRightShift (-5) 1000 |>.toOption), "(some -1)"),
    ("-6n&5n", toString (BigInt.bitwiseAND (-6) 5), "0"),
    ("-6n&-5n", toString (BigInt.bitwiseAND (-6) (-5)), "-6"),
    ("-6n|5n", toString (BigInt.bitwiseOR (-6) 5), "-1"),
    ("6n|-5n", toString (BigInt.bitwiseOR 6 (-5)), "-1"),
    ("-6n|-5n", toString (BigInt.bitwiseOR (-6) (-5)), "-5"),
    ("-6n^5n", toString (BigInt.bitwiseXOR (-6) 5), "-1"),
    ("-6n^-5n", toString (BigInt.bitwiseXOR (-6) (-5)), "1"),
    ("12n&-4n", toString (BigInt.bitwiseAND 12 (-4)), "12"),
    ("asIntN(8,255n)", toString (BigInt.asIntN 8 255), "-1"),
    ("asIntN(64,-1n)", toString (BigInt.asIntN 64 (-1)), "-1"),
    ("asUintN(64,-1n)", toString (BigInt.asUintN 64 (-1)), "18446744073709551615"),
    ("asIntN(0,5n)", toString (BigInt.asIntN 0 5), "0"),
    ("2n**-1n", toString (BigInt.exponentiate 2 (-1) |>.toOption), "none"),
    ("0n**0n", toString (BigInt.exponentiate 0 0 |>.toOption), "(some 1)"),
    ("Number(2n**1024n)", ts (BigInt.toNumber (2 ^ 1024)), "Infinity"),
    ("Number(2n**53n+1n)", ts (BigInt.toNumber (2 ^ 53 + 1)), "9007199254740992"),
    ("BigInt(1.5)", toString (BigInt.ofNumber (num "1.5")), "none"),
    ("BigInt(1e21)", toString (BigInt.ofNumber (num "1e21")), "(some 1000000000000000000000)"),
    ("2n**53n+1n > 2**53", ordStr (BigInt.compareNumber (2 ^ 53 + 1) (num "9007199254740992")), "(some gt)"),
    ("-1n < -0.5", ordStr (BigInt.compareNumber (-1) (num "-0.5")), "(some lt)"),
    ("0n == -0", toString (BigInt.equalNumber 0 negZero), "true"),
    -- Date
    ("day(0)", toString (Date.day 0), "0"),
    ("day(-1)", toString (Date.day (-1)), "-1"),
    ("year 2000-03-01", toString (Date.yearFromTime 951868800000), "2000"),
    ("month 2000-03-01", toString (Date.monthFromTime 951868800000), "2"),
    ("date 2000-02-29", toString (Date.dateFromTime 951782400000), "29"),
    ("weekday 1970-01-01", toString (Date.weekDay 0), "4"),
    ("year -1", toString (Date.yearFromTime (-1)), "1969"),
    ("year -62198755200000", toString (Date.yearFromTime (-62198755200000)), "-1"),
    ("dayFromYear 2000", toString (Date.dayFromYear 2000), "10957"),
    ("inLeapYear 1900", toString (Date.inLeapYear (Date.timeFromYear 1900)), "false"),
    ("hour", toString (Date.hourFromTime (-1)), "23"),
    ("makeDay(2000,1,29)", ts (Date.makeDay (num "2000") one (num "29")), "11016"),
    ("makeDay(2000,-1,1)", ts (Date.makeDay (num "2000") negOne one), "10926"),
    ("makeTime", ts (Date.makeTime one (num "2") (num "3") (num "4.7")), "3723004"),
    ("makeDate", ts (Date.makeDate (num "1") (num "5")), "86400005"),
    ("timeClip 8.64e15+1", ts (Date.timeClip (num "8640000000000001")), "NaN"),
    ("timeClip -0", hex (Date.timeClip negZero), "0000000000000000"),
    ("makeFullYear 99", ts (Date.makeFullYear (num "99.5")), "1999"),
    ("toISOString", (Date.toISOString posZero).getD "?", "1970-01-01T00:00:00.000Z"),
    ("toISOString max", (Date.toISOString (num "8.64e15")).getD "?", "+275760-09-13T00:00:00.000Z"),
    ("toISOString neg", (Date.toISOString (num "-62198755200001")).getD "?", "-000002-12-31T23:59:59.999Z"),
    ("toString", Date.toDateString posZero, "Thu Jan 01 1970 00:00:00 GMT+0000 (Coordinated Universal Time)"),
    ("toString offset", Date.toDateString posZero (-18000000) "Eastern Standard Time",
      "Wed Dec 31 1969 19:00:00 GMT-0500 (Eastern Standard Time)"),
    ("toUTCString", Date.toUTCString (num "-62198755200000"), "Fri, 01 Jan -0001 00:00:00 GMT"),
    ("toDateString", Date.toDateOnlyString (num "951782400000"), "Tue Feb 29 2000"),
    ("toTimeString", Date.toTimeString (num "3723004"), "01:02:03 GMT+0000 (Coordinated Universal Time)"),
    ("Invalid Date", Date.toDateString .nan, "Invalid Date"),
    ("parse ISO", ts (Date.parse "2000-02-29T12:30:15.5Z"), "951827415500"),
    ("parse ISO date", ts (Date.parse "1970-01-02"), "86400000"),
    ("parse ISO local", ts (Date.parse "1970-01-01T00:00" 3600000), "-3600000"),
    ("parse ISO offset", ts (Date.parse "1970-01-01T00:00:00+01:00"), "-3600000"),
    ("parse ISO year", ts (Date.parse "+275760-09-13T00:00:00.000Z"), "8640000000000000"),
    ("parse ISO year+1ms", ts (Date.parse "+275760-09-13T00:00:00.001Z"), "NaN"),
    ("parse -000000", ts (Date.parse "-000000-01-01T00:00:00Z"), "NaN"),
    ("parse 2000-02-30", ts (Date.parse "2000-02-30"), "NaN"),
    ("parse T24", ts (Date.parse "1970-01-01T24:00:00Z"), "86400000"),
    ("parse YYYY", ts (Date.parse "1970"), "0"),
    ("parse YYYY-MM", ts (Date.parse "1970-02"), "2678400000"),
    ("parse toString", ts (Date.parse "Thu Jan 01 1970 00:00:00 GMT+0100 (CET)"), "-3600000"),
    ("parse toUTCString", ts (Date.parse "Fri, 01 Jan -0001 00:00:00 GMT"), "-62198755200000"),
    ("parse toDateString local", ts (Date.parse "Tue Feb 29 2000" 0), "951782400000"),
    ("parse garbage", ts (Date.parse "hello"), "NaN")
  ]

def runChecks : IO UInt32 := do
  let mut fails := 0
  for (d, got, want) in checks do
    if got != want then
      IO.println s!"FAIL {d}: got {got}, expected {want}"
      fails := fails + 1
  IO.println s!"{checks.length - fails}/{checks.length} checks passed"
  return if fails == 0 then 0 else 1

def unary : List (String × (F64 → F64)) :=
  [("abs", abs), ("acos", acos), ("acosh", acosh), ("asin", asin), ("asinh", asinh), ("atan", atan),
   ("atanh", atanh), ("cbrt", cbrt), ("ceil", ceil), ("cos", cos), ("cosh", cosh), ("exp", exp),
   ("expm1", expm1), ("floor", floor), ("fround", fround), ("f16round", f16round), ("log", log),
   ("log1p", log1p), ("log10", log10), ("log2", log2), ("round", round), ("sign", sign), ("sin", sin),
   ("sinh", sinh), ("sqrt", sqrt), ("tan", tan), ("tanh", tanh), ("trunc", trunc)]

def binary : List (String × (F64 → F64 → F64)) :=
  [("atan2", atan2), ("pow", pow), ("mod", remainder), ("hypot", fun a b => hypot #[a, b]),
   ("add", F64.add), ("mul", F64.mul), ("div", F64.div), ("imul", imul), ("shl", leftShift),
   ("sar", signedRightShift), ("shr", unsignedRightShift), ("and", bitwiseAND), ("or", bitwiseOR),
   ("xor", bitwiseXOR)]

/-- Decodes %XX escapes (strings in the cross-check file). -/
def unescape (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut bytes : ByteArray := .empty
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '%' && i + 2 < cs.size then
      let h (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
      bytes := bytes.push (h cs[i+1]! * 16 + h cs[i+2]!).toUInt8
      i := i + 3
    else
      for b in cs[i]!.toString.toUTF8 do bytes := bytes.push b
      i := i + 1
  return (String.fromUTF8? bytes).getD "?"

def crossLine (line : String) : String :=
  match line.splitOn " " with
  | ["ts", x] => toStringDec (ofHex x)
  | ["tr", x, r] => toStringRadix (ofHex x) r.toNat!
  | ["sn", s] => hex (stringToNumber (JSStr.ofString (unescape s)))
  | ["pf", s] => hex (parseFloat (JSStr.ofString (unescape s)))
  | ["pi", s, r] => hex (parseInt (JSStr.ofString (unescape s)) r.toInt!)
  | ["fx", x, f] => (toFixed (ofHex x) (ofInt f.toInt!)).getD "RangeError"
  | ["ex", x, f] => (toExponential (ofHex x) (if f == "u" then none else some (ofInt f.toInt!))).getD "RangeError"
  | ["pr", x, f] => (toPrecision (ofHex x) (if f == "u" then none else some (ofInt f.toInt!))).getD "RangeError"
  | ["i32", x] => toString (toInt32 (ofHex x))
  | ["u8c", x] => toString (toUint8Clamp (ofHex x))
  | ["f32", x] => toString (toFloat32Bits (ofHex x))
  | ["f16", x] => toString (toFloat16Bits (ofHex x))
  | ["iso", x] => (Date.toISOString (ofHex x)).getD "RangeError"
  | ["utc", x] => Date.toUTCString (ofHex x)
  | ["dp", s] => hex (Date.parse (JSStr.ofString (unescape s)))
  | [f, x] => match unary.lookup f with
    | some g => hex (g (ofHex x))
    | none => "?op"
  | [f, x, y] => match binary.lookup f with
    | some g => hex (g (ofHex x) (ofHex y))
    | none => "?op"
  | _ => "?line"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cross", file] =>
    let lines ← IO.FS.lines file
    let out ← IO.getStdout
    for l in lines do
      if !l.isEmpty then out.putStrLn (crossLine l)
    return 0
  | ["time", fn, x, n] =>
    -- (timing: n evaluations)
    let v := ofHex x
    let mut acc : Nat := 0
    for i in [0:n.toNat!] do
      let r := match unary.lookup fn with
        | some g => g (F64.add v (ofInt (i % 2)))
        | none => match fn with
          | "ts" => num (toStringDec (F64.add v (ofInt i)))
          | _ => .nan
      acc := acc + (toFloat64Bits r).toNat % 7
    IO.println s!"{acc}"
    return 0
  | _ => runChecks
