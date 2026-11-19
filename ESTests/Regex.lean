import ES.Regex

/-!
# RegExp engine tests

`lake build es-regex-test && .lake/build/bin/es-regex-test [-v]`

- built-in cases (spec examples and engine corner cases);
- the corpora `ESTests/regex_corpus.js` builds from test262 and V8 in `third_party/regex-corpus/`
  (run `node ESTests/regex_corpus.js` first; missing corpora are reported, not silently skipped):
  `exec.txt` (exec calls of test262's tests, V8's results), `fuzz.txt` (random patterns and
  inputs), `syntax.txt` (test262's regex literals: SyntaxErrors and valid ones), `props.txt`
  (test262's generated property-escape tests).
-/

open ES ES.Regex

/-- Hex code units → string. -/
def unhex (s : String) : JSStr := Id.run do
  let cs := s.toList.toArray
  let mut out : Array UInt16 := #[]
  let hv (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  for k in [0:cs.size / 4] do
    out := out.push (hv cs[4*k]! * 4096 + hv cs[4*k+1]! * 256 + hv cs[4*k+2]! * 16 + hv cs[4*k+3]!).toUInt16
  return JSStr.ofUnits out

def showCaps (m : Option Match) : String :=
  match m with
  | none => "null"
  | some m => ";".intercalate (m.captures.toList.map fun
      | some (a, b) => s!"{a},{b}"
      | none => "-")

/-- RegExpBuiltinExec's matching for `lastIndex` (the result's captures). -/
def execLike (p : Program) (input : JSStr) (lastIndex : Nat) : Except String (Option Match) :=
  let li := if p.global || p.sticky then lastIndex else 0
  if li > input.length then .ok none
  else if p.sticky then matchAt p input li
  else search p input li

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  failures : Array String := #[]

def Tally.add (t : Tally) (ok : Bool) (msg : Thunk String) : Tally :=
  if ok then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1, failures := if t.failures.size < 400 then t.failures.push msg.get else t.failures }

def showPat (p : JSStr) (f : String) : String := s!"/{p.toString}/{f}"

/-- An exec case: pattern, flags, input, lastIndex, the expected result. -/
def checkExec (t : Tally) (pat : JSStr) (flags : String) (input : JSStr) (li : Nat) (exp : String) : Tally :=
  match compile pat flags with
  | .error e => t.add (exp == "err") s!"{showPat pat flags}: compile error {e}, expected {exp}"
  | .ok p =>
    if exp == "err" then t.add false s!"{showPat pat flags}: compiled, expected SyntaxError"
    else match execLike p input li with
      | .error e => t.add false s!"{showPat pat flags} on {repr input.toString}@{li}: {e}"
      | .ok m =>
        let got := showCaps m
        t.add (got == exp) s!"{showPat pat flags} on {repr input.toString}@{li}: got {got}, expected {exp}"

/-- Built-in cases: (pattern, flags, input, lastIndex, expected). -/
def builtin : Array (String × String × String × Nat × String) := #[
  -- spec examples (22.2.2)
  ("a|ab", "", "abc", 0, "0,1"),
  ("((a)|(ab))((c)|(bc))", "", "abc", 0, "0,3;0,1;0,1;-;1,3;-;1,3"),
  ("a[a-z]{2,4}", "", "abcdefghi", 0, "0,5"),
  ("a[a-z]{2,4}?", "", "abcdefghi", 0, "0,3"),
  ("(aa|aabaac|ba|b|c)*", "", "aabaac", 0, "0,4;2,4"),
  ("(z)((a+)?(b+)?(c))*", "", "zaacbbbcac", 0, "0,10;0,1;8,10;8,9;-;9,10"),
  ("(a*)*", "", "b", 0, "0,0;-"),
  ("(a*)b\\1+", "", "baaaac", 0, "0,1;0,0"),
  ("(?=(a+))", "", "baaabac", 0, "1,1;1,4"),
  ("(?=(a+))a*b\\1", "", "baaabac", 0, "3,6;3,4"),
  ("(.*?)a(?!(a+)b\\2c)\\2(.*)", "", "baaabaac", 0, "0,8;0,2;-;3,8"),
  ("(?<=\\$)\\d+(\\.\\d*)?", "", "cost $10.53", 0, "6,11;8,11"),
  ("(?<=(\\d+)(\\d+))$", "", "1053", 0, "4,4;0,1;1,4"),
  ("(?<=\\1(a))b", "", "aab", 0, "2,3;1,2"),
  -- case-insensitive
  ("\\u212A", "i", "k", 0, "null"),
  ("\\u212A", "iu", "k", 0, "0,1"),
  ("\\w", "iu", "ſ", 0, "0,1"),
  ("\\W", "iu", "ſ", 0, "null"),
  ("[^\\W]", "iu", "S", 0, "0,1"),
  ("ß", "i", "SS", 0, "null"),
  ("σ", "i", "Σ", 0, "0,1"),
  ("ς", "iu", "Σ", 0, "0,1"),
  -- unicode
  ("^.$", "u", "😀", 0, "0,2"),
  ("^.$", "", "😀", 0, "null"),
  ("\\udf06", "u", "𝌆", 0, "null"),
  ("(?<=😀)a", "u", "😀a", 0, "2,3"),
  ("[😀-😂]", "u", "😁", 0, "0,2"),
  -- annex B
  ("\\8", "", "8", 0, "0,1"),
  ("a{,5}", "", "a{,5}", 0, "0,5"),
  ("]", "", "]", 0, "0,1"),
  ("\\c", "", "\\c", 0, "0,2"),
  ("[\\c_]", "", "\u001F", 0, "0,1"),
  ("\\1(a)", "", "a", 0, "0,1;0,1"),
  ("\\2(a)", "", "\u0002a", 0, "0,2;1,2"),
  ("(?=a)*a", "", "a", 0, "0,1"),
  -- modifiers
  ("(?i:a)b", "", "Ab", 0, "0,2"),
  ("(?i:a)b", "", "AB", 0, "null"),
  ("(?-i:a)b", "i", "aB", 0, "0,2"),
  ("(?-i:a)b", "i", "AB", 0, "null"),
  ("(?s:.)", "", "\n", 0, "0,1"),
  ("(?m:^b)", "", "a\nb", 0, "2,3"),
  -- v flag
  ("[\\q{abc|d}]", "v", "abc", 0, "0,3"),
  ("^[\\p{RGI_Emoji}--\\q{😀}]$", "v", "😀", 0, "null"),
  ("[[a-z]--[aeiou]]+", "v", "bcdea", 0, "0,3"),
  ("[\\w&&\\d]+", "v", "ab12", 0, "2,4"),
  ("[^\\q{a}]", "v", "a", 0, "null"),
  -- duplicate named groups
  ("(?<a>x)|(?<a>y)", "", "y", 0, "0,1;-;0,1"),
  ("(?:(?<a>x)|(?<a>y))\\k<a>", "", "yy", 0, "0,2;-;0,1"),
  -- sticky / global
  ("a", "y", "ba", 1, "1,2"),
  ("a", "y", "ba", 0, "null"),
  ("a", "g", "aba", 1, "2,3"),
  -- quantifier limits
  ("b{9007199254740991}", "", "b", 0, "null"),
  ("a{0,4294967295}", "", "aaa", 0, "0,3"),
  -- syntax errors
  ("(?<a>x)(?<a>y)", "", "", 0, "err"),
  ("\\k<a>", "u", "", 0, "err"),
  ("{1}", "", "", 0, "err"),
  ("a{2,1}", "", "", 0, "err"),
  ("(?<=a)*", "", "", 0, "err"),
  ("(?=a)*", "u", "", 0, "err"),
  ("[b-a]", "", "", 0, "err"),
  ("[\\d-a]", "u", "", 0, "err"),
  ("\\p{RGI_Emoji}", "u", "", 0, "err"),
  ("[^\\p{RGI_Emoji}]", "v", "", 0, "err"),
  ("(?ii:a)", "", "", 0, "err"),
  ("(?i-i:a)", "", "", 0, "err"),
  ("(?-:a)", "", "", 0, "err"),
  ("a", "uv", "", 0, "err"),
  ("a", "gg", "", 0, "err"),
  ("[a&&&b]", "v", "", 0, "err"),
  ("[a-z&&b]", "v", "", 0, "err")
]

def readLines (path : String) : IO (Option (Array String)) := do
  if !(← System.FilePath.pathExists path) then return none
  let s ← IO.FS.readFile path
  return some ((s.splitOn "\n").filter (!·.isEmpty)).toArray

def report (name : String) (t : Tally) (verbose : Bool) : IO Unit := do
  IO.println s!"{name}: {t.pass}/{t.pass + t.fail} pass"
  let shown := if verbose then t.failures else t.failures.extract 0 15
  for f in shown do IO.println s!"  FAIL {f}"
  if !verbose && t.failures.size > 15 then IO.println s!"  … {t.fail - 15} more (-v)"

def parseRanges (s : String) : CharSet :=
  let hv (x : String) : Nat := x.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0
  CharSet.ofPairs (((s.splitOn ",").filter (!·.isEmpty)).toArray.map fun r =>
    match r.splitOn "-" with
    | [a, b] => (hv a, hv b)
    | _ => (1, 0))

/-- The character class a `^X+$`-shaped program tests (inverted classes complemented). -/
def progClass (p : Program) : Option CharSet :=
  p.insts.findSome? fun
    | .cls k _ _ =>
      let c := p.classes[k]!
      some (if c.invert then c.set.complement 0x10FFFF else c.set)
    | _ => none

/-! ## Benchmarks (`es-regex-test --bench`) -/

def benchOne (name : String) (pat flags : String) (input : JSStr) (reps : Nat) (sticky : Bool := false) : IO Unit := do
  let p ← match compile pat flags with
    | .ok p => pure p
    | .error e => IO.println s!"{name}: {e}"; return
  let t0 ← IO.monoNanosNow
  let mut found := 0
  let mut status := ""
  for _ in [0:reps] do
    -- all matches, as a global exec loop does
    let mut i := 0
    for _ in [0:input.length + 1] do
      match (if sticky then matchAt p input i else search p input i) with
      | .ok (some m) =>
        found := found + 1
        i := if m.endIndex == i then i + 1 else m.endIndex
        if i > input.length then break
      | .ok none => break
      | .error e => status := e; break
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  let mb := input.length * reps
  IO.println s!"{name}: {ms} ms for {reps} × {input.length} units ({found} matches; {if ms == 0 then 0 else mb / ms / 1000} M units/s) {status}"

def bench : IO Unit := do
  let words := "the quick brown fox jumps over the lazy dog alice@example.com bob@test.com 12345 "
  let text := JSStr.ofString (String.join (List.replicate 12000 words))
  benchOne "literal" "lazy" "g" text 3
  benchOne "email" "\\w+@\\w+\\.com" "g" text 3
  benchOne "words" "\\b\\w+\\b" "g" text 3
  benchOne "alt" "fox|dog|cat" "g" text 3
  benchOne "digits" "\\d+" "g" text 3
  benchOne "caseless" "QUICK" "gi" text 3
  benchOne "unicode" "\\p{L}+" "gu" text 3
  benchOne "group-loop" "(?:(\\w)\\w)+" "g" text 3
  benchOne "lookbehind" "(?<=@)\\w+" "g" text 3
  benchOne "backtrack" "^(\\w+\\s?)*$" "" (JSStr.ofString (String.join (List.replicate 22 "a") ++ "!")) 1
  benchOne "dotstar" ".*dog" "g" text 3

def main (args : List String) : IO UInt32 := do
  if args.contains "--bench" then bench; return 0
  let verbose := args.contains "-v"
  let dir := "third_party/regex-corpus"
  let mut bad := false
  -- built-in cases
  let mut tb : Tally := {}
  for (pat, flags, input, li, exp) in builtin do
    tb := checkExec tb pat flags input li exp
  -- the step limit: catastrophic backtracking ends in `.error`
  match compile "(a*)*b" "" with
  | .ok p =>
    let r := matchAt p (JSStr.ofString (String.join (List.replicate 40 "a"))) 0 (limit := 1000000)
    tb := tb.add (match r with | .error _ => true | _ => false) "step limit: expected an error"
  | .error e => tb := tb.add false s!"step limit: {e}"
  report "built-in" tb verbose
  bad := bad || tb.fail > 0
  -- exec corpora
  for name in ["exec", "fuzz"] do
    match ← readLines s!"{dir}/{name}.txt" with
    | none => IO.println s!"{name}: MISSING {dir}/{name}.txt (run node ESTests/regex_corpus.js)"; bad := true
    | some lines =>
      let mut t : Tally := {}
      for l in lines do
        match l.splitOn "\t" with
        | ["E", p, f, i, li, exp] => t := checkExec t (unhex p) f (unhex i) li.toNat! exp
        | _ => pure ()
      report name t verbose
      bad := bad || t.fail > 0
  -- syntax
  for name in ["syntax", "ctor-syntax", "fuzz-syntax"] do
    match ← readLines s!"{dir}/{name}.txt" with
    | none => IO.println s!"{name}: MISSING"; bad := true
    | some lines =>
      let mut t : Tally := {}
      for l in lines do
        match l.splitOn "\t" with
        | ["S", p, f, exp, file] =>
          let pat := unhex p
          let ok := match compile pat f with | .ok _ => "ok" | .error _ => "err"
          t := t.add (ok == exp) s!"{file}: {showPat pat f}: got {ok}, expected {exp}"
        | _ => pure ()
      report name t verbose
      bad := bad || t.fail > 0
  -- property escapes
  match ← readLines s!"{dir}/props.txt" with
  | none => IO.println s!"props: MISSING"; bad := true
  | some lines =>
    let mut t : Tally := {}
    for l in lines do
      match l.splitOn "\t" with
      | ["P", p, f, ranges, file] =>
        let pat := unhex p
        match compile pat f with
        | .error e => t := t.add false s!"{file}: {showPat pat f}: {e}"
        | .ok prog =>
          let exp := parseRanges ranges
          let got := (progClass prog).getD #[]
          -- and, as testPropertyEscapes does, the whole string of those characters must match
          -- (for the smaller sets: the machine's class test over every character)
          -- (not when a high and a low surrogate would meet and form a pair)
          let full := if exp.card > 30000 || (exp.contains 0xDBFF && exp.contains 0xDC00) then true else
            let str := Id.run do
              let mut str := JSStr.empty
              for k in [0:exp.nRanges] do
                for c in [exp[2 * k]!:exp[2 * k + 1]! + 1] do str := str.pushCodePoint c
              return str
            match matchAt prog str 0 with
            | .ok (some m) => m.endIndex == str.length
            | _ => exp.card == 0
          t := t.add (got == exp && full) s!"{file}: {showPat pat f}: {got.nRanges} ranges, expected {exp.nRanges} (first difference near {(got.diff exp).take 2} / {(exp.diff got).take 2})"
      | ["Q", p, f, strs, file] =>
        let pat := unhex p
        match compile pat f with
        | .error e => t := t.add false s!"{file}: {showPat pat f}: {e}"
        | .ok prog =>
          let (strs, nonStrs) := match strs.splitOn "!" with
            | [a, b] => (a, b)
            | _ => (strs, "")
          let ss := (strs.splitOn ",").filter (!·.isEmpty)
          let nss := (nonStrs.splitOn ",").filter (!·.isEmpty)
          let mut ok := true
          let mut firstBad := ""
          for s in ss do
            let input := unhex s
            match matchAt prog input 0 with
            | .ok (some m) => if m.endIndex != input.length then ok := false; firstBad := s
            | _ => ok := false; firstBad := s
          let all := JSStr.join (ss.toArray.map unhex)
          match matchAt prog all 0 with
          | .ok (some m) => if m.endIndex != all.length then ok := false
          | _ => ok := false
          -- (as testPropertyOfStrings: each non-match string only if their concatenation matches)
          let allNon := JSStr.join (nss.toArray.map unhex)
          if !(nss.isEmpty) && (match matchAt prog allNon 0 with | .ok none => false | _ => true) then
            for s in nss do
              match matchAt prog (unhex s) 0 with
              | .ok none => pure ()
              | _ => ok := false; firstBad := s!"non-match {s}"
          t := t.add ok s!"{file}: {showPat pat f}: a string does not match ({firstBad})"
      | _ => pure ()
    report "props" t verbose
    bad := bad || t.fail > 0
  return if bad then 1 else 0

