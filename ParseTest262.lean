import ES.Parser

/-!
# test262 parse conformance (exe `es-parse-test`)

`es-parse-test [paths…] [-v]`: parses every test262 test (default: `test/language`,
`test/annexB`, `test/built-ins` under `third_party/test262`) as its flags say (INTERPRETING.md:
`module` → Module; `onlyStrict` → Script with `"use strict";` prepended; `noStrict`/`raw` →
sloppy Script only; otherwise both) and checks the parse-phase expectation: a test with
`negative: {phase: parse, type: SyntaxError}` must fail to parse, every other test must parse.
Failures whose message comes from `Regex.compile`, or tests of regular expression syntax that
we accept but should reject, are counted separately (the RegExp pattern parser's). Tests of
features outside the target (proposals below stage 4) are skipped with their reason.
-/

open ES ES.Lex

structure Meta where
  flags : Array String := #[]
  features : Array String := #[]
  negativeParse : Bool := false
  negativeOther : Bool := false

/-- The items of a YAML flow list `[a, b]`. -/
def flowList (s : String) : Array String :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "[" then (s.drop 1).toString else s
  let s := if s.endsWith "]" then (s.dropEnd 1).toString else s
  ((s.splitOn ",").map (fun x => x.trimAscii.toString)).filter (· ≠ "") |>.toArray

def parseMeta (src : String) : Meta := Id.run do
  let parts := src.splitOn "/*---"
  if parts.length < 2 then return {}
  let body := ((parts[1]!).splitOn "---*/")[0]!
  let mut m : Meta := {}
  let mut inNeg := false
  let mut inFeatures := false
  let mut phase := ""
  let mut ty := ""
  for line in body.splitOn "\n" do
    let t := line.trimAscii.toString
    let indented := line.startsWith " " || line.startsWith "\t"
    if !indented then inNeg := false; inFeatures := false
    if t.startsWith "flags:" then m := { m with flags := flowList (t.drop 6).toString }
    else if t.startsWith "features:" then
      let rest := (t.drop 9).trimAscii.toString
      if rest.isEmpty then inFeatures := true
      else m := { m with features := flowList rest }
    else if t.startsWith "negative:" then inNeg := true
    else if inNeg && t.startsWith "phase:" then phase := (t.drop 6).trimAscii.toString
    else if inNeg && t.startsWith "type:" then ty := (t.drop 5).trimAscii.toString
    else if inFeatures && t.startsWith "- " then m := { m with features := m.features.push (t.drop 2).trimAscii.toString }
  if phase == "parse" && ty == "SyntaxError" then m := { m with negativeParse := true }
  else if phase != "" then m := { m with negativeOther := true }
  return m

/-- Features not in ES2025 or stage 4 that this parser does not implement. -/
def skippedFeatures : List (String × String) := [
  ("decorators", "stage 3 proposal"),
  ("source-phase-imports", "stage 3 proposal (import source)"),
  ("source-phase-imports-module-source", "stage 3 proposal (import source)"),
  ("import-defer", "stage 3 proposal (import defer)"),
  ("import-text", "stage 3 proposal (import text)"),
  ("import-bytes", "stage 2.7 proposal (import bytes)")]

inductive Outcome where
  | pass | fail (msg : String) | regexFail (msg : String) | skip (reason : String)

def isRegexTest (path : String) (src : String) : Bool :=
  (path.splitOn "literals/regexp").length > 1 || (path.splitOn "built-ins/RegExp").length > 1 ||
  (path.splitOn "annexB/language/literals/regexp").length > 1 ||
  ((src.splitOn "regexp-").length > 1 && (src.splitOn "features:").length > 1)

def runOne (path src : String) : Outcome := Id.run do
  let m := parseMeta src
  for f in m.features do
    if let some (_, why) := skippedFeatures.find? (·.1 == f) then return .skip s!"{f}: {why}"
  let has (f : String) := m.flags.contains f
  let attempts : Array (String × Except SyntaxError Unit) :=
    if has "module" then #[("module", (parseModule src).map (fun _ => ()))]
    else if has "onlyStrict" then #[("strict", (parseScript ("\"use strict\";\n" ++ src)).map (fun _ => ()))]
    else if has "noStrict" || has "raw" then #[("sloppy", (parseScript src).map (fun _ => ()))]
    else #[("sloppy", (parseScript src).map (fun _ => ())),
           ("strict", (parseScript ("\"use strict\";\n" ++ src)).map (fun _ => ()))]
  for (mode, res) in attempts do
    match res, m.negativeParse with
    | .ok _, true =>
      let msg := s!"[{mode}] parsed, expected SyntaxError"
      return if isRegexTest path src then .regexFail msg else .fail msg
    | .error e, false =>
      let msg := s!"[{mode}] {e.msg} at {e.pos}"
      return if e.msg.startsWith "Invalid regular expression" then .regexFail msg else .fail msg
    | _, _ => pure ()
  return .pass

partial def collect (p : System.FilePath) (acc : Array System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let mut acc := acc
    let entries ← p.readDir
    for e in entries.qsort (fun a b => a.fileName < b.fileName) do
      acc ← collect e.path acc
    return acc
  let s := p.toString
  if s.endsWith ".js" && !s.endsWith "_FIXTURE.js" then return acc.push p
  return acc

/-- The directory a test is counted under: `test/<top>/<second>`. -/
def groupOf (root : String) (p : String) : String :=
  let rel := if p.startsWith root then (p.drop root.length).toString else p
  let parts := (rel.splitOn "/").filter (· ≠ "")
  match parts with
  | a :: b :: _ :: _ => a ++ "/" ++ b
  | a :: _ => a
  | [] => rel

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let root := "third_party/test262/test/"
  let paths := args.filter (fun a => !a.startsWith "-")
  let paths := if paths.isEmpty then [root ++ "language", root ++ "annexB", root ++ "built-ins"] else paths
  let mut files : Array System.FilePath := #[]
  for p in paths do files ← collect p files
  -- parse in parallel chunks (parsing is pure)
  let chunk := 256
  let mut tasks : Array (Task (Array (String × Outcome))) := #[]
  let mut i := 0
  while i < files.size do
    let batch := files.extract i (i + chunk)
    let mut inputs : Array (String × String) := #[]
    for f in batch do
      let src ← IO.FS.readFile f
      inputs := inputs.push (f.toString, src)
    tasks := tasks.push (Task.spawn fun _ => inputs.map fun (p, s) => (p, runOne p s))
    i := i + chunk
  let mut groups : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut order : Array String := #[]
  let mut failures : Array String := #[]
  let mut regexFailures : Array String := #[]
  let mut skipReasons : Std.HashMap String Nat := {}
  for t in tasks do
    for (p, o) in t.get do
      let g := groupOf root p
      if !groups.contains g then order := order.push g
      let (ps, fl, rx, sk) := groups.getD g (0, 0, 0, 0)
      match o with
      | .pass => groups := groups.insert g (ps + 1, fl, rx, sk)
      | .fail msg =>
        groups := groups.insert g (ps, fl + 1, rx, sk)
        failures := failures.push s!"{p}: {msg}"
      | .regexFail msg =>
        groups := groups.insert g (ps, fl, rx + 1, sk)
        regexFailures := regexFailures.push s!"{p}: {msg}"
      | .skip why =>
        groups := groups.insert g (ps, fl, rx, sk + 1)
        skipReasons := skipReasons.insert why (skipReasons.getD why 0 + 1)
  if verbose then
    for f in failures do IO.println s!"FAIL {f}"
    for f in regexFailures do IO.println s!"REGEX {f}"
  let mut tp := 0; let mut tf := 0; let mut tr := 0; let mut ts := 0
  IO.println s!"{"directory".pushn ' ' 40} pass   fail  regex   skip"
  for g in order do
    let (ps, fl, rx, sk) := groups.getD g (0, 0, 0, 0)
    tp := tp + ps; tf := tf + fl; tr := tr + rx; ts := ts + sk
    let pad (n : Nat) (w : Nat) := let s := toString n; "".pushn ' ' (w - s.length) ++ s
    IO.println s!"{g.pushn ' ' (49 - g.length)}{pad ps 6} {pad fl 6} {pad rx 6} {pad sk 6}"
  IO.println s!"total: {tp} pass, {tf} fail, {tr} regex (RegExp parser), {ts} skipped"
  for (why, n) in skipReasons.toList do IO.println s!"  skipped {n}: {why}"
  return if tf == 0 then 0 else 1
