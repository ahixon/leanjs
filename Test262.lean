import ES.Engine

/-!
# test262 runner (exe `test262`)

`test262 [paths…] [-v] [--update] [-j N] [--filter TEXT]` runs tc39/test262 tests
(`tools/fetch-test262.sh`; default: test/language, test/built-ins, test/annexB) with the ES
engine, following test262's INTERPRETING.md: the harness (`assert.js`, `sta.js`,
`doneprintHandle.js` for async tests, the `includes`), strict and sloppy runs per the flags,
negative tests (parse/early errors, runtime errors), async completion via `print`.

Tests run in worker processes (`test262 --worker files…`), batches in parallel with a time
limit each; a test whose worker times out or crashes fails. Results are compared with
`Tests/test262-baseline.txt` (one passing `path mode` per line): a regression fails the run;
`--update` records the passes of the tests that ran. Tests needing features outside ECMA-262
(proposals) are skipped, and listed with counts.
-/

open ES

def root : System.FilePath := "third_party/test262"
def baselinePath : System.FilePath := "Tests/test262-baseline.txt"

/-- Features of proposals not in the standard (skipped, with counts). -/
def skippedFeatures : List String :=
  ["decorators", "source-phase-imports", "source-phase-imports-module-source", "import-defer",
   "ShadowRealm", "IsHTMLDDA", "Temporal", "Intl.Locale-info", "Atomics.waitAsync",
   "tail-call-optimization", "host-gc-required", "legacy-regexp", "uint8array-base64",
   "canonical-tz", "await-dictionary", "joint-iteration", "immutable-arraybuffer",
   "nonextensible-applies-to-private", "upsert", "iterator-sequencing",
   "import-text", "import-bytes"]

/-- Test paths excluded as too slow for the interpreter (each listed in the summary with the reason). -/
def slowPaths : List (String × String) :=
  [("test/built-ins/RegExp/property-escapes/generated/", "too slow for the interpreter (20-60 s each: loops over ~1.1M code points)")]

structure Meta where
  includes : Array String := #[]
  flags : Array String := #[]
  features : Array String := #[]
  negPhase : Option String := none
  negType : Option String := none
  deriving Inhabited

/-- Parses the YAML frontmatter `/*--- … ---*/` (the subset test262 uses). -/
def parseMeta (src : String) : Meta := Id.run do
  let parts := src.splitOn "/*---"
  if parts.length < 2 then return {}
  let body := ((parts[1]!).splitOn "---*/")[0]!
  let lines := body.splitOn "\n"
  let mut m : Meta := {}
  let mut key := ""
  let listItems (v : String) : Array String :=
    let v := v.trimAscii.toString
    if v.startsWith "[" then
      ((v.drop 1).toString.takeWhile (· != ']')).toString.splitOn "," |>.map (·.trimAscii.toString)
        |>.filter (· != "") |>.toArray
    else #[]
  for l in lines do
    let t := l.trimAscii.toString
    if t.startsWith "- " && (key == "includes" || key == "flags" || key == "features") then
      let item := (t.drop 2).toString.trimAscii.toString
      if key == "includes" then m := { m with includes := m.includes.push item }
      else if key == "flags" then m := { m with flags := m.flags.push item }
      else m := { m with features := m.features.push item }
      continue
    if !l.startsWith " " && !l.startsWith "\t" then
      match t.splitOn ":" with
      | k :: rest =>
        key := k.trimAscii.toString
        let v := (":".intercalate rest).trimAscii.toString
        if key == "includes" then m := { m with includes := m.includes ++ listItems v }
        else if key == "flags" then m := { m with flags := m.flags ++ listItems v }
        else if key == "features" then m := { m with features := m.features ++ listItems v }
      | [] => pure ()
    else if key == "negative" then
      match t.splitOn ":" with
      | [k, v] =>
        if k.trimAscii.toString == "phase" then m := { m with negPhase := some v.trimAscii.toString }
        if k.trimAscii.toString == "type" then m := { m with negType := some v.trimAscii.toString }
      | _ => pure ()
  return m

/-- One run's result. -/
inductive Verdict where
  | pass
  | fail (msg : String)
  | skip (reason : String)

def describe (sess : Session) (v : Value) : String :=
  match (sess.run (describeThrown v)).1 with
  | .ok (.ok s) => s
  | _ => "(exception)"

def nameOf (sess : Session) (v : Value) : String :=
  match (sess.run (thrownName v)).1 with
  | .ok (.ok s) => s
  | _ => ""

/-- The `.js` files a source names in string literals (relative to `dir`), read transitively:
module fixtures for imports and `import()`. -/
partial def gatherSources (path : String) (src : String) (acc : Std.HashMap String String) : IO (Std.HashMap String String) := do
  let mut acc := acc.insert path src
  let dir := "/".intercalate (path.splitOn "/").dropLast
  -- (each `….js`/`….json` token preceded by a quote)
  let chars := src.toList.toArray
  let isTok (c : Char) := c.isAlphanum || c == '.' || c == '/' || c == '_' || c == '-' || c == '$'
  for i in [0:chars.size] do
    let ext := if i + 3 ≤ chars.size && chars[i]! == '.' && chars[i+1]! == 'j' && chars[i+2]! == 's' then 3
      else 0
    if ext == 0 then continue
    let ext := if i + 5 ≤ chars.size && chars[i+3]! == 'o' && chars[i+4]! == 'n' then 5 else ext
    let mut j := i
    while j > 0 && isTok chars[j-1]! do j := j - 1
    if j == 0 then continue
    let q := chars[j-1]!
    if q != '\'' && q != '"' then continue
    let lit := String.ofList (chars.extract j (i + ext)).toList
    let p := if lit.startsWith "./" || lit.startsWith "../" then ES.resolveSpecifier path lit else dir ++ "/" ++ lit
    if !acc.contains p && (← System.FilePath.pathExists p) then
      let s ← IO.FS.readFile p
      acc ← gatherSources p s acc
  return acc

/-- Runs one test in one mode ("strict", "sloppy", "raw", "module"). -/
def runOne (harness : String → IO String) (m : Meta) (path : String) (src : String) (mode : String) : IO Verdict := do
  let isModule := mode == "module"
  let src := if mode == "strict" then "\"use strict\";\n" ++ src else src
  -- negative parse/early errors: the test's source must not parse
  if m.negPhase == some "parse" || m.negPhase == some "early" then
    match (if isModule then parseModule src else parseScript src) with
    | .error _ => return .pass
    | .ok _ => return .fail "expected a SyntaxError at parse time"
  let sources ← gatherSources path src {}
  let .ok sess0 := newSession test262Builtins test262HostSetup 50000000
    | return .fail "realm creation failed"
  let mut sess := sess0
  let isAsync := m.flags.contains "async"
  if !m.flags.contains "raw" then
    let mut files := #["assert.js", "sta.js"]
    if isAsync then files := files.push "doneprintHandle.js"
    for f in m.includes do
      if !files.contains f then files := files.push f
    for f in files do
      let h ← harness f
      let (r, s') := sess.runScript h
      sess := s'
      match r with
      | .value _ => pure ()
      | .threw e => return .fail s!"harness {f} threw {describe sess e}"
      | .halted msg => return .fail s!"harness {f}: halted: {msg}"
  let sessS := sess.addSources sources
  let (r, sessF) := if isModule then sessS.runModule path sources else sessS.runScript src path
  match r with
  | .halted msg => return .fail s!"halted: {msg}"
  | .threw e =>
    if m.negPhase == some "runtime" || m.negPhase == some "resolution" then
      let nm := nameOf sessF e
      if some nm == m.negType then return .pass
      return .fail s!"expected {m.negType.getD "?"}, got {describe sessF e}"
    return .fail s!"threw {describe sessF e}"
  | .value _ =>
    if m.negPhase.isSome then return .fail s!"expected {m.negType.getD "an error"} ({m.negPhase.getD ""})"
    if isAsync then
      let out := sessF.state.output
      if out.any (·.startsWith "Test262:AsyncTestFailure") then
        return .fail ((out.find? (·.startsWith "Test262:AsyncTestFailure")).getD "")
      if out.contains "Test262:AsyncTestComplete" then return .pass
      return .fail "async test did not complete"
    return .pass

/-- The modes a test runs in. -/
def modesOf (m : Meta) : Array String :=
  if m.flags.contains "module" then #["module"]
  else if m.flags.contains "raw" then #["raw"]
  else if m.flags.contains "onlyStrict" then #["strict"]
  else if m.flags.contains "noStrict" then #["sloppy"]
  else #["sloppy", "strict"]

def oneLine (s : String) : String := (s.replace "\n" " ").replace "\t" " "

/-- Worker: runs the given files, printing `path\tmode\tverdict\tmessage` per run. -/
def worker (files : List String) : IO Unit := do
  let cache ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap String String)
  let harness (f : String) : IO String := do
    match (← cache.get).get? f with
    | some s => pure s
    | none =>
      let s ← IO.FS.readFile (root / "harness" / f)
      cache.modify (·.insert f s)
      pure s
  let out ← IO.getStdout
  for f in files do
    let src ← IO.FS.readFile f
    let m := parseMeta src
    let rel := (f.drop (root.toString.length + 1)).toString
    let slow := slowPaths.find? (fun (p, _) => rel.startsWith p)
    match m.features.find? (skippedFeatures.contains ·), slow with
    | _, some (_, why) =>
      out.putStrLn s!"{rel}\t-\tskip\t{why}"
    | some feat, none =>
      out.putStrLn s!"{rel}\t-\tskip\t{feat}"
    | none, none =>
      for mode in modesOf m do
        let v ← runOne harness m f src mode
        match v with
        | .pass => out.putStrLn s!"{rel}\t{mode}\tpass\t"
        | .fail msg => out.putStrLn s!"{rel}\t{mode}\tfail\t{oneLine msg |>.take 300}"
        | .skip r => out.putStrLn s!"{rel}\t{mode}\tskip\t{r}"
    out.flush

/-- All `.js` test files under a path (fixtures excluded), sorted. -/
partial def collect (p : System.FilePath) : IO (Array String) := do
  if ← p.isDir then
    let entries ← p.readDir
    let mut acc := #[]
    for e in entries.qsort (·.fileName < ·.fileName) do
      acc := acc ++ (← collect e.path)
    return acc
  else
    let s := p.toString
    if s.endsWith ".js" && !s.endsWith "_FIXTURE.js" then return #[s] else return #[]

structure RunResult where
  path : String
  mode : String
  verdict : String
  msg : String

def parseLine (l : String) : Option RunResult :=
  match l.splitOn "\t" with
  | p :: md :: v :: rest => some { path := p, mode := md, verdict := v, msg := "\t".intercalate rest }
  | _ => none

/-- Runs a batch in a worker with a time limit; tests not reported (timeout/crash) fail. -/
partial def runBatch (exe : String) (files : Array String) (timeoutMs : Nat) : IO (Array RunResult) := do
  if files.isEmpty then return #[]
  let child ← IO.Process.spawn { cmd := exe, args := #["--worker"] ++ files, stdout := .piped, stderr := .null }
  let reader ← IO.asTask child.stdout.readToEnd
  let start ← IO.monoMsNow
  let mut timedOut := false
  repeat
    if ← IO.hasFinished reader then break
    if (← IO.monoMsNow) - start > timeoutMs then
      child.kill
      timedOut := true
      break
    IO.sleep 50
  let outText ← match ← IO.wait reader with
    | .ok s => pure s
    | .error _ => pure ""
  let _ ← child.wait
  let results := (outText.splitOn "\n").filterMap parseLine |>.toArray
  let done := results.map (·.path)
  let rel (f : String) := (f.drop (root.toString.length + 1)).toString
  match files.findIdx? (fun f => !done.contains (rel f)) with
  | none => return results
  | some i =>
    let bad := files[i]!
    let why := if timedOut then "timeout" else "worker crashed"
    let rest ← runBatch exe (files.extract (i + 1) files.size) timeoutMs
    -- (a partially reported file: drop its partial lines, report it failed once)
    let results := results.filter (·.path != rel bad)
    return results.push { path := rel bad, mode := "-", verdict := "fail", msg := why } ++ rest

def groupOf (path : String) : String :=
  let ps := path.splitOn "/"
  "/".intercalate (ps.take 3)

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--worker" then
    worker args.tail
    return 0
  let verbose := args.contains "-v"
  let update := args.contains "--update"
  let rec opts : List String → Nat × Option String × List String
    | "-j" :: n :: rest => let (_, f, ps) := opts rest; (n.toNat!, f, ps)
    | "--filter" :: t :: rest => let (j, _, ps) := opts rest; (j, some t, ps)
    | a :: rest => let (j, f, ps) := opts rest; (j, f, if a.startsWith "-" then ps else a :: ps)
    | [] => (4, none, [])
  let (jobs, filter, paths) := opts args
  let jobs := if jobs == 0 then 4 else jobs
  let paths := if paths.isEmpty then ["test/language", "test/built-ins", "test/annexB"] else paths
  unless ← root.isDir do
    IO.eprintln "third_party/test262 is missing: run tools/fetch-test262.sh"
    return 2
  let mut files := #[]
  for p in paths do
    let p := if p.startsWith root.toString then p else (root / p).toString
    files := files ++ (← collect p)
  if let some t := filter then files := files.filter (fun f => (f.splitOn t).length > 1)
  let exe := (← IO.appPath).toString
  -- batches, `jobs` at a time
  let batchSize := 25
  let batches := (Array.range ((files.size + batchSize - 1) / batchSize)).map fun i =>
    files.extract (i * batchSize) ((i + 1) * batchSize)
  let mut results : Array RunResult := #[]
  let mut i := 0
  let total := batches.size
  while i < total do
    let group := batches.extract i (i + jobs)
    let tasks ← group.mapM fun b => IO.asTask (runBatch exe b 300000)
    for t in tasks do
      match ← IO.wait t with
      | .ok rs => results := results ++ rs
      | .error e => IO.eprintln s!"batch failed: {e}"
    i := i + jobs
    if i % (jobs * 20) == 0 then
      let p := results.filter (·.verdict == "pass") |>.size
      IO.eprintln s!"[{min i total}/{total} batches] {p}/{results.size} runs pass"
  -- summary
  let mut groups : Std.HashMap String (Nat × Nat × Nat) := {}
  for r in results do
    let g := groupOf r.path
    let (p, f, s) := groups.getD g (0, 0, 0)
    groups := groups.insert g (match r.verdict with
      | "pass" => (p + 1, f, s) | "skip" => (p, f, s + 1) | _ => (p, f + 1, s))
  let keys := groups.toArray.qsort (fun a b => a.1 < b.1)
  for (g, (p, f, s)) in keys do
    IO.println s!"{g}: {p}/{p + f} pass{if s > 0 then s!" ({s} skipped)" else ""}"
  let passN := (results.filter (·.verdict == "pass")).size
  let failN := (results.filter (·.verdict == "fail")).size
  let skipN := (results.filter (·.verdict == "skip")).size
  IO.println s!"total: {passN}/{passN + failN} runs pass, {skipN} tests skipped"
  -- skipped features
  let mut skips : Std.HashMap String Nat := {}
  for r in results do
    if r.verdict == "skip" then skips := skips.insert r.msg (skips.getD r.msg 0 + 1)
  if !skips.isEmpty then
    IO.println s!"skipped (proposal features, slow tests): {(skips.toArray.qsort (fun a b => a.2 > b.2)).toList}"
  if verbose then
    for r in results do
      if r.verdict == "fail" then IO.println s!"FAIL {r.path} [{r.mode}]: {r.msg}"
  -- baseline
  let passing := results.filter (·.verdict == "pass") |>.map (fun r => s!"{r.path} {r.mode}")
  let old : Array String ← if ← baselinePath.pathExists then
      pure ((← IO.FS.readFile baselinePath).splitOn "\n" |>.filter (· != "") |>.toArray)
    else pure #[]
  let ranPaths : Std.HashSet String := results.foldl (fun s r => s.insert r.path) {}
  let passSet : Std.HashSet String := passing.foldl (fun s x => s.insert x) {}
  let regressions := old.filter fun l =>
    let p := (l.splitOn " ")[0]!
    ranPaths.contains p && !passSet.contains l
  if update then
    let kept := old.filter fun l => !ranPaths.contains ((l.splitOn " ")[0]!)
    let all := (kept ++ passing).qsort (· < ·)
    IO.FS.writeFile baselinePath ("\n".intercalate all.toList ++ "\n")
    IO.println s!"baseline updated: {all.size} passing runs"
    return 0
  if !regressions.isEmpty then
    IO.println s!"{regressions.size} regressions against {baselinePath}:"
    for r in regressions.extract 0 50 do IO.println s!"  {r}"
    return 1
  return 0
