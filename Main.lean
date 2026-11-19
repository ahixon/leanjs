import ES.Engine
import ES.Quote
import ES.Gen

/-!
# `leanjs`

- `leanjs run file.js` — runs a script with the engine.
- `leanjs compile file.js Out.lean` — JS → Lean: a Lean module that runs the program on the
  engine's runtime (`program` is its syntax tree; `main` runs it). Compiled programs mean exactly
  what the engine says they mean.
-/

open ES

/-- Runs a program and prints its output (and an uncaught exception). -/
def runAndReport (sess : Session) (r : Outcome' × Session) : IO UInt32 := do
  let (r, sess) := r
  for line in sess.state.output do IO.println line
  match r with
  | .value _ => return 0
  | .threw e =>
    let (d, _) := sess.run (describeThrown e)
    match d with
    | .ok (.ok s) => IO.eprintln s!"Uncaught {s}"
    | _ => IO.eprintln "Uncaught exception"
    return 1
  | .halted m => IO.eprintln s!"Halted: {m}"; return 3

def newSessionIO : IO Session := do
  match newSession test262Builtins test262HostSetup with
  | .ok s => pure s
  | .error m => throw (IO.userError s!"realm creation failed: {m}")

def compileFile (src : String) (input : String) : Except String String := do
  let prog ← match parseScript src with
    | .ok p => pure p
    | .error e => throw s!"SyntaxError: {e.msg} (at byte {e.pos})"
  -- (the name goes in a comment: `/-` and `-/` would open or close one)
  let name := (input.replace "/-" "/ -").replace "-/" "- /"
  return s!"import ES.Engine

/-! Compiled from `{name}` by leanjs: the program's syntax tree, run on the engine's runtime. -/

open ES

def program : ES.Program :=
  {Quote.quoteProgram prog}

def main : IO UInt32 := ES.runCompiled program
"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", f] =>
    let src ← IO.FS.readFile f
    let sess ← newSessionIO
    runAndReport sess (sess.runScript src f)
  | ["compile", "--defs", f, out] =>
    let src ← IO.FS.readFile f
    match parseScript src with
    | .error e => IO.eprintln s!"SyntaxError: {e.msg} (at byte {e.pos})"; return 1
    | .ok prog =>
      let name := (f.replace "/-" "/ -").replace "-/" "- /"
      IO.FS.writeFile out (Gen.emitModule prog s!"Compiled from `{name}`.")
      return 0
  | ["compile", f, out] =>
    let src ← IO.FS.readFile f
    match compileFile src f with
    | .ok lean => IO.FS.writeFile out lean; return 0
    | .error m => IO.eprintln m; return 1
  | _ =>
    IO.eprintln "usage: leanjs run file.js | leanjs compile [--defs] file.js Out.lean"
    return 2
