import ES.Engine

/-! `es file.js` / `es -e 'code'`: runs a script with the ES engine (print() writes a line). -/

open ES

def main (args : List String) : IO UInt32 := do
  let src ← match args with
    | ["-e", code] => pure code
    | [file] => IO.FS.readFile file
    | _ => IO.eprintln "usage: es file.js | es -e 'code'"; return 2
  let .ok sess := newSession test262Builtins test262HostSetup | IO.eprintln "realm creation failed"; return 1
  let (r, sess) := sess.runScript src
  for line in sess.state.output do IO.println line
  match r with
  | .value v =>
    let (d, _) := sess.run (do toStr v)
    match d with
    | .ok (.ok s) => IO.println s!"=> {s}"
    | _ => IO.println "=> (value)"
    return 0
  | .threw e =>
    let (d, _) := sess.run (describeThrown e)
    match d with
    | .ok (.ok s) => IO.eprintln s!"Uncaught {s}"
    | _ => IO.eprintln "Uncaught exception"
    return 1
  | .halted m => IO.eprintln s!"Halted: {m}"; return 3
