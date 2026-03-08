import LeanJS

def main (args : List String) : IO UInt32 := do
  match args with
  | ["parse", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.JS.Parser.parseProgram contents with
    | .ok prog =>
      let output := LeanJS.JS.Emit.emitProgram prog
      IO.println output
      return 0
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1
  | _ =>
    IO.eprintln "Usage: lean-js parse <file.js>"
    return 1
