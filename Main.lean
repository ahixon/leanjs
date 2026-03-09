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

  | ["ir", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.JS.Parser.parseProgram contents with
    | .ok prog =>
      match LeanJS.Trans.JSToIR.translateToIR prog with
      | .ok ir =>
        IO.println (LeanJS.IR.Print.printExpr ir)
        return 0
      | .error err =>
        IO.eprintln s!"Translation error: {err}"
        return 1
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | ["roundtrip", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.JS.Parser.parseProgram contents with
    | .ok prog =>
      match LeanJS.Trans.JSToIR.translateToIR prog with
      | .ok ir =>
        match LeanJS.Trans.IRToJS.translateToJS ir with
        | .ok stmts =>
          let output := LeanJS.JS.Emit.emitProgram stmts
          IO.println output
          return 0
        | .error err =>
          IO.eprintln s!"IR→JS error: {err}"
          return 1
      | .error err =>
        IO.eprintln s!"JS→IR error: {err}"
        return 1
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | _ =>
    IO.eprintln "Usage: lean-js <command> <file.js>"
    IO.eprintln "Commands:"
    IO.eprintln "  parse      Parse JS and emit it back"
    IO.eprintln "  ir         Parse JS and show IR"
    IO.eprintln "  roundtrip  JS → IR → JS round-trip"
    return 1
