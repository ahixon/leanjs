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

  | ["lean", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.JS.Parser.parseProgram contents with
    | .ok prog =>
      match LeanJS.Trans.JSToIR.translateToIR prog with
      | .ok ir =>
        match LeanJS.Trans.IRToLean.translateIRToLeanModule ir with
        | .ok mod =>
          let output := LeanJS.Lean.Emit.emitLeanModule mod
          IO.print output
          return 0
        | .error err =>
          IO.eprintln s!"IR→Lean error: {err}"
          return 1
      | .error err =>
        IO.eprintln s!"JS→IR error: {err}"
        return 1
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | ["lean-expr", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.JS.Parser.parseProgram contents with
    | .ok prog =>
      match LeanJS.Trans.JSToIR.translateToIR prog with
      | .ok ir =>
        match LeanJS.Trans.IRToLean.translateIRToLean ir with
        | .ok expr =>
          let output := LeanJS.Lean.Emit.emitLeanExpr expr
          IO.println output
          return 0
        | .error err =>
          IO.eprintln s!"IR→Lean error: {err}"
          return 1
      | .error err =>
        IO.eprintln s!"JS→IR error: {err}"
        return 1
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | ["lean-roundtrip", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.Lean.Parser.parseModule contents with
    | .ok mod =>
      let output := LeanJS.Lean.Emit.emitLeanModule mod
      IO.print output
      return 0
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | ["js", file] =>
    let contents ← IO.FS.readFile file
    match LeanJS.Lean.Parser.parseModule contents with
    | .ok mod =>
      match LeanJS.Trans.LeanToIR.translateModule mod with
      | .ok irMod =>
        match LeanJS.Trans.IRToJS.translateModuleToJS irMod with
        | .ok stmts =>
          let output := LeanJS.JS.Emit.emitProgram stmts
          IO.println output
          return 0
        | .error err =>
          IO.eprintln s!"IR→JS error: {err}"
          return 1
      | .error err =>
        IO.eprintln s!"Lean→IR error: {err}"
        return 1
    | .error err =>
      IO.eprintln s!"Parse error: {err}"
      return 1

  | _ =>
    IO.eprintln "Usage: lean-js <command> <file>"
    IO.eprintln "Commands:"
    IO.eprintln "  parse           Parse JS and emit it back"
    IO.eprintln "  ir              Parse JS and show IR"
    IO.eprintln "  roundtrip       JS → IR → JS round-trip"
    IO.eprintln "  lean            JS → IR → Lean (module-level)"
    IO.eprintln "  lean-expr       JS → IR → Lean (expression-level)"
    IO.eprintln "  lean-roundtrip  Parse Lean and emit it back"
    IO.eprintln "  js              Lean → IR → JS"
    return 1
