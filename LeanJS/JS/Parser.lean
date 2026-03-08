import LeanJS.JS.Parser.Util
import LeanJS.JS.Parser.Expression

namespace LeanJS.JS.Parser

/-- Parse a complete JS program from source text -/
def parseProgram (input : String) : Except String Program := do
  let state ← tokenizeToState input
  let parser : JSParser Program := do
    let mut stmts : List Stmt := []
    while !(← isToken .eof) do
      let s ← parseStmt
      stmts := stmts ++ [s]
    return stmts
  JSParser.run' parser state

end LeanJS.JS.Parser
