import LeanJS.JS.AST

set_option maxHeartbeats 800000

namespace LeanJS.JS.Emit

structure EmitConfig where
  indent : Nat := 2
  semicolons : Bool := true
  deriving Inhabited

structure EmitState where
  output : String := ""
  indentLevel : Nat := 0
  config : EmitConfig := {}
  deriving Inhabited

abbrev Emitter := StateM EmitState

def write (s : String) : Emitter Unit :=
  modify fun st => { st with output := st.output ++ s }

def writeLn (s : String := "") : Emitter Unit := do
  let st ← get
  let ind := String.mk (List.replicate (st.indentLevel * st.config.indent) ' ')
  modify fun st => { st with output := st.output ++ ind ++ s ++ "\n" }

def writeIndent : Emitter Unit := do
  let st ← get
  let ind := String.mk (List.replicate (st.indentLevel * st.config.indent) ' ')
  modify fun st => { st with output := st.output ++ ind }

def incIndent : Emitter Unit :=
  modify fun st => { st with indentLevel := st.indentLevel + 1 }

def decIndent : Emitter Unit :=
  modify fun st => { st with indentLevel := st.indentLevel - 1 }

def semi : Emitter Unit := do
  let st ← get
  if st.config.semicolons then write ";"

/-- Write items separated by a string -/
def commaSep {α : Type} (items : List α) (f : α → Emitter Unit) : Emitter Unit := do
  let mut first := true
  for item in items do
    if !first then write ", "
    first := false
    f item

def binOpPrec : BinOp → Nat
  | .or => 4 | .nullishCoalesce => 4 | .and => 5 | .bitOr => 6
  | .bitXor => 7 | .bitAnd => 8
  | .eq | .neq | .strictEq | .strictNeq => 9
  | .lt | .lte | .gt | .gte | .in | .instanceof => 10
  | .shl | .shr | .ushr => 11 | .add | .sub => 12
  | .mul | .div | .mod => 13 | .exp => 14

def emitBinOp : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .exp => "**" | .eq => "==" | .neq => "!=" | .strictEq => "==="
  | .strictNeq => "!==" | .lt => "<" | .lte => "<=" | .gt => ">"
  | .gte => ">=" | .and => "&&" | .or => "||" | .bitAnd => "&"
  | .bitOr => "|" | .bitXor => "^" | .shl => "<<" | .shr => ">>"
  | .ushr => ">>>" | .nullishCoalesce => "??" | .in => "in"
  | .instanceof => "instanceof"

def emitUnaryOp : UnaryOp → String
  | .neg => "-" | .pos => "+" | .not => "!" | .bitNot => "~"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "

def emitUpdateOp : UpdateOp → String
  | .inc => "++" | .dec => "--"

def emitAssignOp : AssignOp → String
  | .assign => "=" | .addAssign => "+=" | .subAssign => "-="
  | .mulAssign => "*=" | .divAssign => "/=" | .modAssign => "%="
  | .expAssign => "**=" | .andAssign => "&&=" | .orAssign => "||="
  | .nullishAssign => "??=" | .bitAndAssign => "&=" | .bitOrAssign => "|="
  | .bitXorAssign => "^=" | .shlAssign => "<<=" | .shrAssign => ">>="
  | .ushrAssign => ">>>="

def emitVarKind : VarKind → String
  | .var => "var" | .let => "let" | .const => "const"

def escapeString (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  let s := s.replace "\n" "\\n"
  let s := s.replace "\r" "\\r"
  let s := s.replace "\t" "\\t"
  s

def formatFloat (f : Float) : String :=
  if f == Float.ofNat f.toUInt64.toNat && f >= 0 && f < 1e15 then
    toString f.toUInt64.toNat
  else toString f

mutual

partial def emitExpr (e : Expr) (prec : Nat := 0) : Emitter Unit := do
  match e with
  | .ident name => write name
  | .literal lit => emitLiteral lit
  | .this => write "this"
  | .paren inner => write "("; emitExpr inner; write ")"
  | .array elements =>
    write "["
    let mut first := true
    for elem in elements do
      if !first then write ", "
      first := false
      match elem with
      | some e => emitExpr e 2
      | none => pure ()
    write "]"
  | .object props =>
    write "{"
    if !props.isEmpty then
      write " "
      commaSep props emitProperty
      write " "
    write "}"
  | .function name params body =>
    write "function"
    match name with | some n => write s!" {n}" | none => pure ()
    write "("; emitParams params; write ") "; emitBlock body
  | .arrowFunction params body =>
    match params with
    | [.ident name none] => write name
    | _ => write "("; emitParams params; write ")"
    write " => "
    match body with
    | .expr (.object _) => write "("; emitExpr (match body with | .expr e => e | _ => .literal .null); write ")"
    | .expr e => emitExpr e 2
    | .block stmts => emitBlock stmts
  | .unary op arg =>
    if prec > 15 then write "("
    write (emitUnaryOp op); emitExpr arg 15
    if prec > 15 then write ")"
  | .update op arg prefix_ =>
    if prefix_ then write (emitUpdateOp op); emitExpr arg 15
    else emitExpr arg 15; write (emitUpdateOp op)
  | .binary op left right =>
    let p := binOpPrec op
    if prec > p then write "("
    emitExpr left p; write s!" {emitBinOp op} "; emitExpr right (p + 1)
    if prec > p then write ")"
  | .assign op target right =>
    if prec > 2 then write "("
    emitAssignTarget target; write s!" {emitAssignOp op} "; emitExpr right 2
    if prec > 2 then write ")"
  | .conditional test consequent alternate =>
    if prec > 3 then write "("
    emitExpr test 4; write " ? "; emitExpr consequent 2; write " : "; emitExpr alternate 2
    if prec > 3 then write ")"
  | .call callee args =>
    emitExpr callee 18; write "("; commaSep args (emitExpr · 2); write ")"
  | .new callee args =>
    write "new "; emitExpr callee 18; write "("; commaSep args (emitExpr · 2); write ")"
  | .member obj prop =>
    emitExpr obj 18
    match prop with
    | .ident name => write s!".{name}"
    | .computed expr => write "["; emitExpr expr; write "]"
  | .sequence exprs => commaSep exprs (emitExpr · 2)
  | .template _tag quasis expressions =>
    write "`"
    emitTemplateQuasis quasis expressions 0
    write "`"
  | .spread arg => write "..."; emitExpr arg 2

partial def emitTemplateQuasis (quasis : List String) (exprs : List Expr) (idx : Nat) : Emitter Unit := do
  match quasis with
  | [] => pure ()
  | q :: qs =>
    write q
    match exprs[idx]? with
    | some e => write "${"; emitExpr e; write "}"
    | none => pure ()
    emitTemplateQuasis qs exprs (idx + 1)

partial def emitLiteral (lit : Literal) : Emitter Unit :=
  match lit with
  | .string s => write s!"\"{escapeString s}\""
  | .number n => write (formatFloat n)
  | .bool true => write "true"
  | .bool false => write "false"
  | .null => write "null"
  | .undefined => write "undefined"
  | .regex pattern flags => write s!"/{pattern}/{flags}"

partial def emitAssignTarget (t : AssignTarget) : Emitter Unit :=
  match t with | .expr e => emitExpr e | .pat p => emitPattern p

partial def emitProperty (p : Property) : Emitter Unit := do
  match p with
  | .prop key value _kind _computed shorthand =>
    if shorthand then emitExpr key
    else do emitExpr key; write ": "; emitExpr value 2
  | .method key params body kind _computed _async _generator =>
    match kind with
    | .get => write "get "; emitExpr key
    | .set => write "set "; emitExpr key
    | .method => emitExpr key
    write "("; emitParams params; write ") "; emitBlock body

partial def emitPattern (p : Pattern) : Emitter Unit := do
  match p with
  | .ident name default_ =>
    write name
    match default_ with | some d => write " = "; emitExpr d 2 | none => pure ()
  | .array elements rest =>
    write "["
    let mut first := true
    for elem in elements do
      if !first then write ", "
      first := false
      match elem with | some p => emitPattern p | none => pure ()
    match rest with
    | some r => if !elements.isEmpty then write ", "; write "..."; emitPattern r
    | none => pure ()
    write "]"
  | .object props rest =>
    write "{ "
    commaSep props emitPatternProp
    match rest with
    | some r => if !props.isEmpty then write ", "; write "..."; emitPattern r
    | none => pure ()
    write " }"
  | .assign left right =>
    emitPattern left; write " = "; emitExpr right 2

partial def emitPatternProp (p : PatternProp) : Emitter Unit := do
  match p with
  | .keyVal key value _computed => emitExpr key; write ": "; emitPattern value
  | .shorthand name default_ =>
    write name
    match default_ with | some d => write " = "; emitExpr d 2 | none => pure ()

partial def emitParams (params : List Pattern) : Emitter Unit :=
  commaSep params emitPattern

partial def emitBlock (stmts : List Stmt) : Emitter Unit := do
  write "{\n"; incIndent
  for s in stmts do emitStmt s
  decIndent; writeIndent; write "}"

partial def emitStmt (s : Stmt) : Emitter Unit := do
  match s with
  | .expr expression =>
    writeIndent; emitExpr expression; semi; write "\n"
  | .block body =>
    writeIndent; emitBlock body; write "\n"
  | .empty => writeLn ";"
  | .return_ arg =>
    writeIndent; write "return"
    match arg with | some e => write " "; emitExpr e | none => pure ()
    semi; write "\n"
  | .throw arg =>
    writeIndent; write "throw "; emitExpr arg; semi; write "\n"
  | .break_ label =>
    writeIndent; write "break"
    match label with | some l => write s!" {l}" | none => pure ()
    semi; write "\n"
  | .continue_ label =>
    writeIndent; write "continue"
    match label with | some l => write s!" {l}" | none => pure ()
    semi; write "\n"
  | .ifStmt test consequent alternate =>
    writeIndent; write "if ("; emitExpr test; write ") "
    emitStmtBody consequent
    match alternate with
    | some alt => write " else "; emitStmtBody alt; write "\n"
    | none => write "\n"
  | .while_ test body =>
    writeIndent; write "while ("; emitExpr test; write ") "
    emitStmtBody body; write "\n"
  | .doWhile body test =>
    writeIndent; write "do "; emitStmtBody body
    write " while ("; emitExpr test; write ")"; semi; write "\n"
  | .for_ init test update body =>
    writeIndent; write "for ("
    match init with
    | some (.varDecl kind decls) => write (emitVarKind kind); write " "; emitDeclarators decls
    | some (.expr e) => emitExpr e
    | none => pure ()
    write "; "
    match test with | some e => emitExpr e | none => pure ()
    write "; "
    match update with | some e => emitExpr e | none => pure ()
    write ") "; emitStmtBody body; write "\n"
  | .forIn left right body =>
    writeIndent; write "for ("; emitForInit left; write " in "; emitExpr right
    write ") "; emitStmtBody body; write "\n"
  | .forOf left right body =>
    writeIndent; write "for ("; emitForInit left; write " of "; emitExpr right
    write ") "; emitStmtBody body; write "\n"
  | .switch discriminant cases =>
    writeIndent; write "switch ("; emitExpr discriminant; write ") {\n"
    incIndent
    for c in cases do emitSwitchCase c
    decIndent
    writeLn "}"
  | .try_ block_ handler finalizer =>
    writeIndent; write "try "; emitBlock block_
    match handler with
    | some (.mk param body) =>
      write " catch"
      match param with | some p => write " ("; emitPattern p; write ")" | none => pure ()
      write " "; emitBlock body
    | none => pure ()
    match finalizer with | some body => write " finally "; emitBlock body | none => pure ()
    write "\n"
  | .labeled label body =>
    writeIndent; write s!"{label}: "; emitStmtBody body; write "\n"
  | .debugger => writeLn "debugger;"
  | .varDecl kind declarations =>
    writeIndent; write (emitVarKind kind); write " "
    emitDeclarators declarations; semi; write "\n"
  | .funcDecl name params body async _generator =>
    writeIndent
    if async then write "async "
    write s!"function {name}("; emitParams params; write ") "; emitBlock body; write "\n"
  | .classDecl name superClass body =>
    writeIndent; write s!"class {name}"
    match superClass with | some sc => write " extends "; emitExpr sc | none => pure ()
    write " {\n"; incIndent
    for m in body do emitClassMember m
    decIndent; writeLn "}"
  | .importDecl specifiers source =>
    writeIndent; write "import "
    if specifiers.isEmpty then write s!"\"{escapeString source}\""
    else emitImportSpecifiers specifiers; write s!" from \"{escapeString source}\""
    semi; write "\n"
  | .exportNamed decl specifiers source =>
    writeIndent; write "export "
    match decl with
    | some d => emitStmtInline d
    | none =>
      write "{ "
      emitExportSpecs specifiers
      write " }"
      match source with | some src => write s!" from \"{escapeString src}\"" | none => pure ()
      semi; write "\n"
  | .exportDefault decl =>
    writeIndent; write "export default "; emitStmtInline decl
  | .exportAll source =>
    writeIndent; write s!"export * from \"{escapeString source}\""; semi; write "\n"

partial def emitStmtBody (s : Stmt) : Emitter Unit := do
  match s with
  | .block body => emitBlock body
  | _ => write "\n"; incIndent; emitStmt s; decIndent

partial def emitStmtInline (s : Stmt) : Emitter Unit := do
  match s with
  | .varDecl kind declarations =>
    write (emitVarKind kind); write " "; emitDeclarators declarations; semi; write "\n"
  | .funcDecl name params body async _gen =>
    if async then write "async "
    write s!"function {name}("; emitParams params; write ") "; emitBlock body; write "\n"
  | .classDecl name superClass body =>
    write s!"class {name}"
    match superClass with | some sc => write " extends "; emitExpr sc | none => pure ()
    write " {\n"; incIndent
    for m in body do emitClassMember m
    decIndent; writeLn "}"
  | .expr e => emitExpr e; semi; write "\n"
  | _ => emitStmt s

partial def emitForInit (fi : ForInit) : Emitter Unit :=
  match fi with
  | .varDecl kind decls => do write (emitVarKind kind); write " "; emitDeclarators decls
  | .expr e => emitExpr e

partial def emitDeclarators (decls : List VarDeclarator) : Emitter Unit := do
  let mut first := true
  for d in decls do
    if !first then write ", "
    first := false
    match d with
    | .mk pat init =>
      emitPattern pat
      match init with | some e => write " = "; emitExpr e 2 | none => pure ()

partial def emitSwitchCase (c : SwitchCase) : Emitter Unit := do
  match c with
  | .mk test stmts =>
    match test with
    | some t => writeIndent; write "case "; emitExpr t; write ":\n"
    | none => writeLn "default:"
    incIndent
    for s in stmts do emitStmt s
    decIndent

partial def emitClassMember (m : ClassMember) : Emitter Unit := do
  match m with
  | .method key params body kind static_ _computed =>
    writeIndent
    if static_ then write "static "
    match kind with | .get => write "get " | .set => write "set " | .method => pure ()
    emitExpr key; write "("; emitParams params; write ") "; emitBlock body; write "\n"
  | .property key value static_ _computed =>
    writeIndent
    if static_ then write "static "
    emitExpr key
    match value with | some v => write " = "; emitExpr v; semi | none => semi
    write "\n"

partial def emitImportSpecifiers (specs : List ImportSpecifier) : Emitter Unit := do
  let mut namedSpecs : List ImportSpecifier := []
  let mut nsSpec : Option ImportSpecifier := none
  for s in specs do
    match s with
    | .default_ _ => pure ()
    | .namespace _ => nsSpec := some s
    | .named _ _ => namedSpecs := namedSpecs ++ [s]
  for s in specs do
    match s with
    | .default_ name =>
      write name
      if !namedSpecs.isEmpty || nsSpec.isSome then write ", "
    | _ => pure ()
  match nsSpec with
  | some (.namespace name) => write s!"* as {name}"
  | _ =>
    if !namedSpecs.isEmpty then
      write "{ "
      let mut first := true
      for s in namedSpecs do
        if !first then write ", "
        first := false
        match s with
        | .named imported localName =>
          write imported
          if imported != localName then write s!" as {localName}"
        | _ => pure ()
      write " }"

partial def emitExportSpecs (specs : List ExportSpecifier) : Emitter Unit := do
  let mut first := true
  for s in specs do
    if !first then write ", "
    first := false
    match s with
    | .mk localName exported =>
      write localName
      if localName != exported then write s!" as {exported}"

end

def emitProgram (prog : Program) (config : EmitConfig := {}) : String :=
  let emitter : Emitter Unit := do
    for s in prog do emitStmt s
  let (_, state) := emitter.run { config := config }
  state.output

end LeanJS.JS.Emit
