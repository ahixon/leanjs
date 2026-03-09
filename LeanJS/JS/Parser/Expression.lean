import LeanJS.JS.Parser.Util

set_option maxHeartbeats 800000

namespace LeanJS.JS.Parser

/-- Binding power for binary operators -/
def tokenBP (tok : Token) : Option (Nat × Nat) :=
  match tok with
  | .comma         => some (1, 2)
  | .assign | .plusAssign | .minusAssign | .starAssign | .slashAssign
  | .percentAssign | .starStarAssign | .ltLtAssign | .gtGtAssign
  | .gtGtGtAssign | .ampersandAssign | .pipeAssign | .caretAssign
  | .ampersand2Assign | .pipe2Assign | .questionQuestionAssign
                    => some (4, 3)  -- right-associative
  | .question       => some (5, 6)  -- ternary
  | .pipe2          => some (7, 8)
  | .ampersand2     => some (9, 10)
  | .questionQuestion => some (7, 8)
  | .pipe           => some (11, 12)
  | .caret          => some (13, 14)
  | .ampersand      => some (15, 16)
  | .eq2 | .neq | .eq3 | .neq2 => some (17, 18)
  | .lt | .gt | .ltEq | .gtEq  => some (19, 20)
  | .keyword "instanceof"       => some (19, 20)
  | .keyword "in"               => some (19, 20)
  | .ltLt | .gtGt | .gtGtGt    => some (21, 22)
  | .plus | .minus              => some (23, 24)
  | .star | .slash | .percent   => some (25, 26)
  | .starStar                   => some (28, 27)  -- right-associative
  | _ => none

def tokenToBinOp : Token → Option BinOp
  | .plus => some .add
  | .minus => some .sub
  | .star => some .mul
  | .slash => some .div
  | .percent => some .mod
  | .starStar => some .exp
  | .eq2 => some .eq
  | .neq => some .neq
  | .eq3 => some .strictEq
  | .neq2 => some .strictNeq
  | .lt => some .lt
  | .ltEq => some .lte
  | .gt => some .gt
  | .gtEq => some .gte
  | .ampersand2 => some .and
  | .pipe2 => some .or
  | .ampersand => some .bitAnd
  | .pipe => some .bitOr
  | .caret => some .bitXor
  | .ltLt => some .shl
  | .gtGt => some .shr
  | .gtGtGt => some .ushr
  | .questionQuestion => some .nullishCoalesce
  | .keyword "in" => some .in
  | .keyword "instanceof" => some .instanceof
  | _ => none

def tokenToAssignOp : Token → Option AssignOp
  | .assign => some .assign
  | .plusAssign => some .addAssign
  | .minusAssign => some .subAssign
  | .starAssign => some .mulAssign
  | .slashAssign => some .divAssign
  | .percentAssign => some .modAssign
  | .starStarAssign => some .expAssign
  | .ampersand2Assign => some .andAssign
  | .pipe2Assign => some .orAssign
  | .questionQuestionAssign => some .nullishAssign
  | .ampersandAssign => some .bitAndAssign
  | .pipeAssign => some .bitOrAssign
  | .caretAssign => some .bitXorAssign
  | .ltLtAssign => some .shlAssign
  | .gtGtAssign => some .shrAssign
  | .gtGtGtAssign => some .ushrAssign
  | _ => none

def tokenToUnaryOp : Token → Option UnaryOp
  | .minus => some .neg
  | .plus => some .pos
  | .excl => some .not
  | .tilde => some .bitNot
  | .keyword "typeof" => some .typeof
  | .keyword "void" => some .void
  | .keyword "delete" => some .delete
  | _ => none

-- Forward declarations for mutual recursion
mutual

/-- Parse a primary expression -/
partial def parsePrimary : JSParser Expr := do
  let tok ← peek
  match tok with
  | .number n =>
    let _ ← advance
    return .literal (.number n)
  | .string s =>
    let _ ← advance
    return .literal (.string s)
  | .keyword "true" =>
    let _ ← advance
    return .literal (.bool true)
  | .keyword "false" =>
    let _ ← advance
    return .literal (.bool false)
  | .keyword "null" =>
    let _ ← advance
    return .literal .null
  | .keyword "undefined" =>
    let _ ← advance
    return .literal .undefined
  | .keyword "this" =>
    let _ ← advance
    return .this
  | .keyword "super" =>
    let _ ← advance
    return .ident "super"
  | .ident name =>
    let _ ← advance
    -- Check for single-param arrow function: ident => ...
    let nextTok ← peek
    if nextTok == .arrow then
      let _ ← advance  -- consume =>
      let body ← parseArrowBody
      return .arrowFunction [.ident name none] body
    else
      return .ident name
  | .keyword "function" =>
    let _ ← advance
    parseFunctionExpr
  | .keyword "new" =>
    let _ ← advance
    parseNewExpr
  | .keyword "typeof" | .keyword "void" | .keyword "delete" =>
    let _ ← advance
    let op := match tok with
      | .keyword "typeof" => UnaryOp.typeof
      | .keyword "void" => UnaryOp.void
      | _ => UnaryOp.delete
    let arg ← parseUnary
    return .unary op arg
  | .lparen =>
    -- Try arrow function first, fall back to parenthesized expression
    let pos ← savePos
    match ← tryParseArrowParams with
    | some params =>
      let body ← parseArrowBody
      return .arrowFunction params body
    | none =>
      restorePos pos
      let _ ← advance  -- consume (
      let expr ← parseExpr 0
      expect .rparen "')'"
      return .paren expr
  | .lbracket =>
    let _ ← advance
    parseArrayLiteral
  | .lbrace =>
    let _ ← advance
    parseObjectLiteral
  | .excl =>
    let _ ← advance
    let arg ← parseUnary
    return .unary .not arg
  | .tilde =>
    let _ ← advance
    let arg ← parseUnary
    return .unary .bitNot arg
  | .minus =>
    let _ ← advance
    let arg ← parseUnary
    return .unary .neg arg
  | .plus =>
    let _ ← advance
    let arg ← parseUnary
    return .unary .pos arg
  | .plusPlus =>
    let _ ← advance
    let arg ← parseUnary
    return .update .inc arg true
  | .minusMinus =>
    let _ ← advance
    let arg ← parseUnary
    return .update .dec arg true
  | .ellipsis =>
    let _ ← advance
    let arg ← parseExpr 3
    return .spread arg
  | _ => throw s!"unexpected token in expression: {repr tok}"

/-- Parse unary expression -/
partial def parseUnary : JSParser Expr := do
  let tok ← peek
  match tokenToUnaryOp tok with
  | some op =>
    let _ ← advance
    let arg ← parseUnary
    return .unary op arg
  | none =>
    match tok with
    | .plusPlus =>
      let _ ← advance
      let arg ← parseUnary
      return .update .inc arg true
    | .minusMinus =>
      let _ ← advance
      let arg ← parseUnary
      return .update .dec arg true
    | _ => parsePostfix

/-- Parse postfix expressions (calls, member access, postfix update) -/
partial def parsePostfix : JSParser Expr := do
  let mut expr ← parsePrimary
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    match tok with
    | .lparen =>
      let _ ← advance
      let args ← parseArgList
      expect .rparen "')'"
      expr := .call expr args
    | .dot =>
      let _ ← advance
      let name ← expectIdent
      expr := .member expr (.ident name)
    | .lbracket =>
      let _ ← advance
      let prop ← parseExpr 0
      expect .rbracket "']'"
      expr := .member expr (.computed prop)
    | .plusPlus =>
      let nl ← hadNewline
      if nl then continue_ := false
      else
        let _ ← advance
        expr := .update .inc expr false
    | .minusMinus =>
      let nl ← hadNewline
      if nl then continue_ := false
      else
        let _ ← advance
        expr := .update .dec expr false
    | .questionDot =>
      let _ ← advance
      let next ← peek
      match next with
      | .lparen =>
        let _ ← advance
        let args ← parseArgList
        expect .rparen "')'"
        expr := .call expr args
      | .lbracket =>
        let _ ← advance
        let prop ← parseExpr 0
        expect .rbracket "']'"
        expr := .member expr (.computed prop)
      | _ =>
        let name ← expectIdent
        expr := .member expr (.ident name)
    | _ => continue_ := false
  return expr

/-- Parse expression with minimum binding power (Pratt) -/
partial def parseExpr (minBP : Nat) : JSParser Expr := do
  let mut lhs ← parseUnary
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    match tokenBP tok with
    | none => continue_ := false
    | some (lbp, rbp) =>
      if lbp < minBP then
        continue_ := false
      else
        -- Special case: ternary
        if tok == .question then
          let _ ← advance
          let consequent ← parseExpr 0
          expect .colon "':'"
          let alternate ← parseExpr rbp
          lhs := .conditional lhs consequent alternate
        -- Assignment operators
        else if tok.isAssignOp then
          let _ ← advance
          match tokenToAssignOp tok with
          | some op =>
            let rhs ← parseExpr rbp
            lhs := .assign op (.expr lhs) rhs
          | none => throw "invalid assignment operator"
        -- Comma (sequence)
        else if tok == .comma then
          let _ ← advance
          let rhs ← parseExpr rbp
          match lhs with
          | .sequence exprs => lhs := .sequence (exprs ++ [rhs])
          | _ => lhs := .sequence [lhs, rhs]
        else
          match tokenToBinOp tok with
          | some op =>
            let _ ← advance
            let rhs ← parseExpr rbp
            -- Logical operators get .logical, others .binary
            match op with
            | .and | .or | .nullishCoalesce =>
              lhs := .binary op lhs rhs
            | _ => lhs := .binary op lhs rhs
          | none =>
            continue_ := false
  return lhs

/-- Parse comma-separated argument list -/
partial def parseArgList : JSParser (List Expr) := do
  let tok ← peek
  if tok == .rparen then return []
  let mut args : List Expr := []
  let first ← parseExpr 3  -- above comma precedence
  args := [first]
  while (← eat .comma) do
    let tok ← peek
    if tok == .rparen then break
    let arg ← parseExpr 3
    args := args ++ [arg]
  return args

/-- Parse array literal -/
partial def parseArrayLiteral : JSParser Expr := do
  let mut elements : List (Option Expr) := []
  while !(← isToken .rbracket) do
    if ← eat .comma then
      elements := elements ++ [none]
    else
      let elem ← parseExpr 3
      elements := elements ++ [some elem]
      if !(← isToken .rbracket) then
        expect .comma "','"
  expect .rbracket "']'"
  return .array elements

/-- Parse object literal -/
partial def parseObjectLiteral : JSParser Expr := do
  let mut props : List Property := []
  while !(← isToken .rbrace) do
    let prop ← parseProperty
    props := props ++ [prop]
    if !(← isToken .rbrace) then
      expect .comma "','"
  expect .rbrace "'}'"
  return .object props

/-- Parse a single object property -/
partial def parseProperty : JSParser Property := do
  let tok ← peek
  -- Check for getter/setter
  match tok with
  | .ident "get" =>
    let pos ← savePos
    let _ ← advance
    let next ← peek
    match next with
    | .lparen | .comma | .rbrace | .colon =>
      -- It's actually the identifier "get"
      restorePos pos
      parseSimpleProperty
    | _ =>
      let key ← parsePropertyKey
      expect .lparen "'('"
      expect .rparen "')'"
      let body ← parseBlock
      return .method key [] body .get false false false
  | .ident "set" =>
    let pos ← savePos
    let _ ← advance
    let next ← peek
    match next with
    | .lparen | .comma | .rbrace | .colon =>
      restorePos pos
      parseSimpleProperty
    | _ =>
      let key ← parsePropertyKey
      expect .lparen "'('"
      let param ← parseBindingPattern
      expect .rparen "')'"
      let body ← parseBlock
      return .method key [param] body .set false false false
  | .lbracket =>
    -- Computed property
    let _ ← advance
    let key ← parseExpr 0
    expect .rbracket "']'"
    let next ← peek
    if next == .lparen then
      let _ ← advance
      let params ← parseParamList
      expect .rparen "')'"
      let body ← parseBlock
      return .method key params body .method true false false
    else
      expect .colon "':'"
      let value ← parseExpr 3
      return .prop key value .init true false
  | _ => parseSimpleProperty

/-- Parse a simple property (key: value or shorthand) -/
partial def parseSimpleProperty : JSParser Property := do
  let key ← parsePropertyKey
  let tok ← peek
  match tok with
  | .colon =>
    let _ ← advance
    let value ← parseExpr 3
    return .prop key value .init false false
  | .lparen =>
    -- Method shorthand
    let _ ← advance
    let params ← parseParamList
    expect .rparen "')'"
    let body ← parseBlock
    return .method key params body .method false false false
  | _ =>
    -- Shorthand property
    match key with
    | .ident name => return .prop key (.ident name) .init false true
    | _ => throw "shorthand property must be an identifier"

/-- Parse property key -/
partial def parsePropertyKey : JSParser Expr := do
  let tok ← peek
  match tok with
  | .string s => let _ ← advance; return .literal (.string s)
  | .number n => let _ ← advance; return .literal (.number n)
  | .ident name => let _ ← advance; return .ident name
  | .keyword name => let _ ← advance; return .ident name
  | _ => throw s!"expected property key, got {repr tok}"

/-- Parse function expression (after 'function' keyword) -/
partial def parseFunctionExpr : JSParser Expr := do
  let name ← do
    let tok ← peek
    match tok with
    | .ident n => let _ ← advance; pure (some n)
    | _ => pure none
  expect .lparen "'('"
  let params ← parseParamList
  expect .rparen "')'"
  let body ← parseBlock
  return .function name params body

/-- Parse new expression -/
partial def parseNewExpr : JSParser Expr := do
  let callee ← parsePrimary
  -- Parse constructor arguments if present
  if ← eat .lparen then
    let args ← parseArgList
    expect .rparen "')'"
    return .new callee args
  else
    return .new callee []

/-- Try to parse arrow function parameters (returns none if not arrow) -/
partial def tryParseArrowParams : JSParser (Option (List Pattern)) := do
  -- Expect ( ... ) =>
  let _ ← advance  -- consume (
  let mut params : List Pattern := []
  if !(← isToken .rparen) then
    let first ← parseSimpleParam
    params := [first]
    while (← eat .comma) do
      let p ← parseSimpleParam
      params := params ++ [p]
  expect .rparen "')'"
  let tok ← peek
  if tok == .arrow then
    let _ ← advance
    return some params
  else
    return none

/-- Parse simple parameter (identifier, optionally with default) -/
partial def parseSimpleParam : JSParser Pattern := do
  let tok ← peek
  match tok with
  | .ident name =>
    let _ ← advance
    if ← eat .assign then
      let def_ ← parseExpr 3
      return .ident name (some def_)
    else
      return .ident name none
  | .ellipsis =>
    let _ ← advance
    let name ← expectIdent
    return .ident name none  -- rest param simplified
  | .lbrace =>
    parseObjectPattern
  | .lbracket =>
    parseArrayPattern
  | _ => throw s!"expected parameter, got {repr tok}"

/-- Parse arrow function body -/
partial def parseArrowBody : JSParser ExprOrBlock := do
  let tok ← peek
  if tok == .lbrace then
    let body ← parseBlock
    return .block body
  else
    let expr ← parseExpr 3
    return .expr expr

/-- Parse a block { ... } -/
partial def parseBlock : JSParser (List Stmt) := do
  expect .lbrace "'{'"
  let mut stmts : List Stmt := []
  while !(← isToken .rbrace) do
    let stmt ← parseStmt
    stmts := stmts ++ [stmt]
  expect .rbrace "'}'"
  return stmts

/-- Parse parameter list -/
partial def parseParamList : JSParser (List Pattern) := do
  if ← isToken .rparen then return []
  let mut params : List Pattern := []
  let first ← parseSimpleParam
  params := [first]
  while (← eat .comma) do
    if ← isToken .rparen then break
    let p ← parseSimpleParam
    params := params ++ [p]
  return params

/-- Parse binding pattern (for destructuring) -/
partial def parseBindingPattern : JSParser Pattern := do
  let tok ← peek
  match tok with
  | .ident name =>
    let _ ← advance
    -- Don't consume `=` here for simple identifiers.
    -- Default values for simple idents are handled by the caller
    -- (parseVarDeclarator handles initializers, parseParamList handles defaults).
    return .ident name none
  | .lbrace => parseObjectPattern
  | .lbracket => parseArrayPattern
  | _ => throw s!"expected binding pattern, got {repr tok}"

/-- Parse object destructuring pattern -/
partial def parseObjectPattern : JSParser Pattern := do
  expect .lbrace "'{'"
  let mut props : List PatternProp := []
  let mut rest : Option Pattern := none
  while !(← isToken .rbrace) do
    if ← eat .ellipsis then
      let name ← expectIdent
      rest := some (.ident name none)
      break
    let key ← parsePropertyKey
    if ← eat .colon then
      let value ← parseBindingPattern
      props := props ++ [.keyVal key value false]
    else
      match key with
      | .ident name =>
        let def_ ← if ← eat .assign then
          let d ← parseExpr 3
          pure (some d)
        else pure none
        props := props ++ [.shorthand name def_]
      | _ => throw "expected identifier in shorthand pattern"
    if !(← isToken .rbrace) then
      expect .comma "','"
  expect .rbrace "'}'"
  return .object props rest

/-- Parse array destructuring pattern -/
partial def parseArrayPattern : JSParser Pattern := do
  expect .lbracket "'['"
  let mut elems : List (Option Pattern) := []
  let mut rest : Option Pattern := none
  while !(← isToken .rbracket) do
    if ← eat .comma then
      elems := elems ++ [none]
    else if ← eat .ellipsis then
      let p ← parseBindingPattern
      rest := some p
      break
    else
      let p ← parseBindingPattern
      elems := elems ++ [some p]
      if !(← isToken .rbracket) then
        if !(← eat .comma) then break
  expect .rbracket "']'"
  return .array elems rest

/-- Parse a statement (forward declaration used by parseBlock) -/
partial def parseStmt : JSParser Stmt := do
  let tok ← peek
  match tok with
  | .lbrace =>
    let body ← parseBlock
    return .block body
  | .semi =>
    let _ ← advance
    return .empty
  | .keyword "var" =>
    let _ ← advance
    parseVarDecl .var
  | .keyword "let" =>
    let _ ← advance
    parseVarDecl .let
  | .keyword "const" =>
    let _ ← advance
    parseVarDecl .const
  | .keyword "if" =>
    let _ ← advance
    parseIfStmt
  | .keyword "while" =>
    let _ ← advance
    parseWhileStmt
  | .keyword "do" =>
    let _ ← advance
    parseDoWhileStmt
  | .keyword "for" =>
    let _ ← advance
    parseForStmt
  | .keyword "return" =>
    let _ ← advance
    parseReturnStmt
  | .keyword "throw" =>
    let _ ← advance
    let arg ← parseExpr 0
    semicolon
    return .throw arg
  | .keyword "break" =>
    let _ ← advance
    let nl ← hadNewline
    let label ← if nl then pure none
    else do
      let tok ← peek
      match tok with
      | .ident name => let _ ← advance; pure (some name)
      | _ => pure none
    semicolon
    return .break_ label
  | .keyword "continue" =>
    let _ ← advance
    let nl ← hadNewline
    let label ← if nl then pure none
    else do
      let tok ← peek
      match tok with
      | .ident name => let _ ← advance; pure (some name)
      | _ => pure none
    semicolon
    return .continue_ label
  | .keyword "function" =>
    let _ ← advance
    parseFuncDecl false false
  | .keyword "class" =>
    let _ ← advance
    parseClassDecl
  | .keyword "switch" =>
    let _ ← advance
    parseSwitchStmt
  | .keyword "try" =>
    let _ ← advance
    parseTryStmt
  | .keyword "debugger" =>
    let _ ← advance
    semicolon
    return .debugger
  | .keyword "import" =>
    let _ ← advance
    parseImportDecl
  | .keyword "export" =>
    let _ ← advance
    parseExportDecl
  | .keyword "async" =>
    let pos ← savePos
    let _ ← advance
    if ← isKeyword "function" then
      let _ ← advance
      parseFuncDecl true false
    else
      restorePos pos
      parseExpressionStmt
  | .ident _ =>
    -- Check for labeled statement
    let pos ← savePos
    let name ← expectIdent
    if ← eat .colon then
      let body ← parseStmt
      return .labeled name body
    else
      restorePos pos
      parseExpressionStmt
  | _ => parseExpressionStmt

/-- Parse expression statement -/
partial def parseExpressionStmt : JSParser Stmt := do
  let expr ← parseExpr 0
  semicolon
  return .expr expr

/-- Parse variable declaration -/
partial def parseVarDecl (kind : VarKind) : JSParser Stmt := do
  let mut decls : List VarDeclarator := []
  let first ← parseVarDeclarator
  decls := [first]
  while (← eat .comma) do
    let d ← parseVarDeclarator
    decls := decls ++ [d]
  semicolon
  return .varDecl kind decls

/-- Parse a single variable declarator -/
partial def parseVarDeclarator : JSParser VarDeclarator := do
  let pat ← parseBindingPattern
  let init ← if ← eat .assign then
    let e ← parseExpr 3
    pure (some e)
  else pure none
  return .mk pat init

/-- Parse if statement -/
partial def parseIfStmt : JSParser Stmt := do
  expect .lparen "'('"
  let test ← parseExpr 0
  expect .rparen "')'"
  let consequent ← parseStmt
  let alternate ← if ← eatKeyword "else" then
    let s ← parseStmt
    pure (some s)
  else pure none
  return .ifStmt test consequent alternate

/-- Parse while statement -/
partial def parseWhileStmt : JSParser Stmt := do
  expect .lparen "'('"
  let test ← parseExpr 0
  expect .rparen "')'"
  let body ← parseStmt
  return .while_ test body

/-- Parse do-while statement -/
partial def parseDoWhileStmt : JSParser Stmt := do
  let body ← parseStmt
  expectKeyword "while"
  expect .lparen "'('"
  let test ← parseExpr 0
  expect .rparen "')'"
  semicolon
  return .doWhile body test

/-- Parse for statement (for, for-in, for-of) -/
partial def parseForStmt : JSParser Stmt := do
  expect .lparen "'('"
  let tok ← peek
  match tok with
  | .keyword "var" | .keyword "let" | .keyword "const" =>
    let kind : VarKind := match tok with
      | .keyword "let" => .let
      | .keyword "const" => .const
      | _ => .var
    let _ ← advance
    let pat ← parseBindingPattern
    let next ← peek
    match next with
    | .keyword "in" =>
      let _ ← advance
      let right ← parseExpr 0
      expect .rparen "')'"
      let body ← parseStmt
      return .forIn (.varDecl kind [.mk pat none]) right body
    | .keyword "of" =>
      let _ ← advance
      let right ← parseExpr 0
      expect .rparen "')'"
      let body ← parseStmt
      return .forOf (.varDecl kind [.mk pat none]) right body
    | _ =>
      let init_ ← if ← eat .assign then
        let e ← parseExpr 3
        pure (some e)
      else pure none
      let mut decls : List VarDeclarator := [.mk pat init_]
      while (← eat .comma) do
        let d ← parseVarDeclarator
        decls := decls ++ [d]
      expect .semi "';'"
      let test ← if ← isToken .semi then pure none
      else do let e ← parseExpr 0; pure (some e)
      expect .semi "';'"
      let update ← if ← isToken .rparen then pure none
      else do let e ← parseExpr 0; pure (some e)
      expect .rparen "')'"
      let body ← parseStmt
      return .for_ (some (.varDecl kind decls)) test update body
  | .semi =>
    let _ ← advance
    let test ← if ← isToken .semi then pure none
    else do let e ← parseExpr 0; pure (some e)
    expect .semi "';'"
    let update ← if ← isToken .rparen then pure none
    else do let e ← parseExpr 0; pure (some e)
    expect .rparen "')'"
    let body ← parseStmt
    return .for_ none test update body
  | _ =>
    let expr ← parseExpr 0
    let next ← peek
    match next with
    | .keyword "in" =>
      let _ ← advance
      let right ← parseExpr 0
      expect .rparen "')'"
      let body ← parseStmt
      return .forIn (.expr expr) right body
    | .keyword "of" =>
      let _ ← advance
      let right ← parseExpr 0
      expect .rparen "')'"
      let body ← parseStmt
      return .forOf (.expr expr) right body
    | _ =>
      expect .semi "';'"
      let test ← if ← isToken .semi then pure none
      else do let e ← parseExpr 0; pure (some e)
      expect .semi "';'"
      let update ← if ← isToken .rparen then pure none
      else do let e ← parseExpr 0; pure (some e)
      expect .rparen "')'"
      let body ← parseStmt
      return .for_ (some (.expr expr)) test update body

/-- Parse return statement -/
partial def parseReturnStmt : JSParser Stmt := do
  let nl ← hadNewline
  if nl then
    return .return_ none
  else
    let tok ← peek
    match tok with
    | .semi | .rbrace | .eof =>
      semicolon
      return .return_ none
    | _ =>
      let expr ← parseExpr 0
      semicolon
      return .return_ (some expr)

/-- Parse function declaration -/
partial def parseFuncDecl (async : Bool) (generator : Bool) : JSParser Stmt := do
  let gen ← if ← eat .star then pure true else pure generator
  let name ← expectIdent
  expect .lparen "'('"
  let params ← parseParamList
  expect .rparen "')'"
  let body ← parseBlock
  return .funcDecl name params body async gen

/-- Parse class declaration -/
partial def parseClassDecl : JSParser Stmt := do
  let name ← expectIdent
  let superClass ← if ← eatKeyword "extends" then
    let e ← parseExpr 0
    pure (some e)
  else pure none
  expect .lbrace "'{'"
  let mut members : List ClassMember := []
  while !(← isToken .rbrace) do
    if ← eat .semi then continue
    let m ← parseClassMember
    members := members ++ [m]
  expect .rbrace "'}'"
  return .classDecl name superClass members

/-- Parse class member -/
partial def parseClassMember : JSParser ClassMember := do
  let static_ ← eatKeyword "static"
  let tok ← peek
  match tok with
  | .ident "get" =>
    let pos ← savePos
    let _ ← advance
    let next ← peek
    match next with
    | .lparen =>
      restorePos pos
      parseClassMethod static_
    | _ =>
      let key ← parsePropertyKey
      expect .lparen "'('"
      expect .rparen "')'"
      let body ← parseBlock
      return .method key [] body .get static_ false
  | .ident "set" =>
    let pos ← savePos
    let _ ← advance
    let next ← peek
    match next with
    | .lparen =>
      restorePos pos
      parseClassMethod static_
    | _ =>
      let key ← parsePropertyKey
      expect .lparen "'('"
      let param ← parseBindingPattern
      expect .rparen "')'"
      let body ← parseBlock
      return .method key [param] body .set static_ false
  | _ => parseClassMethod static_

/-- Parse class method -/
partial def parseClassMethod : Bool → JSParser ClassMember := fun static_ => do
  let key ← parsePropertyKey
  let tok ← peek
  match tok with
  | .lparen =>
    let _ ← advance
    let params ← parseParamList
    expect .rparen "')'"
    let body ← parseBlock
    return .method key params body .method static_ false
  | .assign =>
    let _ ← advance
    let value ← parseExpr 3
    semicolon
    return .property key (some value) static_ false
  | _ =>
    semicolon
    return .property key none static_ false

/-- Parse switch statement -/
partial def parseSwitchStmt : JSParser Stmt := do
  expect .lparen "'('"
  let discriminant ← parseExpr 0
  expect .rparen "')'"
  expect .lbrace "'{'"
  let mut cases : List SwitchCase := []
  while !(← isToken .rbrace) do
    let c ← parseSwitchCase
    cases := cases ++ [c]
  expect .rbrace "'}'"
  return .switch discriminant cases

/-- Parse switch case -/
partial def parseSwitchCase : JSParser SwitchCase := do
  let test ← if ← eatKeyword "case" then
    let e ← parseExpr 0
    expect .colon "':'"
    pure (some e)
  else do
    expectKeyword "default"
    expect .colon "':'"
    pure none
  let mut stmts : List Stmt := []
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    match tok with
    | .keyword "case" | .keyword "default" | .rbrace => continue_ := false
    | _ =>
      let s ← parseStmt
      stmts := stmts ++ [s]
  return .mk test stmts

/-- Parse try statement -/
partial def parseTryStmt : JSParser Stmt := do
  let block_ ← parseBlock
  let handler ← if ← eatKeyword "catch" then
    let param ← if ← eat .lparen then
      let p ← parseBindingPattern
      expect .rparen "')'"
      pure (some p)
    else pure none
    let body ← parseBlock
    pure (some (CatchClause.mk param body))
  else pure none
  let finalizer ← if ← eatKeyword "finally" then
    let body ← parseBlock
    pure (some body)
  else pure none
  return .try_ block_ handler finalizer

/-- Parse import declaration -/
partial def parseImportDecl : JSParser Stmt := do
  let tok ← peek
  match tok with
  | .string source =>
    let _ ← advance
    semicolon
    return .importDecl [] source
  | _ =>
    let mut specifiers : List ImportSpecifier := []
    let tok ← peek
    match tok with
    | .ident name =>
      let _ ← advance
      specifiers := [.default_ name]
      if ← eat .comma then
        let more ← parseImportSpecifiers
        specifiers := specifiers ++ more
    | .star =>
      let _ ← advance
      expectKeyword "as"
      let name ← expectIdent
      specifiers := [.namespace name]
    | .lbrace =>
      specifiers ← parseImportSpecifiers
    | _ => throw s!"unexpected token in import: {repr tok}"
    expectKeyword "from"
    let srcTok ← advance
    let source ← match srcTok with
      | .string s => pure s
      | _ => throw "expected string literal for import source"
    semicolon
    return .importDecl specifiers source

/-- Parse named import specifiers { a, b as c } -/
partial def parseImportSpecifiers : JSParser (List ImportSpecifier) := do
  expect .lbrace "'{'"
  let mut specs : List ImportSpecifier := []
  while !(← isToken .rbrace) do
    let imported ← expectIdent
    let localName ← if ← eatKeyword "as" then expectIdent else pure imported
    specs := specs ++ [.named imported localName]
    if !(← isToken .rbrace) then
      expect .comma "','"
  expect .rbrace "'}'"
  return specs

/-- Parse export declaration -/
partial def parseExportDecl : JSParser Stmt := do
  let tok ← peek
  match tok with
  | .keyword "default" =>
    let _ ← advance
    let stmt ← parseStmt
    return .exportDefault stmt
  | .lbrace =>
    let specs ← parseExportSpecifiers
    let source ← if ← eatKeyword "from" then
      let s ← advance
      match s with
      | .string str => pure (some str)
      | _ => throw "expected string"
    else pure none
    semicolon
    return .exportNamed none specs source
  | .star =>
    let _ ← advance
    expectKeyword "from"
    let s ← advance
    match s with
    | .string source => semicolon; return .exportAll source
    | _ => throw "expected string after 'from'"
  | _ =>
    let stmt ← parseStmt
    return .exportNamed (some stmt) [] none

/-- Parse export specifiers { a, b as c } -/
partial def parseExportSpecifiers : JSParser (List ExportSpecifier) := do
  expect .lbrace "'{'"
  let mut specs : List ExportSpecifier := []
  while !(← isToken .rbrace) do
    let localName ← expectIdent
    let exported ← if ← eatKeyword "as" then expectIdent else pure localName
    specs := specs ++ [.mk localName exported]
    if !(← isToken .rbrace) then
      expect .comma "','"
  expect .rbrace "'}'"
  return specs

end

end LeanJS.JS.Parser
