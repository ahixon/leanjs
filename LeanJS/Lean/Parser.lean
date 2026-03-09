/-
  Lean 4 Parser

  Parses Lean surface syntax into LeanAST.
  Uses StateT ParserState (Except String) monad, same pattern as JS parser.
  Indentation-sensitive via LocatedToken.col.
-/
import LeanJS.Lean.Token
import LeanJS.Lean.Lexer
import LeanJS.Lean.AST

set_option maxHeartbeats 1600000

namespace LeanJS.Lean.Parser

open LeanJS.Lean

-- ============================================================
-- Parser monad and state
-- ============================================================

structure ParserState where
  tokens : Array LocatedToken
  pos : Nat := 0
  deriving Inhabited

abbrev LeanParser := StateT ParserState (Except String)

/-- Get current located token without consuming -/
def peekLoc : LeanParser LocatedToken := do
  let s ← get
  if h : s.pos < s.tokens.size then
    return s.tokens[s.pos]
  else
    return { token := .eof, line := 0, col := 0 }

/-- Get current token without consuming -/
def peek : LeanParser LeanToken := do
  let lt ← peekLoc
  return lt.token

/-- Consume current token and advance -/
def advance : LeanParser LeanToken := do
  let s ← get
  if h : s.pos < s.tokens.size then
    let tok := s.tokens[s.pos]
    set { s with pos := s.pos + 1 }
    return tok.token
  else
    return .eof

/-- Get current column -/
def currentCol : LeanParser Nat := do
  let lt ← peekLoc
  return lt.col

/-- Expect and consume a specific token -/
def expect (tok : LeanToken) (msg : String := "") : LeanParser Unit := do
  let t ← advance
  if t == tok then pure ()
  else throw s!"expected {msg}, got {repr t}"

/-- Expect a keyword -/
def expectKeyword (kw : String) : LeanParser Unit := do
  let t ← advance
  match t with
  | .keyword k => if k == kw then pure () else throw s!"expected '{kw}', got keyword '{k}'"
  | _ => throw s!"expected keyword '{kw}', got {repr t}"

/-- Check if current token is a keyword -/
def isKeyword (kw : String) : LeanParser Bool := do
  let t ← peek
  return t == .keyword kw

/-- Check if current token matches -/
def isToken (tok : LeanToken) : LeanParser Bool := do
  let t ← peek
  return t == tok

/-- Consume token if it matches -/
def eat (tok : LeanToken) : LeanParser Bool := do
  let t ← peek
  if t == tok then
    let _ ← advance
    return true
  else
    return false

/-- Consume keyword if it matches -/
def eatKeyword (kw : String) : LeanParser Bool := do
  if ← isKeyword kw then
    let _ ← advance
    return true
  else
    return false

/-- Expect an identifier -/
def expectIdent : LeanParser String := do
  let t ← advance
  match t with
  | .ident name => return name
  | _ => throw s!"expected identifier, got {repr t}"

/-- Save parser position -/
def savePos : LeanParser Nat := do
  let s ← get
  return s.pos

/-- Restore parser position -/
def restorePos (pos : Nat) : LeanParser Unit := do
  let s ← get
  set { s with pos := pos }

/-- Try a parser, backtrack on failure -/
def tryParse {α : Type} (p : LeanParser α) : LeanParser (Option α) := do
  let pos ← savePos
  try
    let a ← p
    return some a
  catch _ =>
    restorePos pos
    return none

/-- Check if current token can start an argument in function application -/
def canStartArg : LeanParser Bool := do
  let t ← peek
  match t with
  | .ident _ | .nat _ | .float _ | .string _ => return true
  | .lparen | .hashBracket | .lbrace | .underscore => return true
  | .keyword "true" | .keyword "false" => return true
  | .keyword "fun" | .keyword "if" | .keyword "match" => return true
  -- Not: do, then, else, with, in — these are clause terminators
  -- Not: let, while, for, return, try, throw — these start new do-elements
  | _ => return false

/-- Check if current token is an operator -/
def isOperator : LeanParser Bool := do
  let t ← peek
  match t with
  | .plus | .minus | .star | .slash | .percent | .caret => return true
  | .eq2 | .neq | .lt | .gt | .ltEq | .gtEq => return true
  | .ampersand2 | .pipe2 | .plusPlus => return true
  | .ampersand3 | .pipe3 | .caret3 | .ltLtLt | .gtGtGt | .tilde3 => return true
  | _ => return false

/-- Binding power for Lean binary operators -/
def tokenBP (tok : LeanToken) : Option (Nat × Nat) :=
  match tok with
  | .pipe2       => some (3, 4)
  | .ampersand2  => some (5, 6)
  | .eq2 | .neq  => some (7, 8)
  | .lt | .gt | .ltEq | .gtEq => some (9, 10)
  | .plusPlus    => some (11, 12)
  | .plus | .minus => some (13, 14)
  | .star | .slash | .percent => some (15, 16)
  | .caret       => some (18, 17)  -- right-associative
  | .ampersand3  => some (5, 6)
  | .pipe3       => some (3, 4)
  | .caret3      => some (7, 8)
  | .ltLtLt      => some (11, 12)
  | .gtGtGt      => some (11, 12)
  | _ => none

/-- Map token to operator string -/
def tokenToOpStr : LeanToken → Option String
  | .plus => some "+" | .minus => some "-" | .star => some "*"
  | .slash => some "/" | .percent => some "%" | .caret => some "^"
  | .eq2 => some "==" | .neq => some "!="
  | .lt => some "<" | .gt => some ">" | .ltEq => some "<=" | .gtEq => some ">="
  | .ampersand2 => some "&&" | .pipe2 => some "||" | .plusPlus => some "++"
  | .ampersand3 => some "&&&" | .pipe3 => some "|||" | .caret3 => some "^^^"
  | .ltLtLt => some "<<<" | .gtGtGt => some ">>>"
  | _ => none

-- ============================================================
-- Expression parsing (mutual block)
-- ============================================================

mutual

/-- Parse a primary expression -/
partial def parsePrimary : LeanParser LeanExpr := do
  let tok ← peek
  match tok with
  | .nat n =>
    let _ ← advance
    return .lit (.natVal n)
  | .float f =>
    let _ ← advance
    return .lit (.float f)
  | .string s =>
    let _ ← advance
    return .lit (.string s)
  | .keyword "true" =>
    let _ ← advance
    return .lit (.bool true)
  | .keyword "false" =>
    let _ ← advance
    return .lit (.bool false)
  | .ident name =>
    let _ ← advance
    return .ident name
  | .underscore =>
    let _ ← advance
    return .hole
  | .lparen =>
    let _ ← advance
    let tok2 ← peek
    if tok2 == .rparen then
      let _ ← advance
      return .unit
    else
      let expr ← parseExpr 0
      expect .rparen "')'"
      return .paren expr
  | .hashBracket =>
    let _ ← advance
    parseArrayLit
  | .lbrace =>
    let _ ← advance
    parseStructLit
  | .keyword "fun" =>
    let _ ← advance
    parseFun
  | .keyword "let" =>
    let _ ← advance
    parseLet
  | .keyword "if" =>
    let _ ← advance
    parseIf
  | .keyword "match" =>
    let _ ← advance
    parseMatch
  | .keyword "do" =>
    let _ ← advance
    parseDo
  | .keyword "while" =>
    let _ ← advance
    parseWhile
  | .keyword "for" =>
    let _ ← advance
    parseFor
  | .keyword "return" =>
    let _ ← advance
    let val ← parseExpr 0
    return .«return» val
  | .keyword "try" =>
    let _ ← advance
    parseTry
  | .keyword "throw" =>
    let _ ← advance
    let val ← parseExpr 0
    return .«throw» val
  | .excl =>
    let _ ← advance
    let arg ← parsePrimary
    return .unaryOp "!" arg
  | .minus =>
    let _ ← advance
    let arg ← parsePrimary
    return .unaryOp "-" arg
  | .tilde3 =>
    let _ ← advance
    let arg ← parsePrimary
    return .unaryOp "~~~" arg
  | _ => throw s!"unexpected token: {repr tok}"

/-- Parse postfix expressions (field projection, array index) -/
partial def parsePostfix : LeanParser LeanExpr := do
  let mut expr ← parsePrimary
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    match tok with
    | .dot =>
      let _ ← advance
      let name ← expectIdent
      expr := .proj expr name
    | .lbracket =>
      let _ ← advance
      let idx ← parseExpr 0
      expect .rbracket "']'"
      if ← eat .excl then
        expr := .arrayIdx expr idx
      else
        expr := .arrayIdx expr idx
    | _ => continue_ := false
  return expr

/-- Parse function application (juxtaposition) -/
partial def parseApp : LeanParser LeanExpr := do
  let startLoc ← peekLoc
  let mut expr ← parsePostfix
  let mut continue_ := true
  while continue_ do
    let nextLoc ← peekLoc
    -- Don't consume args on a new line at same or lesser indentation
    if nextLoc.line > startLoc.line && nextLoc.col ≤ startLoc.col then
      continue_ := false
    else
      let canArg ← canStartArg
      let isOp ← isOperator
      if canArg && !isOp then
        let arg ← parsePostfix
        expr := .app expr arg
      else
        continue_ := false
  return expr

/-- Parse expression with Pratt precedence climbing -/
partial def parseExpr (minBP : Nat) : LeanParser LeanExpr := do
  let mut lhs ← parseApp
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    -- Check for right arrow (function type or special operator)
    if tok == .rightArrow then
      if minBP ≤ 2 then
        let _ ← advance
        let rhs ← parseExpr 1  -- right-associative
        lhs := .binOp "→" lhs rhs
      else
        continue_ := false
    else
      match tokenBP tok with
      | none => continue_ := false
      | some (lbp, rbp) =>
        if lbp < minBP then
          continue_ := false
        else
          match tokenToOpStr tok with
          | some op =>
            let _ ← advance
            let rhs ← parseExpr rbp
            lhs := .binOp op lhs rhs
          | none => continue_ := false
  return lhs

/-- Parse let expression: let [mut] name [:Type] := val -/
partial def parseLet : LeanParser LeanExpr := do
  let isMut ← eatKeyword "mut"
  let name ← expectIdent
  -- Optional type annotation
  let ty ← if ← eat .colon then
    let t ← parseType
    pure (some t)
  else pure none
  -- Check for bind (←) vs assign (:=)
  let tok ← peek
  if tok == .leftArrow then
    let _ ← advance
    let value ← parseExpr 0
    return .bind name ty value
  else
    expect .colonEq "':='"
    let value ← parseExpr 0
    -- In expression context, check if there's a body after newline
    -- For do-blocks, let declarations are handled by parseDoElem
    if isMut then
      -- Return as a bind with special marker in the name
      return .bind (name) ty value
    else
      return .«let» name ty value .hole

/-- Parse fun expression: fun params => body -/
partial def parseFun : LeanParser LeanExpr := do
  let mut params : List LeanParam := []
  -- Parse parameters until =>
  let mut done := false
  while !done do
    let tok ← peek
    match tok with
    | .fatArrow => done := true
    | .ident name =>
      let _ ← advance
      -- Check for type annotation
      if ← eat .colon then
        let ty ← parseType
        params := params ++ [{ name, type := some ty }]
      else
        params := params ++ [{ name }]
    | .underscore =>
      let _ ← advance
      params := params ++ [{ name := "_" }]
    | .lparen =>
      let _ ← advance
      let name ← expectIdent
      let ty ← if ← eat .colon then
        let t ← parseType
        pure (some t)
      else pure none
      expect .rparen "')'"
      params := params ++ [{ name, type := ty }]
    | _ => throw s!"expected parameter or '=>', got {repr tok}"
  expect .fatArrow "'=>'"
  let body ← parseExpr 0
  return .lam params body

/-- Parse if expression: if cond then t [else e] -/
partial def parseIf : LeanParser LeanExpr := do
  let cond ← parseExpr 0
  expectKeyword "then"
  let then_ ← parseExpr 0
  let else_ ← if ← eatKeyword "else" then
    let e ← parseExpr 0
    pure (some e)
  else pure none
  return .«if» cond then_ else_

/-- Parse match expression: match scrutinee with | pat => body ... -/
partial def parseMatch : LeanParser LeanExpr := do
  let scrutinee ← parseExpr 0
  expectKeyword "with"
  let mut alts : List LeanMatchAlt := []
  -- Parse alternatives
  while (← isToken .pipe) do
    let _ ← advance
    let pat ← parsePattern
    expect .fatArrow "'=>'"
    let body ← parseExpr 0
    alts := alts ++ [.mk pat body]
  return .«match» scrutinee alts

/-- Parse do block -/
partial def parseDo : LeanParser LeanExpr := do
  let baseCol ← currentCol
  let mut elems : List LeanDoElem := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol then
      continue_ := false
    else
      let elem ← parseDoElem
      elems := elems ++ [elem]
  return .doBlock elems

/-- Parse a single do-block element -/
partial def parseDoElem : LeanParser LeanDoElem := do
  let tok ← peek
  match tok with
  | .keyword "let" =>
    let _ ← advance
    let isMut ← eatKeyword "mut"
    let name ← expectIdent
    let ty ← if ← eat .colon then
      let t ← parseType
      pure (some t)
    else pure none
    let nextTok ← peek
    if nextTok == .leftArrow then
      let _ ← advance
      let value ← parseExpr 0
      return .bind name ty value
    else
      expect .colonEq "':='"
      let value ← parseExpr 0
      if isMut then
        return .mutDecl name ty value
      else
        return .letDecl name ty value
  | .keyword "return" =>
    let _ ← advance
    let value ← parseExpr 0
    return .doReturn value
  | .keyword "if" =>
    let _ ← advance
    parseDoIf
  | .keyword "while" =>
    let _ ← advance
    parseDoWhile
  | .keyword "for" =>
    let _ ← advance
    parseDoFor
  | .keyword "try" =>
    let _ ← advance
    parseDoTry
  | .ident name =>
    -- Check for reassignment: name := value
    let pos ← savePos
    let _ ← advance
    let nextTok ← peek
    if nextTok == .colonEq then
      let _ ← advance
      let value ← parseExpr 0
      return .reassign name value
    else
      restorePos pos
      let expr ← parseExpr 0
      return .eval expr
  | _ =>
    let expr ← parseExpr 0
    return .eval expr

/-- Parse do-block if -/
partial def parseDoIf : LeanParser LeanDoElem := do
  let cond ← parseExpr 0
  expectKeyword "then"
  let baseCol ← currentCol
  let mut thenElems : List LeanDoElem := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol || (← isKeyword "else") then
      continue_ := false
    else
      let elem ← parseDoElem
      thenElems := thenElems ++ [elem]
  let elseElems ← if ← eatKeyword "else" then
    let baseCol2 ← currentCol
    let mut elems : List LeanDoElem := []
    let mut cont := true
    while cont do
      let col ← currentCol
      let tok ← peek
      if tok == .eof || col < baseCol2 then
        cont := false
      else
        let elem ← parseDoElem
        elems := elems ++ [elem]
    pure elems
  else pure []
  return .doIf cond thenElems elseElems

/-- Parse do-block while -/
partial def parseDoWhile : LeanParser LeanDoElem := do
  let cond ← parseExpr 0
  expectKeyword "do"
  let baseCol ← currentCol
  let mut body : List LeanDoElem := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol then
      continue_ := false
    else
      let elem ← parseDoElem
      body := body ++ [elem]
  return .doWhile cond body

/-- Parse do-block for -/
partial def parseDoFor : LeanParser LeanDoElem := do
  let var ← expectIdent
  expectKeyword "in"
  let iter ← parseExpr 0
  expectKeyword "do"
  let baseCol ← currentCol
  let mut body : List LeanDoElem := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol then
      continue_ := false
    else
      let elem ← parseDoElem
      body := body ++ [elem]
  return .doFor var iter body

/-- Parse do-block try -/
partial def parseDoTry : LeanParser LeanDoElem := do
  let baseCol ← currentCol
  let mut body : List LeanDoElem := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol || (← isKeyword "catch") || (← isKeyword "finally") then
      continue_ := false
    else
      let elem ← parseDoElem
      body := body ++ [elem]
  let catchVar ← if ← eatKeyword "catch" then
    let name ← expectIdent
    expect .fatArrow "'=>'"
    pure (some name)
  else pure none
  let handler ← if catchVar.isSome then
    let baseCol2 ← currentCol
    let mut elems : List LeanDoElem := []
    let mut cont := true
    while cont do
      let col ← currentCol
      let tok ← peek
      if tok == .eof || col < baseCol2 || (← isKeyword "finally") then
        cont := false
      else
        let elem ← parseDoElem
        elems := elems ++ [elem]
    pure elems
  else pure []
  let finalizer ← if ← eatKeyword "finally" then
    let baseCol3 ← currentCol
    let mut elems : List LeanDoElem := []
    let mut cont := true
    while cont do
      let col ← currentCol
      let tok ← peek
      if tok == .eof || col < baseCol3 then
        cont := false
      else
        let elem ← parseDoElem
        elems := elems ++ [elem]
    pure elems
  else pure []
  return .doTry body catchVar handler finalizer

/-- Parse while expression -/
partial def parseWhile : LeanParser LeanExpr := do
  let cond ← parseExpr 0
  expectKeyword "do"
  let body ← parseExpr 0
  return .«while» cond body

/-- Parse for expression -/
partial def parseFor : LeanParser LeanExpr := do
  let var ← expectIdent
  expectKeyword "in"
  let iter ← parseExpr 0
  expectKeyword "do"
  let body ← parseExpr 0
  return .«for» var iter body

/-- Parse try expression -/
partial def parseTry : LeanParser LeanExpr := do
  let body ← parseExpr 0
  let catchVar ← if ← eatKeyword "catch" then
    let name ← expectIdent
    expect .fatArrow "'=>'"
    pure (some name)
  else pure none
  let handler ← if catchVar.isSome then
    let e ← parseExpr 0
    pure (some e)
  else pure none
  let finalizer ← if ← eatKeyword "finally" then
    let e ← parseExpr 0
    pure (some e)
  else pure none
  return .«try» body catchVar handler finalizer

/-- Parse #[elem, ...] -/
partial def parseArrayLit : LeanParser LeanExpr := do
  let mut elems : List LeanExpr := []
  if !(← isToken .rbracket) then
    let first ← parseExpr 0
    elems := [first]
    while (← eat .comma) do
      if ← isToken .rbracket then break
      let elem ← parseExpr 0
      elems := elems ++ [elem]
  expect .rbracket "']'"
  return .arrayLit elems

/-- Parse { [Name with] field := val, ... } -/
partial def parseStructLit : LeanParser LeanExpr := do
  -- Check for { Name with ... }
  let mut structName : Option String := none
  let pos ← savePos
  let tok ← peek
  match tok with
  | .ident name =>
    let _ ← advance
    if ← eatKeyword "with" then
      structName := some name
    else
      restorePos pos
  | _ => pure ()
  let mut fields : List (String × LeanExpr) := []
  if !(← isToken .rbrace) then
    let fname ← expectIdent
    expect .colonEq "':='"
    let fval ← parseExpr 0
    fields := [(fname, fval)]
    while (← eat .comma) do
      if ← isToken .rbrace then break
      let fname ← expectIdent
      expect .colonEq "':='"
      let fval ← parseExpr 0
      fields := fields ++ [(fname, fval)]
  expect .rbrace "'}'"
  return .structLit structName fields

/-- Parse a type expression -/
partial def parseType : LeanParser LeanType := do
  let startLoc ← peekLoc
  let base ← parseTypeAtom
  -- Check for type application: Name ArgType
  -- Only consume next ident if on the same line (to avoid eating structure fields)
  let mut result := base
  let mut continue_ := true
  while continue_ do
    let nextLoc ← peekLoc
    let tok := nextLoc.token
    match tok with
    | .ident _ | .lparen =>
      -- Only apply if on the same line as the type started
      if nextLoc.line == startLoc.line then
        match result with
        | .name _ | .app _ _ =>
          let arg ← parseTypeAtom
          result := .app result arg
        | _ => continue_ := false
      else continue_ := false
    | _ => continue_ := false
  -- Check for arrow
  let tok ← peek
  if tok == .rightArrow then
    let _ ← advance
    let cod ← parseType
    return .arrow result cod
  else
    return result

/-- Parse atomic type -/
partial def parseTypeAtom : LeanParser LeanType := do
  let tok ← peek
  match tok with
  | .ident name =>
    let _ ← advance
    -- Check for type application: only apply if next is ( or known type-forming ident
    let nextTok ← peek
    match nextTok with
    | .lparen =>
      let arg ← parseTypeAtom
      return .app (.name name) arg
    | _ => return .name name
  | .underscore =>
    let _ ← advance
    return .hole
  | .lparen =>
    let _ ← advance
    let t ← parseType
    expect .rparen "')'"
    return t
  | _ => throw s!"expected type, got {repr tok}"

/-- Parse a pattern -/
partial def parsePattern : LeanParser LeanPattern := do
  let tok ← peek
  match tok with
  | .underscore =>
    let _ ← advance
    return .wildcard
  | .nat n =>
    let _ ← advance
    return .lit (.natVal n)
  | .float f =>
    let _ ← advance
    return .lit (.float f)
  | .string s =>
    let _ ← advance
    return .lit (.string s)
  | .keyword "true" =>
    let _ ← advance
    return .lit (.bool true)
  | .keyword "false" =>
    let _ ← advance
    return .lit (.bool false)
  | .ident name =>
    let _ ← advance
    -- Check if this is a constructor with arguments
    let mut args : List LeanPattern := []
    let mut continue_ := true
    while continue_ do
      let nextTok ← peek
      match nextTok with
      | .ident _ | .underscore | .nat _ | .float _ | .string _ =>
        let arg ← parsePattern
        args := args ++ [arg]
      | .lparen =>
        let _ ← advance
        let arg ← parsePattern
        expect .rparen "')'"
        args := args ++ [arg]
      | .keyword "true" | .keyword "false" =>
        let arg ← parsePattern
        args := args ++ [arg]
      | _ => continue_ := false
    if args.isEmpty then
      -- Could be a variable or a nullary constructor
      -- Lowercase = variable, Uppercase = constructor
      if name.front.isUpper then return .constructor name []
      else return .var name
    else
      return .constructor name args
  | _ => throw s!"expected pattern, got {repr tok}"

end

-- ============================================================
-- Declaration parsing
-- ============================================================

/-- Parse def: def name params [: Type] := body -/
partial def parseDef : LeanParser LeanDecl := do
  let name ← expectIdent
  let mut params : List LeanParam := []
  -- Parse parameters until : or :=
  let mut done := false
  while !done do
    let tok ← peek
    match tok with
    | .colon | .colonEq => done := true
    | .ident pname =>
      let _ ← advance
      params := params ++ [{ name := pname }]
    | .lparen =>
      let _ ← advance
      let pname ← expectIdent
      let pty ← if ← eat .colon then
        let t ← parseType
        pure (some t)
      else pure none
      expect .rparen "')'"
      params := params ++ [{ name := pname, type := pty }]
    | _ => done := true
  -- Optional return type
  let retType ← if ← eat .colon then
    let t ← parseType
    pure (some t)
  else pure none
  expect .colonEq "':='"
  let body ← parseExpr 0
  return .def_ name params retType body

/-- Parse structure: structure Name [extends X, Y] where ... -/
partial def parseStructure : LeanParser LeanDecl := do
  let name ← expectIdent
  -- Optional extends
  let extends_ ← if ← eatKeyword "extends" then
    let mut parents : List String := []
    let first ← expectIdent
    parents := [first]
    while (← eat .comma) do
      let p ← expectIdent
      parents := parents ++ [p]
    pure parents
  else pure []
  expectKeyword "where"
  -- Parse fields
  let baseCol ← currentCol
  let mut fields : List (String × LeanType) := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol then
      continue_ := false
    else
      match tok with
      | .ident _ =>
        let fname ← expectIdent
        expect .colon "':'"
        let ftype ← parseType
        fields := fields ++ [(fname, ftype)]
      | _ => continue_ := false
  return .structure_ name extends_ fields

/-- Parse inductive: inductive Name [params] where | ctor ... -/
partial def parseInductive : LeanParser LeanDecl := do
  let name ← expectIdent
  -- Optional type parameters
  let mut params : List LeanParam := []
  let mut parsingParams := true
  while parsingParams do
    let tok ← peek
    match tok with
    | .lparen =>
      let _ ← advance
      let pname ← expectIdent
      let pty ← if ← eat .colon then
        let t ← parseType
        pure (some t)
      else pure none
      expect .rparen "')'"
      params := params ++ [{ name := pname, type := pty }]
    | _ => parsingParams := false
  expectKeyword "where"
  -- Parse constructors
  let baseCol ← currentCol
  let mut ctors : List (String × List LeanType) := []
  let mut continue_ := true
  while continue_ do
    let col ← currentCol
    let tok ← peek
    if tok == .eof || col < baseCol then
      continue_ := false
    else if tok == .pipe then
      let _ ← advance
      let cname ← expectIdent
      let mut ctypes : List LeanType := []
      let mut parsingTypes := true
      while parsingTypes do
        let nextTok ← peek
        match nextTok with
        | .lparen =>
          let _ ← advance
          let ty ← parseType
          expect .rparen "')'"
          ctypes := ctypes ++ [ty]
        | .ident _ =>
          let pos ← savePos
          let ty ← tryParse parseTypeAtom
          match ty with
          | some t => ctypes := ctypes ++ [t]
          | none => restorePos pos; parsingTypes := false
        | _ => parsingTypes := false
      ctors := ctors ++ [(cname, ctypes)]
    else
      continue_ := false
  return .inductive_ name params ctors

/-- Parse a top-level declaration -/
partial def parseDecl : LeanParser LeanDecl := do
  let tok ← peek
  match tok with
  | .keyword "def" =>
    let _ ← advance
    parseDef
  | .keyword "let" =>
    let _ ← advance
    let name ← expectIdent
    let ty ← if ← eat .colon then
      let t ← parseType
      pure (some t)
    else pure none
    expect .colonEq "':='"
    let value ← parseExpr 0
    return .let_ name ty value
  | .keyword "structure" =>
    let _ ← advance
    parseStructure
  | .keyword "inductive" =>
    let _ ← advance
    parseInductive
  | .keyword "open" =>
    let _ ← advance
    let name ← expectIdent
    return .open_ name
  | .keyword "import" =>
    let _ ← advance
    let name ← expectIdent
    return .import_ name
  | _ => throw s!"expected declaration, got {repr tok}"

-- ============================================================
-- Module-level entry point
-- ============================================================

/-- Parse a Lean module from tokens -/
partial def parseModuleFromTokens : LeanParser LeanModule := do
  let mut decls : List LeanDecl := []
  let mut opens : List String := []
  let mut imports : List String := []
  let mut continue_ := true
  while continue_ do
    let tok ← peek
    match tok with
    | .eof => continue_ := false
    | .keyword "open" =>
      let _ ← advance
      let name ← expectIdent
      opens := opens ++ [name]
    | .keyword "import" =>
      let _ ← advance
      let name ← expectIdent
      imports := imports ++ [name]
    | _ =>
      let decl ← parseDecl
      decls := decls ++ [decl]
  return { header := imports.map (s!"import {·}"), opens, decls }

/-- Parse a Lean module from source string -/
def parseModule (input : String) : Except String LeanModule := do
  let tokens ← Lexer.tokenize input
  let state : ParserState := { tokens, pos := 0 }
  let (result, _) ← parseModuleFromTokens state
  return result

end LeanJS.Lean.Parser
