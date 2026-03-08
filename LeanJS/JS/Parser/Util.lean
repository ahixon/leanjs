import LeanJS.JS.Token
import LeanJS.JS.AST
import LeanJS.JS.Lexer

namespace LeanJS.JS.Parser

open Std.Internal.Parsec.String in
open Std.Internal.Parsec in
/-- Dummy to bring Parsec-related names into scope for the Lexer calls -/
private def _root_.LeanJS.JS.Lexer.runToken := @Lexer.nextToken

/-- Parser state tracking JS parsing context -/
structure ParserState where
  tokens : Array Token
  pos : Nat := 0
  hadNewlineBefore : Array Bool
  deriving Inhabited

/-- The JS parser monad -/
abbrev JSParser := StateT ParserState (Except String)

/-- Run a parser -/
def JSParser.run' {α : Type} (p : JSParser α) (s : ParserState) : Except String α :=
  match p.run s with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- Get current token without consuming -/
def peek : JSParser Token := do
  let s ← get
  if h : s.pos < s.tokens.size then
    return s.tokens[s.pos]
  else
    return .eof

/-- Consume current token and advance -/
def advance : JSParser Token := do
  let s ← get
  if h : s.pos < s.tokens.size then
    let tok := s.tokens[s.pos]
    set { s with pos := s.pos + 1 }
    return tok
  else
    return .eof

/-- Check if there was a newline before current token -/
def hadNewline : JSParser Bool := do
  let s ← get
  if h : s.pos < s.hadNewlineBefore.size then
    return s.hadNewlineBefore[s.pos]
  else
    return false

/-- Expect and consume a specific token -/
def expect (tok : Token) (msg : String := "") : JSParser Unit := do
  let t ← advance
  if t == tok then pure ()
  else throw s!"expected {msg}, got {repr t}"

/-- Expect a keyword -/
def expectKeyword (kw : String) : JSParser Unit := do
  let t ← advance
  match t with
  | .keyword k => if k == kw then pure () else throw s!"expected '{kw}', got keyword '{k}'"
  | _ => throw s!"expected keyword '{kw}', got {repr t}"

/-- Check if current token is a keyword -/
def isKeyword (kw : String) : JSParser Bool := do
  let t ← peek
  match t with
  | .keyword k => return k == kw
  | _ => return false

/-- Check if current token matches -/
def isToken (tok : Token) : JSParser Bool := do
  let t ← peek
  return t == tok

/-- Consume token if it matches, return whether consumed -/
def eat (tok : Token) : JSParser Bool := do
  let t ← peek
  if t == tok then
    let _ ← advance
    return true
  else
    return false

/-- Consume keyword if it matches -/
def eatKeyword (kw : String) : JSParser Bool := do
  if ← isKeyword kw then
    let _ ← advance
    return true
  else
    return false

/-- Expect a semicolon with ASI (Automatic Semicolon Insertion) -/
def semicolon : JSParser Unit := do
  let t ← peek
  match t with
  | .semi => let _ ← advance; pure ()
  | .rbrace => pure ()
  | .eof => pure ()
  | _ =>
    let nl ← hadNewline
    if nl then pure ()
    else throw s!"expected ';', got {repr t}"

/-- Expect and consume an identifier, return its name -/
def expectIdent : JSParser String := do
  let t ← advance
  match t with
  | .ident name => return name
  | .keyword name =>
    if name ∈ ["get", "set", "of", "async", "from", "as", "let", "static", "constructor"] then
      return name
    else
      throw s!"expected identifier, got keyword '{name}'"
  | _ => throw s!"expected identifier, got {repr t}"

/-- Save parser position for backtracking -/
def savePos : JSParser Nat := do
  let s ← get
  return s.pos

/-- Restore parser position -/
def restorePos (pos : Nat) : JSParser Unit := do
  let s ← get
  set { s with pos := pos }

/-- Try a parser, backtrack on failure -/
def tryParse {α : Type} (p : JSParser α) : JSParser (Option α) := do
  let pos ← savePos
  try
    let a ← p
    return some a
  catch _ =>
    restorePos pos
    return none

/-- Tokenize input string into ParserState -/
partial def tokenizeToState (input : String) : Except String ParserState := do
  let mut tokens : Array Token := #[]
  let mut newlines : Array Bool := #[]
  let mut it := input.mkIterator
  let mut hadNl := false
  while it.hasNext || tokens.isEmpty || tokens.back? != some .eof do
    -- Skip whitespace, track newlines
    let mut foundNl := hadNl
    let mut skipMore := true
    while skipMore do
      if it.hasNext then
        let c := it.curr
        if c == ' ' || c == '\t' || c == '\r' then
          it := it.next
        else if c == '\n' then
          foundNl := true
          it := it.next
        else if c == '/' && it.next.hasNext then
          let c2 := it.next.curr
          if c2 == '/' then
            -- Line comment
            it := it.next.next
            while it.hasNext && it.curr != '\n' do
              it := it.next
          else if c2 == '*' then
            -- Block comment
            it := it.next.next
            let mut inComment := true
            while inComment do
              if !it.hasNext then
                inComment := false
              else if it.curr == '*' && it.next.hasNext && it.next.curr == '/' then
                it := it.next.next
                inComment := false
              else
                if it.curr == '\n' then foundNl := true
                it := it.next
          else
            skipMore := false
        else
          skipMore := false
      else
        skipMore := false
    hadNl := foundNl

    if !it.hasNext then
      newlines := newlines.push hadNl
      tokens := tokens.push .eof
      break

    -- Lex one token
    match Lexer.nextToken it with
    | .success it' tok =>
      match tok with
      | .eof =>
        newlines := newlines.push hadNl
        tokens := tokens.push .eof
        break
      | _ =>
        newlines := newlines.push hadNl
        tokens := tokens.push tok
        hadNl := false
        it := it'
    | .error _it' err =>
      throw s!"Lex error: {err}"

  if tokens.isEmpty || tokens.back? != some .eof then
    newlines := newlines.push false
    tokens := tokens.push .eof

  return { tokens, pos := 0, hadNewlineBefore := newlines }

end LeanJS.JS.Parser
