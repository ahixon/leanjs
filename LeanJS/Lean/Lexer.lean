/-
  Lean 4 Lexer

  Manual tokenizer (no Parsec) that walks String.Iterator and tracks line/col
  for indentation-sensitive parsing.
-/
import LeanJS.Lean.Token

namespace LeanJS.Lean.Lexer

open LeanJS.Lean

/-- Lexer state -/
structure LexState where
  it : String.Iterator
  line : Nat := 1
  col : Nat := 1
  deriving Inhabited

/-- Check if iterator has more characters -/
def LexState.hasNext (s : LexState) : Bool := s.it.hasNext

/-- Current character (assumes hasNext) -/
def LexState.curr (s : LexState) : Char := s.it.curr

/-- Advance iterator by one character, updating line/col -/
def LexState.advance (s : LexState) : LexState :=
  let c := s.it.curr
  let it' := s.it.next
  if c == '\n' then
    { it := it', line := s.line + 1, col := 1 }
  else
    { it := it', line := s.line, col := s.col + 1 }

/-- Skip whitespace and comments, updating line/col -/
partial def skipWsAndComments (s : LexState) : LexState :=
  if !s.hasNext then s
  else
    let c := s.curr
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
      skipWsAndComments s.advance
    else if c == '-' then
      let s1 := s.advance
      if s1.hasNext && s1.curr == '-' then
        -- Line comment: skip to end of line
        skipLineComment s1.advance
      else s  -- just a minus
    else if c == '/' then
      let s1 := s.advance
      if s1.hasNext && s1.curr == '-' then
        -- Block comment: /- ... -/
        skipBlockComment s1.advance 1
      else s  -- just a slash
    else s
where
  skipLineComment (s : LexState) : LexState :=
    if !s.hasNext then s
    else if s.curr == '\n' then skipWsAndComments s.advance
    else skipLineComment s.advance

  skipBlockComment (s : LexState) (depth : Nat) : LexState :=
    if depth == 0 then skipWsAndComments s
    else if !s.hasNext then s
    else
      let c := s.curr
      if c == '/' then
        let s1 := s.advance
        if s1.hasNext && s1.curr == '-' then
          skipBlockComment s1.advance (depth + 1)
        else skipBlockComment s1 depth
      else if c == '-' then
        let s1 := s.advance
        if s1.hasNext && s1.curr == '/' then
          skipBlockComment s1.advance (depth - 1)
        else skipBlockComment s1 depth
      else
        skipBlockComment s.advance depth

/-- Check if character can start an identifier -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Check if character can continue an identifier -/
def isIdentPart (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Read an identifier or keyword -/
partial def identOrKeyword (s : LexState) : LexState × LeanToken :=
  let rec go (s : LexState) (acc : String) : LexState × String :=
    if s.hasNext && isIdentPart s.curr then
      go s.advance (acc.push s.curr)
    else (s, acc)
  let (s', name) := go s.advance (s.curr.toString)
  if name ∈ leanKeywords then (s', .keyword name)
  else (s', .ident name)

/-- Read a guillemet-escaped identifier: «...» -/
partial def guillemetIdent (s : LexState) : Except String (LexState × LeanToken) :=
  -- s points past the opening «
  let rec go (s : LexState) (acc : String) : Except String (LexState × String) :=
    if !s.hasNext then .error "unterminated guillemet identifier"
    else if s.curr == '»' then .ok (s.advance, acc)
    else go s.advance (acc.push s.curr)
  do
    let (s', name) ← go s ""
    return (s', .ident name)

/-- Read a numeric literal -/
partial def numericLiteral (s : LexState) : LexState × LeanToken :=
  let rec readDigits (s : LexState) (acc : String) : LexState × String :=
    if s.hasNext && s.curr.isDigit then
      readDigits s.advance (acc.push s.curr)
    else (s, acc)
  let (s', intPart) := readDigits s ""
  -- Check for decimal point
  if s'.hasNext && s'.curr == '.' then
    let s'' := s'.advance
    if s''.hasNext && s''.curr.isDigit then
      let (s''', fracPart) := readDigits s'' ""
      let intVal := stringToNat intPart
      let fracVal := stringToNat fracPart
      let divisor := pow10 fracPart.length
      let f := Float.ofNat intVal + Float.ofNat fracVal / divisor
      (s''', .float f)
    else
      -- Just an integer followed by dot
      let n := stringToNat intPart
      (s', .nat n)
  else
    let n := stringToNat intPart
    (s', .nat n)
where
  stringToNat (s : String) : Nat :=
    s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  pow10 : Nat → Float
    | 0 => 1.0
    | n + 1 => 10.0 * pow10 n

/-- Read a string literal -/
partial def stringLiteral (s : LexState) : Except String (LexState × LeanToken) :=
  -- s points past the opening "
  let rec go (s : LexState) (acc : String) : Except String (LexState × String) :=
    if !s.hasNext then .error "unterminated string literal"
    else
      let c := s.curr
      if c == '"' then .ok (s.advance, acc)
      else if c == '\\' then
        let s1 := s.advance
        if !s1.hasNext then .error "unterminated escape sequence"
        else
          let esc := s1.curr
          let ch := match esc with
            | 'n' => '\n' | 't' => '\t' | 'r' => '\r'
            | '\\' => '\\' | '"' => '"' | '\'' => '\''
            | '0' => Char.ofNat 0
            | other => other
          go s1.advance (acc.push ch)
      else
        go s.advance (acc.push c)
  do
    let (s', str) ← go s ""
    return (s', .string str)

/-- Read a punctuator or operator -/
def punctuator (s : LexState) : Except String (LexState × LeanToken) :=
  let c := s.curr
  let s1 := s.advance
  match c with
  | '(' => .ok (s1, .lparen)
  | ')' => .ok (s1, .rparen)
  | '{' => .ok (s1, .lbrace)
  | '}' => .ok (s1, .rbrace)
  | '[' => .ok (s1, .lbracket)
  | ']' => .ok (s1, .rbracket)
  | ',' => .ok (s1, .comma)
  | '_' =>
    -- Check if followed by ident part (then it's start of identifier)
    if s1.hasNext && isIdentPart s1.curr then
      .ok (identOrKeyword s)
    else
      .ok (s1, .underscore)
  | '|' =>
    if s1.hasNext then
      match s1.curr with
      | '|' =>
        let s2 := s1.advance
        if s2.hasNext && s2.curr == '|' then .ok (s2.advance, .pipe3)
        else .ok (s2, .pipe2)
      | _ => .ok (s1, .pipe)
    else .ok (s1, .pipe)
  | ':' =>
    if s1.hasNext && s1.curr == '=' then .ok (s1.advance, .colonEq)
    else .ok (s1, .colon)
  | '.' => .ok (s1, .dot)
  | '!' =>
    if s1.hasNext && s1.curr == '=' then .ok (s1.advance, .neq)
    else .ok (s1, .excl)
  | '=' =>
    if s1.hasNext then
      match s1.curr with
      | '=' => .ok (s1.advance, .eq2)
      | '>' => .ok (s1.advance, .fatArrow)
      | _ => .error s!"unexpected '=' at {s.line}:{s.col}"
    else .error s!"unexpected '=' at end of input"
  | '+' =>
    if s1.hasNext && s1.curr == '+' then .ok (s1.advance, .plusPlus)
    else .ok (s1, .plus)
  | '-' =>
    if s1.hasNext then
      match s1.curr with
      | '>' => .ok (s1.advance, .rightArrow)
      | _ => .ok (s1, .minus)
    else .ok (s1, .minus)
  | '*' => .ok (s1, .star)
  | '/' => .ok (s1, .slash)
  | '%' => .ok (s1, .percent)
  | '^' =>
    if s1.hasNext && s1.curr == '^' then
      let s2 := s1.advance
      if s2.hasNext && s2.curr == '^' then .ok (s2.advance, .caret3)
      else .ok (s1, .caret)  -- just one ^
    else .ok (s1, .caret)
  | '<' =>
    if s1.hasNext then
      match s1.curr with
      | '-' => .ok (s1.advance, .leftArrow)
      | '=' => .ok (s1.advance, .ltEq)
      | '<' =>
        let s2 := s1.advance
        if s2.hasNext && s2.curr == '<' then .ok (s2.advance, .ltLtLt)
        else .ok (s1, .lt)  -- just <
      | _ => .ok (s1, .lt)
    else .ok (s1, .lt)
  | '>' =>
    if s1.hasNext then
      match s1.curr with
      | '=' => .ok (s1.advance, .gtEq)
      | '>' =>
        let s2 := s1.advance
        if s2.hasNext && s2.curr == '>' then .ok (s2.advance, .gtGtGt)
        else .ok (s1, .gt)  -- just >
      | _ => .ok (s1, .gt)
    else .ok (s1, .gt)
  | '&' =>
    if s1.hasNext && s1.curr == '&' then
      let s2 := s1.advance
      if s2.hasNext && s2.curr == '&' then .ok (s2.advance, .ampersand3)
      else .ok (s2, .ampersand2)
    else .error s!"unexpected '&' at {s.line}:{s.col}"
  | '~' =>
    if s1.hasNext && s1.curr == '~' then
      let s2 := s1.advance
      if s2.hasNext && s2.curr == '~' then .ok (s2.advance, .tilde3)
      else .error s!"unexpected '~~' at {s.line}:{s.col}"
    else .error s!"unexpected '~' at {s.line}:{s.col}"
  | '←' => .ok (s1, .leftArrow)
  | '→' => .ok (s1, .rightArrow)
  | '#' =>
    if s1.hasNext && s1.curr == '[' then .ok (s1.advance, .hashBracket)
    else .error s!"unexpected '#' at {s.line}:{s.col}"
  | _ => .error s!"unexpected character '{c}' at {s.line}:{s.col}"

/-- Tokenize an entire Lean source string -/
partial def tokenize (input : String) : Except String (Array LocatedToken) := do
  let mut s : LexState := { it := input.mkIterator }
  let mut tokens : Array LocatedToken := #[]

  -- Main tokenization loop
  let mut done := false
  while !done do
    s := skipWsAndComments s
    let line := s.line
    let col := s.col

    if !s.hasNext then
      tokens := tokens.push { token := .eof, line, col }
      done := true
    else
      let c := s.curr
      if c.isDigit then
        let (s', tok) := numericLiteral s
        tokens := tokens.push { token := tok, line, col }
        s := s'
      else if isIdentStart c then
        let (s', tok) := identOrKeyword s
        tokens := tokens.push { token := tok, line, col }
        s := s'
      else if c == '"' then
        let (s', tok) ← stringLiteral s.advance
        tokens := tokens.push { token := tok, line, col }
        s := s'
      else if c == '«' then
        let (s', tok) ← guillemetIdent s.advance
        tokens := tokens.push { token := tok, line, col }
        s := s'
      else
        -- Check for -- comment that wasn't caught (shouldn't happen but defensive)
        if c == '-' && s.advance.hasNext && s.advance.curr == '-' then
          s := skipWsAndComments s
        else
          let (s', tok) ← punctuator s
          tokens := tokens.push { token := tok, line, col }
          s := s'

  return tokens

end LeanJS.Lean.Lexer
