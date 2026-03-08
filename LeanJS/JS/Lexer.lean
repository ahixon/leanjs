import Std.Internal.Parsec
import Std.Internal.Parsec.String
import LeanJS.JS.Token
import LeanJS.JS.AST

namespace LeanJS.JS.Lexer

open Std.Internal.Parsec Std.Internal.Parsec.String

/-- Skip whitespace and comments -/
partial def skipWsAndComments : Parser Unit := do
  ws
  let c ← peek?
  match c with
  | some '/' =>
    let it ← fun i => .success i i  -- get current iterator
    let next := it.next
    if next.hasNext then
      match next.curr with
      | '/' =>
        -- line comment
        skip; skip  -- consume //
        let _ ← manyChars (satisfy (· != '\n'))
        skipWsAndComments
      | '*' =>
        -- block comment
        skip; skip  -- consume /*
        skipBlockComment
        skipWsAndComments
      | _ => pure ()
    else pure ()
  | _ => pure ()
where
  skipBlockComment : Parser Unit := do
    let c ← any
    if c == '*' then
      let c2 ← peek?
      if c2 == some '/' then skip  -- consume /
      else skipBlockComment
    else skipBlockComment

/-- Check if character is a JS identifier start -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

/-- Check if character is a JS identifier part -/
def isIdentPart (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$'

def jsKeywords : List String :=
  ["break", "case", "catch", "continue", "debugger", "default", "delete",
   "do", "else", "export", "extends", "finally", "for", "function", "if",
   "import", "in", "instanceof", "new", "return", "super", "switch",
   "this", "throw", "try", "typeof", "var", "void", "while", "with",
   "yield", "let", "const", "class", "async", "await", "of",
   "true", "false", "null", "undefined"]

/-- Parse an identifier or keyword -/
def identOrKeyword : Parser Token := do
  let first ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentPart)
  let name := first.toString ++ rest
  if name ∈ jsKeywords then
    return .keyword name
  else
    return .ident name

/-- Parse a numeric literal -/
partial def numericLiteral : Parser Token := do
  let c ← peek!
  if c == '0' then
    skip
    let next ← peek?
    match next with
    | some 'x' | some 'X' =>
      skip
      let digits ← many1Chars (satisfy fun c => c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F'))
      let val := hexToFloat digits
      return .number val
    | some 'o' | some 'O' =>
      skip
      let digits ← many1Chars (satisfy fun c => '0' ≤ c ∧ c ≤ '7')
      let val := octToFloat digits
      return .number val
    | some 'b' | some 'B' =>
      skip
      let digits ← many1Chars (satisfy fun c => c == '0' || c == '1')
      let val := binToFloat digits
      return .number val
    | _ =>
      let rest ← manyChars (satisfy Char.isDigit)
      let s := "0" ++ rest
      parseDecimalPart s
  else
    let digits ← many1Chars (satisfy Char.isDigit)
    parseDecimalPart digits
where
  parseDecimalPart (intPart : String) : Parser Token := do
    let intVal := stringToNat intPart
    let c ← peek?
    let (fracVal, fracDigits) ← match c with
    | some '.' =>
      skip
      let frac ← manyChars (satisfy Char.isDigit)
      pure (stringToNat frac, frac.length)
    | _ => pure (0, 0)
    let c2 ← peek?
    let expVal ← match c2 with
    | some 'e' | some 'E' =>
      skip
      let sign ← peek?
      let negative ← match sign with
        | some '+' => skip; pure false
        | some '-' => skip; pure true
        | _ => pure false
      let exp ← many1Chars (satisfy Char.isDigit)
      let e := stringToNat exp
      pure (if negative then -(Int.ofNat e) else Int.ofNat e)
    | _ => pure (0 : Int)
    let base := Float.ofNat intVal +
      Float.ofNat fracVal / pow10 fracDigits
    let result := base * floatPow10 expVal
    return .number result

  stringToNat (s : String) : Nat :=
    s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

  pow10 (n : Nat) : Float :=
    match n with
    | 0 => 1.0
    | n + 1 => 10.0 * pow10 n

  floatPow10 (n : Int) : Float :=
    match n with
    | .ofNat k => pow10 k
    | .negSucc k => 1.0 / pow10 (k + 1)

  hexToFloat (s : String) : Float :=
    let val := s.foldl (fun acc c =>
      let d := if c.isDigit then c.toNat - '0'.toNat
               else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
               else c.toNat - 'A'.toNat + 10
      acc * 16 + d) 0
    Float.ofNat val

  octToFloat (s : String) : Float :=
    let val := s.foldl (fun acc c => acc * 8 + (c.toNat - '0'.toNat)) 0
    Float.ofNat val

  binToFloat (s : String) : Float :=
    let val := s.foldl (fun acc c => acc * 2 + (c.toNat - '0'.toNat)) 0
    Float.ofNat val

/-- Parse a string literal -/
def stringLiteral : Parser Token := do
  let quote ← satisfy (fun c => c == '"' || c == '\'')
  let s ← stringBody quote
  return .string s
where
  stringBody (quote : Char) : Parser String := do
    let mut result := ""
    repeat do
      let c ← any
      if c == quote then return result
      else if c == '\\' then
        let esc ← any
        let escaped ← match esc with
          | 'n' => pure '\n'
          | 't' => pure '\t'
          | 'r' => pure '\r'
          | '\\' => pure '\\'
          | '\'' => pure '\''
          | '"' => pure '"'
          | '0' => pure (Char.ofNat 0)
          | _ => pure esc
        result := result.push escaped
      else
        result := result.push c
    fail "unterminated string"

/-- Parse a punctuator or operator token -/
def punctuator : Parser Token := do
  let c ← any
  match c with
  | '(' => return .lparen
  | ')' => return .rparen
  | '{' => return .lbrace
  | '}' => return .rbrace
  | '[' => return .lbracket
  | ']' => return .rbracket
  | ';' => return .semi
  | ',' => return .comma
  | '~' => return .tilde
  | ':' => return .colon
  | '.' =>
    let c2 ← peek?
    match c2 with
    | some '.' =>
      skip
      let c3 ← peek?
      if c3 == some '.' then
        skip; return .ellipsis
      else fail "expected ..."
    | _ => return .dot
  | '?' =>
    let c2 ← peek?
    match c2 with
    | some '?' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .questionQuestionAssign
      else return .questionQuestion
    | some '.' => skip; return .questionDot
    | _ => return .question
  | '=' =>
    let c2 ← peek?
    match c2 with
    | some '=' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .eq3
      else return .eq2
    | some '>' => skip; return .arrow
    | _ => return .assign
  | '!' =>
    let c2 ← peek?
    match c2 with
    | some '=' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .neq2
      else return .neq
    | _ => return .excl
  | '<' =>
    let c2 ← peek?
    match c2 with
    | some '<' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .ltLtAssign
      else return .ltLt
    | some '=' => skip; return .ltEq
    | _ => return .lt
  | '>' =>
    let c2 ← peek?
    match c2 with
    | some '>' =>
      skip
      let c3 ← peek?
      match c3 with
      | some '>' =>
        skip
        let c4 ← peek?
        if c4 == some '=' then do skip; return .gtGtGtAssign
        else return .gtGtGt
      | some '=' => skip; return .gtGtAssign
      | _ => return .gtGt
    | some '=' => skip; return .gtEq
    | _ => return .gt
  | '+' =>
    let c2 ← peek?
    match c2 with
    | some '+' => skip; return .plusPlus
    | some '=' => skip; return .plusAssign
    | _ => return .plus
  | '-' =>
    let c2 ← peek?
    match c2 with
    | some '-' => skip; return .minusMinus
    | some '=' => skip; return .minusAssign
    | _ => return .minus
  | '*' =>
    let c2 ← peek?
    match c2 with
    | some '*' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .starStarAssign
      else return .starStar
    | some '=' => skip; return .starAssign
    | _ => return .star
  | '/' =>
    let c2 ← peek?
    match c2 with
    | some '=' => skip; return .slashAssign
    | _ => return .slash
  | '%' =>
    let c2 ← peek?
    match c2 with
    | some '=' => skip; return .percentAssign
    | _ => return .percent
  | '&' =>
    let c2 ← peek?
    match c2 with
    | some '&' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .ampersand2Assign
      else return .ampersand2
    | some '=' => skip; return .ampersandAssign
    | _ => return .ampersand
  | '|' =>
    let c2 ← peek?
    match c2 with
    | some '|' =>
      skip
      let c3 ← peek?
      if c3 == some '=' then do skip; return .pipe2Assign
      else return .pipe2
    | some '=' => skip; return .pipeAssign
    | _ => return .pipe
  | '^' =>
    let c2 ← peek?
    match c2 with
    | some '=' => skip; return .caretAssign
    | _ => return .caret
  | _ => fail s!"unexpected character: {c}"

/-- Lex a single token -/
def nextToken : Parser Token := do
  skipWsAndComments
  let c ← peek?
  match c with
  | none => return .eof
  | some c =>
    if isIdentStart c then identOrKeyword
    else if c.isDigit then numericLiteral
    else if c == '"' || c == '\'' then stringLiteral
    else punctuator

/-- Tokenize an entire input string -/
partial def tokenize (input : String) : Except String (Array Token) := do
  let rec go (it : String.Iterator) (tokens : Array Token) : Except String (Array Token) :=
    match nextToken it with
    | .success it' tok =>
      match tok with
      | .eof => .ok (tokens.push tok)
      | _ => go it' (tokens.push tok)
    | .error it' err => .error s!"Lex error at offset {it'.pos}: {err}"
  go input.mkIterator #[]

end LeanJS.JS.Lexer
