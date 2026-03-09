/-
  Lean 4 Token Types

  Token type with position info for indentation-sensitive parsing.
-/

namespace LeanJS.Lean

/-- Lean token type -/
inductive LeanToken where
  -- Literals
  | nat (value : Nat)
  | float (value : Float)
  | string (value : String)
  -- Identifiers and keywords
  | ident (name : String)
  | keyword (name : String)
  -- Delimiters
  | lparen | rparen       -- ( )
  | lbrace | rbrace       -- { }
  | lbracket | rbracket   -- [ ]
  | hashBracket           -- #[
  -- Punctuation
  | colon        -- :
  | colonEq      -- :=
  | dot          -- .
  | comma        -- ,
  | pipe         -- |
  | underscore   -- _
  | fatArrow     -- =>
  | leftArrow    -- ← or <-
  | rightArrow   -- → or ->
  | excl         -- !
  -- Operators
  | plus | minus | star | slash | percent | caret
  | eq2          -- ==
  | neq          -- !=
  | lt | gt | ltEq | gtEq
  | ampersand2   -- &&
  | pipe2        -- ||
  | plusPlus     -- ++
  | ampersand3   -- &&&
  | pipe3        -- |||
  | caret3       -- ^^^
  | ltLtLt       -- <<<
  | gtGtGt       -- >>>
  | tilde3       -- ~~~
  -- Special
  | eof
  deriving Repr, BEq, Inhabited

/-- Token with source location (line/col for indentation tracking) -/
structure LocatedToken where
  token : LeanToken
  line : Nat
  col : Nat
  deriving Repr, Inhabited

/-- Lean keywords -/
def leanKeywords : List String :=
  ["def", "let", "fun", "if", "then", "else", "match", "with", "do",
   "return", "where", "structure", "inductive", "open", "import",
   "for", "in", "while", "try", "catch", "finally", "throw",
   "true", "false", "mut"]

end LeanJS.Lean
