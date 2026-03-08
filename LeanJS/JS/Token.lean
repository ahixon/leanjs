namespace LeanJS.JS

inductive Token where
  -- Literals
  | number (value : Float)
  | string (value : String)
  | regex (pattern : String) (flags : String)
  | template (raw : String) (tail : Bool)
  -- Identifiers and keywords
  | ident (name : String)
  | keyword (name : String)
  -- Punctuation
  | lparen | rparen | lbrace | rbrace | lbracket | rbracket
  | semi | comma | dot | ellipsis
  | colon | question | questionDot
  | arrow  -- =>
  -- Operators
  | plus | minus | star | starStar | slash | percent
  | ampersand | pipe | caret | tilde
  | excl | excl2  -- ! !!
  | lt | gt | ltEq | gtEq
  | eq2 | eq3 | neq | neq2
  | ltLt | gtGt | gtGtGt
  | ampersand2 | pipe2 | questionQuestion
  | assign | plusAssign | minusAssign | starAssign | slashAssign
  | percentAssign | starStarAssign
  | ltLtAssign | gtGtAssign | gtGtGtAssign
  | ampersandAssign | pipeAssign | caretAssign
  | ampersand2Assign | pipe2Assign | questionQuestionAssign
  | plusPlus | minusMinus
  -- Special
  | eof
  deriving Repr, BEq, Inhabited

def Token.isAssignOp : Token → Bool
  | .assign | .plusAssign | .minusAssign | .starAssign | .slashAssign
  | .percentAssign | .starStarAssign | .ltLtAssign | .gtGtAssign | .gtGtGtAssign
  | .ampersandAssign | .pipeAssign | .caretAssign
  | .ampersand2Assign | .pipe2Assign | .questionQuestionAssign => true
  | _ => false

end LeanJS.JS
