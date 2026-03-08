namespace LeanJS.JS

inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | lte | gt | gte
  | and | or
  | bitAnd | bitOr | bitXor
  | shl | shr | ushr
  | nullishCoalesce
  | «in» | «instanceof»
  deriving Repr, BEq, Inhabited, DecidableEq

inductive UnaryOp where
  | neg | pos | not | bitNot
  | typeof | void | delete
  deriving Repr, BEq, Inhabited, DecidableEq

inductive UpdateOp where
  | inc | dec
  deriving Repr, BEq, Inhabited, DecidableEq

inductive AssignOp where
  | assign
  | addAssign | subAssign | mulAssign | divAssign | modAssign | expAssign
  | andAssign | orAssign | nullishAssign
  | bitAndAssign | bitOrAssign | bitXorAssign
  | shlAssign | shrAssign | ushrAssign
  deriving Repr, BEq, Inhabited, DecidableEq

end LeanJS.JS
