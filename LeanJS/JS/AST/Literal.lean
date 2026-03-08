namespace LeanJS.JS

inductive Literal where
  | string (value : String)
  | number (value : Float)
  | bool (value : Bool)
  | null
  | undefined
  | regex (pattern : String) (flags : String)
  deriving Repr, BEq, Inhabited

end LeanJS.JS
