namespace LeanJS.JS

structure SourcePos where
  line : Nat
  column : Nat
  offset : Nat
  deriving Repr, BEq, Inhabited

structure SourceSpan where
  start : SourcePos
  stop : SourcePos
  deriving Repr, BEq, Inhabited

structure Located (α : Type) where
  span : Option SourceSpan := none
  val : α
  deriving Repr, Inhabited

def Ident := String
  deriving Repr, BEq, Inhabited, Hashable, DecidableEq, ToString

end LeanJS.JS
