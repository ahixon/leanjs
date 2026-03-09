/-
  Lean 4 Surface Syntax AST

  Minimal types covering the Lean 4 subset that IR can target.
  Used for IR→Lean translation and (future) Lean parsing.
-/

namespace LeanJS.Lean

/-- Lean literals -/
inductive LeanLit where
  | natVal (n : Nat)
  | float (f : Float)
  | string (s : String)
  | bool (b : Bool)
  deriving Inhabited

/-- Lean type expressions -/
inductive LeanType where
  | name (n : String)
  | app (fn : LeanType) (arg : LeanType)
  | arrow (dom : LeanType) (cod : LeanType)
  | product (types : List LeanType)
  | hole
  deriving Inhabited

/-- Lean parameter (name + optional type) -/
structure LeanParam where
  name : String
  type : Option LeanType := none
  deriving Inhabited

set_option maxHeartbeats 800000

mutual

/-- Lean expressions -/
inductive LeanExpr where
  | ident (name : String)
  | lit (value : LeanLit)
  | app (fn : LeanExpr) (arg : LeanExpr)
  | lam (params : List LeanParam) (body : LeanExpr)
  | «let» (name : String) (type : Option LeanType) (value : LeanExpr) (body : LeanExpr)
  | bind (name : String) (type : Option LeanType) (value : LeanExpr)
  | doBlock (elems : List LeanDoElem)
  | «if» (cond : LeanExpr) (then_ : LeanExpr) (else_ : Option LeanExpr)
  | «match» (scrutinee : LeanExpr) (alts : List LeanMatchAlt)
  | «while» (cond : LeanExpr) (body : LeanExpr)
  | «for» (var : String) (iter : LeanExpr) (body : LeanExpr)
  | «return» (value : LeanExpr)
  | structLit (name : Option String) (fields : List (String × LeanExpr))
  | arrayLit (elements : List LeanExpr)
  | arrayIdx (arr : LeanExpr) (idx : LeanExpr)
  | proj (expr : LeanExpr) (field : String)
  | binOp (op : String) (left : LeanExpr) (right : LeanExpr)
  | unaryOp (op : String) (arg : LeanExpr)
  | refNew (value : LeanExpr)
  | refGet (ref : LeanExpr)
  | refSet (ref : LeanExpr) (value : LeanExpr)
  | «try» (body : LeanExpr) (catchVar : Option String) (handler : Option LeanExpr)
        (finalizer : Option LeanExpr)
  | «throw» (value : LeanExpr)
  | paren (inner : LeanExpr)
  | unit
  | hole

/-- Do-block elements -/
inductive LeanDoElem where
  | eval (expr : LeanExpr)
  | bind (name : String) (type : Option LeanType) (value : LeanExpr)
  | letDecl (name : String) (type : Option LeanType) (value : LeanExpr)
  | mutDecl (name : String) (type : Option LeanType) (value : LeanExpr)
  | reassign (name : String) (value : LeanExpr)
  | doReturn (value : LeanExpr)
  | doIf (cond : LeanExpr) (then_ : List LeanDoElem) (else_ : List LeanDoElem)
  | doWhile (cond : LeanExpr) (body : List LeanDoElem)
  | doFor (var : String) (iter : LeanExpr) (body : List LeanDoElem)
  | doTry (body : List LeanDoElem) (catchVar : Option String)
      (handler : List LeanDoElem) (finalizer : List LeanDoElem)

/-- Match alternatives -/
inductive LeanMatchAlt where
  | mk (pattern : LeanPattern) (body : LeanExpr)

/-- Patterns -/
inductive LeanPattern where
  | wildcard
  | var (name : String)
  | lit (value : LeanLit)
  | constructor (name : String) (args : List LeanPattern)

end

-- Inhabited instances for mutual types
instance : Inhabited LeanExpr := ⟨.unit⟩
instance : Inhabited LeanDoElem := ⟨.eval .unit⟩
instance : Inhabited LeanMatchAlt := ⟨.mk .wildcard .unit⟩
instance : Inhabited LeanPattern := ⟨.wildcard⟩

/-- Top-level Lean declarations -/
inductive LeanDecl where
  | def_ (name : String) (params : List LeanParam) (retType : Option LeanType)
      (body : LeanExpr)
  | let_ (name : String) (type : Option LeanType) (value : LeanExpr)
  | structure_ (name : String) (extends_ : List String)
      (fields : List (String × LeanType))
  | inductive_ (name : String) (params : List LeanParam)
      (ctors : List (String × List LeanType))
  | open_ (name : String)
  | import_ (name : String)
  deriving Inhabited

/-- A Lean module -/
structure LeanModule where
  header : List String := []
  opens : List String := []
  decls : List LeanDecl := []
  deriving Inhabited

end LeanJS.Lean
