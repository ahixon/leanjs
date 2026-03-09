import LeanJS.JS.AST.Common
import LeanJS.JS.AST.Operator
import LeanJS.JS.AST.Literal

set_option maxHeartbeats 1600000

namespace LeanJS.JS

inductive VarKind where
  | var | «let» | «const»
  deriving Repr, BEq, Inhabited

inductive PropKind where
  | init | get | set
  deriving Repr, BEq, Inhabited

inductive MethodKind where
  | method | get | set
  deriving Repr, BEq, Inhabited

-- Non-recursive types defined outside mutual block
inductive ImportSpecifier where
  | default_ (localName : Ident)
  | named (imported : Ident) (localName : Ident)
  | namespace (localName : Ident)
  deriving Repr, BEq, Inhabited

inductive ExportSpecifier where
  | mk (localName : Ident) (exported : Ident)
  deriving Repr, BEq, Inhabited

-- All mutually recursive types
mutual

inductive Expr where
  | ident (name : Ident)
  | literal (lit : Literal)
  | this
  | array (elements : List (Option Expr))
  | object (properties : List Property)
  | function (name : Option Ident) (params : List Pattern) (body : List Stmt)
      (async_ : Bool) (generator : Bool)
  | arrowFunction (params : List Pattern) (body : ExprOrBlock) (async_ : Bool)
  | unary (op : UnaryOp) (argument : Expr)
  | update (op : UpdateOp) (argument : Expr) (prefix_ : Bool)
  | binary (op : BinOp) (left : Expr) (right : Expr)
  | assign (op : AssignOp) (left : AssignTarget) (right : Expr)
  | conditional (test : Expr) (consequent : Expr) (alternate : Expr)
  | call (callee : Expr) (arguments : List Expr)
  | «new» (callee : Expr) (arguments : List Expr)
  | member (object : Expr) (property : MemberProp)
  | sequence (expressions : List Expr)
  | template (tag : Option Expr) (quasis : List String) (expressions : List Expr)
  | spread (argument : Expr)
  | paren (expr : Expr)
  | await (argument : Expr)
  | yield (argument : Option Expr) (delegate : Bool)

inductive Stmt where
  | expr (expression : Expr)
  | block (body : List Stmt)
  | empty
  | return_ (argument : Option Expr)
  | throw (argument : Expr)
  | break_ (label : Option Ident)
  | continue_ (label : Option Ident)
  | ifStmt (test : Expr) (consequent : Stmt) (alternate : Option Stmt)
  | while_ (test : Expr) (body : Stmt)
  | doWhile (body : Stmt) (test : Expr)
  | for_ (init : Option ForInit) (test : Option Expr) (update : Option Expr) (body : Stmt)
  | forIn (left : ForInit) (right : Expr) (body : Stmt)
  | forOf (left : ForInit) (right : Expr) (body : Stmt)
  | switch (discriminant : Expr) (cases : List SwitchCase)
  | try_ (block_ : List Stmt) (handler : Option CatchClause) (finalizer : Option (List Stmt))
  | labeled (label : Ident) (body : Stmt)
  | debugger
  | varDecl (kind : VarKind) (declarations : List VarDeclarator)
  | funcDecl (name : Ident) (params : List Pattern) (body : List Stmt)
      (async : Bool) (generator : Bool)
  | classDecl (name : Ident) (superClass : Option Expr) (body : List ClassMember)
  | importDecl (specifiers : List ImportSpecifier) (source : String)
  | exportNamed (declaration : Option Stmt) (specifiers : List ExportSpecifier)
      (source : Option String)
  | exportDefault (declaration : Stmt)
  | exportAll (source : String)

inductive Pattern where
  | ident (name : Ident) (default_ : Option Expr)
  | array (elements : List (Option Pattern)) (rest : Option Pattern)
  | object (properties : List PatternProp) (rest : Option Pattern)
  | assign (left : Pattern) (right : Expr)

inductive Property where
  | prop (key : Expr) (value : Expr) (kind : PropKind)
      (computed : Bool) (shorthand : Bool)
  | method (key : Expr) (params : List Pattern) (body : List Stmt)
      (kind : MethodKind) (computed : Bool) (async : Bool) (generator : Bool)

inductive MemberProp where
  | ident (name : Ident)
  | computed (expr : Expr)

inductive AssignTarget where
  | expr (e : Expr)
  | pat (p : Pattern)

inductive ForInit where
  | varDecl (kind : VarKind) (decls : List VarDeclarator)
  | expr (e : Expr)

inductive ExprOrBlock where
  | expr (e : Expr)
  | block (stmts : List Stmt)

inductive VarDeclarator where
  | mk (id : Pattern) (init : Option Expr)

inductive SwitchCase where
  | mk (test : Option Expr) (consequent : List Stmt)

inductive CatchClause where
  | mk (param : Option Pattern) (body : List Stmt)

inductive ClassMember where
  | method (key : Expr) (params : List Pattern) (body : List Stmt)
      (kind : MethodKind) (static_ : Bool) (computed : Bool)
  | property (key : Expr) (value : Option Expr)
      (static_ : Bool) (computed : Bool)

inductive PatternProp where
  | keyVal (key : Expr) (value : Pattern) (computed : Bool)
  | shorthand (name : Ident) (default_ : Option Expr)

end

abbrev Program := List Stmt

-- Inhabited instances for mutual types (no mutual dependence in the values)
instance : Inhabited Expr := ⟨.literal .null⟩
instance : Inhabited Stmt := ⟨.empty⟩
instance : Inhabited Pattern := ⟨.ident "" none⟩
instance : Inhabited MemberProp := ⟨.ident ""⟩
instance : Inhabited AssignTarget := ⟨.expr (.literal .null)⟩
instance : Inhabited ForInit := ⟨.expr (.literal .null)⟩
instance : Inhabited ExprOrBlock := ⟨.expr (.literal .null)⟩
instance : Inhabited VarDeclarator := ⟨.mk (.ident "" none) none⟩
instance : Inhabited SwitchCase := ⟨.mk none []⟩
instance : Inhabited CatchClause := ⟨.mk none []⟩
instance : Inhabited Property := ⟨.prop (.literal .null) (.literal .null) .init false false⟩
instance : Inhabited ClassMember := ⟨.property (.literal .null) none false false⟩
instance : Inhabited PatternProp := ⟨.shorthand "" none⟩

end LeanJS.JS
