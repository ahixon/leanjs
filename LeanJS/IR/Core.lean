/-
  LeanJS Intermediate Representation (IR)

  Hub architecture: both JS→Lean and Lean→JS go through this shared typed IR.
  Gradual type system: `IRType.any` for untyped JS, concrete types for Lean-origin code.
  Key features vs JS AST:
  - Explicit mutation: `ref`/`deref`/`assign` instead of mutable variables
  - Explicit closures: `lam` with capture lists
  - Explicit records: named fields instead of JS object semantics
  - No statement/expression distinction: everything is an expression
-/

namespace LeanJS.IR

/-- IR types — gradual type system -/
inductive IRType where
  | any                                          -- untyped (JS default)
  | number                                       -- IEEE 754 float
  | string
  | bool
  | unit                                         -- void/undefined
  | func (params : List IRType) (ret : IRType)   -- function type
  | record (fields : List (String × IRType))     -- named record
  | array (elem : IRType)                        -- homogeneous array
  | ref (inner : IRType)                         -- mutable reference
  | option (inner : IRType)                      -- nullable
  | union (tag : String) (variants : List (String × List IRType))  -- tagged union
  deriving Inhabited

/-- IR literals -/
inductive IRLit where
  | number (value : Float)
  | string (value : String)
  | bool (value : Bool)
  | unit
  deriving Repr, BEq, Inhabited

/-- IR binary operators -/
inductive IRBinOp where
  -- Arithmetic
  | add | sub | mul | div | mod | exp
  -- Comparison
  | eq | neq | lt | lte | gt | gte
  -- Logical
  | and | or
  -- Bitwise
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  -- String
  | strConcat
  deriving Repr, BEq, Inhabited

/-- IR unary operators -/
inductive IRUnaryOp where
  | neg | not | bitNot | typeof
  deriving Repr, BEq, Inhabited

/-- Capture mode for closures -/
inductive CaptureMode where
  | byValue   -- immutable capture (const)
  | byRef     -- mutable capture (let/var)
  deriving Repr, BEq, Inhabited

/-- A captured variable -/
structure Capture where
  name : String
  mode : CaptureMode
  type : IRType
  deriving Inhabited

mutual
/-- IR expressions — the core calculus -/

inductive IRExpr where
  | lit (value : IRLit)
  | var (name : String)
  | «let» (name : String) (type : IRType) (value : IRExpr) (body : IRExpr)
  | lam (name : Option String) (params : List (String × IRType))
      (captures : List Capture) (body : IRExpr)
  | app (func : IRExpr) (args : List IRExpr)
  | binOp (op : IRBinOp) (left : IRExpr) (right : IRExpr)
  | unaryOp (op : IRUnaryOp) (arg : IRExpr)
  -- Mutation
  | mkRef (value : IRExpr)            -- create mutable ref
  | deref (ref : IRExpr)              -- read from ref
  | assign (ref : IRExpr) (value : IRExpr)  -- write to ref
  -- Records/objects
  | record (fields : List (String × IRExpr))
  | project (expr : IRExpr) (field : String)
  | projectIdx (expr : IRExpr) (idx : IRExpr)  -- computed access
  -- Arrays
  | array (elements : List IRExpr)
  | index (arr : IRExpr) (idx : IRExpr)
  -- Control flow
  | «if» (cond : IRExpr) (then_ : IRExpr) (else_ : IRExpr)
  | loop (cond : IRExpr) (body : IRExpr)          -- while loop
  | seq (exprs : List IRExpr)                     -- sequencing
  | «return» (value : IRExpr)
  | «break»
  | «continue»
  | throw (value : IRExpr)
  | tryCatch (body : IRExpr) (catchVar : Option String) (handler : IRExpr)
      (finalizer : Option IRExpr)
  -- Pattern matching (for Lean inductives)
  | «match» (scrutinee : IRExpr) (cases : List IRMatchCase)
  -- New/construction
  | construct (name : String) (args : List IRExpr)  -- constructor call
  | newObj (callee : IRExpr) (args : List IRExpr)   -- JS new
  -- Special
  | spread (expr : IRExpr)
  | ternary (cond : IRExpr) (then_ : IRExpr) (else_ : IRExpr)
  | undefined
  | this

inductive IRMatchCase where
  | mk (pattern : IRPattern) (body : IRExpr)

inductive IRPattern where
  | wildcard
  | var (name : String)
  | lit (value : IRLit)
  | constructor (tag : String) (bindings : List String)

end

/-- Top-level IR declarations -/
inductive IRDecl where
  | letDecl (name : String) (type : IRType) (value : IRExpr)
  | funcDecl (name : String) (params : List (String × IRType))
      (retType : IRType) (body : IRExpr)
  | typeDecl (name : String) (type : IRType)
  | classDecl (name : String) (parent : Option String)
      (fields : List (String × IRType))
      (methods : List (String × IRExpr))
  deriving Inhabited

/-- An IR module -/
structure IRModule where
  name : String := ""
  imports : List String := []
  decls : List IRDecl := []
  deriving Inhabited

-- Inhabited instances for mutual types
instance : Inhabited IRExpr := ⟨.undefined⟩
instance : Inhabited IRMatchCase := ⟨.mk .wildcard .undefined⟩
instance : Inhabited IRPattern := ⟨.wildcard⟩

end LeanJS.IR
