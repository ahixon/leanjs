/-
  Translation relations for the verified core fragment (all four passes).

  These are the specifications that the simulation theorems are proved
  against. The executable translators in `LeanJS.Trans.Core` are total
  functions that return a proof of the relation alongside their output, so
  they are sound with respect to these relations by construction.

  Each relation is stateless: the core fragment has no mutation, so no
  mutated-variable / ref-variable bookkeeping is needed.
-/
import LeanJS.JS.AST
import LeanJS.Lean.AST
import LeanJS.IR.Core
import LeanJS.Semantics.JSEval
import LeanJS.Semantics.LeanEval

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR

/-! ## Operator / literal maps -/

def irBinOpToJS : IRBinOp → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .exp => some .exp
  | .eq => some .strictEq
  | .neq => some .strictNeq
  | .lt => some .lt
  | .lte => some .lte
  | .gt => some .gt
  | .gte => some .gte
  | .and => some .and
  | .or => some .or
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor
  | .shl => some .shl
  | .shr => some .shr
  | .ushr => some .ushr
  | .strConcat => some .add

def irUnaryOpToJS : IRUnaryOp → Option UnaryOp
  | .neg => some .neg
  | .not => some .not
  | .bitNot => some .bitNot
  | .typeof => some .typeof

def irBinOpToLean : IRBinOp → Option String
  | .add => some "+"
  | .sub => some "-"
  | .mul => some "*"
  | .div => some "/"
  | .mod => some "%"
  | .eq => some "=="
  | .neq => some "!="
  | .lt => some "<"
  | .lte => some "<="
  | .gt => some ">"
  | .gte => some ">="
  | .and => some "&&"
  | .or => some "||"
  | .strConcat => some "++"
  | _ => none

def irUnaryOpToLean : IRUnaryOp → Option String
  | .neg => some "-"
  | .not => some "!"
  | _ => none

def leanLitToIRLit : LeanLit → IRLit
  | .natVal n => .number (Float.ofNat n)
  | .float f => .number f
  | .string s => .string s
  | .bool b => .bool b

/-- IR parameter list with every parameter untyped -/
def anyParams (names : List String) : List (String × IRType) :=
  names.map (·, IRType.any)

/-- `const x = e;` -/
def constDecl (x : String) (e : JS.Expr) : Stmt :=
  .varDecl .const [.mk (.ident x none) (some e)]

/-! ## JS → IR -/

set_option autoImplicit true in
mutual

inductive JSToIRExpr : JS.Expr → IRExpr → Prop where
  | ident : JSToIRExpr (.ident x) (.var x)
  | str : JSToIRExpr (.literal (.string s)) (.lit (.string s))
  | num : JSToIRExpr (.literal (.number n)) (.lit (.number n))
  | bool : JSToIRExpr (.literal (.bool b)) (.lit (.bool b))
  | null : JSToIRExpr (.literal .null) .undefined
  | undef : JSToIRExpr (.literal .undefined) .undefined
  | paren : JSToIRExpr e e' → JSToIRExpr (.paren e) e'
  | binary :
      JSToIRExpr l l' → JSToIRExpr r r' → jsBinOpToIR op = some irop →
      JSToIRExpr (.binary op l r) (.binOp irop l' r')
  | unary :
      JSToIRExpr a a' → jsUnaryOpToIR op = some irop →
      JSToIRExpr (.unary op a) (.unaryOp irop a')
  | cond :
      JSToIRExpr c c' → JSToIRExpr t t' → JSToIRExpr e e' →
      JSToIRExpr (.conditional c t e) (.«if» c' t' e')
  | call :
      JSToIRExpr f f' → JSToIRExprs args args' →
      JSToIRExpr (.call f args) (.app f' args')
  | arrow_expr :
      simpleParamNames params = some names →
      JSToIRExpr body body' →
      JSToIRExpr (.arrowFunction params (.expr body) false)
        (.lam none (anyParams names) [] body')
  | arrow_block :
      simpleParamNames params = some names →
      JSToIRFunBody body body' →
      JSToIRExpr (.arrowFunction params (.block body) false)
        (.lam none (anyParams names) [] body')
  | function :
      simpleParamNames params = some names →
      JSToIRFunBody body body' →
      JSToIRExpr (.function name params body false false)
        (.lam name (anyParams names) [] body')
  | array :
      JSToIRElems elems elems' →
      JSToIRExpr (.array elems) (.array elems')
  | object :
      JSToIRProps props fields →
      JSToIRExpr (.object props) (.record fields)

inductive JSToIRExprs : List JS.Expr → List IRExpr → Prop where
  | nil : JSToIRExprs [] []
  | cons : JSToIRExpr e e' → JSToIRExprs es es' → JSToIRExprs (e :: es) (e' :: es')

inductive JSToIRElems : List (Option JS.Expr) → List IRExpr → Prop where
  | nil : JSToIRElems [] []
  | some : JSToIRExpr e e' → JSToIRElems es es' → JSToIRElems (some e :: es) (e' :: es')
  | hole : JSToIRElems es es' → JSToIRElems (none :: es) (.undefined :: es')

inductive JSToIRProps : List Property → List (String × IRExpr) → Prop where
  | nil : JSToIRProps [] []
  | cons :
      JSToIRExpr e e' → JSToIRProps ps ps' →
      JSToIRProps (.prop (.ident k) e .init false false :: ps) ((k, e') :: ps')

/-- A function body. A body that is a single `return e` becomes just `e`;
    otherwise the statements are followed by `undefined`, which is what a
    JS function returns when control falls off the end. -/
inductive JSToIRFunBody : List Stmt → IRExpr → Prop where
  | ret : JSToIRExpr e e' → JSToIRFunBody [.return_ (some e)] e'
  | general : JSToIRStmts ss b → JSToIRFunBody ss (.seq [b, .undefined])

inductive JSToIRStmts : List Stmt → IRExpr → Prop where
  | nil : JSToIRStmts [] .undefined
  | decl :
      (kind = .const ∨ kind = .let) →
      JSToIRExpr init init' → JSToIRStmts rest rest' →
      JSToIRStmts (.varDecl kind [.mk (.ident x none) (some init)] :: rest)
        (.«let» x .any init' rest')
  | funcDecl :
      simpleParamNames params = some names →
      JSToIRFunBody body body' → JSToIRStmts rest rest' →
      JSToIRStmts (.funcDecl f params body false false :: rest)
        (.«let» f .any (.lam (some f) (anyParams names) [] body') rest')
  | last :
      s.isDecl = false → JSToIRStmt s s' →
      JSToIRStmts [s] s'
  | cons :
      s.isDecl = false → JSToIRStmt s s' → JSToIRStmts rest rest' → rest ≠ [] →
      JSToIRStmts (s :: rest) (.seq [s', rest'])

inductive JSToIRStmt : Stmt → IRExpr → Prop where
  | expr : JSToIRExpr e e' → JSToIRStmt (.expr e) e'
  | block : JSToIRStmts ss b → JSToIRStmt (.block ss) b
  | empty : JSToIRStmt .empty .undefined
  | return_some : JSToIRExpr e e' → JSToIRStmt (.return_ (some e)) (.«return» e')
  | return_none : JSToIRStmt (.return_ none) (.«return» .undefined)
  | throw : JSToIRExpr e e' → JSToIRStmt (.throw e) (.throw e')
  | if_else :
      JSToIRExpr c c' → JSToIRStmt t t' → JSToIRStmt e e' →
      JSToIRStmt (.ifStmt c t (some e)) (.«if» c' t' e')
  | if_noelse :
      JSToIRExpr c c' → JSToIRStmt t t' →
      JSToIRStmt (.ifStmt c t none) (.«if» c' t' .undefined)

end

/-! ## IR → JS

  Expression mode (`IRToJSExpr`) translates pure IR expressions to JS
  expressions; an IR `let` becomes an immediately-invoked arrow function.
  Statement mode (`IRToJSStmts m`) translates IR to a JS statement list:
  in `.tail` mode the IR value is *returned* (function bodies), in
  `.discard` mode it is dropped (top-level programs).
-/

inductive StmtMode where
  | tail
  | discard
  deriving DecidableEq, Repr

/-- No top-level declarations: concatenating such a list onto another
    cannot change the other's scope. -/
def noDecls (ss : List Stmt) : Bool := ss.all (fun s => !s.isDecl)

set_option autoImplicit true in
mutual

inductive IRToJSExpr : IRExpr → JS.Expr → Prop where
  | var : IRToJSExpr (.var x) (.ident x)
  | num : IRToJSExpr (.lit (.number n)) (.literal (.number n))
  | str : IRToJSExpr (.lit (.string s)) (.literal (.string s))
  | bool : IRToJSExpr (.lit (.bool b)) (.literal (.bool b))
  | unit : IRToJSExpr (.lit .unit) (.literal .undefined)
  | undef : IRToJSExpr .undefined (.literal .undefined)
  | binOp :
      IRToJSExpr l l' → IRToJSExpr r r' → irBinOpToJS op = some jop →
      IRToJSExpr (.binOp op l r) (.binary jop l' r')
  | unaryOp :
      IRToJSExpr a a' → irUnaryOpToJS op = some jop →
      IRToJSExpr (.unaryOp op a) (.unary jop a')
  | if_ :
      IRToJSExpr c c' → IRToJSExpr t t' → IRToJSExpr e e' →
      IRToJSExpr (.«if» c t e) (.conditional c' t' e')
  | app :
      IRToJSExpr f f' → IRToJSExprs args args' →
      IRToJSExpr (.app f args) (.call f' args')
  | let_ :
      IRToJSExpr v v' → IRToJSExpr b b' →
      IRToJSExpr (.«let» x ty v b)
        (.call (.arrowFunction [pid x] (.expr b') false) [v'])
  | lam_expr :
      IRToJSExpr body body' →
      IRToJSExpr (.lam none params caps body false false)
        (.arrowFunction ((params.map Prod.fst).map pid) (.expr body') false)
  | lam_block :
      IRToJSStmts .tail body ss →
      IRToJSExpr (.lam none params caps body false false)
        (.arrowFunction ((params.map Prod.fst).map pid) (.block ss) false)
  | lam_named :
      IRToJSStmts .tail body ss →
      IRToJSExpr (.lam (some f) params caps body false false)
        (.function (some f) ((params.map Prod.fst).map pid) ss false false)
  | record :
      IRToJSFields fs ps →
      IRToJSExpr (.record fs) (.object ps)
  | project :
      IRToJSExpr e e' →
      IRToJSExpr (.project e k) (.member e' (.ident k))
  | array :
      IRToJSExprs es es' →
      IRToJSExpr (.array es) (.array (es'.map some))

inductive IRToJSExprs : List IRExpr → List JS.Expr → Prop where
  | nil : IRToJSExprs [] []
  | cons : IRToJSExpr e e' → IRToJSExprs es es' → IRToJSExprs (e :: es) (e' :: es')

inductive IRToJSFields : List (String × IRExpr) → List Property → Prop where
  | nil : IRToJSFields [] []
  | cons :
      IRToJSExpr e e' → IRToJSFields fs ps →
      IRToJSFields ((k, e) :: fs) (.prop (.ident k) e' .init false false :: ps)

inductive IRToJSStmts : StmtMode → IRExpr → List Stmt → Prop where
  | let_ :
      IRToJSExpr v v' → IRToJSStmts m b ss →
      IRToJSStmts m (.«let» x ty v b) (constDecl x v' :: ss)
  | if_ :
      IRToJSExpr c c' → IRToJSStmts m t ts → IRToJSStmts m e es →
      IRToJSStmts m (.«if» c t e) [.ifStmt c' (.block ts) (some (.block es))]
  | if_noelse :
      IRToJSExpr c c' → IRToJSStmts m t ts → IRToJSStmts m e [] →
      IRToJSStmts m (.«if» c t e) [.ifStmt c' (.block ts) none]
  | seq_one :
      IRToJSStmts m e ss →
      IRToJSStmts m (.seq [e]) ss
  | seq_block :
      IRToJSStmts .discard e ss → IRToJSStmts m (.seq rest) rs → rest ≠ [] →
      IRToJSStmts m (.seq (e :: rest)) (.block ss :: rs)
  | seq_flat :
      IRToJSStmts .discard e ss → noDecls ss = true →
      IRToJSStmts m (.seq rest) rs → rest ≠ [] →
      IRToJSStmts m (.seq (e :: rest)) (ss ++ rs)
  | seq_last :
      IRToJSStmts .discard e ss → IRToJSStmts m (.seq rest) [] → rest ≠ [] →
      IRToJSStmts m (.seq (e :: rest)) ss
  | funcDecl :
      IRToJSStmts .tail body ss → IRToJSStmts m b rs →
      IRToJSStmts m (.«let» f ty (.lam (some f) params caps body false false) b)
        (.funcDecl f ((params.map Prod.fst).map pid) ss false false :: rs)
  | if_elseif :
      IRToJSExpr c c' → IRToJSStmts m t ts → IRToJSStmts m e [s] → s.isDecl = false →
      IRToJSStmts m (.«if» c t e) [.ifStmt c' (.block ts) (some s)]
  | ret :
      IRToJSExpr e e' →
      IRToJSStmts m (.«return» e) [.return_ (some e')]
  | throw :
      IRToJSExpr e e' →
      IRToJSStmts m (.throw e) [.throw e']
  | expr_tail :
      IRToJSExpr e e' →
      IRToJSStmts .tail e [.return_ (some e')]
  | expr_discard :
      IRToJSExpr e e' →
      IRToJSStmts .discard e [.expr e']
  | undef :
      IRToJSStmts m .undefined []
  | unit :
      IRToJSStmts m (.lit .unit) []

end

/-! ## Lean → IR -/

set_option autoImplicit true in
mutual

inductive LeanToIRExpr : LeanExpr → IRExpr → Prop where
  | ident : LeanToIRExpr (.ident x) (.var x)
  | lit : LeanToIRExpr (.lit l) (.lit (leanLitToIRLit l))
  | unit : LeanToIRExpr .unit (.lit .unit)
  | paren : LeanToIRExpr e e' → LeanToIRExpr (.paren e) e'
  | lam_one :
      LeanToIRExpr body body' →
      LeanToIRExpr (.lam [p] body) (.lam none [(p.name, .any)] [] body')
  | lam_cons :
      ps ≠ [] → LeanToIRExpr (.lam ps body) body' →
      LeanToIRExpr (.lam (p :: ps) body) (.lam none [(p.name, .any)] [] body')
  | app :
      LeanToIRExpr f f' → LeanToIRExpr a a' →
      LeanToIRExpr (.app f a) (.app f' [a'])
  | let_ :
      LeanToIRExpr v v' → LeanToIRExpr b b' →
      LeanToIRExpr (.«let» x ty v b) (.«let» x .any v' b')
  | if_ :
      LeanToIRExpr c c' → LeanToIRExpr t t' → LeanToIRExpr e e' →
      LeanToIRExpr (.«if» c t (some e)) (.«if» c' t' e')
  | binOp :
      LeanToIRExpr l l' → LeanToIRExpr r r' → leanBinOpToIR op = some irop →
      LeanToIRExpr (.binOp op l r) (.binOp irop l' r')
  | unaryOp :
      LeanToIRExpr a a' → leanUnaryOpToIR op = some irop →
      LeanToIRExpr (.unaryOp op a) (.unaryOp irop a')
  | structLit :
      LeanToIRFields fs fs' →
      LeanToIRExpr (.structLit name fs) (.record fs')
  | arrayLit :
      LeanToIRExprs es es' →
      LeanToIRExpr (.arrayLit es) (.array es')
  | proj :
      LeanToIRExpr e e' →
      LeanToIRExpr (.proj e k) (.project e' k)
  | throw :
      LeanToIRExpr e e' →
      LeanToIRExpr (.«throw» e) (.throw e')

inductive LeanToIRExprs : List LeanExpr → List IRExpr → Prop where
  | nil : LeanToIRExprs [] []
  | cons : LeanToIRExpr e e' → LeanToIRExprs es es' → LeanToIRExprs (e :: es) (e' :: es')

inductive LeanToIRFields : List (String × LeanExpr) → List (String × IRExpr) → Prop where
  | nil : LeanToIRFields [] []
  | cons :
      LeanToIRExpr e e' → LeanToIRFields fs fs' →
      LeanToIRFields ((k, e) :: fs) ((k, e') :: fs')

end

/-! ## IR → Lean

  A multi-parameter IR function becomes a curried Lean `fun`, and an
  application to several arguments becomes nested one-argument
  applications. Lean evaluates `f a b` as `(f a) b`, applying `f` before
  evaluating `b`, while IR evaluates all arguments before calling `f`. The
  two orders agree when the arguments after the first cannot signal, so
  those must be atoms (variables and literals).
-/

/-- IR expressions that evaluate without effects and never signal -/
inductive IsAtom : IRExpr → Prop where
  | var {x : String} : IsAtom (.var x)
  | lit {l : IRLit} : IsAtom (.lit l)
  | undef : IsAtom .undefined

/-- Untyped Lean parameters with the given names -/
def leanParamsOf (names : List String) : List LeanParam :=
  names.map fun n => ⟨n, none⟩

/-- What remains of a curried `fun p q₁ … qₙ => b` once `p` is bound -/
def leanTail : List String → LeanExpr → LeanExpr
  | [], b => b
  | q :: qs, b => .lam (leanParamsOf (q :: qs)) b

set_option autoImplicit true in
mutual

inductive IRToLeanExpr : IRExpr → LeanExpr → Prop where
  | var : IRToLeanExpr (.var x) (.ident x)
  | num : IRToLeanExpr (.lit (.number n)) (.lit (.float n))
  | str : IRToLeanExpr (.lit (.string s)) (.lit (.string s))
  | bool : IRToLeanExpr (.lit (.bool b)) (.lit (.bool b))
  | unit : IRToLeanExpr (.lit .unit) .unit
  | undef : IRToLeanExpr .undefined .unit
  | let_ :
      IRToLeanExpr v v' → IRToLeanExpr b b' →
      IRToLeanExpr (.«let» x ty v b) (.«let» x none v' b')
  | lam :
      IRToLeanExpr body body' → params ≠ [] →
      IRToLeanExpr (.lam none params caps body false false)
        (.lam (leanParamsOf (params.map Prod.fst)) body')
  | app :
      IRToLeanExpr f f' → IRToLeanExpr a a' → IRToLeanAtoms as as' →
      IRToLeanExpr (.app f (a :: as)) (as'.foldl .app (.app f' a'))
  | binOp :
      IRToLeanExpr l l' → IRToLeanExpr r r' → irBinOpToLean op = some lop →
      IRToLeanExpr (.binOp op l r) (.binOp lop l' r')
  | unaryOp :
      IRToLeanExpr a a' → irUnaryOpToLean op = some lop →
      IRToLeanExpr (.unaryOp op a) (.unaryOp lop a')
  | if_ :
      IRToLeanExpr c c' → IRToLeanExpr t t' → IRToLeanExpr e e' →
      IRToLeanExpr (.«if» c t e) (.«if» c' t' (some e'))
  | record :
      IRToLeanFields fs fs' →
      IRToLeanExpr (.record fs) (.structLit none fs')
  | array :
      IRToLeanExprs es es' →
      IRToLeanExpr (.array es) (.arrayLit es')
  | project :
      IRToLeanExpr e e' →
      IRToLeanExpr (.project e k) (.proj e' k)
  | throw :
      IRToLeanExpr e e' →
      IRToLeanExpr (.throw e) (.«throw» e')

inductive IRToLeanExprs : List IRExpr → List LeanExpr → Prop where
  | nil : IRToLeanExprs [] []
  | cons : IRToLeanExpr e e' → IRToLeanExprs es es' → IRToLeanExprs (e :: es) (e' :: es')

/-- Arguments after the first: atoms only -/
inductive IRToLeanAtoms : List IRExpr → List LeanExpr → Prop where
  | nil : IRToLeanAtoms [] []
  | cons : IsAtom e → IRToLeanExpr e e' → IRToLeanAtoms es es' →
      IRToLeanAtoms (e :: es) (e' :: es')

inductive IRToLeanFields : List (String × IRExpr) → List (String × LeanExpr) → Prop where
  | nil : IRToLeanFields [] []
  | cons :
      IRToLeanExpr e e' → IRToLeanFields fs fs' →
      IRToLeanFields ((k, e) :: fs) ((k, e') :: fs')

end

end LeanJS.Semantics
