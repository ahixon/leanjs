/-
  Inductive translation relations for all 4 passes.

  Each relation mirrors the `partial def` translator, with one constructor
  per pattern match arm. These are structural relations (not fuel-indexed)
  that thread the translator's state (mutation tracking, ref vars, counters).

  Used in forward simulation proofs as the "translate" predicate.
-/
import LeanJS.JS.AST
import LeanJS.Lean.AST
import LeanJS.IR.Core
import LeanJS.Semantics.JSEval
import LeanJS.Semantics.LeanEval

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR

/-! ## Translation State Types (mirror the partial def states) -/

/-- JS→IR translation environment -/
structure JSTransEnv where
  mutated : List String := []
  scope : List String := []
  freshCounter : Nat := 0
  deriving Inhabited

/-- IR→JS translation state -/
structure IRJSState where
  refVars : List String := []
  counter : Nat := 0
  deriving Inhabited

/-- IR→Lean translation state -/
structure IRLeanState where
  refVars : List String := []
  counter : Nat := 0
  deriving Inhabited

/-- Lean→IR translation environment -/
structure LeanIREnv where
  mutVars : List String := []
  refVars : List String := []
  deriving Inhabited

/-! ## Helper functions (must be defined before mutual blocks) -/

/-- Convert JS literal to IR literal -/
def jsLitToIRLit : Literal → IRLit
  | .string s => .string s
  | .number n => .number n
  | .bool b => .bool b
  | .null => .unit
  | .undefined => .unit
  | .regex _ _ => .string "<regex>"

/-- Convert Lean literal to IR literal -/
def leanLitToIRLit : LeanLit → IRLit
  | .natVal n => .number (Float.ofNat n)
  | .float f => .number f
  | .string s => .string s
  | .bool b => .bool b

/-- Convert IR binary op to JS binary op -/
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

/-- Convert IR unary op to JS unary op -/
def irUnaryOpToJS : IRUnaryOp → Option UnaryOp
  | .neg => some .neg
  | .not => some .not
  | .bitNot => some .bitNot
  | .typeof => some .typeof

/-- Convert IR binary op to Lean op string -/
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

/-- Convert IR unary op to Lean op string -/
def irUnaryOpToLean : IRUnaryOp → Option String
  | .neg => some "-"
  | .not => some "!"
  | _ => none

/-- Convert IR pattern to Lean pattern -/
def irPatToLean : IRPattern → LeanPattern
  | .wildcard => .wildcard
  | .var name => .var name
  | .lit (.number n) => .lit (.float n)
  | .lit (.string s) => .lit (.string s)
  | .lit (.bool b) => .lit (.bool b)
  | .lit .unit => .wildcard
  | .constructor tag bindings => .constructor tag (bindings.map .var)

/-- Convert Lean pattern to IR pattern -/
def leanPatToIR : LeanPattern → IRPattern
  | .wildcard => .wildcard
  | .var name => .var name
  | .lit (.natVal n) => .lit (.number (Float.ofNat n))
  | .lit (.float f) => .lit (.number f)
  | .lit (.string s) => .lit (.string s)
  | .lit (.bool b) => .lit (.bool b)
  | .constructor tag args => .constructor tag (args.map leanPatternToBinding)
where
  leanPatternToBinding : LeanPattern → String
    | .var name => name
    | _ => "_"

/-- Fold Lean curried application -/
def foldApp : LeanExpr → List LeanExpr → LeanExpr
  | f, [] => f
  | f, a :: rest => foldApp (.app f a) rest

/-- Fold sequence in Lean (nested lets) -/
def foldSeqLean : List LeanExpr → LeanExpr
  | [] => .unit
  | [e] => e
  | e :: rest => .«let» "_" none e (foldSeqLean rest)

/-- Thread let binding for JS→IR statement sequence -/
def threadLetBinding (s : Stmt) (ir_s ir_rest : IRExpr) : IRExpr :=
  match s with
  | .varDecl _ [.mk (.ident name _) _] =>
    match ir_s with
    | .«let» n ty v _ => .«let» n ty v ir_rest
    | _ => .seq [ir_s, ir_rest]
  | .funcDecl _ _ _ _ _ =>
    match ir_s with
    | .«let» n ty v _ => .«let» n ty v ir_rest
    | _ => .seq [ir_s, ir_rest]
  | _ => .seq [ir_s, ir_rest]

/-- Build template string concatenation from quasis and expressions -/
def buildTemplateConcat : List String → List IRExpr → IRExpr
  | [], _ => .lit (.string "")
  | [s], [] => .lit (.string s)
  | s :: srest, e :: erest =>
    .binOp .strConcat
      (.binOp .strConcat (.lit (.string s)) e)
      (buildTemplateConcat srest erest)
  | s :: srest, [] =>
    .binOp .strConcat (.lit (.string s)) (buildTemplateConcat srest [])

/-- Convert IR literal to JS literal -/
def irLitToJSLit : IRLit → Literal
  | .number n => .number n
  | .string s => .string s
  | .bool b => .bool b
  | .unit => .undefined

/-- Convert IR literal to Lean literal -/
def irLitToLeanLit : IRLit → LeanLit
  | .number n => .float n
  | .string s => .string s
  | .bool b => .bool b
  | .unit => .bool true  -- approximation

/-- Convert list of IR params to Lean params -/
def irParamsToLean (params : List (String × IRType)) : List LeanParam :=
  params.map fun (n, _) => LeanParam.mk n none

/-- Convert list of IR params to list of (String × IRType) -/
def paramNamesToIR (names : List String) : List (String × IRType) :=
  names.map (·, IRType.any)

/-! ## JS→IR Translation Relation -/

set_option maxHeartbeats 3200000 in
mutual

/-- JS expression → IR expression translation relation -/
inductive JSToIRExpr : JSTransEnv → Expr → IRExpr → JSTransEnv → Prop where
  | ident_pure :
      name ∉ tenv.mutated →
      JSToIRExpr tenv (.ident name) (.var name) tenv
  | ident_mut :
      name ∈ tenv.mutated →
      JSToIRExpr tenv (.ident name) (.deref (.var name)) tenv
  | literal :
      JSToIRExpr tenv (.literal lit) (.lit (jsLitToIRLit lit)) tenv
  | binary :
      JSToIRExpr tenv left ir_left tenv1 →
      JSToIRExpr tenv1 right ir_right tenv2 →
      jsBinOpToIR op = some irop →
      JSToIRExpr tenv (.binary op left right) (.binOp irop ir_left ir_right) tenv2
  | unary :
      JSToIRExpr tenv arg ir_arg tenv1 →
      jsUnaryOpToIR op = some irop →
      JSToIRExpr tenv (.unary op arg) (.unaryOp irop ir_arg) tenv1
  | conditional :
      JSToIRExpr tenv test ir_test tenv1 →
      JSToIRExpr tenv1 consequent ir_cons tenv2 →
      JSToIRExpr tenv2 alternate ir_alt tenv3 →
      JSToIRExpr tenv (.conditional test consequent alternate)
        (.«if» ir_test ir_cons ir_alt) tenv3
  | call :
      JSToIRExpr tenv callee ir_callee tenv1 →
      JSToIRExprs tenv1 args ir_args tenv2 →
      JSToIRExpr tenv (.call callee args) (.app ir_callee ir_args) tenv2
  | function :
      JSToIRBody tenv body ir_body tenv' →
      JSToIRExpr tenv (.function name params body false false)
        (.lam name (paramNamesToIR (extractParamNames params)) [] ir_body) tenv
  | arrowFunction_block :
      JSToIRBody tenv stmts ir_body tenv' →
      JSToIRExpr tenv (.arrowFunction params (.block stmts) false)
        (.lam none (paramNamesToIR (extractParamNames params)) [] ir_body) tenv
  | arrowFunction_expr :
      JSToIRExpr tenv e ir_e tenv' →
      JSToIRExpr tenv (.arrowFunction params (.expr e) false)
        (.lam none (paramNamesToIR (extractParamNames params)) [] (.«return» ir_e)) tenv
  | member_ident :
      JSToIRExpr tenv obj ir_obj tenv1 →
      JSToIRExpr tenv (.member obj (.ident prop)) (.project ir_obj prop) tenv1
  | array :
      JSToIROptionExprs tenv elements ir_elems tenv1 →
      JSToIRExpr tenv (.array elements) (.array ir_elems) tenv1
  | object :
      JSToIRProps tenv properties ir_fields tenv1 →
      JSToIRExpr tenv (.object properties) (.record ir_fields) tenv1
  | this :
      JSToIRExpr tenv .this .this tenv
  | paren :
      JSToIRExpr tenv e ir_e tenv1 →
      JSToIRExpr tenv (.paren e) ir_e tenv1
  | assign_var :
      name ∈ tenv.mutated →
      JSToIRExpr tenv right ir_right tenv1 →
      JSToIRExpr tenv (.assign .assign (.expr (.ident name)) right)
        (.assign (.var name) ir_right) tenv1
  | template :
      JSToIRExprs tenv exprs ir_exprs tenv1 →
      JSToIRExpr tenv (.template none quasis exprs)
        (buildTemplateConcat quasis ir_exprs) tenv1

/-- Translate a list of JS expressions -/
inductive JSToIRExprs : JSTransEnv → List Expr → List IRExpr → JSTransEnv → Prop where
  | nil : JSToIRExprs tenv [] [] tenv
  | cons :
      JSToIRExpr tenv e ir_e tenv1 →
      JSToIRExprs tenv1 rest ir_rest tenv2 →
      JSToIRExprs tenv (e :: rest) (ir_e :: ir_rest) tenv2

/-- Translate optional expressions (for sparse arrays) -/
inductive JSToIROptionExprs : JSTransEnv → List (Option Expr) → List IRExpr →
    JSTransEnv → Prop where
  | nil : JSToIROptionExprs tenv [] [] tenv
  | cons_some :
      JSToIRExpr tenv e ir_e tenv1 →
      JSToIROptionExprs tenv1 rest ir_rest tenv2 →
      JSToIROptionExprs tenv (some e :: rest) (ir_e :: ir_rest) tenv2
  | cons_none :
      JSToIROptionExprs tenv rest ir_rest tenv1 →
      JSToIROptionExprs tenv (none :: rest) (.undefined :: ir_rest) tenv1

/-- Translate object properties -/
inductive JSToIRProps : JSTransEnv → List Property → List (String × IRExpr) →
    JSTransEnv → Prop where
  | nil : JSToIRProps tenv [] [] tenv
  | cons_init :
      JSToIRExpr tenv value ir_value tenv1 →
      JSToIRProps tenv1 rest ir_rest tenv2 →
      JSToIRProps tenv (.prop (.ident key) value .init false false :: rest)
        ((key, ir_value) :: ir_rest) tenv2

/-- JS statement → IR expression translation relation -/
inductive JSToIRStmt : JSTransEnv → Stmt → IRExpr → JSTransEnv → Prop where
  | expr :
      JSToIRExpr tenv e ir_e tenv1 →
      JSToIRStmt tenv (.expr e) ir_e tenv1
  | varDecl_const :
      name ∉ tenv.mutated →
      JSToIRExpr tenv initExpr ir_init tenv1 →
      JSToIRStmt tenv
        (.varDecl .«const» [.mk (.ident name none) (some initExpr)])
        (.«let» name .any ir_init (.var name)) tenv1
  | varDecl_let_mut :
      name ∈ tenv.mutated →
      JSToIRExpr tenv initExpr ir_init tenv1 →
      JSToIRStmt tenv
        (.varDecl .«let» [.mk (.ident name none) (some initExpr)])
        (.«let» name .any (.mkRef ir_init) (.var name)) tenv1
  | varDecl_let_pure :
      name ∉ tenv.mutated →
      JSToIRExpr tenv initExpr ir_init tenv1 →
      JSToIRStmt tenv
        (.varDecl .«let» [.mk (.ident name none) (some initExpr)])
        (.«let» name .any ir_init (.var name)) tenv1
  | return_some :
      JSToIRExpr tenv arg ir_arg tenv1 →
      JSToIRStmt tenv (.return_ (some arg)) (.«return» ir_arg) tenv1
  | return_none :
      JSToIRStmt tenv (.return_ none) (.«return» (.lit .unit)) tenv
  | throw :
      JSToIRExpr tenv arg ir_arg tenv1 →
      JSToIRStmt tenv (.throw arg) (.throw ir_arg) tenv1
  | ifStmt_else :
      JSToIRExpr tenv test ir_test tenv1 →
      JSToIRBody tenv1 [cons] ir_cons tenv2 →
      JSToIRBody tenv2 [alt] ir_alt tenv3 →
      JSToIRStmt tenv (.ifStmt test cons (some alt))
        (.«if» ir_test ir_cons ir_alt) tenv3
  | ifStmt_no_else :
      JSToIRExpr tenv test ir_test tenv1 →
      JSToIRBody tenv1 [cons] ir_cons tenv2 →
      JSToIRStmt tenv (.ifStmt test cons none)
        (.«if» ir_test ir_cons (.lit .unit)) tenv2
  | while_ :
      JSToIRExpr tenv test ir_test tenv1 →
      JSToIRBody tenv1 [body] ir_body tenv2 →
      JSToIRStmt tenv (.while_ test body) (.loop ir_test ir_body) tenv2
  | block :
      JSToIRBody tenv stmts ir_body tenv1 →
      JSToIRStmt tenv (.block stmts) ir_body tenv1
  | funcDecl :
      JSToIRBody tenv body ir_body tenv' →
      JSToIRStmt tenv (.funcDecl name params body false false)
        (.«let» name .any (.lam (some name) (paramNamesToIR (extractParamNames params)) [] ir_body) (.var name)) tenv
  | break_ :
      JSToIRStmt tenv (.break_ none) .«break» tenv
  | continue_ :
      JSToIRStmt tenv (.continue_ none) .«continue» tenv
  | try_no_fin :
      JSToIRBody tenv block_ ir_block tenv1 →
      JSToIRBody tenv1 handlerBody ir_handler tenv2 →
      JSToIRStmt tenv (.try_ block_ handler none)
        (.tryCatch ir_block handlerName ir_handler none) tenv2
  | empty :
      JSToIRStmt tenv .empty (.lit .unit) tenv

/-- Translate a body (list of statements) to a single IR expression -/
inductive JSToIRBody : JSTransEnv → List Stmt → IRExpr → JSTransEnv → Prop where
  | nil : JSToIRBody tenv [] (.lit .unit) tenv
  | singleton :
      JSToIRStmt tenv s ir_s tenv1 →
      JSToIRBody tenv [s] ir_s tenv1
  | cons :
      JSToIRStmt tenv s ir_s tenv1 →
      JSToIRBody tenv1 rest ir_rest tenv2 →
      rest ≠ [] →
      JSToIRBody tenv (s :: rest) (threadLetBinding s ir_s ir_rest) tenv2

end

/-! ## IR→JS Translation Relation -/

set_option maxHeartbeats 1600000 in
mutual

/-- IR expression → JS expression translation relation -/
inductive IRToJSExpr : IRJSState → IRExpr → Expr → IRJSState → Prop where
  | var :
      IRToJSExpr st (.var name) (.ident name) st
  | lit :
      IRToJSExpr st (.lit l) (.literal (irLitToJSLit l)) st
  | binOp :
      IRToJSExpr st left js_left st1 →
      IRToJSExpr st1 right js_right st2 →
      irBinOpToJS irop = some jsop →
      IRToJSExpr st (.binOp irop left right) (.binary jsop js_left js_right) st2
  | unaryOp :
      IRToJSExpr st arg js_arg st1 →
      irUnaryOpToJS irop = some jsop →
      IRToJSExpr st (.unaryOp irop arg) (.unary jsop js_arg) st1
  | if_ :
      IRToJSExpr st condE js_cond st1 →
      IRToJSExpr st1 then_ js_then st2 →
      IRToJSExpr st2 else_ js_else st3 →
      IRToJSExpr st (.«if» condE then_ else_) (.conditional js_cond js_then js_else) st3
  | app :
      IRToJSExpr st func js_func st1 →
      IRToJSExprs st1 args js_args st2 →
      IRToJSExpr st (.app func args) (.call js_func js_args) st2
  | let_pure :
      name ∉ st.refVars →
      IRToJSExpr st value js_value st1 →
      (∀ inner, value ≠ .mkRef inner) →
      IRToJSExpr st1 body js_body st2 →
      IRToJSExpr st (.«let» name ty value body)
        (.call (.arrowFunction [.ident name none] (.expr js_body) false) [js_value])
        st2
  | let_ref :
      IRToJSExpr st inner js_inner st1 →
      st' = { st1 with refVars := name :: st1.refVars } →
      IRToJSExpr st' body js_body st2 →
      IRToJSExpr st (.«let» name ty (.mkRef inner) body)
        (.call (.arrowFunction [.ident name none] (.expr js_body) false) [js_inner])
        st2
  | deref :
      name ∈ st.refVars →
      IRToJSExpr st (.deref (.var name)) (.ident name) st
  | assign_ref :
      name ∈ st.refVars →
      IRToJSExpr st val js_val st1 →
      IRToJSExpr st (.assign (.var name) val)
        (.assign .assign (.expr (.ident name)) js_val) st1
  | mkRef_passthrough :
      IRToJSExpr st val js_val st1 →
      IRToJSExpr st (.mkRef val) js_val st1
  | record :
      IRToJSFields st fields js_props st1 →
      IRToJSExpr st (.record fields) (.object js_props) st1
  | project :
      IRToJSExpr st expr js_expr st1 →
      IRToJSExpr st (.project expr field) (.member js_expr (.ident field)) st1
  | array :
      IRToJSExprs st elements js_elems st1 →
      IRToJSExpr st (.array elements) (.array (js_elems.map some)) st1
  | index :
      IRToJSExpr st arr js_arr st1 →
      IRToJSExpr st1 idx js_idx st2 →
      IRToJSExpr st (.index arr idx) (.member js_arr (.computed js_idx)) st2
  | «return» :
      IRToJSExpr st val js_val st1 →
      IRToJSExpr st (.«return» val) js_val st1
  | throw :
      IRToJSExpr st val js_val st1 →
      IRToJSExpr st (.throw val) js_val st1
  | undefined :
      IRToJSExpr st .undefined (.literal .undefined) st
  | construct :
      IRToJSExprs st args js_args st1 →
      IRToJSExpr st (.construct name args)
        (.«new» (.ident name) js_args) st1

/-- Translate a list of IR expressions to JS expressions -/
inductive IRToJSExprs : IRJSState → List IRExpr → List Expr → IRJSState → Prop where
  | nil : IRToJSExprs st [] [] st
  | cons :
      IRToJSExpr st e js_e st1 →
      IRToJSExprs st1 rest js_rest st2 →
      IRToJSExprs st (e :: rest) (js_e :: js_rest) st2

/-- Translate IR record fields to JS object properties -/
inductive IRToJSFields : IRJSState → List (String × IRExpr) → List Property →
    IRJSState → Prop where
  | nil : IRToJSFields st [] [] st
  | cons :
      IRToJSExpr st e js_e st1 →
      IRToJSFields st1 rest js_rest st2 →
      IRToJSFields st ((name, e) :: rest)
        (Property.prop (.ident name) js_e .init false false :: js_rest) st2

end

/-! ## IR→Lean Translation Relation -/

set_option maxHeartbeats 1600000 in
mutual

/-- IR expression → Lean expression translation relation -/
inductive IRToLeanExpr : IRLeanState → IRExpr → LeanExpr → IRLeanState → Prop where
  | var_pure :
      name ∉ st.refVars →
      IRToLeanExpr st (.var name) (.ident name) st
  | var_ref :
      name ∈ st.refVars →
      IRToLeanExpr st (.var name) (.refGet (.ident name)) st
  | lit :
      IRToLeanExpr st (.lit l) (.lit (irLitToLeanLit l)) st
  | let_pure :
      (∀ inner, value ≠ .mkRef inner) →
      IRToLeanExpr st value lean_val st1 →
      IRToLeanExpr st1 body lean_body st2 →
      IRToLeanExpr st (.«let» name ty value body)
        (.«let» name none lean_val lean_body) st2
  | let_ref :
      IRToLeanExpr st inner lean_inner st1 →
      st' = { st1 with refVars := name :: st1.refVars } →
      IRToLeanExpr st' body lean_body st2 →
      IRToLeanExpr st (.«let» name ty (.mkRef inner) body)
        (.doBlock [.mutDecl name none lean_inner, .eval lean_body]) st2
  | lam :
      IRToLeanExpr st body lean_body st1 →
      IRToLeanExpr st (.lam name params captures body async_ gen)
        (.lam (irParamsToLean params) lean_body) st1
  | app :
      IRToLeanExpr st func lean_func st1 →
      IRToLeanExprs st1 args lean_args st2 →
      IRToLeanExpr st (.app func args) (foldApp lean_func lean_args) st2
  | binOp :
      IRToLeanExpr st left lean_left st1 →
      IRToLeanExpr st1 right lean_right st2 →
      irBinOpToLean irop = some lop →
      IRToLeanExpr st (.binOp irop left right) (.binOp lop lean_left lean_right) st2
  | unaryOp :
      IRToLeanExpr st arg lean_arg st1 →
      irUnaryOpToLean irop = some lop →
      IRToLeanExpr st (.unaryOp irop arg) (.unaryOp lop lean_arg) st1
  | if_ :
      IRToLeanExpr st condE lean_cond st1 →
      IRToLeanExpr st1 then_ lean_then st2 →
      IRToLeanExpr st2 else_ lean_else st3 →
      IRToLeanExpr st (.«if» condE then_ else_)
        (.«if» lean_cond lean_then (some lean_else)) st3
  | record :
      IRToLeanFields st fields lean_fields st1 →
      IRToLeanExpr st (.record fields) (.structLit none lean_fields) st1
  | project :
      IRToLeanExpr st expr lean_expr st1 →
      IRToLeanExpr st (.project expr field) (.proj lean_expr field) st1
  | array :
      IRToLeanExprs st elements lean_elems st1 →
      IRToLeanExpr st (.array elements) (.arrayLit lean_elems) st1
  | «return» :
      IRToLeanExpr st val lean_val st1 →
      IRToLeanExpr st (.«return» val) (.«return» lean_val) st1
  | throw :
      IRToLeanExpr st val lean_val st1 →
      IRToLeanExpr st (.throw val) (.«throw» lean_val) st1
  | undefined :
      IRToLeanExpr st .undefined .unit st
  | mkRef :
      IRToLeanExpr st val lean_val st1 →
      IRToLeanExpr st (.mkRef val) (.refNew lean_val) st1
  | deref_var :
      name ∈ st.refVars →
      IRToLeanExpr st (.deref (.var name)) (.refGet (.ident name)) st
  | assign_var :
      name ∈ st.refVars →
      IRToLeanExpr st val lean_val st1 →
      IRToLeanExpr st (.assign (.var name) val) (.refSet (.ident name) lean_val) st1
  | match_ :
      IRToLeanExpr st scrutinee lean_scrut st1 →
      IRToLeanMatchCases st1 cases lean_alts st2 →
      IRToLeanExpr st (.«match» scrutinee cases)
        (.«match» lean_scrut lean_alts) st2
  | tryCatch :
      IRToLeanExpr st body lean_body st1 →
      IRToLeanExpr st1 handler lean_handler st2 →
      IRToLeanExpr st (.tryCatch body catchVar handler finalizer)
        (.«try» lean_body catchVar (some lean_handler) none) st2
  | construct :
      IRToLeanExprs st args lean_args st1 →
      IRToLeanExpr st (.construct name args) (foldApp (.ident name) lean_args) st1
  | loop :
      IRToLeanExpr st condE lean_cond st1 →
      IRToLeanExpr st1 body lean_body st2 →
      IRToLeanExpr st (.loop condE body)
        (.doBlock [.doWhile lean_cond [.eval lean_body]]) st2
  | seq :
      IRToLeanExprs st exprs lean_exprs st1 →
      IRToLeanExpr st (.seq exprs) (foldSeqLean lean_exprs) st1

/-- Translate a list of IR expressions to Lean expressions -/
inductive IRToLeanExprs : IRLeanState → List IRExpr → List LeanExpr →
    IRLeanState → Prop where
  | nil : IRToLeanExprs st [] [] st
  | cons :
      IRToLeanExpr st e lean_e st1 →
      IRToLeanExprs st1 rest lean_rest st2 →
      IRToLeanExprs st (e :: rest) (lean_e :: lean_rest) st2

/-- Translate IR record fields to Lean struct fields -/
inductive IRToLeanFields : IRLeanState → List (String × IRExpr) →
    List (String × LeanExpr) → IRLeanState → Prop where
  | nil : IRToLeanFields st [] [] st
  | cons :
      IRToLeanExpr st e lean_e st1 →
      IRToLeanFields st1 rest lean_rest st2 →
      IRToLeanFields st ((name, e) :: rest) ((name, lean_e) :: lean_rest) st2

/-- Translate IR match cases to Lean match alternatives -/
inductive IRToLeanMatchCases : IRLeanState → List IRMatchCase → List LeanMatchAlt →
    IRLeanState → Prop where
  | nil : IRToLeanMatchCases st [] [] st
  | cons :
      IRToLeanExpr st body lean_body st1 →
      IRToLeanMatchCases st1 rest lean_rest st2 →
      IRToLeanMatchCases st (.mk pat body :: rest) (.mk (irPatToLean pat) lean_body :: lean_rest) st2

end

/-! ## Lean→IR Translation Relation -/

set_option maxHeartbeats 1600000 in
mutual

/-- Lean expression → IR expression translation relation -/
inductive LeanToIRExpr : LeanIREnv → LeanExpr → IRExpr → LeanIREnv → Prop where
  | ident_pure :
      name ∉ lenv.mutVars → name ∉ lenv.refVars →
      LeanToIRExpr lenv (.ident name) (.var name) lenv
  | ident_mut :
      (name ∈ lenv.mutVars ∨ name ∈ lenv.refVars) →
      LeanToIRExpr lenv (.ident name) (.deref (.var name)) lenv
  | lit :
      LeanToIRExpr lenv (.lit l) (.lit (leanLitToIRLit l)) lenv
  | app :
      LeanToIRExpr lenv fn ir_fn lenv1 →
      LeanToIRExpr lenv1 arg ir_arg lenv2 →
      LeanToIRExpr lenv (.app fn arg) (.app ir_fn [ir_arg]) lenv2
  | lam :
      LeanToIRExpr lenv body ir_body lenv' →
      LeanToIRExpr lenv (.lam params body)
        (.lam none (params.map fun p => (p.name, IRType.any)) [] ir_body) lenv
  | let_pure :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRExpr lenv1 body ir_body lenv2 →
      LeanToIRExpr lenv (.«let» name ty value body)
        (.«let» name .any ir_value ir_body) lenv2
  | doBlock :
      LeanToIRDoBlock lenv elems ir_body lenv1 →
      LeanToIRExpr lenv (.doBlock elems) ir_body lenv1
  | if_some :
      LeanToIRExpr lenv condE ir_cond lenv1 →
      LeanToIRExpr lenv1 then_ ir_then lenv2 →
      LeanToIRExpr lenv2 elseExpr ir_else lenv3 →
      LeanToIRExpr lenv (.«if» condE then_ (some elseExpr))
        (.«if» ir_cond ir_then ir_else) lenv3
  | if_none :
      LeanToIRExpr lenv condE ir_cond lenv1 →
      LeanToIRExpr lenv1 then_ ir_then lenv2 →
      LeanToIRExpr lenv (.«if» condE then_ none)
        (.«if» ir_cond ir_then (.lit .unit)) lenv2
  | «match» :
      LeanToIRExpr lenv scrutinee ir_scrut lenv1 →
      LeanToIRMatchAlts lenv1 alts ir_cases lenv2 →
      LeanToIRExpr lenv (.«match» scrutinee alts)
        (.«match» ir_scrut ir_cases) lenv2
  | «return» :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRExpr lenv (.«return» value) (.«return» ir_value) lenv1
  | structLit :
      LeanToIRFields lenv fields ir_fields lenv1 →
      LeanToIRExpr lenv (.structLit sname fields) (.record ir_fields) lenv1
  | arrayLit :
      LeanToIRExprs lenv elements ir_elems lenv1 →
      LeanToIRExpr lenv (.arrayLit elements) (.array ir_elems) lenv1
  | proj :
      LeanToIRExpr lenv expr ir_expr lenv1 →
      LeanToIRExpr lenv (.proj expr field) (.project ir_expr field) lenv1
  | binOp :
      LeanToIRExpr lenv left ir_left lenv1 →
      LeanToIRExpr lenv1 right ir_right lenv2 →
      leanBinOpToIR op = some irop →
      LeanToIRExpr lenv (.binOp op left right) (.binOp irop ir_left ir_right) lenv2
  | unaryOp :
      LeanToIRExpr lenv arg ir_arg lenv1 →
      leanUnaryOpToIR op = some irop →
      LeanToIRExpr lenv (.unaryOp op arg) (.unaryOp irop ir_arg) lenv1
  | unit :
      LeanToIRExpr lenv .unit (.lit .unit) lenv
  | refNew :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRExpr lenv (.refNew value) (.mkRef ir_value) lenv1
  | refGet :
      LeanToIRExpr lenv ref ir_ref lenv1 →
      LeanToIRExpr lenv (.refGet ref) (.deref ir_ref) lenv1
  | refSet :
      LeanToIRExpr lenv ref ir_ref lenv1 →
      LeanToIRExpr lenv1 value ir_value lenv2 →
      LeanToIRExpr lenv (.refSet ref value) (.assign ir_ref ir_value) lenv2
  | try_ :
      LeanToIRExpr lenv body ir_body lenv1 →
      LeanToIRExpr lenv1 handler ir_handler lenv2 →
      LeanToIRExpr lenv (.«try» body catchVar (some handler) finalizer)
        (.tryCatch ir_body catchVar ir_handler none) lenv2
  | «throw» :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRExpr lenv (.«throw» value) (.throw ir_value) lenv1
  | paren :
      LeanToIRExpr lenv inner ir_inner lenv1 →
      LeanToIRExpr lenv (.paren inner) ir_inner lenv1
  | hole :
      LeanToIRExpr lenv .hole .undefined lenv

/-- Translate a do-block element list to IR -/
inductive LeanToIRDoBlock : LeanIREnv → List LeanDoElem → IRExpr → LeanIREnv → Prop where
  | nil :
      LeanToIRDoBlock lenv [] (.lit .unit) lenv
  | singleton_eval :
      LeanToIRExpr lenv e ir_e lenv1 →
      LeanToIRDoBlock lenv [.eval e] ir_e lenv1
  | cons_eval :
      LeanToIRExpr lenv e ir_e lenv1 →
      LeanToIRDoBlock lenv1 rest ir_rest lenv2 →
      rest ≠ [] →
      LeanToIRDoBlock lenv (.eval e :: rest) (.seq [ir_e, ir_rest]) lenv2
  | cons_letDecl :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRDoBlock lenv1 rest ir_rest lenv2 →
      LeanToIRDoBlock lenv (.letDecl name ty value :: rest)
        (.«let» name .any ir_value ir_rest) lenv2
  | cons_bind :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRDoBlock lenv1 rest ir_rest lenv2 →
      LeanToIRDoBlock lenv (.bind name ty value :: rest)
        (.«let» name .any ir_value ir_rest) lenv2
  | cons_mutDecl :
      LeanToIRExpr lenv value ir_value lenv1 →
      lenv' = { lenv1 with mutVars := name :: lenv1.mutVars } →
      LeanToIRDoBlock lenv' rest ir_rest lenv2 →
      LeanToIRDoBlock lenv (.mutDecl name ty value :: rest)
        (.«let» name .any (.mkRef ir_value) ir_rest) lenv2
  | cons_reassign :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRDoBlock lenv1 rest ir_rest lenv2 →
      LeanToIRDoBlock lenv (.reassign name value :: rest)
        (.seq [.assign (.var name) ir_value, ir_rest]) lenv2
  | cons_doReturn :
      LeanToIRExpr lenv value ir_value lenv1 →
      LeanToIRDoBlock lenv [.doReturn value] (.«return» ir_value) lenv1
  | cons_doIf :
      LeanToIRExpr lenv condE ir_cond lenv1 →
      LeanToIRDoBlock lenv1 thenElems ir_then lenv2 →
      LeanToIRDoBlock lenv2 elseElems ir_else lenv3 →
      LeanToIRDoBlock lenv3 rest ir_rest lenv4 →
      LeanToIRDoBlock lenv (.doIf condE thenElems elseElems :: rest)
        (.seq [.«if» ir_cond ir_then ir_else, ir_rest]) lenv4
  | cons_doWhile :
      LeanToIRExpr lenv condE ir_cond lenv1 →
      LeanToIRDoBlock lenv1 body ir_body lenv2 →
      LeanToIRDoBlock lenv2 rest ir_rest lenv3 →
      LeanToIRDoBlock lenv (.doWhile condE body :: rest)
        (.seq [.loop ir_cond ir_body, ir_rest]) lenv3

/-- Translate a list of Lean expressions to IR -/
inductive LeanToIRExprs : LeanIREnv → List LeanExpr → List IRExpr → LeanIREnv → Prop where
  | nil : LeanToIRExprs lenv [] [] lenv
  | cons :
      LeanToIRExpr lenv e ir_e lenv1 →
      LeanToIRExprs lenv1 rest ir_rest lenv2 →
      LeanToIRExprs lenv (e :: rest) (ir_e :: ir_rest) lenv2

/-- Translate Lean struct fields to IR record fields -/
inductive LeanToIRFields : LeanIREnv → List (String × LeanExpr) →
    List (String × IRExpr) → LeanIREnv → Prop where
  | nil : LeanToIRFields lenv [] [] lenv
  | cons :
      LeanToIRExpr lenv e ir_e lenv1 →
      LeanToIRFields lenv1 rest ir_rest lenv2 →
      LeanToIRFields lenv ((name, e) :: rest) ((name, ir_e) :: ir_rest) lenv2

/-- Translate Lean match alts to IR match cases -/
inductive LeanToIRMatchAlts : LeanIREnv → List LeanMatchAlt →
    List IRMatchCase → LeanIREnv → Prop where
  | nil : LeanToIRMatchAlts lenv [] [] lenv
  | cons :
      LeanToIRExpr lenv body ir_body lenv1 →
      LeanToIRMatchAlts lenv1 rest ir_rest lenv2 →
      LeanToIRMatchAlts lenv (.mk pat body :: rest) (.mk (leanPatToIR pat) ir_body :: ir_rest) lenv2

end

end LeanJS.Semantics
