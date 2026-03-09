import LeanJS.JS.AST
import LeanJS.IR.Core

set_option maxHeartbeats 800000

namespace LeanJS.Trans.IRToJS

open LeanJS.JS
open LeanJS.IR

/-- Translation state for IR→JS -/
structure IRToJSState where
  refVars : List String := []
  counter : Nat := 0
  deriving Inhabited

abbrev IRToJSM := StateT IRToJSState (Except String)

def addRefVar (name : String) : IRToJSM Unit :=
  modify fun st => { st with refVars := name :: st.refVars }

def irBinOpToJS : IRBinOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div
  | .mod => .mod | .exp => .exp
  | .eq => .strictEq | .neq => .strictNeq
  | .lt => .lt | .lte => .lte | .gt => .gt | .gte => .gte
  | .and => .and | .or => .or
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor
  | .shl => .shl | .shr => .shr | .ushr => .ushr
  | .strConcat => .add

def irUnaryOpToJS : IRUnaryOp → UnaryOp
  | .neg => .neg | .not => .not | .bitNot => .bitNot | .typeof => .typeof

def irLitToJS : IRLit → Literal
  | .number n => .number n | .string s => .string s
  | .bool b => .bool b | .unit => .undefined

def isUndefined : Expr → Bool
  | .literal .undefined => true
  | _ => false

mutual

partial def translateExpr (e : IRExpr) : IRToJSM Expr := do
  match e with
  | .lit val => return .literal (irLitToJS val)
  | .var name => return .ident name
  | .undefined => return .literal .undefined
  | .this => return .this

  | .«let» name _ty value body =>
    match value with
    | .mkRef inner =>
      addRefVar name
      let initJS ← translateExpr inner
      let bodyJS ← translateExpr body
      -- Use IIFE: (name => body)(init)
      return .call (.arrowFunction [.ident name none] (.expr bodyJS) false) [initJS]
    | .lam fnName params _caps fnBody async_ gen =>
      let bodyExprJS ← translateExpr body
      let fnJS ← translateFuncExpr fnName params fnBody async_ gen
      return .call (.arrowFunction [.ident name none] (.expr bodyExprJS) false) [fnJS]
    | _ =>
      let initJS ← translateExpr value
      let bodyJS ← translateExpr body
      return .call (.arrowFunction [.ident name none] (.expr bodyJS) false) [initJS]

  | .lam name params _caps body async_ gen =>
    translateFuncExpr name params body async_ gen

  | .app func args =>
    let fJS ← translateExpr func
    let aJS ← args.mapM translateExpr
    return .call fJS aJS

  | .binOp op left right =>
    let l ← translateExpr left
    let r ← translateExpr right
    return .binary (irBinOpToJS op) l r

  | .unaryOp op arg =>
    let a ← translateExpr arg
    return .unary (irUnaryOpToJS op) a

  | .mkRef value => translateExpr value
  | .deref ref => translateExpr ref

  | .assign ref value =>
    let v ← translateExpr value
    match ref with
    | .var name => return .assign .assign (.expr (.ident name)) v
    | .project obj field =>
      let o ← translateExpr obj
      return .assign .assign (.expr (.member o (.ident field))) v
    | _ =>
      let r ← translateExpr ref
      return .assign .assign (.expr r) v

  | .record fields =>
    let props ← fields.mapM fun (name, val) => do
      let v ← translateExpr val
      return Property.prop (.ident name) v .init false false
    return .object props

  | .project expr field =>
    let e ← translateExpr expr
    return .member e (.ident field)

  | .projectIdx expr idx =>
    let e ← translateExpr expr
    let i ← translateExpr idx
    return .member e (.computed i)

  | .array elements =>
    let elems ← elements.mapM fun e => do
      let v ← translateExpr e
      return some v
    return .array elems

  | .index arr idx =>
    let a ← translateExpr arr
    let i ← translateExpr idx
    return .member a (.computed i)

  | .«if» cond then_ else_ =>
    let c ← translateExpr cond
    let t ← translateExpr then_
    let e ← translateExpr else_
    return .conditional c t e

  | .loop _cond _body => return .literal .undefined
  | .seq exprs =>
    match exprs with
    | [] => return .literal .undefined
    | [e] => translateExpr e
    | _ =>
      let jsExprs ← exprs.mapM translateExpr
      let filtered := jsExprs.filter (! isUndefined ·)
      match filtered with
      | [] => return .literal .undefined
      | [e] => return e
      | _ => return .sequence filtered

  | .«return» value => translateExpr value
  | .«break» => return .literal .undefined
  | .«continue» => return .literal .undefined
  | .throw value => translateExpr value
  | .tryCatch _ _ _ _ => return .literal .undefined
  | .«match» scrutinee cases =>
    let s ← translateExpr scrutinee
    translateMatchExpr s cases
  | .construct name args =>
    let aJS ← args.mapM translateExpr
    return .call (.ident name) aJS
  | .newObj callee args =>
    let c ← translateExpr callee
    let a ← args.mapM translateExpr
    return .new c a
  | .«await» expr =>
    let e ← translateExpr expr
    return .await e
  | .«yield» expr delegate =>
    let e ← match expr with
      | some ex => do let v ← translateExpr ex; pure (some v)
      | none => pure none
    return .yield e delegate
  | .spread expr =>
    let e ← translateExpr expr
    return .spread e
  | .ternary cond then_ else_ =>
    let c ← translateExpr cond
    let t ← translateExpr then_
    let e ← translateExpr else_
    return .conditional c t e

partial def translateFuncExpr (name : Option String) (params : List (String × IRType))
    (body : IRExpr) (async_ : Bool := false) (generator : Bool := false) : IRToJSM Expr := do
  let paramPats := params.map fun (n, _) => Pattern.ident n none
  let bodyStmts ← translateToStmts body
  return .function name paramPats bodyStmts async_ generator

partial def translateToStmts (e : IRExpr) : IRToJSM (List Stmt) := do
  match e with
  | .seq exprs =>
    let stmtLists ← exprs.mapM translateToStmts
    return stmtLists.flatten

  | .«let» name _ty value body =>
    let kind : VarKind := match value with
      | .mkRef _ => .let
      | _ => .const
    let initExpr ← match value with
      | .mkRef inner => translateExpr inner
      | .lam fnName params _caps fnBody async_ gen => translateFuncExpr fnName params fnBody async_ gen
      | _ => translateExpr value
    match value with
    | .mkRef _ => addRefVar name
    | _ => pure ()
    let bodyStmts ← translateToStmts body
    return [.varDecl kind [.mk (.ident name none) (some initExpr)]] ++ bodyStmts

  | .«if» cond then_ else_ =>
    let c ← translateExpr cond
    let tStmts ← translateToStmts then_
    let eStmts ← translateToStmts else_
    let hasElse := !eStmts.isEmpty &&
      !(eStmts.length == 1 && match eStmts.head? with
        | some (.expr (.literal .undefined)) => true | _ => false)
    let alt := if hasElse then some (Stmt.block eStmts) else none
    return [.ifStmt c (.block tStmts) alt]

  | .loop cond body =>
    let c ← translateExpr cond
    let bStmts ← translateToStmts body
    return [.while_ c (.block bStmts)]

  | .«return» value =>
    let v ← translateExpr value
    if isUndefined v then return [.return_ none]
    else return [.return_ (some v)]

  | .throw value =>
    let v ← translateExpr value
    return [.throw v]

  | .«break» => return [.break_ none]
  | .«continue» => return [.continue_ none]

  | .tryCatch body catchVar handler finalizer =>
    let bodyStmts ← translateToStmts body
    let handlerStmts ← translateToStmts handler
    let catchParam := catchVar.map fun n => Pattern.ident n none
    let finalizerStmts ← match finalizer with
      | some f => do let s ← translateToStmts f; pure (some s)
      | none => pure none
    let handlerClause := if handlerStmts.isEmpty && catchVar.isNone then none
      else some (CatchClause.mk catchParam handlerStmts)
    return [.try_ bodyStmts handlerClause finalizerStmts]

  | .«match» scrutinee cases =>
    let s ← translateExpr scrutinee
    translateMatchStmts s cases

  | .assign ref value =>
    let v ← translateExpr value
    match ref with
    | .var name => return [.expr (.assign .assign (.expr (.ident name)) v)]
    | .project obj field =>
      let o ← translateExpr obj
      return [.expr (.assign .assign (.expr (.member o (.ident field))) v)]
    | _ =>
      let r ← translateExpr ref
      return [.expr (.assign .assign (.expr r) v)]

  | _ =>
    let expr ← translateExpr e
    if isUndefined expr then return []
    else return [.expr expr]

/-- Translate match cases to expression form (nested ternary) -/
partial def translateMatchExpr (scrutinee : Expr) (cases : List IRMatchCase)
    : IRToJSM Expr := do
  match cases with
  | [] => return .literal .undefined
  | [.mk pat body] =>
    match pat with
    | .wildcard =>
      translateExpr body
    | .var name =>
      let b ← translateExpr body
      return .call (.arrowFunction [.ident name none] (.expr b) false) [scrutinee]
    | .lit litVal =>
      let b ← translateExpr body
      let cond := Expr.binary .strictEq scrutinee (.literal (irLitToJS litVal))
      return .conditional cond b (.literal .undefined)
    | .constructor tag bindings =>
      let b ← translateExpr body
      let cond := Expr.binary .strictEq
        (.member scrutinee (.ident "_tag"))
        (.literal (.string tag))
      -- Wrap in IIFE to bind extracted fields
      let mut innerBody := b
      for (binding, idx) in bindings.zipIdx.reverse do
        let extract := Expr.member scrutinee (.computed (.literal (.number (Float.ofNat idx))))
        innerBody := .call (.arrowFunction [.ident binding none] (.expr innerBody) false) [extract]
      return .conditional cond innerBody (.literal .undefined)
  | (.mk pat body) :: rest =>
    let restExpr ← translateMatchExpr scrutinee rest
    match pat with
    | .wildcard =>
      translateExpr body
    | .var name =>
      let b ← translateExpr body
      return .call (.arrowFunction [.ident name none] (.expr b) false) [scrutinee]
    | .lit litVal =>
      let b ← translateExpr body
      let cond := Expr.binary .strictEq scrutinee (.literal (irLitToJS litVal))
      return .conditional cond b restExpr
    | .constructor tag bindings =>
      let b ← translateExpr body
      let cond := Expr.binary .strictEq
        (.member scrutinee (.ident "_tag"))
        (.literal (.string tag))
      let mut innerBody := b
      for (binding, idx) in bindings.zipIdx.reverse do
        let extract := Expr.member scrutinee (.computed (.literal (.number (Float.ofNat idx))))
        innerBody := .call (.arrowFunction [.ident binding none] (.expr innerBody) false) [extract]
      return .conditional cond innerBody restExpr

/-- Translate match cases to statement form (nested if-else) -/
partial def translateMatchStmts (scrutinee : Expr) (cases : List IRMatchCase)
    : IRToJSM (List Stmt) := do
  match cases with
  | [] => return []
  | [.mk pat body] =>
    match pat with
    | .wildcard =>
      translateToStmts body
    | .var name =>
      let bodyStmts ← translateToStmts body
      return [.varDecl .const [.mk (.ident name none) (some scrutinee)]] ++ bodyStmts
    | .lit litVal =>
      let bodyStmts ← translateToStmts body
      let cond := Expr.binary .strictEq scrutinee (.literal (irLitToJS litVal))
      return [.ifStmt cond (.block bodyStmts) none]
    | .constructor tag bindings =>
      let bodyStmts ← translateToStmts body
      let cond := Expr.binary .strictEq
        (.member scrutinee (.ident "_tag"))
        (.literal (.string tag))
      let mut extracts : List Stmt := []
      for (binding, idx) in bindings.zipIdx do
        let extract := Expr.member scrutinee (.computed (.literal (.number (Float.ofNat idx))))
        extracts := extracts ++ [.varDecl .const [.mk (.ident binding none) (some extract)]]
      return [.ifStmt cond (.block (extracts ++ bodyStmts)) none]
  | (.mk pat body) :: rest =>
    let restStmts ← translateMatchStmts scrutinee rest
    let restBlock := if restStmts.isEmpty then none else some (Stmt.block restStmts)
    match pat with
    | .wildcard =>
      translateToStmts body
    | .var name =>
      let bodyStmts ← translateToStmts body
      let stmts := [Stmt.varDecl .const [.mk (.ident name none) (some scrutinee)]] ++ bodyStmts
      return stmts
    | .lit litVal =>
      let bodyStmts ← translateToStmts body
      let cond := Expr.binary .strictEq scrutinee (.literal (irLitToJS litVal))
      return [.ifStmt cond (.block bodyStmts) restBlock]
    | .constructor tag bindings =>
      let bodyStmts ← translateToStmts body
      let cond := Expr.binary .strictEq
        (.member scrutinee (.ident "_tag"))
        (.literal (.string tag))
      let mut extracts : List Stmt := []
      for (binding, idx) in bindings.zipIdx do
        let extract := Expr.member scrutinee (.computed (.literal (.number (Float.ofNat idx))))
        extracts := extracts ++ [.varDecl .const [.mk (.ident binding none) (some extract)]]
      return [.ifStmt cond (.block (extracts ++ bodyStmts)) restBlock]

end

/-- Translate an IR expression to JS statements -/
def translateToJS (ir : IRExpr) : Except String (List Stmt) := do
  let (stmts, _) ← (translateToStmts ir).run {}
  return stmts

/-- Translate an IR declaration to JS statements -/
partial def translateDeclToJS (d : IRDecl) : IRToJSM (List Stmt) := do
  match d with
  | .funcDecl name params _retTy body async_ gen =>
    let paramPats := params.map fun (n, _) => Pattern.ident n none
    let bodyStmts ← translateToStmts body
    return [.funcDecl name paramPats bodyStmts async_ gen]
  | .letDecl name _ty value =>
    let v ← translateExpr value
    return [.varDecl .const [.mk (.ident name none) (some v)]]
  | .classDecl name parent fields methods =>
    let superExpr := parent.map fun p => Expr.ident p
    let mut members : List ClassMember := []
    -- Constructor with fields
    if !fields.isEmpty then
      let paramPats := fields.map fun (n, _) => Pattern.ident n none
      let bodyStmts := fields.map fun (n, _) =>
        Stmt.expr (.assign .assign (.expr (.member .this (.ident n))) (.ident n))
      members := members ++ [.method (.ident "constructor") paramPats bodyStmts .method false false]
    -- Methods
    for (mname, mbody) in methods do
      let mStmts ← translateToStmts mbody
      members := members ++ [.method (.ident mname) [] mStmts .method false false]
    return [.classDecl name superExpr members]
  | .typeDecl _name _ty =>
    return []  -- Type declarations don't produce JS output
  | .importDecl specs source =>
    let jsSpecs := specs.map fun s => match s with
      | .default_ n => ImportSpecifier.default_ n
      | .named imp loc => ImportSpecifier.named imp loc
      | .namespace n => ImportSpecifier.namespace n
    return [.importDecl jsSpecs source]
  | .exportDecl names source =>
    let jsSpecs := names.map fun (loc, exp) => ExportSpecifier.mk loc exp
    return [.exportNamed none jsSpecs source]
  | .exportDefault value =>
    let v ← translateExpr value
    return [.exportDefault (.expr v)]

/-- Translate an IR module to JS statements -/
def translateModuleToJS (m : IRModule) : Except String (List Stmt) := do
  let mut allStmts : List Stmt := []
  for d in m.decls do
    let (stmts, _) ← (translateDeclToJS d).run {}
    allStmts := allStmts ++ stmts
  return allStmts

end LeanJS.Trans.IRToJS
