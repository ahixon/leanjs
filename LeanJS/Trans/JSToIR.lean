import LeanJS.JS.AST
import LeanJS.IR.Core

set_option maxHeartbeats 800000

namespace LeanJS.Trans.JSToIR

open LeanJS.JS
open LeanJS.IR

/-- Translation environment -/
structure TransEnv where
  /-- Variables known to be mutated (need ref wrapping) -/
  mutated : List String := []
  /-- Variables in scope -/
  scope : List String := []
  /-- Counter for generating fresh names -/
  freshCounter : Nat := 0
  deriving Inhabited

/-- Translation monad -/
abbrev TransM := StateT TransEnv (Except String)

/-- Check if a variable is mutated -/
def isMutated (name : String) : TransM Bool := do
  let env ← get
  return name ∈ env.mutated

/-- Mark a variable as mutated -/
def markMutated (name : String) : TransM Unit :=
  modify fun env => { env with mutated := name :: env.mutated }

/-- Add variable to scope -/
def addToScope (name : String) : TransM Unit :=
  modify fun env => { env with scope := name :: env.scope }

/-- Generate a fresh temporary variable name -/
def freshName (prefix_ : String := "__tmp") : TransM String := do
  let env ← get
  modify fun e => { e with freshCounter := e.freshCounter + 1 }
  return s!"{prefix_}{env.freshCounter}"

-- ============================================================
-- Mutation analysis: scan JS AST to find assigned variables
-- ============================================================

mutual

/-- Collect all variables that are assigned to (mutated) in an expression -/
partial def collectMutatedExpr (e : Expr) : List String :=
  match e with
  | .assign _op target _right =>
    let targetVars := match target with
      | .expr (.ident name) => [name]
      | _ => []
    targetVars ++ collectMutatedExpr (match target with | .expr e => e | _ => .literal .null)
      ++ collectMutatedExpr _right
  | .update _op arg _prefix =>
    match arg with
    | .ident name => [name]
    | _ => collectMutatedExpr arg
  | .binary _ l r => collectMutatedExpr l ++ collectMutatedExpr r
  | .unary _ arg => collectMutatedExpr arg
  | .call callee args =>
    collectMutatedExpr callee ++ args.flatMap collectMutatedExpr
  | .new callee args =>
    collectMutatedExpr callee ++ args.flatMap collectMutatedExpr
  | .member obj _ => collectMutatedExpr obj
  | .conditional t c a => collectMutatedExpr t ++ collectMutatedExpr c ++ collectMutatedExpr a
  | .array elems => elems.flatMap fun e => match e with | some x => collectMutatedExpr x | none => []
  | .object props => props.flatMap collectMutatedProp
  | .function _ _ body _ _ => body.flatMap collectMutatedStmt
  | .arrowFunction _ body _ =>
    match body with
    | .expr e => collectMutatedExpr e
    | .block stmts => stmts.flatMap collectMutatedStmt
  | .await arg => collectMutatedExpr arg
  | .yield (some arg) _ => collectMutatedExpr arg
  | .yield none _ => []
  | .sequence exprs => exprs.flatMap collectMutatedExpr
  | .paren inner => collectMutatedExpr inner
  | .spread arg => collectMutatedExpr arg
  | .template _ _ exprs => exprs.flatMap collectMutatedExpr
  | _ => []

partial def collectMutatedStmt (s : Stmt) : List String :=
  match s with
  | .expr e => collectMutatedExpr e
  | .block body => body.flatMap collectMutatedStmt
  | .return_ (some e) => collectMutatedExpr e
  | .throw e => collectMutatedExpr e
  | .ifStmt t c a =>
    collectMutatedExpr t ++ collectMutatedStmt c ++
    (match a with | some s => collectMutatedStmt s | none => [])
  | .while_ t body => collectMutatedExpr t ++ collectMutatedStmt body
  | .doWhile body t => collectMutatedStmt body ++ collectMutatedExpr t
  | .for_ init test update body =>
    (match init with
     | some (.expr e) => collectMutatedExpr e
     | some (.varDecl _ decls) => decls.flatMap fun d => match d with
       | .mk _ (some e) => collectMutatedExpr e | _ => []
     | none => []) ++
    (match test with | some e => collectMutatedExpr e | none => []) ++
    (match update with | some e => collectMutatedExpr e | none => []) ++
    collectMutatedStmt body
  | .forIn _ right body => collectMutatedExpr right ++ collectMutatedStmt body
  | .forOf _ right body => collectMutatedExpr right ++ collectMutatedStmt body
  | .switch disc cases =>
    collectMutatedExpr disc ++ cases.flatMap fun c => match c with
      | .mk (some t) stmts => collectMutatedExpr t ++ stmts.flatMap collectMutatedStmt
      | .mk none stmts => stmts.flatMap collectMutatedStmt
  | .try_ block handler finalizer =>
    block.flatMap collectMutatedStmt ++
    (match handler with
     | some (.mk _ body) => body.flatMap collectMutatedStmt
     | none => []) ++
    (match finalizer with
     | some body => body.flatMap collectMutatedStmt
     | none => [])
  | .labeled _ body => collectMutatedStmt body
  | .varDecl _ decls => decls.flatMap fun d => match d with
    | .mk _ (some e) => collectMutatedExpr e | _ => []
  | .funcDecl _ _ body _ _ => body.flatMap collectMutatedStmt
  | .classDecl _ superClass members =>
    (match superClass with | some e => collectMutatedExpr e | none => []) ++
    members.flatMap fun m => match m with
      | .method _ _ body _ _ _ => body.flatMap collectMutatedStmt
      | .property _ (some e) _ _ => collectMutatedExpr e
      | _ => []
  | _ => []

partial def collectMutatedProp (p : Property) : List String :=
  match p with
  | .prop _ v _ _ _ => collectMutatedExpr v
  | .method _ _ body _ _ _ _ => body.flatMap collectMutatedStmt

end

/-- Collect all mutated variables in a list of statements -/
def collectAllMutated (stmts : List Stmt) : List String :=
  (stmts.flatMap collectMutatedStmt).eraseDups

-- ============================================================
-- JS AST → IR translation
-- ============================================================

/-- Convert JS BinOp to IR BinOp -/
def translateBinOp : BinOp → IRBinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div
  | .mod => .mod | .exp => .exp
  | .eq | .strictEq => .eq | .neq | .strictNeq => .neq
  | .lt => .lt | .lte => .lte | .gt => .gt | .gte => .gte
  | .and => .and | .or => .or
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor
  | .shl => .shl | .shr => .shr | .ushr => .ushr
  | .nullishCoalesce => .or  -- simplified
  | .in => .eq              -- simplified
  | .instanceof => .eq     -- simplified

/-- Convert JS UnaryOp to IR UnaryOp -/
def translateUnaryOp : UnaryOp → IRUnaryOp
  | .neg => .neg | .pos => .neg  -- +x simplified (identity for numbers)
  | .not => .not | .bitNot => .bitNot
  | .typeof => .typeof
  | .void => .not  -- simplified
  | .delete => .not  -- simplified

/-- Convert JS AssignOp to optional IR BinOp (for compound assignment) -/
def assignOpToBinOp : AssignOp → Option IRBinOp
  | .assign => none
  | .addAssign => some .add | .subAssign => some .sub
  | .mulAssign => some .mul | .divAssign => some .div
  | .modAssign => some .mod | .expAssign => some .exp
  | .andAssign => some .and | .orAssign => some .or
  | .bitAndAssign => some .bitAnd | .bitOrAssign => some .bitOr
  | .bitXorAssign => some .bitXor
  | .shlAssign => some .shl | .shrAssign => some .shr
  | .ushrAssign => some .ushr
  | .nullishAssign => some .or

/-- Convert JS literal to IR literal -/
def translateLit : Literal → IRLit
  | .number n => .number n
  | .string s => .string s
  | .bool b => .bool b
  | .null => .unit
  | .undefined => .unit
  | .regex _p _f => .string "<regex>"

/-- Thread let-bindings so that variable declarations scope over subsequent expressions -/
partial def threadLets : List IRExpr → IRExpr
  | [] => .undefined
  | [e] => e
  | (.«let» name ty val _) :: rest =>
    .«let» name ty val (threadLets rest)
  | e :: rest => .seq [e, threadLets rest]

/-- Get the name from a pattern (simplified — just identifiers for now) -/
def patternName : Pattern → Option String
  | .ident name _ => some name
  | _ => none

mutual

/-- Translate a JS expression to IR -/
partial def translateExpr (e : Expr) : TransM IRExpr := do
  match e with
  | .ident name =>
    let mut_ ← isMutated name
    if mut_ then return .deref (.var name)
    else return .var name
  | .literal lit => return .lit (translateLit lit)
  | .this => return .this
  | .paren inner => translateExpr inner
  | .array elements =>
    let elems ← elements.mapM fun e => match e with
      | some x => translateExpr x
      | none => pure .undefined
    return .array elems
  | .object props =>
    let fields ← props.mapM translateProperty
    return .record fields
  | .function name params body async_ gen =>
    let paramNames := params.filterMap patternName
    let irParams := paramNames.map (·, IRType.any)
    let irBody ← translateBody body
    return .lam name irParams [] irBody async_ gen
  | .arrowFunction params body async_ =>
    let paramNames := params.filterMap patternName
    let irParams := paramNames.map (·, IRType.any)
    let irBody ← match body with
      | .expr e => translateExpr e
      | .block stmts => translateBody stmts
    return .lam none irParams [] irBody async_ false
  | .binary op left right =>
    let l ← translateExpr left
    let r ← translateExpr right
    return .binOp (translateBinOp op) l r
  | .unary op arg =>
    let a ← translateExpr arg
    match op with
    | .pos => return a  -- +x is identity
    | .void => return .seq [a, .undefined]
    | .delete => return .seq [a, .lit (.bool true)]
    | _ => return .unaryOp (translateUnaryOp op) a
  | .update op arg prefix_ =>
    match arg with
    | .ident name =>
      let irOp := match op with | .inc => IRBinOp.add | .dec => IRBinOp.sub
      let one := IRExpr.lit (.number 1.0)
      let cur := IRExpr.deref (.var name)
      let newVal := IRExpr.binOp irOp cur one
      if prefix_ then
        return .seq [.assign (.var name) newVal, .deref (.var name)]
      else
        return .«let» "__old" .any cur
          (.seq [.assign (.var name) newVal, .var "__old"])
    | _ =>
      let a ← translateExpr arg
      return .binOp (match op with | .inc => .add | .dec => .sub) a (.lit (.number 1.0))
  | .assign op target right =>
    let rhs ← translateExpr right
    match target with
    | .expr (.ident name) =>
      match assignOpToBinOp op with
      | none => return .assign (.var name) rhs
      | some binop =>
        let cur := IRExpr.deref (.var name)
        return .assign (.var name) (.binOp binop cur rhs)
    | .expr (.member obj prop) =>
      let irObj ← translateExpr obj
      let field := match prop with
        | .ident n => n
        | .computed _ => "__computed"
      match assignOpToBinOp op with
      | none => return .seq [.assign (.project irObj field) rhs, rhs]
      | some binop =>
        let cur := IRExpr.project irObj field
        return .assign (.project irObj field) (.binOp binop cur rhs)
    | _ => return rhs
  | .conditional test cons alt =>
    let t ← translateExpr test
    let c ← translateExpr cons
    let a ← translateExpr alt
    return .«if» t c a
  | .call callee args =>
    let c ← translateExpr callee
    let a ← args.mapM translateExpr
    return .app c a
  | .new callee args =>
    let c ← translateExpr callee
    let a ← args.mapM translateExpr
    return .newObj c a
  | .member obj prop =>
    let o ← translateExpr obj
    match prop with
    | .ident name => return .project o name
    | .computed idx =>
      let i ← translateExpr idx
      return .projectIdx o i
  | .sequence exprs =>
    let es ← exprs.mapM translateExpr
    return .seq es
  | .template _tag quasis expressions =>
    -- Translate template literal to string concatenation
    let mut result : IRExpr := .lit (.string "")
    for (q, i) in quasis.zipIdx do
      if !q.isEmpty then
        result := .binOp .strConcat result (.lit (.string q))
      if h : i < expressions.length then
        let e ← translateExpr expressions[i]
        result := .binOp .strConcat result e
    return result
  | .await arg =>
    let a ← translateExpr arg
    return .«await» a
  | .yield arg delegate =>
    let a ← match arg with
      | some e => do let v ← translateExpr e; pure (some v)
      | none => pure none
    return .«yield» a delegate
  | .spread arg =>
    let a ← translateExpr arg
    return .spread a

/-- Translate a JS statement to IR -/
partial def translateStmt (s : Stmt) : TransM IRExpr := do
  match s with
  | .expr e => translateExpr e
  | .block body => translateBody body
  | .empty => return .undefined
  | .return_ arg =>
    match arg with
    | some e =>
      let v ← translateExpr e
      return .«return» v
    | none => return .«return» .undefined
  | .throw arg =>
    let v ← translateExpr arg
    return .throw v
  | .break_ _ => return .«break»
  | .continue_ _ => return .«continue»
  | .ifStmt test cons alt =>
    let t ← translateExpr test
    let c ← translateStmt cons
    let a ← match alt with
      | some s => translateStmt s
      | none => pure .undefined
    return .«if» t c a
  | .while_ test body =>
    let t ← translateExpr test
    let b ← translateStmt body
    return .loop t b
  | .doWhile body test =>
    let b ← translateStmt body
    let t ← translateExpr test
    -- do { body } while (test) → body; while(test) { body }
    return .seq [b, .loop t b]
  | .for_ init test update body =>
    let initIR ← match init with
      | some (.varDecl kind decls) => translateVarDecls kind decls
      | some (.expr e) => translateExpr e
      | none => pure .undefined
    let testIR ← match test with
      | some e => translateExpr e
      | none => pure (.lit (.bool true))
    let updateIR ← match update with
      | some e => translateExpr e
      | none => pure .undefined
    let bodyIR ← translateStmt body
    -- for(init; test; update) body → init; while(test) { body; update }
    return .seq [initIR, .loop testIR (.seq [bodyIR, updateIR])]
  | .forIn left right body =>
    let rightIR ← translateExpr right
    let bodyIR ← translateStmt body
    let varName := match left with
      | .varDecl _ decls => match decls.head? with
        | some (.mk (.ident n _) _) => n
        | _ => "__key"
      | .expr (.ident n) => n
      | _ => "__key"
    return .«let» varName .any .undefined
      (.seq [.loop (.lit (.bool true)) (.seq [
        .assign (.var varName) (.app (.var "__nextKey") [rightIR]),
        bodyIR
      ])])
  | .forOf left right body =>
    let rightIR ← translateExpr right
    let bodyIR ← translateStmt body
    let varName := match left with
      | .varDecl _ decls => match decls.head? with
        | some (.mk (.ident n _) _) => n
        | _ => "__elem"
      | .expr (.ident n) => n
      | _ => "__elem"
    return .«let» varName .any .undefined
      (.seq [.loop (.lit (.bool true)) (.seq [
        .assign (.var varName) (.app (.var "__nextElem") [rightIR]),
        bodyIR
      ])])
  | .switch disc cases =>
    let d ← translateExpr disc
    translateSwitchCases d cases
  | .try_ block handler finalizer =>
    let bodyIR ← translateBody block
    let catchVar := match handler with
      | some (.mk (some (.ident n _)) _) => some n
      | _ => match handler with | some _ => some "__err" | none => none
    let handlerIR ← match handler with
      | some (.mk _ body) => translateBody body
      | none => pure .undefined
    let finalizerIR ← match finalizer with
      | some body => do let b ← translateBody body; pure (some b)
      | none => pure none
    return .tryCatch bodyIR catchVar handlerIR finalizerIR
  | .labeled _label body => translateStmt body
  | .debugger => return .undefined
  | .varDecl kind decls => translateVarDecls kind decls
  | .funcDecl name params body async_ gen =>
    let paramNames := params.filterMap patternName
    let irParams := paramNames.map (·, IRType.any)
    let irBody ← translateBody body
    return .«let» name (.func (irParams.map Prod.snd) .any) (.lam (some name) irParams [] irBody async_ gen) (.var name)
  | .classDecl name superClass members =>
    translateClassDecl name superClass members
  | .importDecl _specs _source => return .undefined
  | .exportNamed (some decl) _ _ => translateStmt decl
  | .exportNamed none _ _ => return .undefined
  | .exportDefault decl => translateStmt decl
  | .exportAll _ => return .undefined

/-- Translate variable declarations -/
partial def translateVarDecls (kind : VarKind) (decls : List VarDeclarator) : TransM IRExpr := do
  let mut result : IRExpr := .undefined
  for d in decls do
    match d with
    | .mk (.ident name _) init =>
      let initVal ← match init with
        | some e => translateExpr e
        | none => pure .undefined
      let mut_ ← isMutated name
      let declExpr := if mut_ || kind == .var then
        -- Mutable: wrap in ref
        IRExpr.«let» name .any (.mkRef initVal) (.var name)
      else
        -- Immutable: plain let
        IRExpr.«let» name .any initVal (.var name)
      result := if result matches .undefined then declExpr
        else .seq [result, declExpr]
    | .mk (.array elements _rest) init =>
      -- Array destructuring: const [a, b, c] = expr
      let initVal ← match init with
        | some e => translateExpr e
        | none => pure .undefined
      let tmp ← freshName
      let mut bindings : IRExpr := .undefined
      for (elem, idx) in elements.zipIdx do
        match elem with
        | some (.ident name _) =>
          let binding := IRExpr.«let» name .any (.index (.var tmp) (.lit (.number (Float.ofNat idx)))) (.var name)
          bindings := if bindings matches .undefined then binding else .seq [bindings, binding]
        | _ => pure ()
      let declExpr := IRExpr.«let» tmp .any initVal bindings
      result := if result matches .undefined then declExpr else .seq [result, declExpr]
    | .mk (.object props _rest) init =>
      -- Object destructuring: const {a, b} = expr
      let initVal ← match init with
        | some e => translateExpr e
        | none => pure .undefined
      let tmp ← freshName
      let mut bindings : IRExpr := .undefined
      for prop in props do
        match prop with
        | .shorthand name dflt =>
          let access := IRExpr.project (.var tmp) name
          let binding := match dflt with
            | some d =>
              let dIR := IRExpr.lit (.string "TODO")  -- simplified default
              let _ := d  -- suppress unused warning
              IRExpr.«let» name .any (.ternary (.binOp .neq access .undefined) access dIR) (.var name)
            | none =>
              IRExpr.«let» name .any access (.var name)
          bindings := if bindings matches .undefined then binding else .seq [bindings, binding]
        | .keyVal key (.ident name _) _ =>
          let field := match key with
            | .ident n => n
            | .literal (.string s) => s
            | _ => "__computed"
          let access := IRExpr.project (.var tmp) field
          let binding := IRExpr.«let» name .any access (.var name)
          bindings := if bindings matches .undefined then binding else .seq [bindings, binding]
        | _ => pure ()
      let declExpr := IRExpr.«let» tmp .any initVal bindings
      result := if result matches .undefined then declExpr else .seq [result, declExpr]
    | _ =>
      -- Fallback for unsupported patterns
      let initVal ← match d with | .mk _ (some e) => translateExpr e | _ => pure .undefined
      result := .seq [result, initVal]
  return result

/-- Translate a property to an IR field -/
partial def translateProperty (p : Property) : TransM (String × IRExpr) := do
  match p with
  | .prop key value _ _ _shorthand =>
    let fieldName := match key with
      | .ident name => name
      | .literal (.string s) => s
      | _ => "__computed"
    let v ← translateExpr value
    return (fieldName, v)
  | .method key params body _ _ _ _ =>
    let methodName := match key with
      | .ident name => name
      | _ => "__method"
    let paramNames := params.filterMap patternName
    let irParams := paramNames.map (·, IRType.any)
    let irBody ← translateBody body
    return (methodName, .lam (some methodName) irParams [] irBody)

/-- Translate switch cases to nested if-else -/
partial def translateSwitchCases (disc : IRExpr) (cases : List SwitchCase) : TransM IRExpr := do
  match cases with
  | [] => return .undefined
  | (.mk test stmts) :: rest =>
    let bodyIR ← translateBody stmts
    let restIR ← translateSwitchCases disc rest
    match test with
    | some testExpr =>
      let t ← translateExpr testExpr
      return .«if» (.binOp .eq disc t) bodyIR restIR
    | none =>
      -- default case
      return bodyIR

/-- Translate class declaration -/
partial def translateClassDecl (name : String) (superClass : Option Expr)
    (members : List ClassMember) : TransM IRExpr := do
  let mut fields : List (String × IRExpr) := []
  let mut methods : List (String × IRExpr) := []
  for m in members do
    match m with
    | .method key params body kind _static _computed =>
      let methodName := match key with | .ident n => n | _ => "__method"
      let paramNames := params.filterMap patternName
      let irParams := paramNames.map (·, IRType.any)
      let irBody ← translateBody body
      let methodExpr := IRExpr.lam (some methodName) irParams [] irBody false false
      match kind with
      | .method => methods := methods ++ [(methodName, methodExpr)]
      | .get => methods := methods ++ [("get_" ++ methodName, methodExpr)]
      | .set => methods := methods ++ [("set_" ++ methodName, methodExpr)]
    | .property key value _static _computed =>
      let fieldName := match key with | .ident n => n | _ => "__field"
      let v ← match value with
        | some e => translateExpr e
        | none => pure .undefined
      fields := fields ++ [(fieldName, v)]
  let _parentIR ← match superClass with
    | some e => do let p ← translateExpr e; pure (some p)
    | none => pure none
  -- Class → record constructor + methods
  let allFields := fields ++ methods
  return .«let» name .any (.record allFields) (.var name)

/-- Translate a list of statements into a sequenced IR expression -/
partial def translateBody (stmts : List Stmt) : TransM IRExpr := do
  match stmts with
  | [] => return .undefined
  | [s] => translateStmt s
  | _ =>
    -- Collect all mutated vars in this scope
    let mutatedVars := collectAllMutated stmts
    for v in mutatedVars do markMutated v
    let irStmts ← stmts.mapM translateStmt
    -- Thread let-bindings: chain variable declarations
    return threadLets irStmts

end

-- ============================================================
-- Top-level translation
-- ============================================================

/-- Translate a JS program to an IR module -/
partial def extractDecls : IRExpr → List IRDecl
  | .«let» name ty (.lam _n params _caps body async_ gen) rest =>
    [.funcDecl name params ty body async_ gen] ++ extractDecls rest
  | .«let» name ty val rest =>
    [.letDecl name ty val] ++ extractDecls rest
  | .seq exprs => exprs.flatMap extractDecls
  | _ => []

/-- Extract import/export declarations from statements -/
def extractImportExport : List Stmt → List IRDecl
  | [] => []
  | (.importDecl specs source) :: rest =>
    let irSpecs := specs.map fun s => match s with
      | .default_ n => IRImportSpec.default_ n
      | .named imp loc => IRImportSpec.named imp loc
      | .namespace n => IRImportSpec.namespace n
    [.importDecl irSpecs source] ++ extractImportExport rest
  | (.exportNamed none specs source) :: rest =>
    let names := specs.map fun s => match s with
      | .mk loc exp => (loc, exp)
    [.exportDecl names source] ++ extractImportExport rest
  | (.exportDefault decl) :: rest =>
    -- For default exports of expression statements, extract the expression
    let irExpr := match decl with
      | .expr _ => IRExpr.undefined  -- will be translated normally
      | _ => IRExpr.undefined
    [.exportDefault irExpr] ++ extractImportExport rest
  | _ :: rest => extractImportExport rest

def translateProgram (prog : List Stmt) : Except String IRModule := do
  let env : TransEnv := { mutated := collectAllMutated prog }
  let (irExpr, _) ← (translateBody prog).run env
  let importExportDecls := extractImportExport prog
  let decls := importExportDecls ++ extractDecls irExpr
  return { name := "", decls := decls }

/-- Translate a JS program to a single IR expression (simpler for round-trips) -/
def translateToIR (prog : List Stmt) : Except String IRExpr := do
  let env : TransEnv := { mutated := collectAllMutated prog }
  let (irExpr, _) ← (translateBody prog).run env
  return irExpr

end LeanJS.Trans.JSToIR
