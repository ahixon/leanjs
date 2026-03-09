import LeanJS.Lean.AST
import LeanJS.IR.Core

set_option maxHeartbeats 800000

namespace LeanJS.Trans.IRToLean

open LeanJS.IR
open LeanJS.Lean

/-- Translation state -/
structure IRToLeanState where
  refVars : List String := []
  counter : Nat := 0
  deriving Inhabited

abbrev IRToLeanM := StateT IRToLeanState (Except String)

def freshName (prefix_ : String := "_x") : IRToLeanM String := do
  let st ← get
  modify fun s => { s with counter := s.counter + 1 }
  return s!"{prefix_}{st.counter}"

def addRefVar (name : String) : IRToLeanM Unit :=
  modify fun st => { st with refVars := name :: st.refVars }

def isRefVar (name : String) : IRToLeanM Bool := do
  let st ← get
  return name ∈ st.refVars

-- ============================================================
-- Helpers (outside mutual block)
-- ============================================================

/-- Check if an IR expression contains any ref operations (mutation, loops) -/
partial def containsRefs : IRExpr → Bool
  | .mkRef _ => true
  | .deref _ => true
  | .assign _ _ => true
  | .loop _ _ => true
  | .«let» _ _ val body => containsRefs val || containsRefs body
  | .lam _ _ _ body _ _ => containsRefs body
  | .app func args => containsRefs func || args.any containsRefs
  | .binOp _ l r => containsRefs l || containsRefs r
  | .unaryOp _ a => containsRefs a
  | .«if» c t e => containsRefs c || containsRefs t || containsRefs e
  | .seq exprs => exprs.any containsRefs
  | .«return» v => containsRefs v
  | .throw v => containsRefs v
  | .tryCatch body _ handler fin =>
    containsRefs body || containsRefs handler ||
    (match fin with | some f => containsRefs f | none => false)
  | .record fields => fields.any (containsRefs ·.2)
  | .array elems => elems.any containsRefs
  | .project e _ => containsRefs e
  | .projectIdx e i => containsRefs e || containsRefs i
  | .index a i => containsRefs a || containsRefs i
  | .ternary c t e => containsRefs c || containsRefs t || containsRefs e
  | .«match» s cases =>
    containsRefs s || cases.any fun c => match c with | .mk _ b => containsRefs b
  | .construct _ args => args.any containsRefs
  | .newObj c args => containsRefs c || args.any containsRefs
  | .«await» e => containsRefs e
  | .«yield» (some e) _ => containsRefs e
  | .«yield» none _ => false
  | .spread e => containsRefs e
  | _ => false

/-- Translate IRType to LeanType -/
partial def translateType : IRType → LeanType
  | .any => .hole
  | .number => .name "Float"
  | .string => .name "String"
  | .bool => .name "Bool"
  | .unit => .name "Unit"
  | .func params ret =>
    params.foldr (fun p acc => .arrow (translateType p) acc) (translateType ret)
  | .record _fields => .hole
  | .array elem => .app (.name "Array") (translateType elem)
  | .ref inner => .app (.name "IO.Ref") (translateType inner)
  | .option inner => .app (.name "Option") (translateType inner)
  | .union _ _ => .hole

/-- Translate IRType to optional LeanType (None for .any) -/
def translateTypeOpt : IRType → Option LeanType
  | .any => none
  | t => some (translateType t)

/-- Map IR binary op to Lean operator string -/
def irBinOpToLean : IRBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .mod => "%" | .exp => "^"
  | .eq => "==" | .neq => "!=" | .lt => "<" | .lte => "<="
  | .gt => ">" | .gte => ">="
  | .and => "&&" | .or => "||"
  | .bitAnd => "&&&" | .bitOr => "|||" | .bitXor => "^^^"
  | .shl => "<<<" | .shr => ">>>" | .ushr => ">>>"
  | .strConcat => "++"

/-- Map IR unary op to Lean operator string -/
def irUnaryOpToLean : IRUnaryOp → String
  | .neg => "-" | .not => "!" | .bitNot => "~~~" | .typeof => "typeof "

/-- Translate IR pattern to Lean pattern -/
def translatePattern : IRPattern → LeanPattern
  | .wildcard => .wildcard
  | .var name => .var name
  | .lit (.number n) =>
    if n == Float.ofNat n.toUInt64.toNat && n >= 0 then
      .lit (.natVal n.toUInt64.toNat)
    else .lit (.float n)
  | .lit (.string s) => .lit (.string s)
  | .lit (.bool b) => .lit (.bool b)
  | .lit .unit => .constructor "Unit.unit" []
  | .constructor tag bindings => .constructor tag (bindings.map .var)

-- ============================================================
-- Main translation (mutual block)
-- ============================================================

mutual

/-- Translate IR expression to Lean expression (pure context) -/
partial def translateExpr (e : IRExpr) : IRToLeanM LeanExpr := do
  match e with
  | .lit (.number n) =>
    if n == Float.ofNat n.toUInt64.toNat && n >= 0 && n < 1e15 then
      return .lit (.natVal n.toUInt64.toNat)
    else return .lit (.float n)
  | .lit (.string s) => return .lit (.string s)
  | .lit (.bool b) => return .lit (.bool b)
  | .lit .unit => return .unit

  | .var name =>
    let isRef ← isRefVar name
    if isRef then
      return .refGet (.ident name)
    else
      return .ident name

  | .undefined => return .unit

  | .this => return .ident "self"

  | .«let» name _ty value body =>
    if containsRefs value || containsRefs body then
      let doElems ← translateExprDo e
      return .doBlock doElems
    else
      match value with
      | .mkRef _inner =>
        addRefVar name
        let doElems ← translateExprDo e
        return .doBlock doElems
      | .lam fnName params _caps fnBody _ _ =>
        let lamExpr ← translateLambda fnName params fnBody
        let bodyExpr ← translateExpr body
        return .«let» name none lamExpr bodyExpr
      | _ =>
        let valExpr ← translateExpr value
        let bodyExpr ← translateExpr body
        return .«let» name none valExpr bodyExpr

  | .lam name params _caps body _ _ =>
    translateLambda name params body

  | .app func args =>
    let fExpr ← translateExpr func
    let mut result := fExpr
    for arg in args do
      let aExpr ← translateExpr arg
      result := .app result aExpr
    return result

  | .binOp op left right =>
    let l ← translateExpr left
    let r ← translateExpr right
    return .binOp (irBinOpToLean op) l r

  | .unaryOp op arg =>
    let a ← translateExpr arg
    return .unaryOp (irUnaryOpToLean op) a

  | .mkRef value =>
    let v ← translateExpr value
    return .refNew v

  | .deref ref =>
    let r ← translateExpr ref
    return .refGet r

  | .assign _ref _value =>
    let doElems ← translateExprDo e
    return .doBlock doElems

  | .record fields =>
    let leanFields ← fields.mapM fun (name, val) => do
      let v ← translateExpr val
      return (name, v)
    return .structLit none leanFields

  | .project expr field =>
    let e ← translateExpr expr
    return .proj e field

  | .projectIdx expr idx =>
    let e ← translateExpr expr
    let i ← translateExpr idx
    return .arrayIdx e i

  | .array elements =>
    let elems ← elements.mapM translateExpr
    return .arrayLit elems

  | .index arr idx =>
    let a ← translateExpr arr
    let i ← translateExpr idx
    return .arrayIdx a i

  | .«if» cond then_ else_ =>
    let c ← translateExpr cond
    let t ← translateExpr then_
    let e ← translateExpr else_
    return .«if» c t (some e)

  | .loop _cond _body =>
    let doElems ← translateExprDo e
    return .doBlock doElems

  | .seq exprs =>
    match exprs with
    | [] => return .unit
    | [e] => translateExpr e
    | _ =>
      if exprs.any containsRefs then
        let doElems ← translateSeqDo exprs
        return .doBlock doElems
      else
        -- Pure sequence: fold into lets
        translatePureSeq exprs

  | .«return» value =>
    let v ← translateExpr value
    return .«return» v

  | .«break» => return .ident "break"
  | .«continue» => return .ident "continue"

  | .throw value =>
    let v ← translateExpr value
    return .«throw» v

  | .tryCatch _body _catchVar _handler _finalizer =>
    let doElems ← translateExprDo e
    return .doBlock doElems

  | .«match» scrutinee cases =>
    let s ← translateExpr scrutinee
    let alts ← cases.mapM fun c => do
      match c with
      | .mk pat body =>
        let b ← translateExpr body
        return LeanMatchAlt.mk (translatePattern pat) b
    return .«match» s alts

  | .construct name args =>
    let mut result : LeanExpr := .ident name
    for arg in args do
      let a ← translateExpr arg
      result := .app result a
    return result

  | .newObj callee args =>
    let c ← translateExpr callee
    let mut result := c
    for arg in args do
      let a ← translateExpr arg
      result := .app result a
    return result

  | .«await» expr =>
    -- await → monadic bind
    let e ← translateExpr expr
    return .bind "result" none e

  | .«yield» expr _ =>
    -- yield → pure (simplified)
    match expr with
    | some ex => translateExpr ex
    | none => return .unit

  | .spread expr =>
    let e ← translateExpr expr
    return e

  | .ternary cond then_ else_ =>
    let c ← translateExpr cond
    let t ← translateExpr then_
    let e ← translateExpr else_
    return .«if» c t (some e)

/-- Translate IR expression to do-block elements (monadic context) -/
partial def translateExprDo (e : IRExpr) : IRToLeanM (List LeanDoElem) := do
  match e with
  | .«let» name _ty value body =>
    match value with
    | .mkRef inner =>
      addRefVar name
      let innerExpr ← translateExpr inner
      let bodyElems ← translateExprDo body
      return [.bind name none (.refNew innerExpr)] ++ bodyElems
    | .lam fnName params _caps fnBody _ _ =>
      let lamExpr ← translateLambda fnName params fnBody
      let bodyElems ← translateExprDo body
      return [.letDecl name none lamExpr] ++ bodyElems
    | _ =>
      let valExpr ← translateExpr value
      let bodyElems ← translateExprDo body
      if containsRefs value then
        return [.bind name none valExpr] ++ bodyElems
      else
        return [.letDecl name none valExpr] ++ bodyElems

  | .assign ref value =>
    let v ← translateExpr value
    match ref with
    | .var name =>
      let isRef ← isRefVar name
      if isRef then
        return [.eval (.refSet (.ident name) v)]
      else
        return [.reassign name v]
    | .project obj field =>
      let o ← translateExpr obj
      return [.eval (.refSet (.proj o field) v)]
    | _ =>
      let r ← translateExpr ref
      return [.eval (.refSet r v)]

  | .loop cond body =>
    let c ← translateExpr cond
    let bodyElems ← translateExprDo body
    return [.doWhile c bodyElems]

  | .«if» cond then_ else_ =>
    let c ← translateExpr cond
    let thenElems ← translateExprDo then_
    let elseElems ← translateExprDo else_
    return [.doIf c thenElems elseElems]

  | .«return» value =>
    let v ← translateExpr value
    return [.doReturn v]

  | .throw value =>
    let v ← translateExpr value
    return [.eval (.«throw» v)]

  | .tryCatch body catchVar handler finalizer =>
    let bodyElems ← translateExprDo body
    let handlerElems ← translateExprDo handler
    let finalizerElems ← match finalizer with
      | some f => translateExprDo f
      | none => pure []
    return [.doTry bodyElems catchVar handlerElems finalizerElems]

  | .seq exprs => translateSeqDo exprs

  | .«break» => return [.eval (.ident "break")]
  | .«continue» => return [.eval (.ident "continue")]

  | _ =>
    let expr ← translateExpr e
    match expr with
    | .unit => return []
    | _ => return [.eval expr]

/-- Translate a sequence of IR expressions to do-block elements -/
partial def translateSeqDo (exprs : List IRExpr) : IRToLeanM (List LeanDoElem) := do
  let mut result : List LeanDoElem := []
  for e in exprs do
    let elems ← translateExprDo e
    result := result ++ elems
  return result

/-- Translate a pure sequence (no refs) into nested lets or final expression -/
partial def translatePureSeq (exprs : List IRExpr) : IRToLeanM LeanExpr := do
  match exprs with
  | [] => return .unit
  | [e] => translateExpr e
  | e :: rest =>
    match e with
    | .«let» name ty val _ =>
      let valExpr ← translateExpr val
      let bodyExpr ← translatePureSeq rest
      return .«let» name (translateTypeOpt ty) valExpr bodyExpr
    | _ =>
      let _ ← translateExpr e
      translatePureSeq rest

/-- Translate a lambda, choosing pure vs do block based on body -/
partial def translateLambda (_name : Option String) (params : List (String × IRType))
    (body : IRExpr) : IRToLeanM LeanExpr := do
  let leanParams := params.map fun (n, _) => LeanParam.mk n none
  if containsRefs body then
    let doElems ← translateExprDo body
    return .lam leanParams (.doBlock doElems)
  else
    let bodyExpr ← translateExpr body
    return .lam leanParams bodyExpr

end

-- ============================================================
-- Top-level translation
-- ============================================================

/-- Translate an IR declaration to a Lean declaration -/
def translateDecl (d : IRDecl) : IRToLeanM LeanDecl := do
  match d with
  | .letDecl name _ty value =>
    match value with
    | .lam _fnName params _caps body _ _ =>
      let leanParams := params.map fun (n, _) => LeanParam.mk n none
      let bodyExpr ← if containsRefs body then do
        let doElems ← translateExprDo body
        pure (LeanExpr.doBlock doElems)
      else translateExpr body
      return .def_ name leanParams none bodyExpr
    | _ =>
      let valExpr ← translateExpr value
      return .let_ name none valExpr
  | .funcDecl name params _retTy body _ _ =>
    let leanParams := params.map fun (n, _) => LeanParam.mk n none
    let bodyExpr ← if containsRefs body then do
      let doElems ← translateExprDo body
      pure (LeanExpr.doBlock doElems)
    else translateExpr body
    return .def_ name leanParams none bodyExpr
  | .typeDecl name _ty =>
    return .structure_ name [] []
  | .classDecl name parent fields methods =>
    let extends_ := match parent with | some p => [p] | none => []
    let leanFields := fields.map fun (n, t) => (n, translateType t)
    -- Methods become separate defs; for now emit only fields as structure
    let methodDecls := methods.map fun (mname, _) => (mname, LeanType.hole)
    return .structure_ name extends_ (leanFields ++ methodDecls)
  | .importDecl _specs source =>
    return .import_ source
  | .exportDecl _names _source =>
    return .let_ "" none (.unit)
  | .exportDefault _value =>
    return .let_ "" none (.unit)

/-- Translate an IR module to a Lean module -/
def translateModule (m : IRModule) : Except String LeanModule := do
  let (decls, _) ← (m.decls.mapM translateDecl).run {}
  return { decls := decls }

/-- Translate a single IR expression to a Lean expression -/
def translateIRToLean (e : IRExpr) : Except String LeanExpr := do
  let (expr, _) ← (translateExpr e).run {}
  return expr

partial def extractDeclsFromIR : IRExpr → List IRDecl
  | .«let» name ty (.lam _n params _caps body async_ gen) rest =>
    [.funcDecl name params ty body async_ gen] ++ extractDeclsFromIR rest
  | .«let» name ty val rest =>
    [.letDecl name ty val] ++ extractDeclsFromIR rest
  | .seq exprs => exprs.flatMap extractDeclsFromIR
  | _ => []

/-- Translate IR expression to Lean module (via extracting decls) -/
def translateIRToLeanModule (e : IRExpr) : Except String LeanModule := do
  let decls := extractDeclsFromIR e
  let (leanDecls, _) ← (decls.mapM translateDecl).run {}
  return { decls := leanDecls }

end LeanJS.Trans.IRToLean
