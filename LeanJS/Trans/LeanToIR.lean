/-
  Lean AST → IR Translation

  Translates Lean surface syntax AST into the shared IR representation.
  Mirrors JSToIR pattern: StateT LeanTransEnv (Except String).
-/
import LeanJS.Lean.AST
import LeanJS.IR.Core

set_option maxHeartbeats 800000

namespace LeanJS.Trans.LeanToIR

open LeanJS.Lean
open LeanJS.IR

-- ============================================================
-- Translation state and monad
-- ============================================================

structure LeanTransEnv where
  mutVars : List String := []   -- let mut variables
  refVars : List String := []   -- IO.Ref variables
  deriving Inhabited

abbrev LeanTransM := StateT LeanTransEnv (Except String)

def isMutVar (name : String) : LeanTransM Bool := do
  let env ← get
  return name ∈ env.mutVars

def markMut (name : String) : LeanTransM Unit :=
  modify fun env => { env with mutVars := name :: env.mutVars }

def isRefVar (name : String) : LeanTransM Bool := do
  let env ← get
  return name ∈ env.refVars

def markRef (name : String) : LeanTransM Unit :=
  modify fun env => { env with refVars := name :: env.refVars }

-- ============================================================
-- Operator mapping
-- ============================================================

def leanBinOpToIR : String → Option IRBinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul
  | "/" => some .div | "%" => some .mod | "^" => some .exp
  | "==" => some .eq | "!=" => some .neq
  | "<" => some .lt | ">" => some .gt | "<=" => some .lte | ">=" => some .gte
  | "&&" => some .and | "||" => some .or
  | "++" => some .strConcat
  | "&&&" => some .bitAnd | "|||" => some .bitOr | "^^^" => some .bitXor
  | "<<<" => some .shl | ">>>" => some .shr
  | _ => none

def leanUnaryOpToIR : String → Option IRUnaryOp
  | "-" => some .neg | "!" => some .not | "~~~" => some .bitNot
  | _ => none

-- ============================================================
-- Helpers
-- ============================================================

/-- Flatten curried application: app(app(f, x), y) → (f, [x, y]) -/
partial def flattenApp : LeanExpr → (LeanExpr × List LeanExpr)
  | .app fn arg =>
    let (f, args) := flattenApp fn
    (f, args ++ [arg])
  | e => (e, [])

/-- Check if expression is IO.mkRef call -/
def isIOMkRef : LeanExpr → Option LeanExpr
  | .app (.proj (.ident "IO") "mkRef") val => some val
  | .refNew val => some val
  | _ => none

/-- Check if expression is a .get projection (ref dereference) -/
def isRefGet : LeanExpr → Option LeanExpr
  | .proj e "get" => some e
  | .refGet e => some e
  | _ => none

/-- Check if expression is a .set call (ref assignment) -/
def isRefSet : LeanExpr → Option (LeanExpr × LeanExpr)
  | .app (.proj e "set") val => some (e, val)
  | .refSet e val => some (e, val)
  | _ => none

/-- Translate Lean literal to IR literal -/
def translateLit : LeanLit → IRLit
  | .natVal n => .number (Float.ofNat n)
  | .float f => .number f
  | .string s => .string s
  | .bool b => .bool b

/-- Translate Lean type to IR type -/
partial def translateType : LeanType → IRType
  | .name "Float" => .number
  | .name "String" => .string
  | .name "Bool" => .bool
  | .name "Unit" => .unit
  | .name "Nat" => .number
  | .name "Int" => .number
  | .name _ => .any
  | .app (.name "Array") elem => .array (translateType elem)
  | .app (.name "IO.Ref") inner => .ref (translateType inner)
  | .app (.name "Option") inner => .option (translateType inner)
  | .app _ _ => .any
  | .arrow dom cod => .func [translateType dom] (translateType cod)
  | .product types => .record (types.zipIdx.map fun (t, i) => (s!"_{i}", translateType t))
  | .hole => .any

/-- Translate Lean pattern to IR pattern -/
def translatePattern : LeanPattern → IRPattern
  | .wildcard => .wildcard
  | .var name => .var name
  | .lit l => .lit (translateLit l)
  | .constructor name args =>
    let bindings := args.filterMap fun p =>
      match p with | .var n => some n | _ => none
    .constructor name bindings

/-- Thread let-bindings so declarations scope over subsequent expressions -/
partial def threadLets : List IRExpr → IRExpr
  | [] => .undefined
  | [e] => e
  | (.«let» name ty val _) :: rest =>
    .«let» name ty val (threadLets rest)
  | e :: rest => .seq [e, threadLets rest]

-- ============================================================
-- Main translation (mutual block)
-- ============================================================

mutual

/-- Translate a Lean expression to IR -/
partial def translateExpr (e : LeanExpr) : LeanTransM IRExpr := do
  match e with
  | .ident name =>
    let isMut ← isMutVar name
    let isRef ← isRefVar name
    if isMut || isRef then return .deref (.var name)
    else return .var name

  | .lit l => return .lit (translateLit l)
  | .unit => return .undefined
  | .hole => return .undefined

  | .paren inner => translateExpr inner

  | .app fn arg =>
    -- Check for special patterns first
    let (f, args) := flattenApp (.app fn arg)
    -- IO.mkRef pattern
    match f with
    | .proj (.ident "IO") "mkRef" =>
      match args with
      | [val] =>
        let v ← translateExpr val
        return .mkRef v
      | _ =>
        let fIR ← translateExpr f
        let aIR ← args.mapM translateExpr
        return .app fIR aIR
    | _ =>
      -- Check for ref.get / ref.set at the top level
      match isRefGet (.app fn arg) with
      | some e =>
        let r ← translateExpr e
        return .deref r
      | none =>
        match isRefSet (.app fn arg) with
        | some (ref, val) =>
          let r ← translateExpr ref
          let v ← translateExpr val
          return .assign r v
        | none =>
          let fIR ← translateExpr f
          let aIR ← args.mapM translateExpr
          return .app fIR aIR

  | .lam params body =>
    let irParams := params.map fun p =>
      let ty := match p.type with
        | some t => translateType t
        | none => .any
      (p.name, ty)
    let bodyIR ← translateExpr body
    return .lam none irParams [] bodyIR

  | .«let» name _ty value body =>
    -- Check for IO.mkRef in value
    match isIOMkRef value with
    | some inner =>
      markMut name
      let v ← translateExpr inner
      let b ← translateExpr body
      return .«let» name .any (.mkRef v) b
    | none =>
      let v ← translateExpr value
      let b ← translateExpr body
      return .«let» name .any v b

  | .bind name _ty value =>
    -- Monadic bind: let x ← val, treat as let
    match isIOMkRef value with
    | some inner =>
      markRef name
      let v ← translateExpr inner
      return .«let» name .any (.mkRef v) (.var name)
    | none =>
      let v ← translateExpr value
      return .«let» name .any v (.var name)

  | .doBlock elems =>
    translateDoBlock elems

  | .«if» cond then_ else_ =>
    let c ← translateExpr cond
    let t ← translateExpr then_
    let e ← match else_ with
      | some el => translateExpr el
      | none => pure .undefined
    return .«if» c t e

  | .«match» scrutinee alts =>
    let s ← translateExpr scrutinee
    let cases ← alts.mapM translateMatchAlt
    return .«match» s cases

  | .«while» cond body =>
    let c ← translateExpr cond
    let b ← translateExpr body
    return .loop c b

  | .«for» var iter body =>
    let it ← translateExpr iter
    let b ← translateExpr body
    return .«let» var .any .undefined
      (.loop (.lit (.bool true))
        (.seq [.assign (.var var) (.app (.var "__nextElem") [it]), b]))

  | .«return» value =>
    let v ← translateExpr value
    return .«return» v

  | .structLit _name fields =>
    let irFields ← fields.mapM fun (fname, fval) => do
      let v ← translateExpr fval
      return (fname, v)
    return .record irFields

  | .arrayLit elements =>
    let elems ← elements.mapM translateExpr
    return .array elems

  | .arrayIdx arr idx =>
    let a ← translateExpr arr
    let i ← translateExpr idx
    return .index a i

  | .proj expr field =>
    let e ← translateExpr expr
    -- Check for .get / .set projections
    if field == "get" then return .deref e
    else return .project e field

  | .binOp op left right =>
    let l ← translateExpr left
    let r ← translateExpr right
    match leanBinOpToIR op with
    | some irOp => return .binOp irOp l r
    | none =>
      -- Arrow type or unknown operator — treat as app
      return .app (.var op) [l, r]

  | .unaryOp op arg =>
    let a ← translateExpr arg
    match leanUnaryOpToIR op with
    | some irOp => return .unaryOp irOp a
    | none => return .app (.var op) [a]

  | .refNew value =>
    let v ← translateExpr value
    return .mkRef v

  | .refGet ref =>
    let r ← translateExpr ref
    return .deref r

  | .refSet ref value =>
    let r ← translateExpr ref
    let v ← translateExpr value
    return .assign r v

  | .«try» body catchVar handler finalizer =>
    let b ← translateExpr body
    let h ← match handler with
      | some e => translateExpr e
      | none => pure .undefined
    let f ← match finalizer with
      | some e => do let v ← translateExpr e; pure (some v)
      | none => pure none
    return .tryCatch b catchVar h f

  | .«throw» value =>
    let v ← translateExpr value
    return .throw v

/-- Translate a do-block to IR -/
partial def translateDoBlock (elems : List LeanDoElem) : LeanTransM IRExpr := do
  let irExprs ← elems.mapM translateDoElem
  return threadLets irExprs

/-- Translate a single do-block element to IR -/
partial def translateDoElem (elem : LeanDoElem) : LeanTransM IRExpr := do
  match elem with
  | .eval expr => translateExpr expr

  | .letDecl name _ty value =>
    let v ← translateExpr value
    return .«let» name .any v (.var name)

  | .bind name _ty value =>
    match isIOMkRef value with
    | some inner =>
      markRef name
      let v ← translateExpr inner
      return .«let» name .any (.mkRef v) (.var name)
    | none =>
      let v ← translateExpr value
      return .«let» name .any v (.var name)

  | .mutDecl name _ty value =>
    markMut name
    let v ← translateExpr value
    return .«let» name .any (.mkRef v) (.var name)

  | .reassign name value =>
    let v ← translateExpr value
    return .assign (.var name) v

  | .doReturn value =>
    let v ← translateExpr value
    return .«return» v

  | .doIf cond thenElems elseElems =>
    let c ← translateExpr cond
    let t ← translateDoBlock thenElems
    let e ← translateDoBlock elseElems
    return .«if» c t e

  | .doWhile cond body =>
    let c ← translateExpr cond
    let b ← translateDoBlock body
    return .loop c b

  | .doFor var iter body =>
    let it ← translateExpr iter
    let b ← translateDoBlock body
    return .«let» var .any .undefined
      (.loop (.lit (.bool true))
        (.seq [.assign (.var var) (.app (.var "__nextElem") [it]), b]))

  | .doTry body catchVar handler finalizer =>
    let b ← translateDoBlock body
    let h ← translateDoBlock handler
    let f ← if finalizer.isEmpty then pure none
      else do let v ← translateDoBlock finalizer; pure (some v)
    return .tryCatch b catchVar h f

/-- Translate a match alternative -/
partial def translateMatchAlt (alt : LeanMatchAlt) : LeanTransM IRMatchCase := do
  match alt with
  | .mk pat body =>
    let b ← translateExpr body
    return .mk (translatePattern pat) b

end

-- ============================================================
-- Declaration-level translation
-- ============================================================

/-- Translate a Lean declaration to IR declaration -/
def translateDecl (d : LeanDecl) : LeanTransM IRDecl := do
  match d with
  | .def_ name params retType body =>
    let irParams := params.map fun p =>
      let ty := match p.type with
        | some t => translateType t
        | none => .any
      (p.name, ty)
    let retTy := match retType with
      | some t => translateType t
      | none => .any
    let bodyIR ← translateExpr body
    return .funcDecl name irParams retTy bodyIR

  | .let_ name ty value =>
    let irTy := match ty with
      | some t => translateType t
      | none => .any
    let v ← translateExpr value
    return .letDecl name irTy v

  | .structure_ name extends_ fields =>
    let irFields := fields.map fun (fname, ftype) => (fname, translateType ftype)
    let parent := extends_.head?
    return .classDecl name parent irFields []

  | .inductive_ name _params ctors =>
    let variants := ctors.map fun (cname, ctypes) =>
      (cname, ctypes.map translateType)
    return .typeDecl name (.union name variants)

  | .open_ _ => return .letDecl "" .unit .undefined  -- skip
  | .import_ _ => return .letDecl "" .unit .undefined  -- skip

/-- Translate a Lean module to IR module -/
def translateModule (m : LeanModule) : Except String IRModule := do
  let (decls, _) ← (m.decls.mapM translateDecl).run {}
  -- Filter out empty skip declarations
  let decls := decls.filter fun d => match d with
    | .letDecl "" _ _ => false
    | _ => true
  return { name := "", imports := m.opens, decls }

end LeanJS.Trans.LeanToIR
