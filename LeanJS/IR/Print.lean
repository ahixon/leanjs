import LeanJS.IR.Core

namespace LeanJS.IR.Print

open LeanJS.IR

partial def printType : IRType → String
  | .any => "Any"
  | .number => "Number"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "Unit"
  | .func params ret => s!"({", ".intercalate (params.map printType)}) → {printType ret}"
  | .record fields => s!"\{{ ", ".intercalate (fields.map fun (n, t) => s!"{n}: {printType t}") }}"
  | .array elem => s!"Array({printType elem})"
  | .ref inner => s!"Ref({printType inner})"
  | .option inner => s!"Option({printType inner})"
  | .union tag _variants => s!"Union({tag})"

def printBinOp : IRBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .exp => "**" | .eq => "==" | .neq => "!=" | .lt => "<" | .lte => "<="
  | .gt => ">" | .gte => ">=" | .and => "&&" | .or => "||"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .shl => "<<" | .shr => ">>" | .ushr => ">>>"
  | .strConcat => "++"

def printUnaryOp : IRUnaryOp → String
  | .neg => "-" | .not => "!" | .bitNot => "~" | .typeof => "typeof "

mutual

partial def printExpr (e : IRExpr) (indent : Nat := 0) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  match e with
  | .lit (.number n) =>
    if n == Float.ofNat n.toUInt64.toNat && n >= 0 && n < 1e15 then
      toString n.toUInt64.toNat
    else toString n
  | .lit (.string s) => s!"\"{s}\""
  | .lit (.bool true) => "true"
  | .lit (.bool false) => "false"
  | .lit .unit => "()"
  | .var name => name
  | .undefined => "undefined"
  | .this => "this"
  | .«let» name ty val body =>
    s!"{pad}let {name} : {printType ty} = {printExpr val}\n{printExpr body indent}"
  | .lam name params _caps body async_ gen =>
    let nameStr := match name with | some n => n | none => "λ"
    let paramsStr := ", ".intercalate (params.map fun (n, t) => s!"{n}: {printType t}")
    let pfx := (if async_ then "async " else "") ++ (if gen then "gen " else "")
    s!"{pfx}fun {nameStr}({paramsStr}) =>\n{printExpr body (indent + 1)}"
  | .app func args =>
    let argsStr := ", ".intercalate (args.map (printExpr · indent))
    s!"{printExpr func indent}({argsStr})"
  | .binOp op left right =>
    s!"({printExpr left indent} {printBinOp op} {printExpr right indent})"
  | .unaryOp op arg =>
    s!"({printUnaryOp op}{printExpr arg indent})"
  | .mkRef val => s!"ref({printExpr val indent})"
  | .deref ref => s!"!{printExpr ref indent}"
  | .assign ref val => s!"{printExpr ref indent} := {printExpr val indent}"
  | .record fields =>
    let fieldsStr := ", ".intercalate (fields.map fun (n, v) => s!"{n}: {printExpr v indent}")
    s!"\{{ fieldsStr }}"
  | .project expr field => s!"{printExpr expr indent}.{field}"
  | .projectIdx expr idx => s!"{printExpr expr indent}[{printExpr idx indent}]"
  | .array elements =>
    let elemsStr := ", ".intercalate (elements.map (printExpr · indent))
    s!"[{elemsStr}]"
  | .index arr idx => s!"{printExpr arr indent}[{printExpr idx indent}]"
  | .«if» cond then_ else_ =>
    s!"{pad}if {printExpr cond} then\n{printExpr then_ (indent+1)}\n{pad}else\n{printExpr else_ (indent+1)}"
  | .loop cond body =>
    s!"{pad}while {printExpr cond} do\n{printExpr body (indent + 1)}"
  | .seq exprs =>
    "\n".intercalate (exprs.map fun e => s!"{pad}{printExpr e indent}")
  | .«return» val => s!"{pad}return {printExpr val indent}"
  | .«break» => s!"{pad}break"
  | .«continue» => s!"{pad}continue"
  | .throw val => s!"{pad}throw {printExpr val indent}"
  | .tryCatch body catchVar handler _fin =>
    let catchStr := match catchVar with | some n => n | none => "_"
    s!"{pad}try\n{printExpr body (indent+1)}\n{pad}catch {catchStr}\n{printExpr handler (indent+1)}"
  | .«match» scrutinee cases =>
    let casesStr := "\n".intercalate (cases.map fun c => printMatchCase c (indent + 1))
    s!"{pad}match {printExpr scrutinee} with\n{casesStr}"
  | .construct name args =>
    let argsStr := ", ".intercalate (args.map (printExpr · indent))
    s!"{name}({argsStr})"
  | .newObj callee args =>
    let argsStr := ", ".intercalate (args.map (printExpr · indent))
    s!"new {printExpr callee indent}({argsStr})"
  | .«await» expr => s!"await {printExpr expr indent}"
  | .«yield» (some expr) delegate =>
    let star := if delegate then "*" else ""
    s!"yield{star} {printExpr expr indent}"
  | .«yield» none delegate =>
    let star := if delegate then "*" else ""
    s!"yield{star}"
  | .spread expr => s!"...{printExpr expr indent}"
  | .ternary cond then_ else_ =>
    s!"({printExpr cond} ? {printExpr then_} : {printExpr else_})"

partial def printMatchCase (c : IRMatchCase) (indent : Nat) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  match c with
  | .mk pat body => s!"{pad}| {printPattern pat} => {printExpr body indent}"

partial def printPattern (p : IRPattern) : String :=
  match p with
  | .wildcard => "_"
  | .var name => name
  | .lit (.number n) => s!"{n}"
  | .lit (.string s) => s!"\"{s}\""
  | .lit (.bool b) => s!"{b}"
  | .lit .unit => "()"
  | .constructor tag bindings => s!"{tag} {" ".intercalate bindings}"

end

def printModule (m : IRModule) : String :=
  let declStrs := m.decls.map fun d =>
    match d with
    | .letDecl name ty val =>
      s!"let {name} : {printType ty} = {printExpr val}"
    | .funcDecl name params retTy body async_ gen =>
      let paramsStr := ", ".intercalate (params.map fun (n, t) => s!"{n}: {printType t}")
      let pfx := (if async_ then "async " else "") ++ (if gen then "gen " else "")
      s!"{pfx}def {name}({paramsStr}) : {printType retTy} =\n{printExpr body 1}"
    | .typeDecl name ty => s!"type {name} = {printType ty}"
    | .classDecl name parent fields methods =>
      let parentStr := match parent with | some p => s!" extends {p}" | none => ""
      let fieldsStr := ", ".intercalate (fields.map fun (n, t) => s!"{n}: {printType t}")
      let methodsStr := ", ".intercalate (methods.map fun (n, _) => n)
      s!"class {name}{parentStr} \{{ fieldsStr }; methods: {methodsStr} }"
    | .importDecl _specs source => s!"import \"{source}\""
    | .exportDecl names _source =>
      let namesStr := ", ".intercalate (names.map fun (l, _) => l)
      s!"export \{{ namesStr }}"
    | .exportDefault value => s!"export default {printExpr value}"
  "\n\n".intercalate declStrs

end LeanJS.IR.Print
