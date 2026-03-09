import LeanJS.Lean.AST

set_option maxHeartbeats 800000

namespace LeanJS.Lean.Emit

structure EmitState where
  output : String := ""
  indentLevel : Nat := 0
  deriving Inhabited

abbrev Emitter := StateM EmitState

def write (s : String) : Emitter Unit :=
  modify fun st => { st with output := st.output ++ s }

def writeLn (s : String := "") : Emitter Unit := do
  let st ← get
  let ind := String.mk (List.replicate (st.indentLevel * 2) ' ')
  modify fun st => { st with output := st.output ++ ind ++ s ++ "\n" }

def writeIndent : Emitter Unit := do
  let st ← get
  let ind := String.mk (List.replicate (st.indentLevel * 2) ' ')
  modify fun st => { st with output := st.output ++ ind }

def incIndent : Emitter Unit :=
  modify fun st => { st with indentLevel := st.indentLevel + 1 }

def decIndent : Emitter Unit :=
  modify fun st => { st with indentLevel := st.indentLevel - 1 }

/-- Lean keywords that need guillemet escaping -/
def leanKeywords : List String :=
  ["let", "in", "do", "if", "then", "else", "match", "with", "where",
   "fun", "return", "def", "structure", "class", "instance", "import",
   "open", "namespace", "section", "variable", "theorem", "lemma",
   "example", "inductive", "mutual", "for", "while", "try", "catch",
   "throw", "type", "end", "set_option", "attribute", "derive",
   "sorry", "by", "have", "show", "at", "this", "true", "false",
   "or", "and", "not"]

/-- Wrap name in guillemets if it clashes with a Lean keyword -/
def sanitizeName (name : String) : String :=
  if name ∈ leanKeywords then s!"«{name}»"
  else name

def escapeString (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  let s := s.replace "\n" "\\n"
  let s := s.replace "\r" "\\r"
  let s := s.replace "\t" "\\t"
  s

def formatFloat (f : Float) : String :=
  if f == Float.ofNat f.toUInt64.toNat && f >= 0 && f < 1e15 then
    toString f.toUInt64.toNat ++ ".0"
  else toString f

/-- Whether an expression needs parens when used as a function argument -/
def needsParens : LeanExpr → Bool
  | .app _ _ => true
  | .binOp _ _ _ => true
  | .unaryOp _ _ => true
  | .lam _ _ => true
  | .«let» _ _ _ _ => true
  | .«if» _ _ _ => true
  | .«match» _ _ => true
  | _ => false

partial def emitType (t : LeanType) : Emitter Unit := do
  match t with
  | .name n => write n
  | .app fn arg =>
    emitType fn
    write " "
    match arg with
    | .app _ _ => write "("; emitType arg; write ")"
    | _ => emitType arg
  | .arrow dom cod =>
    match dom with
    | .arrow _ _ => write "("; emitType dom; write ")"
    | _ => emitType dom
    write " → "
    emitType cod
  | .product types =>
    let mut first := true
    for t in types do
      if !first then write " × "
      first := false
      emitType t
  | .hole => write "_"

mutual

partial def emitExpr (e : LeanExpr) : Emitter Unit := do
  match e with
  | .ident name => write (sanitizeName name)
  | .lit l => emitLit l
  | .app fn arg =>
    emitExpr fn
    write " "
    if needsParens arg then
      write "("
      emitExpr arg
      write ")"
    else
      emitExpr arg
  | .lam params body =>
    write "fun"
    for p in params do
      write s!" {sanitizeName p.name}"
    write " => "
    emitExpr body
  | .«let» name ty value body =>
    write s!"let {sanitizeName name}"
    match ty with
    | some t => write " : "; emitType t
    | none => pure ()
    write " := "
    emitExpr value
    write "\n"
    writeIndent
    emitExpr body
  | .bind name _ty value =>
    write s!"let {sanitizeName name} ← "
    emitExpr value
  | .doBlock elems =>
    write "do\n"
    incIndent
    for elem in elems do
      emitDoElem elem
    decIndent
  | .«if» cond then_ else_ =>
    write "if "
    emitExpr cond
    write " then "
    emitExpr then_
    match else_ with
    | some e => write " else "; emitExpr e
    | none => pure ()
  | .«match» scrutinee alts =>
    write "match "
    emitExpr scrutinee
    write " with\n"
    for alt in alts do
      writeIndent
      emitMatchAlt alt
  | .«while» cond body =>
    write "while "
    emitExpr cond
    write " do\n"
    incIndent
    writeIndent
    emitExpr body
    write "\n"
    decIndent
  | .«for» var iter body =>
    write s!"for {sanitizeName var} in "
    emitExpr iter
    write " do\n"
    incIndent
    writeIndent
    emitExpr body
    write "\n"
    decIndent
  | .«return» value =>
    write "return "
    emitExpr value
  | .structLit name fields =>
    match name with
    | some n => write s!"\{ {n} with "
    | none => write "{ "
    let mut first := true
    for (fname, fval) in fields do
      if !first then write ", "
      first := false
      write s!"{sanitizeName fname} := "
      emitExpr fval
    write " }"
  | .arrayLit elements =>
    write "#["
    let mut first := true
    for elem in elements do
      if !first then write ", "
      first := false
      emitExpr elem
    write "]"
  | .arrayIdx arr idx =>
    emitExpr arr
    write "["
    emitExpr idx
    write "]!"
  | .proj expr field =>
    if needsParens expr then
      write "("
      emitExpr expr
      write ")"
    else
      emitExpr expr
    write s!".{sanitizeName field}"
  | .binOp op left right =>
    emitExpr left
    write s!" {op} "
    emitExpr right
  | .unaryOp op arg =>
    write op
    if needsParens arg then
      write "("
      emitExpr arg
      write ")"
    else
      emitExpr arg
  | .refNew value =>
    write "IO.mkRef "
    if needsParens value then
      write "("
      emitExpr value
      write ")"
    else
      emitExpr value
  | .refGet ref =>
    if needsParens ref then
      write "("
      emitExpr ref
      write ")"
    else
      emitExpr ref
    write ".get"
  | .refSet ref value =>
    if needsParens ref then
      write "("
      emitExpr ref
      write ")"
    else
      emitExpr ref
    write ".set "
    if needsParens value then
      write "("
      emitExpr value
      write ")"
    else
      emitExpr value
  | .«try» body catchVar handler finalizer =>
    write "try\n"
    incIndent
    writeIndent
    emitExpr body
    write "\n"
    decIndent
    match handler with
    | some h =>
      let cv := match catchVar with | some n => sanitizeName n | none => "_"
      writeIndent
      write s!"catch {cv} =>\n"
      incIndent
      writeIndent
      emitExpr h
      write "\n"
      decIndent
    | none => pure ()
    match finalizer with
    | some f =>
      writeIndent
      write "finally\n"
      incIndent
      writeIndent
      emitExpr f
      write "\n"
      decIndent
    | none => pure ()
  | .«throw» value =>
    write "throw "
    emitExpr value
  | .paren inner =>
    write "("
    emitExpr inner
    write ")"
  | .unit => write "()"
  | .hole => write "_"

partial def emitLit (l : LeanLit) : Emitter Unit := do
  match l with
  | .natVal n => write (toString n)
  | .float f => write (formatFloat f)
  | .string s => write s!"\"{escapeString s}\""
  | .bool true => write "true"
  | .bool false => write "false"

partial def emitDoElem (elem : LeanDoElem) : Emitter Unit := do
  match elem with
  | .eval expr =>
    writeIndent
    emitExpr expr
    write "\n"
  | .bind name _ty value =>
    writeIndent
    write s!"let {sanitizeName name} ← "
    emitExpr value
    write "\n"
  | .letDecl name _ty value =>
    writeIndent
    write s!"let {sanitizeName name} := "
    emitExpr value
    write "\n"
  | .mutDecl name _ty value =>
    writeIndent
    write s!"let mut {sanitizeName name} := "
    emitExpr value
    write "\n"
  | .reassign name value =>
    writeIndent
    write s!"{sanitizeName name} := "
    emitExpr value
    write "\n"
  | .doReturn value =>
    writeIndent
    write "return "
    emitExpr value
    write "\n"
  | .doIf cond then_ else_ =>
    writeIndent
    write "if "
    emitExpr cond
    write " then\n"
    incIndent
    for elem in then_ do
      emitDoElem elem
    decIndent
    if !else_.isEmpty then
      writeIndent
      write "else\n"
      incIndent
      for elem in else_ do
        emitDoElem elem
      decIndent
  | .doWhile cond body =>
    writeIndent
    write "while "
    emitExpr cond
    write " do\n"
    incIndent
    for elem in body do
      emitDoElem elem
    decIndent
  | .doFor var iter body =>
    writeIndent
    write s!"for {sanitizeName var} in "
    emitExpr iter
    write " do\n"
    incIndent
    for elem in body do
      emitDoElem elem
    decIndent
  | .doTry body catchVar handler finalizer =>
    writeIndent
    write "try\n"
    incIndent
    for elem in body do
      emitDoElem elem
    decIndent
    if !handler.isEmpty then
      let cv := match catchVar with | some n => sanitizeName n | none => "_"
      writeIndent
      write s!"catch {cv} =>\n"
      incIndent
      for elem in handler do
        emitDoElem elem
      decIndent
    if !finalizer.isEmpty then
      writeIndent
      write "finally\n"
      incIndent
      for elem in finalizer do
        emitDoElem elem
      decIndent

partial def emitMatchAlt (alt : LeanMatchAlt) : Emitter Unit := do
  match alt with
  | .mk pat body =>
    write "| "
    emitPattern pat
    write " => "
    emitExpr body
    write "\n"

partial def emitPattern (p : LeanPattern) : Emitter Unit := do
  match p with
  | .wildcard => write "_"
  | .var name => write (sanitizeName name)
  | .lit l => emitLit l
  | .constructor name args =>
    write (sanitizeName name)
    for arg in args do
      write " "
      match arg with
      | .constructor _ (_::_) => write "("; emitPattern arg; write ")"
      | _ => emitPattern arg

end

def emitDecl (d : LeanDecl) : Emitter Unit := do
  match d with
  | .def_ name params retType body =>
    writeIndent
    write s!"def {sanitizeName name}"
    for p in params do
      match p.type with
      | some t => write s!" ({sanitizeName p.name} : "; emitType t; write ")"
      | none => write s!" {sanitizeName p.name}"
    match retType with
    | some t => write " : "; emitType t
    | none => pure ()
    write " :=\n"
    incIndent
    writeIndent
    emitExpr body
    write "\n"
    decIndent
  | .let_ name ty value =>
    writeIndent
    write s!"def {sanitizeName name}"
    match ty with
    | some t => write " : "; emitType t
    | none => pure ()
    write " :=\n"
    incIndent
    writeIndent
    emitExpr value
    write "\n"
    decIndent
  | .structure_ name extends_ fields =>
    writeIndent
    write s!"structure {sanitizeName name}"
    if !extends_.isEmpty then
      write " extends "
      write (", ".intercalate extends_)
    write " where\n"
    incIndent
    for (fname, ftype) in fields do
      writeIndent
      write s!"{sanitizeName fname} : "
      emitType ftype
      write "\n"
    decIndent
  | .inductive_ name params ctors =>
    writeIndent
    write s!"inductive {sanitizeName name}"
    for p in params do
      match p.type with
      | some t => write s!" ({sanitizeName p.name} : "; emitType t; write ")"
      | none => write s!" {sanitizeName p.name}"
    write " where\n"
    incIndent
    for (cname, ctypes) in ctors do
      writeIndent
      write s!"| {sanitizeName cname}"
      for ct in ctypes do
        write " ("
        emitType ct
        write ")"
      write "\n"
    decIndent
  | .open_ name =>
    writeLn s!"open {name}"
  | .import_ name =>
    writeLn s!"import {name}"

def emitModule (m : LeanModule) : Emitter Unit := do
  for h in m.header do
    writeLn h
  if !m.header.isEmpty then write "\n"
  for o in m.opens do
    writeLn s!"open {o}"
  if !m.opens.isEmpty then write "\n"
  let mut first := true
  for d in m.decls do
    if !first then write "\n"
    first := false
    emitDecl d

/-- Emit a single Lean expression -/
def emitLeanExpr (e : LeanExpr) : String :=
  let emitter : Emitter Unit := emitExpr e
  let (_, state) := emitter.run {}
  state.output

/-- Emit a full Lean module -/
def emitLeanModule (m : LeanModule) : String :=
  let emitter : Emitter Unit := emitModule m
  let (_, state) := emitter.run {}
  state.output

end LeanJS.Lean.Emit
