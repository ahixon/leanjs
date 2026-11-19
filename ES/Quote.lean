import ES.AST

/-!
# Quoting syntax trees as Lean source

`quoteProgram p` is Lean source text that elaborates to `p` (fully qualified constructor
applications), so a compiled program can carry its syntax tree and run it on the engine. Recursion
is structural on a depth parameter; `quoteDepth` is far above any tree the parser accepts (its
nesting limit bounds tree height, docs/es.md L2), and an exhausted depth prints `default`, which
would not elaborate to the same tree — so the bound must be (and is) sufficient.
-/

namespace ES.Quote

open ES (F64)

def quoteDepth : Nat := 1000000

def app (c : String) (args : List String) : String :=
  if args.isEmpty then c else "(" ++ c ++ " " ++ " ".intercalate args ++ ")"

def qBool (b : Bool) : String := if b then "true" else "false"
def qNat (n : Nat) : String := toString n
def qInt (i : Int) : String := if i < 0 then s!"({i})" else toString i

/-- A Lean string literal for a string without lone surrogates. -/
def qLeanString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      let h := Nat.toDigits 16 c.toNat
      out := out ++ "\\x" ++ (if h.length < 2 then "0" else "") ++ String.ofList h
    else out := out.push c
  return out ++ "\""

/-- A `JSStr` (UTF-16; lone surrogates as code units). -/
def qStr (s : JSStr) : String :=
  let units := s.toUnits
  let lone := (Array.range units.size).any fun i => (s.codePointAt i).2.2
  if lone then
    "(ES.JSStr.ofUnits #[" ++ ", ".intercalate (units.toList.map (fun u => toString u.toNat)) ++ "])"
  else "(ES.JSStr.ofString " ++ qLeanString s.toString ++ ")"

def qOpt {α} (f : α → String) : Option α → String
  | none => "none"
  | some a => "(some " ++ f a ++ ")"

def qArr {α} (f : α → String) (xs : Array α) : String :=
  "#[" ++ ", ".intercalate (xs.toList.map f) ++ "]"

def qPair (p : JSStr × JSStr) : String := "(" ++ qStr p.1 ++ ", " ++ qStr p.2 ++ ")"

def qF64 : F64 → String
  | .nan => "ES.F64.nan"
  | .inf n => app "ES.F64.inf" [qBool n]
  | .fin n m e => app "ES.F64.fin" [qBool n, qNat m, qInt e]

def qLit : Lit → String
  | .null => "ES.Lit.null"
  | .bool b => app "ES.Lit.bool" [qBool b]
  | .num x => app "ES.Lit.num" [qF64 x]
  | .str s => app "ES.Lit.str" [qStr s]
  | .bigint i => app "ES.Lit.bigint" [qInt i]

def qUnOp (o : UnOp) : String := "ES.UnOp." ++ ((reprStr o).replace "ES.UnOp." "")
def qBinOp (o : BinOp) : String := "ES.BinOp." ++ ((reprStr o).replace "ES.BinOp." "")
def qLogOp (o : LogOp) : String := "ES.LogOp." ++ ((reprStr o).replace "ES.LogOp." "")
def qVarKind (k : VarKind) : String := "ES.VarKind." ++ ((reprStr k).replace "ES.VarKind." "")

def qAssignOp : AssignOp → String
  | .assign => "ES.AssignOp.assign"
  | .op o => app "ES.AssignOp.op" [qBinOp o]
  | .logical o => app "ES.AssignOp.logical" [qLogOp o]

def qFuncKind : FuncKind → String
  | .normal => "ES.FuncKind.normal" | .arrow => "ES.FuncKind.arrow" | .method => "ES.FuncKind.method"
  | .getter => "ES.FuncKind.getter" | .setter => "ES.FuncKind.setter"
  | .classConstructor d => app "ES.FuncKind.classConstructor" [qBool d]
  | .classField => "ES.FuncKind.classField" | .classStaticBlock => "ES.FuncKind.classStaticBlock"

def qSpan (s : Span) : String := s!"\{ start := {s.start}, stop := {s.stop} : ES.Span }"

def qInfo (i : FuncInfo) : String :=
  s!"\{ strict := {qBool i.strict}, span := {qSpan i.span}, simpleParams := {qBool i.simpleParams}, " ++
  s!"expectedArgs := {i.expectedArgs}, hasDirectEval := {qBool i.hasDirectEval}, " ++
  s!"usesArguments := {qBool i.usesArguments}, usesThis := {qBool i.usesThis}, " ++
  s!"paramsHaveExpressions := {qBool i.paramsHaveExpressions}, id := {i.id} : ES.FuncInfo }"

def qImport : ImportDecl → String
  | .mk d ns named m attrs ph =>
    app "ES.ImportDecl.mk" [qOpt qStr d, qOpt qStr ns, qArr qPair named, qStr m, qArr qPair attrs, qOpt qStr ph]

mutual

def qExpr : Nat → Expr → String
  | 0, _ => "default"
  | n + 1, e => match e with
    | .this => "ES.Expr.this"
    | .ident x => app "ES.Expr.ident" [qStr x]
    | .lit l => app "ES.Expr.lit" [qLit l]
    | .template c r es => app "ES.Expr.template" [qArr (qOpt qStr) c, qArr qStr r, qArr (qExpr n) es]
    | .tagged t c r es site => app "ES.Expr.tagged" [qExpr n t, qArr (qOpt qStr) c, qArr qStr r, qArr (qExpr n) es, qNat site]
    | .regex p f => app "ES.Expr.regex" [qStr p, qStr f]
    | .array els => app "ES.Expr.array" [qArr (qArrElem n) els]
    | .object ps => app "ES.Expr.object" [qArr (qPropDef n) ps]
    | .func f => app "ES.Expr.func" [qFunc n f]
    | .cls c => app "ES.Expr.cls" [qClass n c]
    | .unary o e => app "ES.Expr.unary" [qUnOp o, qExpr n e]
    | .update i p t => app "ES.Expr.update" [qBool i, qBool p, qExpr n t]
    | .binary o l r => app "ES.Expr.binary" [qBinOp o, qExpr n l, qExpr n r]
    | .logical o l r => app "ES.Expr.logical" [qLogOp o, qExpr n l, qExpr n r]
    | .privIn nm r => app "ES.Expr.privIn" [qStr nm, qExpr n r]
    | .assign o t v => app "ES.Expr.assign" [qAssignOp o, qPattern n t, qExpr n v]
    | .cond a b c => app "ES.Expr.cond" [qExpr n a, qExpr n b, qExpr n c]
    | .call c args o de => app "ES.Expr.call" [qExpr n c, qArr (qArg n) args, qBool o, qBool de]
    | .new c args => app "ES.Expr.new" [qExpr n c, qArr (qArg n) args]
    | .member o k opt => app "ES.Expr.member" [qExpr n o, qMemberKey n k, qBool opt]
    | .chain e => app "ES.Expr.chain" [qExpr n e]
    | .superMember k => app "ES.Expr.superMember" [qMemberKey n k]
    | .superCall args => app "ES.Expr.superCall" [qArr (qArg n) args]
    | .newTarget => "ES.Expr.newTarget"
    | .importMeta => "ES.Expr.importMeta"
    | .importCall s o => app "ES.Expr.importCall" [qExpr n s, qOpt (qExpr n) o]
    | .seq es => app "ES.Expr.seq" [qArr (qExpr n) es]
    | .yield a d => app "ES.Expr.yield" [qOpt (qExpr n) a, qBool d]
    | .await e => app "ES.Expr.await" [qExpr n e]
    | .paren e => app "ES.Expr.paren" [qExpr n e]

def qMemberKey : Nat → MemberKey → String
  | 0, _ => "default"
  | n + 1, k => match k with
    | .name x => app "ES.MemberKey.name" [qStr x]
    | .computed e => app "ES.MemberKey.computed" [qExpr n e]
    | .priv x => app "ES.MemberKey.priv" [qStr x]

def qArg : Nat → Arg → String
  | 0, _ => "default"
  | n + 1, a => match a with
    | .expr e => app "ES.Arg.expr" [qExpr n e]
    | .spread e => app "ES.Arg.spread" [qExpr n e]

def qArrElem : Nat → ArrElem → String
  | 0, _ => "default"
  | n + 1, a => match a with
    | .hole => "ES.ArrElem.hole"
    | .expr e => app "ES.ArrElem.expr" [qExpr n e]
    | .spread e => app "ES.ArrElem.spread" [qExpr n e]

def qPropName : Nat → PropName → String
  | 0, _ => "default"
  | n + 1, p => match p with
    | .ident x => app "ES.PropName.ident" [qStr x]
    | .str x => app "ES.PropName.str" [qStr x]
    | .num x => app "ES.PropName.num" [qF64 x]
    | .bigint i => app "ES.PropName.bigint" [qInt i]
    | .computed e => app "ES.PropName.computed" [qExpr n e]
    | .priv x => app "ES.PropName.priv" [qStr x]

def qPropDef : Nat → PropDef → String
  | 0, _ => "default"
  | n + 1, p => match p with
    | .init k v ps => app "ES.PropDef.init" [qPropName n k, qExpr n v, qBool ps]
    | .shorthand x => app "ES.PropDef.shorthand" [qStr x]
    | .method k f => app "ES.PropDef.method" [qPropName n k, qFunc n f]
    | .spread e => app "ES.PropDef.spread" [qExpr n e]

def qPattern : Nat → Pattern → String
  | 0, _ => "default"
  | n + 1, p => match p with
    | .ident x => app "ES.Pattern.ident" [qStr x]
    | .expr e => app "ES.Pattern.expr" [qExpr n e]
    | .obj ps r => app "ES.Pattern.obj" [qArr (qPatProp n) ps, qOpt (qPattern n) r]
    | .arr es r => app "ES.Pattern.arr" [qArr (qOpt (qPatElem n)) es, qOpt (qPattern n) r]

def qPatProp : Nat → PatProp → String
  | 0, _ => "default"
  | n + 1, .mk k t i => app "ES.PatProp.mk" [qPropName n k, qPattern n t, qOpt (qExpr n) i]

def qPatElem : Nat → PatElem → String
  | 0, _ => "default"
  | n + 1, .mk t i => app "ES.PatElem.mk" [qPattern n t, qOpt (qExpr n) i]

def qStmt : Nat → Stmt → String
  | 0, _ => "default"
  | n + 1, s => match s with
    | .expr e => app "ES.Stmt.expr" [qExpr n e]
    | .varDecl k ds => app "ES.Stmt.varDecl" [qVarKind k, qArr (qDeclarator n) ds]
    | .funDecl f => app "ES.Stmt.funDecl" [qFunc n f]
    | .classDecl c => app "ES.Stmt.classDecl" [qClass n c]
    | .block b => app "ES.Stmt.block" [qArr (qStmt n) b]
    | .empty => "ES.Stmt.empty"
    | .ret e => app "ES.Stmt.ret" [qOpt (qExpr n) e]
    | .ifS t c a => app "ES.Stmt.ifS" [qExpr n t, qStmt n c, qOpt (qStmt n) a]
    | .whileS t b => app "ES.Stmt.whileS" [qExpr n t, qStmt n b]
    | .doWhile b t => app "ES.Stmt.doWhile" [qStmt n b, qExpr n t]
    | .forS i t u b => app "ES.Stmt.forS" [qOpt (qForInit n) i, qOpt (qExpr n) t, qOpt (qExpr n) u, qStmt n b]
    | .forIn l r b => app "ES.Stmt.forIn" [qForLhs n l, qExpr n r, qStmt n b]
    | .forOf l r b a => app "ES.Stmt.forOf" [qForLhs n l, qExpr n r, qStmt n b, qBool a]
    | .brk l => app "ES.Stmt.brk" [qOpt qStr l]
    | .cont l => app "ES.Stmt.cont" [qOpt qStr l]
    | .throw e => app "ES.Stmt.throw" [qExpr n e]
    | .tryS b h f => app "ES.Stmt.tryS" [qArr (qStmt n) b, qOpt (qCatch n) h, qOpt (qArr (qStmt n)) f]
    | .switch d cs => app "ES.Stmt.switch" [qExpr n d, qArr (qCase n) cs]
    | .labeled l b => app "ES.Stmt.labeled" [qStr l, qStmt n b]
    | .with o b => app "ES.Stmt.with" [qExpr n o, qStmt n b]
    | .debugger => "ES.Stmt.debugger"
    | .importDecl d => app "ES.Stmt.importDecl" [qImport d]
    | .exportDecl d => app "ES.Stmt.exportDecl" [qExport n d]

def qDeclarator : Nat → VarDeclarator → String
  | 0, _ => "default"
  | n + 1, .mk t i => app "ES.VarDeclarator.mk" [qPattern n t, qOpt (qExpr n) i]

def qForInit : Nat → ForInit → String
  | 0, _ => "default"
  | n + 1, i => match i with
    | .decl k ds => app "ES.ForInit.decl" [qVarKind k, qArr (qDeclarator n) ds]
    | .expr e => app "ES.ForInit.expr" [qExpr n e]

def qForLhs : Nat → ForLhs → String
  | 0, _ => "default"
  | n + 1, l => match l with
    | .decl k t i => app "ES.ForLhs.decl" [qVarKind k, qPattern n t, qOpt (qExpr n) i]
    | .pattern t => app "ES.ForLhs.pattern" [qPattern n t]

def qCatch : Nat → CatchClause → String
  | 0, _ => "default"
  | n + 1, .mk p b => app "ES.CatchClause.mk" [qOpt (qPattern n) p, qArr (qStmt n) b]

def qCase : Nat → SwitchCase → String
  | 0, _ => "default"
  | n + 1, .mk t b => app "ES.SwitchCase.mk" [qOpt (qExpr n) t, qArr (qStmt n) b]

def qParam : Nat → Param → String
  | 0, _ => "default"
  | n + 1, .mk t i r => app "ES.Param.mk" [qPattern n t, qOpt (qExpr n) i, qBool r]

def qFunc : Nat → Func → String
  | 0, _ => "default"
  | n + 1, .mk nm k a g ps b i =>
    app "ES.Func.mk" [qOpt qStr nm, qFuncKind k, qBool a, qBool g, qArr (qParam n) ps, qFuncBody n b, qInfo i]

def qFuncBody : Nat → FuncBody → String
  | 0, _ => "default"
  | n + 1, b => match b with
    | .stmts ss => app "ES.FuncBody.stmts" [qArr (qStmt n) ss]
    | .expr e => app "ES.FuncBody.expr" [qExpr n e]

def qClass : Nat → Class → String
  | 0, _ => "default"
  | n + 1, .mk nm sc es sp => app "ES.Class.mk" [qOpt qStr nm, qOpt (qExpr n) sc, qArr (qClassElem n) es, qSpan sp]

def qClassElem : Nat → ClassElem → String
  | 0, _ => "default"
  | n + 1, e => match e with
    | .method s k f => app "ES.ClassElem.method" [qBool s, qPropName n k, qFunc n f]
    | .field s k i sp => app "ES.ClassElem.field" [qBool s, qPropName n k, qOpt (qExpr n) i, qSpan sp]
    | .staticBlock b sp => app "ES.ClassElem.staticBlock" [qArr (qStmt n) b, qSpan sp]
    | .accessor s k i => app "ES.ClassElem.accessor" [qBool s, qPropName n k, qOpt (qExpr n) i]

def qExport : Nat → ExportDecl → String
  | 0, _ => "default"
  | n + 1, d => match d with
    | .named s => app "ES.ExportDecl.named" [qArr qPair s]
    | .namedFrom s m a => app "ES.ExportDecl.namedFrom" [qArr qPair s, qStr m, qArr qPair a]
    | .all a m at_ => app "ES.ExportDecl.all" [qOpt qStr a, qStr m, qArr qPair at_]
    | .decl s => app "ES.ExportDecl.decl" [qStmt n s]
    | .defaultFunc f => app "ES.ExportDecl.defaultFunc" [qFunc n f]
    | .defaultClass c => app "ES.ExportDecl.defaultClass" [qClass n c]
    | .defaultExpr e => app "ES.ExportDecl.defaultExpr" [qExpr n e]

end

/-- A program as Lean source (the source text included, for `Function.prototype.toString`). -/
def quoteProgram (p : Program) : String :=
  "{ body := " ++ qArr (qStmt quoteDepth) p.body ++ ", isModule := " ++ qBool p.isModule ++
  ", strict := " ++ qBool p.strict ++ ", source := " ++ qLeanString p.source ++ " : ES.Program }"

end ES.Quote
