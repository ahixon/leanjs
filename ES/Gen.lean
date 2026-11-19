import ES.Quote
import ES.Interp

/-!
# Generating Lean definitions from programs (docs/compile.md)

`genStmts k ss` prints a Lean term of type `ES.Sem.CStmt` equal to `(ES.evalStmts (n + k) · ss)`
(likewise `genExpr`, `genStmt`, …): the interpreter's fold unrolled into `ES.Sem` combinators. A
construct the generator does not cover is printed as the interpreter applied to its subtree at the
depth the interpreter would use there (`(ES.evalExpr (n + k) · …)`), so every generated term is
the interpreter's denotation, which the generated `_eq` theorems state (and check).

The printed depth is `n + k` for a symbolic `n` (the theorems hold for every `n`). The generator
mirrors the interpreter's cases exactly; a mismatch makes the generated proof fail.
-/

namespace ES.Gen

open ES.Quote

/-- Names of the generated definitions of functions, by `FuncInfo.id`. -/
abbrev Names := Std.HashMap Nat String

def d (k : Nat) : String := s!"(n + {k})"

/-- The quoted function, or the name of its generated AST definition. -/
def funcRef (names : Names) (f : Func) : String :=
  match names.get? f.info.id with
  | some nm => nm ++ "_func"
  | none => qFunc quoteDepth f

def qCallee : ES.CalleeDesc → String
  | .ident x => app "ES.CalleeDesc.ident" [qStr x]
  | .prop k => app "ES.CalleeDesc.prop" [qStr k]
  | .priv k => app "ES.CalleeDesc.priv" [qStr k]
  | .computed => "ES.CalleeDesc.computed"
  | .superProp k => app "ES.CalleeDesc.superProp" [qStr k]
  | .other => "ES.CalleeDesc.other"

def isCallTarget : Nat → Expr → Bool
  | 0, _ => false
  | k + 1, e => match e with | .call .. => true | .paren e => isCallTarget k e | _ => false

mutual

/-- `(ES.evalExpr (n + k) · e)` -/
def genExpr (names : Names) : Nat → Expr → String
  | 0, e => s!"(ES.evalExpr {d 0} · {qExpr quoteDepth e})"
  | k + 1, e =>
    let fb := s!"(ES.evalExpr {d (k + 1)} · {qExpr quoteDepth e})"
    match e with
    | .this => "ES.Sem.this"
    | .ident x => app "ES.Sem.ident" [qStr x]
    | .lit l => app "ES.Sem.lit" [qLit l]
    | .paren e => genExpr names k e
    | .template c _ es => app "ES.Sem.template" [qArr (qOpt qStr) c, qArr (genExpr names k) es]
    | .unary .delete e => app "ES.Sem.deleteRef" [genRef names k e]
    | .unary .typeof e => app "ES.Sem.typeofRef" [genRef names k e]
    | .unary op e => app "ES.Sem.unary" [qUnOp op, genExpr names k e]
    | .update i p t => app "ES.Sem.update" [qBool i, qBool p, genTargetRef names k t]
    | .binary op l r => app "ES.Sem.binary" [qBinOp op, genExpr names k l, genExpr names k r]
    | .logical op l r => app "ES.Sem.logical" [qLogOp op, genExpr names k l, genExpr names k r]
    | .cond a b c => app "ES.Sem.cond" [genExpr names k a, genExpr names k b, genExpr names k c]
    | .call callee args opt directEval =>
      if directEval then fb
      else app "ES.Sem.call" [genRef names k callee, app "ES.Sem.args" [qArr (genArg names k) args],
        qBool opt, qCallee (ES.calleeDesc callee)]
    | .new c args => app "ES.Sem.new" [genExpr names k c, app "ES.Sem.args" [qArr (genArg names k) args]]
    | .member .. | .superMember _ => app "ES.Sem.getValue" [genRef names k e]
    | .chain inner => app "ES.Sem.chain" [genExpr names k inner]
    | .func f => app "ES.Sem.func" [funcRef names f, "none"]
    | .array els => app "ES.Sem.array" [qArr (genElem names k) els]
    | .object ps => app "ES.Sem.object" [qArr (genProp names k) ps]
    | .newTarget => "ES.Sem.newTarget"
    | .seq es => app "ES.Sem.seq" [qArr (genExpr names k) es]
    | .await e => app "ES.Sem.await" [genExpr names k e]
    | .assign op target value =>
      match op, target with
      | .assign, .obj .. | .assign, .arr .. => fb
      | _, _ => genAssign names k op target value
    | _ => fb

/-- `ES.elemD (n + k) el` -/
def genElem (names : Names) : Nat → ArrElem → String
  | 0, el => s!"(ES.elemD {d 0} {qArrElem quoteDepth el})"
  | k + 1, el => match el with
    | .hole => "ES.Sem.ElemD.hole"
    | .expr e => app "ES.Sem.ElemD.expr" [genExpr names k e]
    | .spread e => app "ES.Sem.ElemD.spread" [genExpr names k e]

/-- `ES.propD (n + k) pd` -/
def genProp (names : Names) : Nat → PropDef → String
  | 0, pd => s!"(ES.propD {d 0} {qPropDef quoteDepth pd})"
  | k + 1, pd =>
    let kd (key : PropName) : String := match key with
      | .computed e => app "ES.Sem.KeyD.computed" [genExpr names k e]
      | pn => app "ES.Sem.KeyD.name" [qPropName quoteDepth pn]
    match pd with
    | .init _ value true => app "ES.Sem.PropD.protoSet" [genExpr names k value]
    | .init key value false =>
      let v := if ES.isAnonymousFn value then s!"(ES.namedEval {d k} · {qExpr quoteDepth value} k)"
        else genExpr names k value
      app "ES.Sem.PropD.init" [kd key, s!"(fun k => {v})"]
    | .shorthand nm => app "ES.Sem.PropD.shorthand" [qStr nm]
    | .spread e => app "ES.Sem.PropD.spread" [genExpr names k e]
    | .method key f => app "ES.Sem.PropD.method" [kd key, funcRef names f]

/-- `ES.catchD (n + k) c` -/
def genCatch (names : Names) : Nat → CatchClause → String
  | 0, c => s!"(ES.catchD {d 0} {qCatch quoteDepth c})"
  | k + 1, .mk param body =>
    let bind := match param with
      | some p => s!"(fun c v => ES.bindPattern {d k} c {qPattern quoteDepth p} v (.init (some c.lex)))"
      | none => "(fun _ _ => pure ())"
    "{ param := " ++ qOpt (qPattern quoteDepth) param ++ ", bind := " ++ bind ++ ", body := " ++
      genStmt names k (.block body) ++ " : ES.Sem.CatchD }"

/-- `ES.caseD (n + k) c` -/
def genCase (names : Names) : Nat → SwitchCase → String
  | 0, c => s!"(ES.caseD {d 0} {qCase quoteDepth c})"
  | k + 1, .mk test body =>
    let b := match k with
      | 0 => s!"(ES.evalStmts {d 0} · {qArr (qStmt quoteDepth) body})"
      | j + 1 => app "ES.Sem.stmts" [qArr (genStmt names j) body]
    "{ test := " ++ qOpt (genExpr names k) test ++ ", body := " ++ b ++ " : ES.Sem.CaseD }"

/-- `ES.argD (n + k) a` -/
def genArg (names : Names) : Nat → Arg → String
  | 0, a => s!"(ES.argD {d 0} {qArg quoteDepth a})"
  | k + 1, a => match a with
    | .expr e => app "ES.Sem.ArgD.expr" [genExpr names k e]
    | .spread e => app "ES.Sem.ArgD.spread" [genExpr names k e]

/-- `(ES.evalRef (n + k) · e)` -/
def genRef (names : Names) : Nat → Expr → String
  | 0, e => s!"(ES.evalRef {d 0} · {qExpr quoteDepth e})"
  | k + 1, e =>
    match e with
    | .ident x => app "ES.Sem.identRef" [qStr x]
    | .paren e => genRef names k e
    | .member obj key opt =>
      let kd := match key with
        | .name x => app "ES.Sem.Key.name" [qStr x]
        | .computed ke => app "ES.Sem.Key.computed" [genExpr names k ke]
        | .priv x => app "ES.Sem.Key.priv" [qStr x]
      app "ES.Sem.memberRef" [genExpr names k obj, kd, qBool opt]
    | .chain inner => app "ES.Sem.chainRef" [genRef names k inner]
    | .superMember _ => s!"(ES.evalRef {d (k + 1)} · {qExpr quoteDepth e})"
    | e => app "ES.Sem.valueRef" [genExpr names k e]

/-- `(ES.evalTargetRef (n + k) · e)` -/
def genTargetRef (names : Names) : Nat → Expr → String
  | 0, e => s!"(ES.evalTargetRef {d 0} · {qExpr quoteDepth e})"
  | k + 1, e =>
    if isCallTarget 64 e then app "ES.Sem.callTargetRef" [genExpr names k e]
    else genRef names k e

/-- `(fun c => ES.evalAssign (n + k) c op target value)` -/
def genAssign (names : Names) : Nat → AssignOp → Pattern → Expr → String
  | 0, op, t, v => s!"(fun c => ES.evalAssign {d 0} c {qAssignOp op} {qPattern quoteDepth t} {qExpr quoteDepth v})"
  | k + 1, op, target, value =>
    let tD := match target with
      | .ident x => app "ES.Sem.identRef" [qStr x]
      | .expr e => genTargetRef names k e
      | _ => "(fun _ => pure (.value .undefined))"
    let rD := match target with
      | .ident x =>
        if ES.isAnonymousFn value then
          s!"(ES.namedEval {d k} · {qExpr quoteDepth value} (ES.PropKey.str {qStr x}))"
        else genExpr names k value
      | _ => genExpr names k value
    match op with
    | .assign => app "ES.Sem.assign" [tD, rD]
    | .op o => app "ES.Sem.assignOp" [qBinOp o, tD, genExpr names k value]
    | .logical o => app "ES.Sem.assignLogical" [qLogOp o, tD, rD]

/-- `(ES.evalStmt (n + k) · s)` -/
def genStmt (names : Names) : Nat → Stmt → String
  | 0, s => s!"(ES.evalStmt {d 0} · {qStmt quoteDepth s})"
  | k + 1, s =>
    match s with
    | .expr e => app "ES.Sem.exprStmt" [genExpr names k e]
    | .varDecl kind ds => app "ES.Sem.varDecl" [qArr (genDecl names k kind) ds]
    | .funDecl f => app "ES.Sem.funDecl" [funcRef names f]
    | .block body =>
      app "ES.Sem.block" [app "ES.lexicallyScoped" [qArr (qStmt quoteDepth) body], qArr (genStmt names k) body]
    | .empty | .debugger => "ES.Sem.empty"
    | .ret e => app "ES.Sem.ret" [qOpt (genExpr names k) e]
    | .ifS t c a => app "ES.Sem.ifS" [genExpr names k t, genStmt names k c, qOpt (genStmt names k) a]
    | .whileS t b => app "ES.Sem.whileS" [genExpr names k t, genStmt names k b]
    | .doWhile b t => app "ES.Sem.doWhile" [genStmt names k b, genExpr names k t]
    | .brk l => app "ES.Sem.brk" [qOpt qStr l]
    | .cont l => app "ES.Sem.cont" [qOpt qStr l]
    | .throw e => app "ES.Sem.throw" [genExpr names k e]
    | .forS init test update body =>
      let initD := match init with
        | none => "ES.Sem.ForInitD.none"
        | some (.expr e) => app "ES.Sem.ForInitD.expr" [genExpr names k e]
        | some (.decl .var ds) => app "ES.Sem.ForInitD.var" [genStmt names k (.varDecl .var ds)]
        | some (.decl kd ds) =>
          app "ES.Sem.ForInitD.lex" [qVarKind kd, qArr (qDeclarator quoteDepth) ds, genStmt names k (.varDecl kd ds)]
      app "ES.Sem.forS" [initD, qOpt (genExpr names k) test, qOpt (genExpr names k) update, genStmt names k body]
    | .tryS blk h fin =>
      app "ES.Sem.tryS" [genStmt names k (.block blk), qOpt (genCatch names k) h,
        qOpt (fun f => genStmt names k (.block f)) fin]
    | .switch disc cases =>
      app "ES.Sem.switch" [genExpr names k disc,
        app "ES.lexicallyScoped" [app "ES.caseBodies" [qArr (qCase quoteDepth) cases]],
        qArr (genCase names k) cases]
    | .labeled l b =>
      let breakable := match b with
        | .labeled .. | .whileS .. | .doWhile .. | .forS .. | .forIn .. | .forOf .. | .switch .. => true
        | _ => false
      app "ES.Sem.labeled" [qStr l, qBool breakable, genStmt names k b]
    | s => s!"(ES.evalStmt {d (k + 1)} · {qStmt quoteDepth s})"

/-- `ES.declD (n + k) kind d` -/
def genDecl (names : Names) : Nat → VarKind → VarDeclarator → String
  | 0, kind, dd => s!"(ES.declD {d 0} {qVarKind kind} {qDeclarator quoteDepth dd})"
  | k + 1, kind, dd =>
    let fb := s!"(ES.declD {d (k + 1)} {qVarKind kind} {qDeclarator quoteDepth dd})"
    let .mk target init := dd
    let rhs (x : JSStr) (ie : Expr) : String :=
      if ES.isAnonymousFn ie then s!"(ES.namedEval {d k} · {qExpr quoteDepth ie} (ES.PropKey.str {qStr x}))"
      else genExpr names k ie
    match kind, target, init with
    | .var, _, none => "(fun _ => pure ())"
    | .var, .ident x, some ie => app "ES.Sem.declVar" [qStr x, rhs x ie]
    | .var, _, some _ => fb
    | kd, .ident x, none => app "ES.Sem.declLex" [qVarKind kd, qStr x, "none"]
    | kd, .ident x, some ie => app "ES.Sem.declLex" [qVarKind kd, qStr x, "(some " ++ rhs x ie ++ ")"]
    | _, _, _ => fb

end

/-- `(ES.evalStmts (n + k) · ss)` -/
def genStmts (names : Names) (k : Nat) (ss : Array Stmt) : String :=
  match k with
  | 0 => s!"(ES.evalStmts {d 0} · {qArr (qStmt quoteDepth) ss})"
  | k + 1 => app "ES.Sem.stmts" [qArr (genStmt names k) ss]

mutual
/-- The functions a statement contains (outermost first). Depth-bounded like the walks in
`ES/Decls.lean` (statement nesting is far below `declDepth`). -/
def funcsStmt : Nat → Stmt → Array Func
  | 0, _ => #[]
  | n + 1, s => match s with
    | .funDecl f => #[f] ++ funcsFunc n f
    | .expr e | .throw e => funcsExpr n e
    | .varDecl _ ds => ds.foldl (fun acc (dd : VarDeclarator) => match dd with
        | .mk _ (some e) => acc ++ funcsExpr n e | _ => acc) #[]
    | .block b => b.foldl (fun acc s => acc ++ funcsStmt n s) #[]
    | .ret (some e) => funcsExpr n e
    | .ifS t c a => funcsExpr n t ++ funcsStmt n c ++ (match a with | some a => funcsStmt n a | none => #[])
    | .whileS t b | .doWhile b t => funcsExpr n t ++ funcsStmt n b
    | .labeled _ b => funcsStmt n b
    | .forS _ t u b =>
      (match t with | some t => funcsExpr n t | none => #[]) ++ (match u with | some u => funcsExpr n u | none => #[]) ++ funcsStmt n b
    | .forIn _ r b | .forOf _ r b _ => funcsExpr n r ++ funcsStmt n b
    | .tryS b h f =>
      b.foldl (fun acc s => acc ++ funcsStmt n s) #[] ++
      (match h with | some (.mk _ hb) => hb.foldl (fun acc s => acc ++ funcsStmt n s) #[] | none => #[]) ++
      (match f with | some f => f.foldl (fun acc s => acc ++ funcsStmt n s) #[] | none => #[])
    | _ => #[]

def funcsFunc : Nat → Func → Array Func
  | 0, _ => #[]
  | n + 1, f => match f.body with
    | .stmts b => b.foldl (fun acc s => acc ++ funcsStmt n s) #[]
    | .expr e => funcsExpr n e

def funcsExpr : Nat → Expr → Array Func
  | 0, _ => #[]
  | n + 1, e => match e with
    | .func f => #[f] ++ funcsFunc n f
    | .call c args _ | .new c args =>
      funcsExpr n c ++ args.foldl (fun acc a => match a with | .expr e | .spread e => acc ++ funcsExpr n e) #[]
    | .binary _ l r | .logical _ l r => funcsExpr n l ++ funcsExpr n r
    | .cond a b c => funcsExpr n a ++ funcsExpr n b ++ funcsExpr n c
    | .assign _ _ v => funcsExpr n v
    | .unary _ e | .paren e | .chain e | .await e => funcsExpr n e
    | .seq es => es.foldl (fun acc e => acc ++ funcsExpr n e) #[]
    | .member o _ _ => funcsExpr n o
    | _ => #[]
end

/-- The functions a program contains, outermost first. -/
def collectFuncs (ss : Array Stmt) : Array Func := ss.foldl (fun acc s => acc ++ funcsStmt declDepth s) #[]

/-- A Lean identifier for a JS function. -/
def defName (used : Std.HashSet String) (f : Func) : String :=
  let base := match f.name with
    | some n =>
      let s := n.toString
      if s.all (fun c => c.isAlphanum || c == '_') && !s.isEmpty && !(s.get 0).isDigit then s else s!"fn{f.info.id}"
    | none => s!"fn{f.info.id}"
  if used.contains base then s!"{base}_{f.info.id}" else base

/-- The maximum parenthesis nesting of a quoted tree: at least its height (each node's quote is
one more level of parentheses). -/
def parenDepth (s : String) : Nat :=
  (s.foldl (fun (cur, mx) c =>
    if c == '(' then (cur + 1, max mx (cur + 1)) else if c == ')' then (cur - 1, mx) else (cur, mx)) (0, 0)).2

/-- The depth the generated definitions start at: above what the interpreter spends on the tree
(at most 3 steps per level of the tree: e.g. expression → assignment → target). -/
def depthFor (quoted : String) : Nat := 3 * parenDepth quoted + 8

/-- Generated code for reading: within `open ES`, names without the `ES.` prefix and strings as
literals (the `String → JSStr` coercion elaborates to the same `JSStr.ofString` term, which the
`rfl` theorems check). -/
def tidy (code : String) : String := Id.run do
  -- (ES.JSStr.ofString "…") → "…"
  let parts := code.splitOn "(ES.JSStr.ofString "
  let mut out := parts.head!
  for p in parts.tail! do
    -- p starts with the string literal, then ")"
    let chars := p.toList
    let mut i := 1
    let mut esc := false
    for c in chars.drop 1 do
      i := i + 1
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then break
    out := out ++ String.ofList (chars.take i) ++ String.ofList (chars.drop (i + 1))
  return out.replace "(ES." "(" |>.replace " ES." " " |>.replace "[ES." "[" |>.replace "#[ES." "#["

/-- A Lean module with, for the program and each of its functions, the syntax tree, the
generated denotation, and its theorem. -/
def emitModule (prog : Program) (title : String) : String := Id.run do
  let fs := collectFuncs prog.body
  let mut names : Names := {}
  let mut used : Std.HashSet String := {}
  for f in fs do
    let nm := defName used f
    used := used.insert nm
    names := names.insert f.info.id nm
  let mut out := s!"import ES.Engine

/-! {title}

Generated by `leanjs compile --defs`: for the script and each function, its syntax tree, its
denotation built from `ES.Sem` combinators, and a theorem that the denotation is the interpreter's
(`ES.evalStmts`) for every depth above the tree's height. -/

open ES

namespace Compiled

"
  -- (functions: their ASTs first, outermost first: nested functions are referenced by name)
  for f in fs.reverse do
    let nm := (names.get? f.info.id).getD "fn"
    out := out ++ s!"/-- The syntax tree of `{nm}`. -/\ndef {nm}_func : ES.Func := {qFunc quoteDepth f}\n\n"
  for f in fs do
    let nm := (names.get? f.info.id).getD "fn"
    match f.body with
    | .stmts body =>
      let H := depthFor (qArr (qStmt quoteDepth) body)
      out := out ++ s!"def {nm}_stmts : Array ES.Stmt := {qArr (qStmt quoteDepth) body}\n\n"
      out := out ++ s!"/-- The body of `{nm}`. -/\ndef {nm} (n : Nat) : Sem.CStmt :=\n  {tidy (genStmts names H body)}\n\n"
      out := out ++ s!"set_option maxRecDepth 100000 in\ntheorem {nm}_eq (n : Nat) : {nm} n = (ES.evalStmts (n + {H}) · {nm}_stmts) := by\n  funext c; rfl\n\n"
    | .expr _ => pure ()
  let H := depthFor (qArr (qStmt quoteDepth) prog.body)
  out := out ++ s!"def script_stmts : Array ES.Stmt := {qArr (qStmt quoteDepth) prog.body}\n\n"
  out := out ++ s!"/-- The script's top-level code. -/\ndef script (n : Nat) : Sem.CStmt :=\n  {tidy (genStmts names H prog.body)}\n\n"
  out := out ++ s!"set_option maxRecDepth 100000 in\ntheorem script_eq (n : Nat) : script n = (ES.evalStmts (n + {H}) · script_stmts) := by\n  funext c; rfl\n\n"
  out := out ++ s!"def program : ES.Program :=\n  \{ body := script_stmts, isModule := false, strict := {qBool prog.strict}, source := {qLeanString prog.source} }\n\n"
  out := out ++ "end Compiled

def main : IO UInt32 := ES.runCompiled Compiled.program
"
  return out

end ES.Gen
