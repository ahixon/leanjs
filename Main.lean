import LeanJS
import LeanJS.Semantics.SimCompose

open LeanJS

/-! ## Lean modules as core expressions

A Lean module made only of non-recursive `def`s is treated as the
expression `let f₁ := … ; … ; let fₙ := … ; ()`, which is what the verified
Lean translations operate on. -/

/-- Does identifier `x` occur anywhere in `e`? (Conservative: ignores shadowing.) -/
partial def leanMentions (x : String) : Lean.LeanExpr → Bool
  | .ident y => x == y
  | .lit _ | .unit | .hole => false
  | .app f a => leanMentions x f || leanMentions x a
  | .lam _ b => leanMentions x b
  | .«let» _ _ v b => leanMentions x v || leanMentions x b
  | .bind _ _ v => leanMentions x v
  | .doBlock _ => true
  | .«if» c t e => leanMentions x c || leanMentions x t || (e.map (leanMentions x)).getD false
  | .«match» s alts => leanMentions x s || alts.any fun | .mk _ b => leanMentions x b
  | .«while» c b => leanMentions x c || leanMentions x b
  | .«for» _ i b => leanMentions x i || leanMentions x b
  | .«return» v | .refNew v | .refGet v | .«throw» v | .paren v => leanMentions x v
  | .proj e _ => leanMentions x e
  | .structLit _ fs => fs.any fun (_, e) => leanMentions x e
  | .arrayLit es => es.any (leanMentions x)
  | .arrayIdx a i => leanMentions x a || leanMentions x i
  | .binOp _ l r => leanMentions x l || leanMentions x r
  | .unaryOp _ a => leanMentions x a
  | .refSet r v => leanMentions x r || leanMentions x v
  | .«try» b _ h f => leanMentions x b || (h.map (leanMentions x)).getD false ||
      (f.map (leanMentions x)).getD false

def moduleToCoreExpr (m : Lean.LeanModule) : Except String Lean.LeanExpr :=
  m.decls.foldr (init := .ok .unit) fun d acc => do
    let rest ← acc
    match d with
    | .def_ name params _ body =>
      if leanMentions name body then
        throw s!"unsupported: recursive definition `{name}`"
      let value := if params.isEmpty then body else .lam params body
      pure (.«let» name none value rest)
    | .let_ name ty value => pure (.«let» name ty value rest)
    | _ => throw "unsupported: only `def` declarations"

/-- Turn a let-chain ending in `()` back into a module of `def`s -/
def coreExprToModule : Lean.LeanExpr → Option Lean.LeanModule
  | .unit => some {}
  | .«let» name _ (.lam ps body) rest => do
    let m ← coreExprToModule rest
    pure { m with decls := .def_ name ps none body :: m.decls }
  | .«let» name _ value rest => do
    let m ← coreExprToModule rest
    pure { m with decls := .def_ name [] none value :: m.decls }
  | _ => none

def emitLeanCore (e : Lean.LeanExpr) : String :=
  match coreExprToModule e with
  | some m => Lean.Emit.emitLeanModule m
  | none => Lean.Emit.emitLeanExpr e ++ "\n"

/-! ## Commands -/

def readFile (file : String) : IO String := IO.FS.readFile file

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def note (verified : Bool) (reason : String := "") : IO Unit :=
  if verified then
    IO.eprintln "[verified] translated by the verified core translator"
  else
    IO.eprintln s!"[unverified] outside the verified core ({reason}); using the legacy translator"

def parseJS (file : String) : IO (Except String JS.Program) := do
  return JS.Parser.parseProgram (← readFile file)

def parseLean (file : String) : IO (Except String Lean.LeanModule) := do
  return Lean.Parser.parseModule (← readFile file)

def cmdParse (file : String) : IO UInt32 := do
  match ← parseJS file with
  | .error err => fail s!"Parse error: {err}"
  | .ok prog => IO.println (JS.Emit.emitProgram prog); return 0

def cmdIR (file : String) : IO UInt32 := do
  match ← parseJS file with
  | .error err => fail s!"Parse error: {err}"
  | .ok prog =>
    match Trans.Core.jsStmts prog with
    | .ok ⟨ir, _⟩ =>
      note true; IO.println (IR.Print.printExpr ir); return 0
    | .error why =>
      note false why
      match Trans.JSToIR.translateToIR prog with
      | .ok ir => IO.println (IR.Print.printExpr ir); return 0
      | .error err => fail s!"Translation error: {err}"

def cmdRoundtrip (file : String) : IO UInt32 := do
  match ← parseJS file with
  | .error err => fail s!"Parse error: {err}"
  | .ok prog =>
    match Trans.Core.jsRoundtrip prog with
    | .ok prog' =>
      note true; IO.println (JS.Emit.emitProgram prog'); return 0
    | .error why =>
      note false why
      match Trans.JSToIR.translateToIR prog with
      | .error err => fail s!"JS→IR error: {err}"
      | .ok ir =>
        match Trans.IRToJS.translateToJS ir with
        | .ok stmts => IO.println (JS.Emit.emitProgram stmts); return 0
        | .error err => fail s!"IR→JS error: {err}"

def cmdLean (file : String) : IO UInt32 := do
  match ← parseJS file with
  | .error err => fail s!"Parse error: {err}"
  | .ok prog =>
    match Trans.JSToIR.translateToIR prog with
    | .error err => fail s!"JS→IR error: {err}"
    | .ok ir =>
      match Trans.IRToLean.translateIRToLeanModule ir with
      | .ok mod => IO.print (Lean.Emit.emitLeanModule mod); return 0
      | .error err => fail s!"IR→Lean error: {err}"

def cmdLeanExpr (file : String) : IO UInt32 := do
  match ← parseJS file with
  | .error err => fail s!"Parse error: {err}"
  | .ok prog =>
    match Trans.Core.jsToLean prog with
    | .ok e => note true; IO.println (Lean.Emit.emitLeanExpr e); return 0
    | .error why =>
      note false why
      match Trans.JSToIR.translateToIR prog with
      | .error err => fail s!"JS→IR error: {err}"
      | .ok ir =>
        match Trans.IRToLean.translateIRToLean ir with
        | .ok expr => IO.println (Lean.Emit.emitLeanExpr expr); return 0
        | .error err => fail s!"IR→Lean error: {err}"

def cmdLeanRoundtrip (file : String) : IO UInt32 := do
  match ← parseLean file with
  | .error err => fail s!"Parse error: {err}"
  | .ok mod => IO.print (Lean.Emit.emitLeanModule mod); return 0

def cmdLeanIRRoundtrip (file : String) : IO UInt32 := do
  match ← parseLean file with
  | .error err => fail s!"Parse error: {err}"
  | .ok mod =>
    match moduleToCoreExpr mod >>= Trans.Core.leanRoundtrip with
    | .ok e => note true; IO.print (emitLeanCore e); return 0
    | .error why =>
      note false why
      match Trans.LeanToIR.translateModule mod with
      | .error err => fail s!"Lean→IR error: {err}"
      | .ok irMod =>
        match Trans.IRToLean.translateModule irMod with
        | .ok mod' => IO.print (Lean.Emit.emitLeanModule mod'); return 0
        | .error err => fail s!"IR→Lean error: {err}"

def cmdJS (file : String) : IO UInt32 := do
  match ← parseLean file with
  | .error err => fail s!"Parse error: {err}"
  | .ok mod =>
    match moduleToCoreExpr mod >>= Trans.Core.leanToJS with
    | .ok prog => note true; IO.println (JS.Emit.emitProgram prog); return 0
    | .error why =>
      note false why
      match Trans.LeanToIR.translateModule mod with
      | .error err => fail s!"Lean→IR error: {err}"
      | .ok irMod =>
        match Trans.IRToJS.translateModuleToJS irMod with
        | .ok stmts => IO.println (JS.Emit.emitProgram stmts); return 0
        | .error err => fail s!"IR→JS error: {err}"

def verdict {α : Type} (name : String) : Except String α → String
  | .ok _ => s!"  {name}: verified"
  | .error why => s!"  {name}: not in verified core — {why}"

def cmdCheck (file : String) : IO UInt32 := do
  if file.endsWith ".lean" then
    match ← parseLean file with
    | .error err => fail s!"Parse error: {err}"
    | .ok mod =>
      let core := moduleToCoreExpr mod
      IO.println s!"{file}:"
      IO.println (verdict "Lean → IR → JS  " (core >>= Trans.Core.leanToJS))
      IO.println (verdict "Lean → IR → Lean" (core >>= Trans.Core.leanRoundtrip))
      return 0
  else
    match ← parseJS file with
    | .error err => fail s!"Parse error: {err}"
    | .ok prog =>
      IO.println s!"{file}:"
      IO.println (verdict "JS → IR → JS    " (Trans.Core.jsRoundtrip prog))
      IO.println (verdict "JS → IR → Lean  " (Trans.Core.jsToLean prog))
      return 0

def usage : IO UInt32 := do
  IO.eprintln "Usage: lean-js <command> <file>"
  IO.eprintln "Commands:"
  IO.eprintln "  parse             Parse JS and emit it back"
  IO.eprintln "  ir                Parse JS and show IR"
  IO.eprintln "  roundtrip         JS → IR → JS"
  IO.eprintln "  lean              JS → IR → Lean (module-level, unverified)"
  IO.eprintln "  lean-expr         JS → IR → Lean (expression-level)"
  IO.eprintln "  lean-roundtrip    Parse Lean and emit it back"
  IO.eprintln "  lean-ir-roundtrip Lean → IR → Lean"
  IO.eprintln "  js                Lean → IR → JS"
  IO.eprintln "  check             Report whether a .js/.lean file is in the verified core"
  IO.eprintln ""
  IO.eprintln "Commands that can use the verified core translator say so on stderr:"
  IO.eprintln "[verified] or [unverified] (with the reason)."
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["parse", f] => cmdParse f
  | ["ir", f] => cmdIR f
  | ["roundtrip", f] => cmdRoundtrip f
  | ["lean", f] => cmdLean f
  | ["lean-expr", f] => cmdLeanExpr f
  | ["lean-roundtrip", f] => cmdLeanRoundtrip f
  | ["lean-ir-roundtrip", f] => cmdLeanIRRoundtrip f
  | ["js", f] => cmdJS f
  | ["check", f] => cmdCheck f
  | _ => usage
