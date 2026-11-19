import ES.Lexer
import ES.Regex
import ES.Decls
import Std.Data.HashSet

/-!
# ECMAScript parser

spec: https://tc39.es/ecma262/#sec-ecmascript-language-source-code

Recursive descent over the syntactic grammar for the Script and Module goals, with every early
error (spec: https://tc39.es/ecma262/#sec-static-semantic-rules) and Annex B's syntax
(spec: https://tc39.es/ecma262/#sec-additional-ecmascript-features-for-web-browsers).

- Tokens come from `ES/Lexer.lean` on demand; `/`, `/=` and `}` are re-scanned as regular
  expressions / template continuations where the grammar asks for them.
- Cover grammars are parsed as expressions and refined: arrow parameters and assignment
  patterns become `Pattern`s (`toPattern`); `Cover` keeps the errors an expression has only
  if it is not refined (CoverInitializedName, duplicate `__proto__`, a comma after a rest).
- Scope analysis (duplicate declarations, var/let conflicts, Annex B's catch and function
  rules) follows the structure of the spec's LexicallyDeclaredNames/VarDeclaredNames early
  errors, incrementally: each scope keeps its names.
- Recursion is bounded by `maxNesting` (see there): every recursive call goes through a `Rec`
  record of the next level down, so all functions are total without `partial`.
-/

namespace ES.Parse

/-- A callee that makes a call a direct-eval candidate: the identifier `eval`. -/
def isEvalIdent : Expr → Bool
  | .ident n => n == JSStr.ofString "eval"
  | _ => false

open ES (F64)
open Std (HashSet HashMap)
open ES.Lex

instance : Inhabited Expr := ⟨.this⟩
instance : Inhabited Stmt := ⟨.empty⟩
instance : Inhabited Pattern := ⟨.ident JSStr.empty⟩
instance : Inhabited PropDef := ⟨.shorthand JSStr.empty⟩
instance : Inhabited ArrElem := ⟨.hole⟩
instance : Inhabited Arg := ⟨.expr .this⟩
instance : Inhabited Param := ⟨.mk (.ident JSStr.empty) none false⟩
instance : Inhabited PropName := ⟨.ident JSStr.empty⟩
instance : Inhabited Class := ⟨.mk none none #[] {}⟩

/-- RegExp pattern validation (`Regex.compile`). -/
def regexCompile (pattern flags : JSStr) : Except String Unit :=
  (Regex.compile pattern flags).map fun _ => ()

/-! ## Parser state -/

/-- Scope flags. -/
def sVar : Nat := 1        -- a var scope (function, script, eval, static block)
def sTop : Nat := 2        -- the script/module/eval top level
def sFunction : Nat := 4   -- a function's scope (parameters and body)
def sSimpleCatch : Nat := 8
def sStaticBlock : Nat := 16

@[inline] def hasFlag (flags f : Nat) : Bool := flags &&& f != 0

structure Scope where
  flags : Nat
  vars : HashSet JSStr := {}
  lexical : HashSet JSStr := {}
  /-- Function declarations that are not lexical here: top-level ones in functions/scripts and
  sloppy-mode plain functions in blocks (Annex B.3.2.4 allows their duplicates). -/
  funcs : HashSet JSStr := {}
  catchName : Option JSStr := none
  deriving Inhabited

/-- The innermost function-like code being parsed: what its grammar parameters ([Yield],
[Await], [Return]) and contained-in early errors allow, and the facts `FuncInfo` records. -/
structure Fn where
  isArrow : Bool := false
  /-- `await` starts an AwaitExpression. -/
  awaitExpr : Bool := false
  /-- `await` may not be an identifier here (besides module code). -/
  awaitReserved : Bool := false
  /-- `yield` starts a YieldExpression (generator bodies and parameters). -/
  yieldExpr : Bool := false
  superProp : Bool := false
  superCall : Bool := false
  newTarget : Bool := false
  /-- ContainsArguments is an error (class field initializers, static blocks). -/
  noArguments : Bool := false
  returnOk : Bool := false
  /-- In a class static block (await is reserved; no `arguments`). -/
  staticBlock : Bool := false
  /-- In a class field initializer (no yield/await expressions). -/
  fieldInit : Bool := false
  -- facts for FuncInfo
  argsRef : Bool := false
  thisRef : Bool := false
  arrowThis : Bool := false
  hasEval : Bool := false
  deriving Inhabited

structure Label where
  name : Option JSStr
  /-- 0: plain label, 1: iteration, 2: switch. -/
  kind : Nat
  stmtStart : Nat
  deriving Inhabited

/-- A class body's private names: declared (kinds: 1 getter, 2 setter, 4 other, +8 static) and
referenced ones (resolved when the class ends). -/
structure ClassCtx where
  declared : HashMap JSStr Nat := {}
  used : Array (JSStr × Nat) := #[]
  deriving Inhabited

/-- Errors of a cover grammar that apply only if the expression is not refined to a pattern
(positions + 1; 0 = none). -/
structure Cover where
  shorthand : Nat := 0
  proto : Nat := 0
  trailing : Nat := 0
  deriving Inhabited

def Cover.merge (a b : Cover) : Cover :=
  { shorthand := if a.shorthand != 0 then a.shorthand else b.shorthand
    proto := if a.proto != 0 then a.proto else b.proto
    trailing := if a.trailing != 0 then a.trailing else b.trailing }

structure PState where
  src : ByteArray
  isModule : Bool
  tok : Token := {}
  prevEnd : Nat := 0
  strict : Bool := false
  fn : Fn := {}
  scopes : Array Scope := #[]
  labels : Array Label := #[]
  classes : Array ClassCtx := #[]
  /-- Private names visible from outside the parsed text (direct eval in a class). -/
  outerPrivate : Array JSStr := #[]
  /-- First YieldExpression / AwaitExpression / `await` identifier since the last reset
  (position + 1): arrow and async arrow parameters must not contain them. -/
  yieldPos : Nat := 0
  awaitPos : Nat := 0
  awaitIdentPos : Nat := 0
  nextId : Nat := 0
  nextSite : Nat := 0
  /-- Remaining nesting budget (see `maxNesting`). -/
  budget : Nat := 0
  exported : HashSet JSStr := {}
  exportLocals : Array (JSStr × Nat) := #[]
  deriving Inhabited

abbrev P := EStateM SyntaxError PState

@[inline] def fail {α : Type} (msg : String) (pos : Nat) : P α := throw { msg, pos }

/-- The nesting limit: how deeply the grammar's recursive productions (nested expressions,
statements, functions, patterns) and left-associative chains (binary operators, member and
call suffixes) may nest. Exceeding it is a SyntaxError ("too much nesting"), a resource limit
like engines' parser stack limits. It bounds both the parser's own recursion (each level is a
`Rec` one level down, so `maxNesting` levels of `Rec` always suffice: the budget runs out
first) and the height of the syntax trees produced: every node is built at a level at most
`maxNesting` deep, and each level adds a bounded number (≤ 8) of nested constructors, so
recursion over a tree from the parser terminates with fuel `8 * maxNesting + 64` (`astFuel`). -/
def maxNesting : Nat := 1000

/-- Fuel for recursion over parsed syntax trees (see `maxNesting`). -/
def astFuel : Nat := 8 * maxNesting + 64

@[inline] def tok : P Token := return (← get).tok
@[inline] def tokKind : P T := return (← get).tok.kind

/-- Advances to the next token (InputElementDiv). -/
def next : P Unit := do
  let s ← get
  match lex s.src s.tok.stop s.isModule with
  | .ok t => set { s with prevEnd := s.tok.stop, tok := t }
  | .error e => throw e

/-- The token after the current one, without consuming anything. -/
def peek : P Token := do
  let s ← get
  match lex s.src s.tok.stop s.isModule with
  | .ok t => return t
  | .error e => throw e

/-- The token after the next one (two-token lookahead). -/
def peek2 : P Token := do
  let s ← get
  let p ← peek
  match lex s.src p.stop s.isModule with
  | .ok t => return t
  | .error e => throw e

/-- The third token from the current one. -/
def peek3 : P Token := do
  let s ← get
  let p ← peek2
  match lex s.src p.stop s.isModule with
  | .ok t => return t
  | .error e => throw e

/-- Re-scans the current token (`/` or `/=`) as a RegularExpressionLiteral. -/
def rescanRegex : P Token := do
  let s ← get
  match lexRegex s.src s.tok.start with
  | .ok t => let t := { t with nl := s.tok.nl }; set { s with tok := t }; return t
  | .error e => throw e

/-- Re-scans the current token (`}`) as a TemplateMiddle / TemplateTail. -/
def rescanTemplate : P Token := do
  let s ← get
  match lexTemplate s.src s.tok.start with
  | .ok t => set { s with tok := t }; return t
  | .error e => throw e

@[inline] def isT (k : T) : P Bool := return (← tokKind) == k

def eat (k : T) : P Bool := do
  if (← tokKind) == k then next; return true
  return false

def unexpected {α : Type} : P α := do
  let t ← tok
  if t.kind == .eof then fail "unexpected end of input" t.start
  fail "unexpected token" t.start

def expect (k : T) : P Unit := do
  if !(← eat k) then unexpected

/-- The current token is the (unescaped) word `kw`. -/
@[inline] def isKw (kw : Kw) : P Bool := do
  let t ← tok
  return t.kind == .name && t.kw == kw && !t.escaped

/-- The current token is the reserved word `kw`; escaped reserved words are errors where a
keyword is expected.
spec: https://tc39.es/ecma262/#sec-keywords-and-reserved-words -/
def isKeyword (kw : Kw) : P Bool := do
  let t ← tok
  if t.kind == .name && t.kw == kw then
    if t.escaped then
      if kw.isReserved then fail "keyword must not contain escaped characters" t.start
      return false
    return true
  return false

def eatKw (kw : Kw) : P Bool := do
  if ← isKw kw then next; return true
  return false

def expectKw (kw : Kw) : P Unit := do
  if !(← eatKw kw) then unexpected

/-- Automatic semicolon insertion: a `;`, or before `}`, the end, or a line terminator.
spec: https://tc39.es/ecma262/#sec-rules-of-automatic-semicolon-insertion -/
def semicolon : P Unit := do
  if ← eat .semi then return
  let t ← tok
  if t.kind == .rbrace || t.kind == .eof || t.nl then return
  unexpected

def canInsertSemi : P Bool := do
  let t ← tok
  return t.kind == .semi || t.kind == .rbrace || t.kind == .eof || t.nl

@[inline] def setFn (f : Fn → Fn) : P Unit := modify fun s => { s with fn := f s.fn }

def freshId : P Nat := modifyGet fun s => (s.nextId, { s with nextId := s.nextId + 1 })

/-- The source text `[a, b)` as raw bytes compared with an ASCII string. -/
def srcIs (a b : Nat) (lit : String) : P Bool := do
  let s ← get
  let bytes := lit.toUTF8
  if b - a != bytes.size then return false
  let mut ok := true
  for i in [0:bytes.size] do
    if s.src.get! (a + i) != bytes.get! i then ok := false
  return ok

/-- One level of nesting (see `maxNesting`). -/
@[inline] def nest {α : Type} (p : P α) : P α := do
  let s ← get
  let b := s.budget
  if b == 0 then fail "too much nesting" s.tok.start
  set { s with budget := b - 1 }
  let x ← p
  modify fun s => { s with budget := b }
  return x

/-- A link in a left-associative chain: uses up nesting budget until the chain is done (the
caller restores the budget). -/
def chainStep : P Unit := do
  let s ← get
  if s.budget == 0 then fail "too much nesting" s.tok.start
  set { s with budget := s.budget - 1 }

@[inline] def restoreBudget (b : Nat) : P Unit := modify fun s => { s with budget := b }

/-! ## Names -/

def kArguments : JSStr := "arguments"
def kEval : JSStr := "eval"
def kLet : JSStr := "let"
def kAsync : JSStr := "async"
def kConstructor : JSStr := "constructor"
def kPrototype : JSStr := "prototype"
def kProto : JSStr := "__proto__"
def kDefault : JSStr := "default"
def kStarDefault : JSStr := "*default*"

def isEvalOrArgs (n : JSStr) : Bool := n == kEval || n == kArguments

/-- The early errors of an Identifier used as IdentifierReference, BindingIdentifier or
LabelIdentifier in the current context.
spec: https://tc39.es/ecma262/#sec-identifiers-static-semantics-early-errors -/
def checkIdent (t : Token) (binding : Bool) : P Unit := do
  let s ← get
  let kw := t.kw
  if kw == .none then
    if binding && s.strict && isEvalOrArgs t.val then
      fail s!"'{t.val}' cannot be a binding in strict mode" t.start
    return
  if kw.isReserved then fail s!"unexpected reserved word '{t.val}'" t.start
  if kw == .kYield then
    if s.strict then fail "'yield' is reserved in strict mode" t.start
    if s.fn.yieldExpr then fail "'yield' cannot be an identifier in a generator" t.start
    return
  if kw == .kAwait then
    if s.isModule || s.fn.awaitExpr || s.fn.awaitReserved then
      fail "'await' cannot be an identifier here" t.start
    if s.awaitIdentPos == 0 then modify fun s => { s with awaitIdentPos := t.start + 1 }
    return
  if s.strict && kw.isStrictReserved then
    fail s!"'{t.val}' is reserved in strict mode" t.start
  if binding && s.strict && (kw == .kEval || kw == .kArguments) then
    fail s!"'{t.val}' cannot be a binding in strict mode" t.start

/-- The re-check of a binding name when a function's code turns out to be strict (a "use
strict" directive in its body). -/
def checkStrictBinding (name : JSStr) (kw : Kw) (pos : Nat) : P Unit := do
  if isEvalOrArgs name then fail s!"'{name}' cannot be a binding in strict mode" pos
  if kw.isStrictReserved then fail s!"'{name}' is reserved in strict mode" pos

/-- An IdentifierReference at the current token: consumes it. -/
def identRef : P JSStr := do
  let t ← tok
  if t.kind != .name then unexpected
  checkIdent t false
  let s ← get
  if t.val == kArguments then
    if s.fn.noArguments then fail "'arguments' is not allowed in class field initializers or static blocks" t.start
    setFn fun f => { f with argsRef := true }
  next
  return t.val

/-- A BindingIdentifier at the current token: the name, its keyword, its position. -/
def bindingIdent : P (JSStr × Kw × Nat) := do
  let t ← tok
  if t.kind != .name then unexpected
  checkIdent t true
  next
  return (t.val, (if t.escaped && t.kw.isReserved then .none else t.kw), t.start)

/-! ## Scopes

spec: https://tc39.es/ecma262/#sec-block-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-variablestatements-in-catch-blocks -/

def enterScope (flags : Nat) : P Unit :=
  modify fun s => { s with scopes := s.scopes.push { flags } }

def exitScope : P Unit := modify fun s => { s with scopes := s.scopes.pop }

/-- Whether function declarations directly in this scope are var-like (function bodies and
the top level of scripts). -/
def funcsAsVar (s : PState) (sc : Scope) : Bool :=
  hasFlag sc.flags sFunction || (!s.isModule && hasFlag sc.flags sTop)

def funcsAsVar' (isModule : Bool) (sc : Scope) : Bool :=
  hasFlag sc.flags sFunction || (!isModule && hasFlag sc.flags sTop)

/-- Declares a `var`-scoped name: conflicts with lexical declarations in every scope up to the
var scope (a simple catch parameter of the same name excepted, Annex B.3.4).
spec: https://tc39.es/ecma262/#sec-variablestatements-in-catch-blocks -/
def declareVar (name : JSStr) (pos : Nat) : P Unit := do
  let isModule := (← get).isModule
  let mut scopes := (← get).scopes
  modify fun s => { s with scopes := #[] }
  let mut i := scopes.size
  let mut bad := false
  for _ in [0:scopes.size] do
    if i == 0 then break
    i := i - 1
    let sc := scopes[i]!
    if (sc.lexical.contains name && !(hasFlag sc.flags sSimpleCatch && sc.catchName == some name)) ||
        (!funcsAsVar' isModule sc && sc.funcs.contains name) then
      bad := true
    scopes := scopes.modify i fun sc => { sc with vars := sc.vars.insert name }
    if hasFlag sc.flags sVar then break
  modify fun s => { s with scopes }
  if bad then fail s!"identifier '{name}' has already been declared" pos

/-- Declares a lexically scoped name in the current scope. -/
def declareLex (name : JSStr) (pos : Nat) : P Unit := do
  let mut scopes := (← get).scopes
  modify fun s => { s with scopes := #[] }
  let i := scopes.size - 1
  let sc := scopes[i]!
  let bad := sc.lexical.contains name || sc.funcs.contains name || sc.vars.contains name
  scopes := scopes.modify i fun sc => { sc with lexical := sc.lexical.insert name }
  modify fun s => { s with scopes }
  if bad then fail s!"identifier '{name}' has already been declared" pos

/-- Declares a function declaration's name: var-like at function/script top level, lexical in
blocks and modules (sloppy-mode plain functions in blocks may repeat: Annex B.3.2.4).
spec: https://tc39.es/ecma262/#sec-block-duplicates-allowed-static-semantics -/
def declareFunc (name : JSStr) (pos : Nat) (plain : Bool) : P Unit := do
  let s ← get
  let i := s.scopes.size - 1
  let sc := s.scopes[i]!
  if funcsAsVar s sc then
    if sc.lexical.contains name then fail s!"identifier '{name}' has already been declared" pos
    modify fun s => { s with scopes := s.scopes.modify i fun sc => { sc with funcs := sc.funcs.insert name } }
  else if s.strict || !plain then declareLex name pos
  else
    if sc.lexical.contains name || sc.vars.contains name then
      fail s!"identifier '{name}' has already been declared" pos
    modify fun s => { s with scopes := s.scopes.modify i fun sc => { sc with funcs := sc.funcs.insert name } }

/-! ## Patterns -/

/-- BoundNames of a pattern (fuel: `astFuel`, see `maxNesting`).
spec: https://tc39.es/ecma262/#sec-static-semantics-boundnames -/
def patNames : Nat → Pattern → Array JSStr → Array JSStr
  | 0, _, acc => acc
  | n + 1, p, acc =>
    match p with
    | .ident x => acc.push x
    | .expr _ => acc
    | .obj props rest =>
      let acc := props.foldl (fun acc pp => match pp with | .mk _ t _ => patNames n t acc) acc
      match rest with | some r => patNames n r acc | none => acc
    | .arr elems rest =>
      let acc := elems.foldl (fun acc e => match e with
        | some (.mk t _) => patNames n t acc | none => acc) acc
      match rest with | some r => patNames n r acc | none => acc

def paramNames (ps : Array Param) : Array JSStr :=
  ps.foldl (fun acc p => match p with | .mk t _ _ => patNames astFuel t acc) #[]

/-- ContainsExpression of a pattern: initializers or computed property names.
spec: https://tc39.es/ecma262/#sec-static-semantics-containsexpression -/
def patHasExpr : Nat → Pattern → Bool
  | 0, _ => false
  | n + 1, p =>
    match p with
    | .ident _ | .expr _ => false
    | .obj props rest =>
      props.any (fun pp => match pp with
        | .mk k t i => i.isSome || (match k with | .computed _ => true | _ => false) || patHasExpr n t) ||
      (match rest with | some r => patHasExpr n r | none => false)
    | .arr elems rest =>
      elems.any (fun e => match e with | some (.mk t i) => i.isSome || patHasExpr n t | none => false) ||
      (match rest with | some r => patHasExpr n r | none => false)

/-- IsSimpleParameterList. spec: https://tc39.es/ecma262/#sec-static-semantics-issimpleparameterlist -/
def isSimpleParams (ps : Array Param) : Bool :=
  ps.all fun p => match p with | .mk (.ident _) none false => true | _ => false

/-- ExpectedArgumentCount. spec: https://tc39.es/ecma262/#sec-static-semantics-expectedargumentcount -/
def expectedArgs (ps : Array Param) : Nat := Id.run do
  let mut n := 0
  for p in ps do
    match p with
    | .mk _ none false => n := n + 1
    | _ => break
  return n

/-- Checks a binding pattern built from an assignment pattern (arrow parameters): only
identifiers are targets. -/
def checkBindingPat : Nat → Pattern → Nat → P Unit
  | 0, _, pos => fail "too much nesting" pos
  | n + 1, p, pos => do
    match p with
    | .ident x =>
      if (← get).strict && isEvalOrArgs x then fail s!"'{x}' cannot be a binding in strict mode" pos
    | .expr _ => fail "invalid destructuring target" pos
    | .obj props rest =>
      for pp in props do
        match pp with | .mk _ t _ => checkBindingPat n t pos
      match rest with
      | some (.ident _) => pure ()
      | some _ => fail "invalid rest element" pos
      | none => pure ()
    | .arr elems rest =>
      for e in elems do
        match e with | some (.mk t _) => checkBindingPat n t pos | none => pure ()
      match rest with | some r => checkBindingPat n r pos | none => pure ()

/-- The target of a simple assignment inside parentheses: identifiers and property accesses
(`(a) = 1`, `((a.b)) = 1`). -/
def simpleParenTarget : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .ident _ | .superMember _ => true
    | .member _ _ false => true
    | .paren e => simpleParenTarget n e
    | _ => false

def parenIdent : Nat → Expr → Option JSStr
  | 0, _ => none
  | n + 1, e => match e with | .ident x => some x | .paren e => parenIdent n e | _ => none

/-- A pattern element or property value: a target with an optional default (`a = 1`);
`rec` refines the target. -/
def elemPattern (rec : Bool → Expr → Nat → P Pattern) (binding : Bool) (v : Expr) (pos : Nat) :
    P (Pattern × Option Expr) := do
  match v with
  | .assign .assign t d =>
    if binding then checkBindingPat astFuel t pos
    if let .expr (.call ..) := t then fail "invalid destructuring target" pos
    return (t, some d)
  | _ =>
    let t ← rec binding v pos
    if let .expr (.call ..) := t then fail "invalid destructuring target" pos
    return (t, none)

/-- Refines an expression (a cover grammar) to an assignment pattern (`binding = false`) or a
binding pattern (`binding = true`, arrow parameters).
spec: https://tc39.es/ecma262/#sec-destructuring-assignment-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-static-semantics-assignmenttargettype -/
def toPattern : Nat → Bool → Expr → Nat → P Pattern
  | 0, _, _, pos => fail "too much nesting" pos
  | n + 1, binding, e, pos => do
    let strict := (← get).strict
    match e with
    | .ident x =>
      if strict && isEvalOrArgs x then fail s!"cannot assign to '{x}' in strict mode" pos
      return .ident x
    | .member _ _ false | .superMember _ =>
      if binding then fail "invalid destructuring target" pos
      return .expr e
    | .paren inner =>
      if binding then fail "invalid destructuring target" pos
      if !simpleParenTarget astFuel inner then fail "invalid assignment target" pos
      if let some x := parenIdent astFuel inner then
        if strict && isEvalOrArgs x then fail s!"cannot assign to '{x}' in strict mode" pos
      return .expr e
    | .object props =>
      let mut out : Array PatProp := #[]
      let mut rest : Option Pattern := none
      for i in [0:props.size] do
        match props[i]! with
        | .init key value _ =>
          let (t, d) ← elemPattern (toPattern n) binding value pos
          out := out.push (.mk key t d)
        | .shorthand name =>
          if strict && isEvalOrArgs name then fail s!"cannot assign to '{name}' in strict mode" pos
          out := out.push (.mk (.ident name) (.ident name) none)
        | .spread arg =>
          if i + 1 != props.size then fail "rest element must be last" pos
          let t ← toPattern n binding arg pos
          match t with
          | .obj .. | .arr .. => fail "invalid rest element" pos
          | _ => pure ()
          if binding then match t with | .ident _ => pure () | _ => fail "invalid rest element" pos
          rest := some t
        | .method .. => fail "invalid destructuring target" pos
      return .obj out rest
    | .array elems =>
      let mut out : Array (Option PatElem) := #[]
      let mut rest : Option Pattern := none
      for i in [0:elems.size] do
        match elems[i]! with
        | .hole => out := out.push none
        | .expr v =>
          let (t, d) ← elemPattern (toPattern n) binding v pos
          out := out.push (some (.mk t d))
        | .spread arg =>
          if i + 1 != elems.size then fail "rest element must be last" pos
          rest := some (← toPattern n binding arg pos)
      return .arr out rest
    | .call _ _ false _ =>
      -- spec: AssignmentTargetType web-compat (runtime ReferenceError in sloppy mode)
      if binding || strict then fail "invalid assignment target" pos
      return .expr e
    | _ => fail (if binding then "invalid destructuring target" else "invalid assignment target") pos

/-- A simple assignment target (AssignmentTargetType simple, or web-compat calls in sloppy
mode when `allowCall`): `++`/`--` operands, compound assignment targets.
spec: https://tc39.es/ecma262/#sec-static-semantics-assignmenttargettype -/
def simpleTarget (e : Expr) (allowCall : Bool) (pos : Nat) : P Pattern := do
  let strict := (← get).strict
  match e with
  | .ident x =>
    if strict && isEvalOrArgs x then fail s!"cannot assign to '{x}' in strict mode" pos
    return .ident x
  | .member _ _ false | .superMember _ => return .expr e
  | .paren inner =>
    if !simpleParenTarget astFuel inner then fail "invalid assignment target" pos
    if let some x := parenIdent astFuel inner then
      if strict && isEvalOrArgs x then fail s!"cannot assign to '{x}' in strict mode" pos
    return .expr e
  | .call _ _ false _ =>
    if allowCall && !strict then return .expr e
    fail "invalid assignment target" pos
  | _ => fail "invalid assignment target" pos

def checkCover (c : Cover) : P Unit := do
  if c.shorthand != 0 then fail "invalid shorthand property initializer" (c.shorthand - 1)
  if c.proto != 0 then fail "duplicate __proto__ property" (c.proto - 1)

/-! ## Private names
spec: https://tc39.es/ecma262/#sec-class-definitions-static-semantics-early-errors -/

def declarePrivate (name : JSStr) (kind : Nat) (pos : Nat) : P Unit := do
  let s ← get
  if s.classes.isEmpty then fail "private name outside class" pos
  let i := s.classes.size - 1
  let c := s.classes[i]!
  match c.declared.get? name with
  | none => pure ()
  | some k =>
    -- a getter and a setter of the same placement may share a name
    let ok := (k &&& 8) == (kind &&& 8) &&
      (((k &&& 7) == 1 && (kind &&& 7) == 2) || ((k &&& 7) == 2 && (kind &&& 7) == 1))
    if !ok then fail s!"duplicate private name #{name}" pos
  let k := match c.declared.get? name with | some k => k ||| kind | none => kind
  modify fun s => { s with classes := s.classes.modify i fun c => { c with declared := c.declared.insert name k } }

def usePrivate (name : JSStr) (pos : Nat) : P Unit := do
  let s ← get
  if s.classes.isEmpty then
    if !s.outerPrivate.contains name then fail s!"undeclared private name #{name}" pos
    return
  let i := s.classes.size - 1
  modify fun s => { s with classes := s.classes.modify i fun c => { c with used := c.used.push (name, pos) } }

/-- At the end of a class body: references to undeclared names go to the enclosing class (or
must be visible from outside).
spec: https://tc39.es/ecma262/#sec-static-semantics-allprivateidentifiersvalid -/
def exitClass : P Unit := do
  let s ← get
  let c := s.classes.back!
  modify fun s => { s with classes := s.classes.pop }
  for (n, pos) in c.used do
    if !c.declared.contains n then usePrivate n pos

/-! ## Recursion -/

/-- Where a statement occurs (what it may be). -/
inductive SPos where
  /-- Script/Module/eval top level. -/
  | top
  /-- StatementListItem in a block or function body. -/
  | item
  /-- StatementListItem of a case clause (no `using`). -/
  | caseItem
  /-- Statement (loop and `with` bodies). -/
  | stmt
  /-- An `if`/`else` clause (Annex B: sloppy function declarations). -/
  | ifBody
  /-- A labelled statement's body; `ok`: labelled function declarations allowed (sloppy). -/
  | label (ok : Bool)
  deriving BEq, Inhabited

def SPos.isItem : SPos → Bool
  | .top | .item | .caseItem => true
  | _ => false

/-- The parser's recursive entry points one nesting level down (see `maxNesting`). -/
structure Rec where
  /-- AssignmentExpression, with the cover errors left to the caller; `noIn`: [~In]. -/
  assignC : Bool → P (Expr × Cover)
  /-- Expression (checked). -/
  expr : Bool → P Expr
  /-- UnaryExpression (an operand of a prefix operator). -/
  unary : P Expr
  stmt : SPos → P Stmt
  /-- A BindingIdentifier or BindingPattern. -/
  binding : P Pattern
  /-- MemberExpression (`new`'s callee). -/
  member : P Expr
  /-- LeftHandSideExpression (`extends`). -/
  lhs : P Expr

def Rec.bottom : Rec :=
  let deep {α : Type} : P α := do fail "too much nesting" (← get).tok.start
  { assignC := fun _ => deep, expr := fun _ => deep, unary := deep, stmt := fun _ => deep,
    binding := deep, member := deep, lhs := deep }

/-- AssignmentExpression with its cover errors checked. -/
def Rec.assign (r : Rec) (noIn : Bool) : P Expr := do
  let (e, c) ← r.assignC noIn
  checkCover c
  return e

/-- Iteration fuel for token loops: each iteration consumes a token (at least one byte), so
the source length bounds them. -/
def loopFuel : P Nat := return (← get).src.size + 2

/-! ## Templates
spec: https://tc39.es/ecma262/#sec-template-literals -/

def parseTemplate (r : Rec) (tagged : Bool) :
    P (Array (Option JSStr) × Array JSStr × Array Expr) := do
  let mut cooked : Array (Option JSStr) := #[]
  let mut raws : Array JSStr := #[]
  let mut exprs : Array Expr := #[]
  let mut t ← tok
  for _ in [0:← loopFuel] do
    if t.badEscape then
      -- spec: https://tc39.es/ecma262/#sec-static-semantics-template-early-errors
      if !tagged then fail "invalid escape sequence in template" t.start
      cooked := cooked.push none
    else cooked := cooked.push (some t.val)
    raws := raws.push t.raw
    next
    if t.tail then return (cooked, raws, exprs)
    exprs := exprs.push (← r.expr false)
    if (← tokKind) != .rbrace then unexpected
    t ← rescanTemplate
  fail "template too long" t.start

/-! ## Property names -/

/-- PropertyName (and ClassElementName when `priv`): the name and the token it started with.
spec: https://tc39.es/ecma262/#prod-PropertyName -/
def parsePropertyName (r : Rec) (priv : Bool) : P (PropName × Token) := do
  let t ← tok
  match t.kind with
  | .name => next; return (.ident t.val, t)
  | .str =>
    if (← get).strict && t.octal != 0 then fail "octal escape sequence in strict mode" t.start
    next; return (.str t.val, t)
  | .num =>
    if (← get).strict && t.octal != 0 then fail "legacy octal literal in strict mode" t.start
    next; return (.num t.num, t)
  | .bigint => next; return (.bigint t.big, t)
  | .lbracket =>
    next
    let e ← r.assign false
    expect .rbracket
    return (.computed e, t)
  | .priv =>
    if !priv then unexpected
    if t.val == kConstructor then fail "#constructor is not a valid private name" t.start
    next; return (.priv t.val, t)
  | _ => unexpected

/-- The string value of a non-computed property name (for `constructor`/`prototype`/
`__proto__` checks). -/
def propStr? : PropName → Option JSStr
  | .ident n | .str n => some n
  | _ => none

/-! ## Binding patterns
spec: https://tc39.es/ecma262/#sec-destructuring-binding-patterns -/

/-- BindingIdentifier or BindingPattern; nested patterns go one level down. -/
def parseBindingAtom (r : Rec) : P Pattern := do
  let t ← tok
  match t.kind with
  | .lbracket =>
    next
    let mut elems : Array (Option PatElem) := #[]
    let mut rest : Option Pattern := none
    for _ in [0:← loopFuel] do
      let k ← tokKind
      if k == .rbracket then break
      if k == .comma then next; elems := elems.push none; continue
      if k == .ellipsis then
        next
        rest := some (← r.binding)
        if (← tokKind) != .rbracket then fail "rest element must be last" (← tok).start
        break
      let target ← r.binding
      let init ← if ← eat .assign then pure (some (← r.assign false)) else pure none
      elems := elems.push (some (.mk target init))
      if (← tokKind) != .rbracket then expect .comma
    expect .rbracket
    return .arr elems rest
  | .lbrace =>
    next
    let mut props : Array PatProp := #[]
    let mut rest : Option Pattern := none
    for _ in [0:← loopFuel] do
      let k ← tokKind
      if k == .rbrace then break
      if k == .ellipsis then
        next
        let (n, _, _) ← bindingIdent
        rest := some (.ident n)
        if (← tokKind) != .rbrace then fail "rest element must be last" (← tok).start
        break
      let (key, kt) ← parsePropertyName r false
      if ← eat .colon then
        let target ← r.binding
        let init ← if ← eat .assign then pure (some (← r.assign false)) else pure none
        props := props.push (.mk key target init)
      else
        -- SingleNameBinding: the key is the BindingIdentifier
        if kt.kind != .name then unexpected
        checkIdent kt true
        let init ← if ← eat .assign then pure (some (← r.assign false)) else pure none
        props := props.push (.mk key (.ident kt.val) init)
      if (← tokKind) != .rbrace then expect .comma
    expect .rbrace
    return .obj props rest
  | .name =>
    let (n, _, _) ← bindingIdent
    return .ident n
  | _ => unexpected

/-! ## Functions
spec: https://tc39.es/ecma262/#sec-function-definitions -/

/-- What is being parsed: a function's kind and what its context allows. -/
structure FnSpec where
  kind : FuncKind
  isAsync : Bool := false
  isGen : Bool := false
  name : Option JSStr := none
  nameKw : Kw := .none
  namePos : Nat := 0
  /-- A function expression's name token: checked in the function's own context. -/
  exprName : Option Token := none
  start : Nat
  superProp : Bool := false
  superCall : Bool := false
  /-- Parameters must be unique (UniqueFormalParameters: methods, arrows). -/
  uniqueParams : Bool := false

structure Saved where
  fn : Fn
  labels : Array Label
  yieldPos : Nat
  awaitPos : Nat
  awaitIdentPos : Nat
  strict : Bool

def saveCtx : P Saved := do
  let s ← get
  return { fn := s.fn, labels := s.labels, yieldPos := s.yieldPos, awaitPos := s.awaitPos,
           awaitIdentPos := s.awaitIdentPos, strict := s.strict }

def restoreCtx (sv : Saved) : P Unit :=
  modify fun s => { s with
    fn := sv.fn, labels := sv.labels, yieldPos := sv.yieldPos,
    awaitPos := sv.awaitPos, awaitIdentPos := sv.awaitIdentPos, strict := sv.strict }

/-- Statements until `stop`, with a directive prologue when `directives`: returns them and
whether a Use Strict Directive occurred (which makes the rest strict).
spec: https://tc39.es/ecma262/#sec-directive-prologues-and-the-use-strict-directive -/
def parseBodyList (r : Rec) (pos : SPos) (stop : T) (directives : Bool) : P (Array Stmt × Bool) := do
  let mut stmts : Array Stmt := #[]
  let mut prologue := directives
  let mut useStrict := false
  let mut octal := 0
  for _ in [0:← loopFuel] do
    let t ← tok
    if t.kind == stop || t.kind == .eof then break
    if prologue && t.kind == .str then
      let st ← r.stmt pos
      let isDir := match st with | .expr (.lit (.str _)) => true | _ => false
      if isDir then
        if t.octal != 0 && octal == 0 then octal := t.octal
        if (← srcIs t.start t.stop "\"use strict\"") || (← srcIs t.start t.stop "'use strict'") then
          useStrict := true
          modify fun s => { s with strict := true }
          if octal != 0 then fail "octal escape sequence in strict mode" (octal - 1)
      else prologue := false
      stmts := stmts.push st
      continue
    prologue := false
    stmts := stmts.push (← r.stmt pos)
  return (stmts, useStrict)

/-- FormalParameters after `(` up to and including `)`: the parameters and their bound names
with positions. -/
def parseParams (r : Rec) : P (Array Param × Array (JSStr × Nat)) := do
  expect .lparen
  let mut ps : Array Param := #[]
  let mut names : Array (JSStr × Nat) := #[]
  for _ in [0:← loopFuel] do
    let k ← tokKind
    if k == .rparen then break
    let start := (← tok).start
    if k == .ellipsis then
      next
      let target ← r.binding
      if (← tokKind) == .assign then fail "rest parameter may not have a default" (← tok).start
      for n in patNames astFuel target #[] do names := names.push (n, start)
      ps := ps.push (.mk target none true)
      if (← tokKind) != .rparen then fail "rest parameter must be last" (← tok).start
      break
    let target ← r.binding
    let init ← if ← eat .assign then pure (some (← r.assign false)) else pure none
    for n in patNames astFuel target #[] do names := names.push (n, start)
    ps := ps.push (.mk target init false)
    if (← tokKind) != .rparen then expect .comma
  expect .rparen
  return (ps, names)

/-- Early errors shared by functions, arrows and methods once the body is parsed: "use
strict" with non-simple parameters, strict-mode names, duplicate parameters.
spec: https://tc39.es/ecma262/#sec-function-definitions-static-semantics-early-errors -/
def checkParamsAfterBody (params : Array Param) (names : Array (JSStr × Nat)) (useStrict : Bool)
    (unique : Bool) (start : Nat) : P Unit := do
  let simple := isSimpleParams params
  if useStrict && !simple then
    fail "\"use strict\" not allowed in function with non-simple parameters" start
  let strict := (← get).strict
  if strict then
    for (n, p) in names do checkStrictBinding n (kwTable.getD n .none) p
  if strict || !simple || unique then
    let mut seen : HashSet JSStr := {}
    for (n, p) in names do
      if seen.contains n then fail s!"duplicate parameter name '{n}'" p
      seen := seen.insert n

/-- A function's parameters and body from `(`: FunctionDeclaration/Expression, methods,
accessors, constructors (with the context `spec` gives them).
spec: https://tc39.es/ecma262/#sec-function-definitions-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-method-definitions-static-semantics-early-errors -/
def parseFunctionRest (r : Rec) (spec : FnSpec) : P Func := do
  let sv ← saveCtx
  let id ← freshId
  let outer := sv.fn
  modify fun s => { s with
    fn := { awaitExpr := spec.isAsync, awaitReserved := spec.isAsync, yieldExpr := spec.isGen,
            superProp := spec.superProp, superCall := spec.superCall, newTarget := true,
            returnOk := true }
    labels := #[], yieldPos := 0, awaitPos := 0, awaitIdentPos := 0 }
  let _ := outer
  if let some t := spec.exprName then checkIdent t true
  enterScope (sVar ||| sFunction)
  let (params, names) ← parseParams r
  let s ← get
  if s.yieldPos != 0 then fail "yield expression in formal parameters" (s.yieldPos - 1)
  if s.awaitPos != 0 then fail "await expression in formal parameters" (s.awaitPos - 1)
  match spec.kind with
  | .getter => if params.size != 0 then fail "getter must have no parameters" spec.start
  | .setter =>
    if params.size != 1 then fail "setter must have exactly one parameter" spec.start
    if let .mk _ _ true := params[0]! then fail "setter parameter may not be a rest parameter" spec.start
  | _ => pure ()
  for (n, p) in names do declareVar n p
  expect .lbrace
  let (body, useStrict) ← parseBodyList r .item .rbrace true
  expect .rbrace
  let unique := spec.uniqueParams || !(spec.kind == .normal)
  checkParamsAfterBody params names useStrict unique spec.start
  let strict := (← get).strict
  if strict && !sv.strict then
    if let some n := spec.name then checkStrictBinding n spec.nameKw spec.namePos
  exitScope
  let f := (← get).fn
  let stop := (← get).prevEnd
  restoreCtx sv
  let pe := params.any (fun p => match p with | .mk t i _ => i.isSome || patHasExpr astFuel t)
  let info : FuncInfo := {
    strict, span := { start := spec.start, stop }, simpleParams := isSimpleParams params,
    expectedArgs := expectedArgs params, hasDirectEval := f.hasEval,
    usesArguments := f.argsRef || f.hasEval, usesThis := f.arrowThis || f.hasEval,
    paramsHaveExpressions := pe, id,
    fdi := analyzeFDI spec.kind strict (f.argsRef || f.hasEval) pe params (.stmts body) }
  return .mk spec.name spec.kind spec.isAsync spec.isGen params (.stmts body) info

/-- An arrow function's body, after `=>` (the parameters are already refined).
spec: https://tc39.es/ecma262/#sec-arrow-function-definitions-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-async-arrow-function-definitions-static-semantics-early-errors -/
def parseArrowBody (r : Rec) (params : Array Param) (isAsync : Bool) (start : Nat) (noIn : Bool) :
    P Func := do
  let sv ← saveCtx
  let id ← freshId
  let outer := sv.fn
  modify fun s => { s with
    fn := { isArrow := true, awaitExpr := isAsync,
            awaitReserved := isAsync, yieldExpr := false,
            superProp := outer.superProp, superCall := outer.superCall,
            newTarget := outer.newTarget, noArguments := outer.noArguments, returnOk := true }
    labels := #[], yieldPos := 0, awaitPos := 0, awaitIdentPos := 0 }
  enterScope (sVar ||| sFunction)
  let names := (paramNames params).map (·, start)
  for (n, p) in names do declareVar n p
  let body ← if (← tokKind) == .lbrace then do
      next
      let (body, useStrict) ← parseBodyList r .item .rbrace true
      expect .rbrace
      checkParamsAfterBody params names useStrict true start
      pure (FuncBody.stmts body)
    else do
      checkParamsAfterBody params names false true start
      pure (FuncBody.expr (← r.assign noIn))
  exitScope
  let f := (← get).fn
  let strict := (← get).strict
  let stop := (← get).prevEnd
  restoreCtx sv
  setFn fun p => { p with
    argsRef := p.argsRef || f.argsRef, thisRef := p.thisRef || f.thisRef,
    arrowThis := p.arrowThis || f.thisRef, hasEval := p.hasEval || f.hasEval }
  let pe := params.any (fun p => match p with | .mk t i _ => i.isSome || patHasExpr astFuel t)
  let info : FuncInfo := {
    strict, span := { start, stop }, simpleParams := isSimpleParams params,
    expectedArgs := expectedArgs params, hasDirectEval := f.hasEval,
    usesArguments := f.argsRef || f.hasEval, usesThis := f.thisRef || f.hasEval,
    paramsHaveExpressions := pe, id,
    fdi := analyzeFDI .arrow strict (f.argsRef || f.hasEval) pe params body }
  return .mk none .arrow isAsync false params body info

/-- Refines a cover's items (`(a, b = 1, ...c)` or `async(…)`) to arrow parameters. -/
def coverToParams (items : Array Arg) (rest : Option Pattern) (c : Cover) (pos : Nat)
    (trailingComma : Bool := false) : P (Array Param) := do
  if c.trailing != 0 then fail "invalid rest element" (c.trailing - 1)
  if trailingComma && (items.back? matches some (.spread _)) then
    fail "rest parameter may not have a trailing comma" pos
  let mut ps : Array Param := #[]
  for i in [0:items.size] do
    match items[i]! with
    | .expr e =>
      let (t, d) ← elemPattern (toPattern astFuel) true e pos
      ps := ps.push (.mk t d false)
    | .spread e =>
      if i + 1 != items.size then fail "rest parameter must be last" pos
      match e with
      | .assign .. => fail "rest parameter may not have a default" pos
      | _ => pure ()
      ps := ps.push (.mk (← toPattern astFuel true e pos) none true)
  if let some p := rest then ps := ps.push (.mk p none true)
  return ps

/-! ## Classes
spec: https://tc39.es/ecma262/#sec-class-definitions -/

/-- A class field's initializer: parsed like a method body (`arguments` and `super()`
forbidden, `super.x` and `new.target` allowed). -/
def parseFieldInit (r : Rec) : P Expr := do
  let sv ← saveCtx
  let outer := sv.fn
  modify fun s => { s with
    fn := { superProp := true, newTarget := true, noArguments := true, fieldInit := true,
            awaitReserved := outer.awaitExpr || outer.awaitReserved, returnOk := false }
    labels := #[] }
  let e ← r.assign false
  restoreCtx sv
  return e

/-- A class static block `static { … }` after `static`.
spec: https://tc39.es/ecma262/#sec-class-definitions-static-semantics-early-errors -/
def parseStaticBlock (r : Rec) : P (Array Stmt) := do
  let sv ← saveCtx
  modify fun s => { s with
    fn := { superProp := true, newTarget := true, noArguments := true, staticBlock := true,
            awaitReserved := true, returnOk := false }
    labels := #[], yieldPos := 0, awaitPos := 0, awaitIdentPos := 0 }
  expect .lbrace
  enterScope (sVar ||| sStaticBlock)
  let (body, _) ← parseBodyList r .item .rbrace false
  expect .rbrace
  exitScope
  restoreCtx sv
  return body

/-- One ClassElement (none for `;`). `ctor`: a constructor was already seen. -/
def parseClassElement (r : Rec) (derived : Bool) (ctor : Bool) : P (Option ClassElem × Bool) := do
  if ← eat .semi then return (none, ctor)
  let start := (← tok).start
  let isModifierFollow (p : Token) : Bool :=
    p.kind == .lparen || p.kind == .assign || p.kind == .semi || p.kind == .rbrace || p.kind == .eof
  let mut isStatic := false
  if ← isKw .kStatic then
    let p ← peek
    if !isModifierFollow p then
      next; isStatic := true
      if (← tokKind) == .lbrace then
        let body ← parseStaticBlock r
        return (some (.staticBlock body { start, stop := (← get).prevEnd }), ctor)
  let mstart := (← tok).start
  let mut isAsync := false
  let mut isGen := false
  let mut acc : Nat := 0   -- 1 get, 2 set
  if ← isKw .kAsync then
    let p ← peek
    if !isModifierFollow p && !p.nl then next; isAsync := true
  if (← tokKind) == .star then next; isGen := true
  if !isAsync && !isGen then
    if (← isKw .kGet) || (← isKw .kSet) then
      let p ← peek
      if !isModifierFollow p && p.kind != .star then
        acc := if (← isKw .kGet) then 1 else 2
        next
  let (key, kt) ← parsePropertyName r true
  let keyStr := match key with | .computed _ | .priv _ => none | k => propStr? k
  if (← tokKind) == .lparen then
    let isCtor := !isStatic && keyStr == some kConstructor
    if isCtor then
      if acc != 0 || isAsync || isGen then fail "class constructor may not be an accessor, generator or async" kt.start
      if ctor then fail "duplicate constructor" kt.start
    if isStatic && keyStr == some kPrototype then fail "static 'prototype' member" kt.start
    let kind : FuncKind := if isCtor then .classConstructor derived
      else if acc == 1 then .getter else if acc == 2 then .setter else .method
    let f ← parseFunctionRest r { kind, isAsync, isGen, start := mstart, superProp := true,
                                  superCall := isCtor && derived, uniqueParams := true }
    if let .priv n := key then
      declarePrivate n ((if acc == 1 then 1 else if acc == 2 then 2 else 4) + (if isStatic then 8 else 0)) kt.start
    return (some (.method isStatic key f), ctor || isCtor)
  if isAsync || isGen || acc != 0 then unexpected
  -- FieldDefinition
  if keyStr == some kConstructor then fail "class field named 'constructor'" kt.start
  if isStatic && keyStr == some kPrototype then fail "static 'prototype' field" kt.start
  if let .priv n := key then declarePrivate n (4 + (if isStatic then 8 else 0)) kt.start
  let init ← if ← eat .assign then pure (some (← parseFieldInit r)) else pure none
  semicolon
  return (some (.field isStatic key init { start, stop := (← get).prevEnd }), ctor)

/-- ClassDeclaration / ClassExpression from `class`. -/
def parseClass (r : Rec) (isDecl : Bool) (nameOptional : Bool) : P Class := do
  let start := (← tok).start
  next
  let wasStrict := (← get).strict
  modify fun s => { s with strict := true }
  let mut name : Option JSStr := none
  let t ← tok
  if t.kind == .name && !(t.kw == .kExtends && !t.escaped) then
    let (n, _, p) ← bindingIdent
    if isDecl then
      modify fun s => { s with strict := wasStrict }
      declareLex n p
      modify fun s => { s with strict := true }
    name := some n
  else if isDecl && !nameOptional then unexpected
  let superClass ← if ← isKeyword .kExtends then do next; pure (some (← r.lhs)) else pure none
  expect .lbrace
  modify fun s => { s with classes := s.classes.push {} }
  let mut elems : Array ClassElem := #[]
  let mut ctor := false
  for _ in [0:← loopFuel] do
    let k ← tokKind
    if k == .rbrace || k == .eof then break
    let (e, c) ← parseClassElement r superClass.isSome ctor
    ctor := c
    if let some e := e then elems := elems.push e
  expect .rbrace
  exitClass
  modify fun s => { s with strict := wasStrict }
  return .mk name superClass elems { start, stop := (← get).prevEnd }

/-! ## Expressions
spec: https://tc39.es/ecma262/#sec-ecmascript-language-expressions -/

/-- Validates a RegularExpressionLiteral: its flags and (via `Regex.compile`) its pattern.
spec: https://tc39.es/ecma262/#sec-primary-expression-regular-expression-literals-static-semantics-early-errors -/
def checkRegex (t : Token) : P Unit := do
  let flags := t.raw
  let mut seen : Array UInt16 := #[]
  for i in [0:flags.length] do
    let u := flags.get i
    -- d g i m s u v y
    if !(u == 100 || u == 103 || u == 105 || u == 109 || u == 115 || u == 117 || u == 118 || u == 121) then
      fail "invalid regular expression flags" t.start
    if seen.contains u then fail "duplicate regular expression flag" t.start
    seen := seen.push u
  if seen.contains 117 && seen.contains 118 then fail "invalid regular expression flags" t.start
  match regexCompile t.val flags with
  | .ok _ => pure ()
  | .error msg => fail s!"Invalid regular expression: {msg}" t.start

/-- Arguments from `(` to `)`; with `cover`, items' cover errors are returned (an async arrow
head) instead of checked. The second result: a trailing comma's position + 1. -/
def parseArgs (r : Rec) (cover : Bool) : P (Array Arg × Cover × Nat) := do
  expect .lparen
  let mut args : Array Arg := #[]
  let mut c : Cover := {}
  let mut trailing := 0
  for _ in [0:← loopFuel] do
    if (← tokKind) == .rparen then break
    trailing := 0
    let spread ← eat .ellipsis
    let (e, ec) ← r.assignC false
    if cover then c := c.merge ec else checkCover ec
    args := args.push (if spread then .spread e else .expr e)
    if (← tokKind) != .rparen then
      expect .comma
      trailing := (← get).prevEnd
  expect .rparen
  return (args, c, trailing)

/-- `( … )`: a ParenthesizedExpression, or an arrow function's parameters
(CoverParenthesizedExpressionAndArrowParameterList).
spec: https://tc39.es/ecma262/#sec-grouping-operator-static-semantics-early-errors -/
def parseParenArrow (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let start := (← tok).start
  next
  let s0 ← get
  let (yp, ap, aip) := (s0.yieldPos, s0.awaitPos, s0.awaitIdentPos)
  modify fun s => { s with yieldPos := 0, awaitPos := 0, awaitIdentPos := 0 }
  let mut items : Array Arg := #[]
  let mut c : Cover := {}
  let mut rest : Option Pattern := none
  let mut trailing := false
  for _ in [0:← loopFuel] do
    if (← tokKind) == .rparen then break
    trailing := false
    if (← tokKind) == .ellipsis then
      next
      rest := some (← r.binding)
      if (← tokKind) != .rparen then fail "rest parameter must be last" (← tok).start
      break
    let (e, ec) ← r.assignC false
    c := c.merge ec
    items := items.push (.expr e)
    if (← tokKind) != .rparen then
      expect .comma
      trailing := true
  expect .rparen
  let t ← tok
  if t.kind == .arrow then
    if t.nl then fail "line terminator before arrow" t.start
    let s ← get
    if s.yieldPos != 0 then fail "yield expression in arrow parameters" (s.yieldPos - 1)
    if s.awaitPos != 0 then fail "await expression in arrow parameters" (s.awaitPos - 1)
    let ps ← coverToParams items rest c start
    modify fun s => { s with
      yieldPos := yp, awaitPos := ap,
      awaitIdentPos := if aip != 0 then aip else s.awaitIdentPos }
    next
    let f ← parseArrowBody r ps false start noIn
    return (.func f, {})
  if items.isEmpty || rest.isSome || trailing then fail "invalid parenthesized expression" start
  checkCover c
  modify fun s => { s with
    yieldPos := if yp != 0 then yp else s.yieldPos, awaitPos := if ap != 0 then ap else s.awaitPos,
    awaitIdentPos := if aip != 0 then aip else s.awaitIdentPos }
  let inner := if items.size == 1 then (match items[0]! with | .expr e => e | .spread e => e)
    else .seq (items.map fun a => match a with | .expr e => e | .spread e => e)
  return (.paren inner, {})

/-- ArrayLiteral. spec: https://tc39.es/ecma262/#sec-array-initializer -/
def parseArray (r : Rec) : P (Expr × Cover) := do
  next
  let mut elems : Array ArrElem := #[]
  let mut c : Cover := {}
  for _ in [0:← loopFuel] do
    let k ← tokKind
    if k == .rbracket then break
    if k == .comma then next; elems := elems.push .hole; continue
    if k == .ellipsis then
      next
      let (e, ec) ← r.assignC false
      c := c.merge ec
      elems := elems.push (.spread e)
      if (← tokKind) == .comma then
        let p := (← tok).start
        next
        if (← tokKind) == .rbracket && c.trailing == 0 then c := { c with trailing := p + 1 }
      else if (← tokKind) != .rbracket then unexpected
      continue
    let (e, ec) ← r.assignC false
    c := c.merge ec
    elems := elems.push (.expr e)
    if (← tokKind) != .rbracket then expect .comma
  expect .rbracket
  return (.array elems, c)

/-- ObjectLiteral (with CoverInitializedName).
spec: https://tc39.es/ecma262/#sec-object-initializer-static-semantics-early-errors -/
def parseObject (r : Rec) : P (Expr × Cover) := do
  next
  let mut props : Array PropDef := #[]
  let mut c : Cover := {}
  let mut sawProto := false
  let isModifierFollow (p : Token) : Bool :=
    p.kind == .comma || p.kind == .colon || p.kind == .lparen || p.kind == .rbrace ||
    p.kind == .assign || p.kind == .eof
  for _ in [0:← loopFuel] do
    if (← tokKind) == .rbrace then break
    if ← eat .ellipsis then
      let (e, ec) ← r.assignC false
      c := c.merge ec
      props := props.push (.spread e)
      if (← tokKind) == .comma then
        let p := (← tok).start
        next
        if (← tokKind) == .rbrace && c.trailing == 0 then c := { c with trailing := p + 1 }
      else if (← tokKind) != .rbrace then unexpected
      continue
    let mstart := (← tok).start
    let mut isAsync := false
    let mut isGen := false
    let mut acc : Nat := 0
    if ← isKw .kAsync then
      let p ← peek
      if !isModifierFollow p && !p.nl then next; isAsync := true
    if (← tokKind) == .star then next; isGen := true
    if !isAsync && !isGen then
      if (← isKw .kGet) || (← isKw .kSet) then
        let p ← peek
        if !isModifierFollow p && p.kind != .star then
          acc := if (← isKw .kGet) then 1 else 2
          next
    let (key, kt) ← parsePropertyName r false
    if (← tokKind) == .lparen then
      let kind : FuncKind := if acc == 1 then .getter else if acc == 2 then .setter else .method
      let f ← parseFunctionRest r { kind, isAsync, isGen, start := mstart, superProp := true,
                                    uniqueParams := true }
      props := props.push (.method key f)
    else
      if isAsync || isGen || acc != 0 then unexpected
      if ← eat .colon then
        let (v, vc) ← r.assignC false
        c := c.merge vc
        let isProto := match key with
          | .ident n => n == kProto | .str n => n == kProto | _ => false
        if isProto then
          if sawProto && c.proto == 0 then c := { c with proto := kt.start + 1 }
          sawProto := true
        props := props.push (.init key v isProto)
      else
        -- IdentifierReference shorthand / CoverInitializedName
        if kt.kind != .name then unexpected
        checkIdent kt false
        if kt.val == kArguments then
          if (← get).fn.noArguments then fail "'arguments' is not allowed in class field initializers or static blocks" kt.start
          setFn fun f => { f with argsRef := true }
        if (← tokKind) == .assign then
          if (← get).strict && isEvalOrArgs kt.val then
            fail s!"cannot assign to '{kt.val}' in strict mode" kt.start
          next
          let d ← r.assign false
          if c.shorthand == 0 then c := { c with shorthand := kt.start + 1 }
          props := props.push (.init key (.assign .assign (.ident kt.val) d) false)
        else props := props.push (.shorthand kt.val)
    if (← tokKind) != .rbrace then expect .comma
  expect .rbrace
  return (.object props, c)

/-- `function` expressions from `function` (after `async` when `isAsync`). -/
def parseFunctionExpr (r : Rec) (start : Nat) (isAsync : Bool) : P Func := do
  next -- function
  let isGen ← eat .star
  let t ← tok
  let exprName := if t.kind == .name then some t else none
  if exprName.isSome then next
  parseFunctionRest r {
    kind := .normal, isAsync, isGen, start, exprName,
    name := exprName.map (·.val), nameKw := (exprName.map (·.kw)).getD .none,
    namePos := t.start }

/-- `new` expressions and `new.target`, from `new`.
spec: https://tc39.es/ecma262/#sec-new-operator -/
def parseNew (r : Rec) : P Expr := do
  let start := (← tok).start
  next
  if ← eat .dot then
    if !(← isKw .kTarget) then unexpected
    next
    -- spec: https://tc39.es/ecma262/#sec-scripts-static-semantics-early-errors (new.target)
    if !(← get).fn.newTarget then fail "new.target outside function" start
    setFn fun f => { f with thisRef := true }
    return .newTarget
  if ← isKw .kImport then
    if (← peek).kind == .lparen then fail "cannot use new with import()" (← tok).start
  let callee ← r.member
  if (← tokKind) == .lparen then
    let (args, _, _) ← parseArgs r false
    return .new callee args
  return .new callee #[]

/-- `super` property accesses and calls.
spec: https://tc39.es/ecma262/#sec-left-hand-side-expressions-static-semantics-early-errors -/
def parseSuper (r : Rec) : P Expr := do
  let start := (← tok).start
  next
  let f := (← get).fn
  setFn fun f => { f with thisRef := true }
  match ← tokKind with
  | .lparen =>
    if !f.superCall then fail "'super' call outside a derived class constructor" start
    let (args, _, _) ← parseArgs r false
    return .superCall args
  | .dot =>
    if !f.superProp then fail "'super' outside a method" start
    next
    let t ← tok
    if t.kind != .name then unexpected
    next
    return .superMember (.name t.val)
  | .lbracket =>
    if !f.superProp then fail "'super' outside a method" start
    next
    let e ← r.expr false
    expect .rbracket
    return .superMember (.computed e)
  | _ => fail "unexpected 'super'" start

/-- `import.meta` and `import(…)`.
spec: https://tc39.es/ecma262/#sec-import-calls
spec: https://tc39.es/ecma262/#sec-meta-properties-static-semantics-early-errors -/
def parseImportExpr (r : Rec) : P Expr := do
  let start := (← tok).start
  next
  if ← eat .dot then
    if ← isKw .kMeta then
      next
      if !(← get).isModule then fail "import.meta outside a module" start
      return .importMeta
    fail "unsupported import phase" start
  if (← tokKind) != .lparen then unexpected
  next
  if (← tokKind) == .rparen then fail "import() requires a specifier" start
  let spec ← r.assign false
  let mut opts : Option Expr := none
  if ← eat .comma then
    if (← tokKind) != .rparen then
      opts := some (← r.assign false)
      discard <| eat .comma
  expect .rparen
  return .importCall spec opts

/-- An async arrow function `async x => …` from the identifier after `async`. -/
def parseAsyncArrowIdent (r : Rec) (start : Nat) (noIn : Bool) : P Expr := do
  let t ← tok
  if t.kw == .kAwait then fail "'await' cannot be an async arrow parameter" t.start
  -- (the parameter is in the arrow's [+Await] context)
  let sv := (← get).fn
  setFn fun f => { f with awaitReserved := true }
  checkIdent t true
  setFn fun _ => sv
  next
  let a ← tok
  if a.kind != .arrow || a.nl then unexpected
  next
  let f ← parseArrowBody r #[.mk (.ident t.val) none false] true start noIn
  return .func f

/-- PrimaryExpression (and the arrow functions, `new`, `super` and `import` forms that start
like one).
spec: https://tc39.es/ecma262/#sec-primary-expression -/
def parseExprAtom (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let t ← tok
  let s ← get
  match t.kind with
  | .name =>
    let kw := if t.escaped then .none else t.kw
    if t.escaped && t.kw.isReserved then
      -- escaped reserved words are neither keywords nor identifiers
      fail "keyword must not contain escaped characters" t.start
    match kw with
    | .kThis => next; setFn (fun f => { f with thisRef := true }); return (.this, {})
    | .kNull => next; return (.lit .null, {})
    | .kTrue => next; return (.lit (.bool true), {})
    | .kFalse => next; return (.lit (.bool false), {})
    | .kFunction => return (.func (← parseFunctionExpr r t.start false), {})
    | .kClass => return (.cls (← parseClass r false true), {})
    | .kNew => return (← parseNew r, {})
    | .kSuper => return (← parseSuper r, {})
    | .kImport => return (← parseImportExpr r, {})
    | .kAsync =>
      let p ← peek
      if p.kind == .name && !p.nl && p.kw == .kFunction && !p.escaped then
        next
        return (.func (← parseFunctionExpr r t.start true), {})
      let arrowNext ← if p.kind == .name && !p.nl && !(p.kw == .kFunction) then
          pure ((← peek2).kind == .arrow) else pure false
      if arrowNext then
        -- `async x => …` (an identifier `async` followed by a name is nothing else)
        next
        return (← parseAsyncArrowIdent r t.start noIn, {})
      next
      checkIdent t false
      return (.ident t.val, {})
    | _ =>
      let n ← identRef
      let a ← tok
      if a.kind == .arrow then
        if a.nl then fail "line terminator before arrow" a.start
        if s.strict && isEvalOrArgs n then fail s!"'{n}' cannot be a binding in strict mode" t.start
        next
        let f ← parseArrowBody r #[.mk (.ident n) none false] false t.start noIn
        return (.func f, {})
      return (.ident n, {})
  | .num =>
    if s.strict && t.octal != 0 then fail "legacy octal literal in strict mode" t.start
    next; return (.lit (.num t.num), {})
  | .bigint => next; return (.lit (.bigint t.big), {})
  | .str =>
    if s.strict && t.octal != 0 then fail "octal escape sequence in strict mode" t.start
    next; return (.lit (.str t.val), {})
  | .tmpl =>
    let (cooked, raws, exprs) ← parseTemplate r false
    return (.template cooked raws exprs, {})
  | .slash | .slashEq =>
    let rt ← rescanRegex
    checkRegex rt
    next
    return (.regex rt.val rt.raw, {})
  | .lparen => parseParenArrow r noIn
  | .lbracket => parseArray r
  | .lbrace => parseObject r
  | _ => unexpected

/-- Whether an expression is a private member access (for `delete`'s early error), looking
through parentheses and optional chains. -/
def isPrivateRef : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .member _ (.priv _) _ => true
    | .paren e | .chain e => isPrivateRef n e
    | _ => false

/-- The suffixes of a MemberExpression / CallExpression / OptionalExpression (`noCalls`: a
`new` callee, which has no arguments or optional chains).
spec: https://tc39.es/ecma262/#sec-left-hand-side-expressions -/
def parseSubscripts (r : Rec) (base : Expr) (noCalls : Bool) : P Expr := do
  let b0 := (← get).budget
  let mut e := base
  let mut opt := false
  for _ in [0:← loopFuel] do
    let t ← tok
    match t.kind with
    | .dot =>
      next
      let n ← tok
      if n.kind == .priv then
        usePrivate n.val n.start; next; e := .member e (.priv n.val) false
      else if n.kind == .name then next; e := .member e (.name n.val) false
      else unexpected
    | .qdot =>
      if noCalls then fail "optional chain in new expression" t.start
      next
      opt := true
      let n ← tok
      match n.kind with
      | .lparen =>
        let (args, _, _) ← parseArgs r false
        e := .call e args true false
      | .lbracket =>
        next
        let k ← r.expr false
        expect .rbracket
        e := .member e (.computed k) true
      | .priv => usePrivate n.val n.start; next; e := .member e (.priv n.val) true
      | .name => next; e := .member e (.name n.val) true
      | .tmpl => fail "tagged template in optional chain" n.start
      | _ => unexpected
    | .lbracket =>
      next
      let k ← r.expr false
      expect .rbracket
      e := .member e (.computed k) false
    | .tmpl =>
      if opt then fail "tagged template in optional chain" t.start
      let (cooked, raws, exprs) ← parseTemplate r true
      let site ← modifyGet fun s => (s.nextSite, { s with nextSite := s.nextSite + 1 })
      e := .tagged e cooked raws exprs site
    | .lparen =>
      if noCalls then break
      let (args, _, _) ← parseArgs r false
      if let .ident n := e then
        if n == kEval then
          -- a direct eval candidate (spec: PerformEval)
          setFn fun f => { f with hasEval := true, argsRef := true, thisRef := true }
      e := .call e args false (isEvalIdent e)
    | _ => break
    chainStep
  restoreBudget b0
  return if opt then .chain e else e

/-- MemberExpression for `new`: an atom and its suffixes without arguments. -/
def parseMemberOnly (r : Rec) : P Expr := do
  let (e, c) ← parseExprAtom r false
  checkCover c
  if let .func f := e then
    if f.kind == .arrow then fail "arrow function cannot be a new callee" f.info.span.start
  parseSubscripts r e true

/-- LeftHandSideExpression: an atom and its suffixes; the cover errors are passed on when the
expression is just the atom. Handles `async(…) => …` (CoverCallExpressionAndAsyncArrowHead).
spec: https://tc39.es/ecma262/#sec-async-arrow-function-definitions -/
def parseExprSubscripts (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let t0 ← tok
  let (e, c) ← parseExprAtom r noIn
  if let .func f := e then
    if f.kind == .arrow then return (e, c)
  let t ← tok
  -- `async (…)`: an async arrow head or a call
  if t0.kind == .name && t0.kw == .kAsync && !t0.escaped && t.kind == .lparen && !t.nl &&
      (← get).prevEnd == t0.stop then
    let s0 ← get
    let (yp, ap, aip) := (s0.yieldPos, s0.awaitPos, s0.awaitIdentPos)
    modify fun s => { s with yieldPos := 0, awaitPos := 0, awaitIdentPos := 0 }
    let (args, ac, trailing) ← parseArgs r true
    let a ← tok
    if a.kind == .arrow && !a.nl then
      let s ← get
      if s.yieldPos != 0 then fail "yield expression in arrow parameters" (s.yieldPos - 1)
      if s.awaitPos != 0 then fail "await expression in async arrow parameters" (s.awaitPos - 1)
      if s.awaitIdentPos != 0 then fail "'await' in async arrow parameters" (s.awaitIdentPos - 1)
      let ps ← coverToParams args none ac t0.start (trailing != 0)
      modify fun s => { s with yieldPos := yp, awaitPos := ap, awaitIdentPos := aip }
      next
      let f ← parseArrowBody r ps true t0.start noIn
      return (.func f, {})
    checkCover ac
    modify fun s => { s with
      yieldPos := if yp != 0 then yp else s.yieldPos, awaitPos := if ap != 0 then ap else s.awaitPos,
      awaitIdentPos := if aip != 0 then aip else s.awaitIdentPos }
    return (← parseSubscripts r (.call e args false (isEvalIdent e)) false, {})
  match t.kind with
  | .dot | .qdot | .lbracket | .lparen | .tmpl =>
    checkCover c
    return (← parseSubscripts r e false, {})
  | _ => return (e, c)

/-- UnaryExpression / UpdateExpression; the flag: a unary operator applied (an
ExponentiationExpression's base may not be one).
spec: https://tc39.es/ecma262/#sec-unary-operators
spec: https://tc39.es/ecma262/#sec-update-expressions-static-semantics-early-errors -/
def parseMaybeUnary (r : Rec) (noIn : Bool) : P (Expr × Cover × Bool) := do
  let t ← tok
  let s ← get
  if t.kind == .name && t.kw == .kAwait && (s.fn.awaitExpr || (s.fn.staticBlock && !s.fn.isArrow)) then
    if t.escaped then fail "keyword must not contain escaped characters" t.start
    if s.fn.staticBlock && !s.fn.awaitExpr then fail "'await' in class static block" t.start
    next
    if s.awaitPos == 0 then modify fun s => { s with awaitPos := t.start + 1 }
    let arg ← r.unary
    return (.await arg, {}, true)
  let unop : Option UnOp := match t.kind with
    | .bang => some .not | .tilde => some .bitNot | .plus => some .pos | .minus => some .neg
    | .name => if t.escaped then none else match t.kw with
      | .kTypeof => some .typeof | .kVoid => some .void | .kDelete => some .delete | _ => none
    | _ => none
  if let some op := unop then
    next
    let arg ← r.unary
    if op == .delete then
      -- spec: https://tc39.es/ecma262/#sec-delete-operator-static-semantics-early-errors
      if s.strict && (parenIdent astFuel arg).isSome then
        fail "delete of an unqualified identifier in strict mode" t.start
      if isPrivateRef astFuel arg then fail "private fields cannot be deleted" t.start
    return (.unary op arg, {}, true)
  if t.kind == .inc || t.kind == .dec then
    next
    let p := (← tok).start
    let arg ← r.unary
    let _ ← simpleTarget arg true p
    return (.update (t.kind == .inc) true arg, {}, false)
  let (e, c) ← parseExprSubscripts r noIn
  if let .func f := e then
    if f.kind == .arrow then return (e, c, false)
  let t2 ← tok
  if (t2.kind == .inc || t2.kind == .dec) && !t2.nl then
    checkCover c
    let _ ← simpleTarget e true t.start
    next
    return (.update (t2.kind == .inc) false e, {}, false)
  return (e, c, false)

/-- Binary operators and their precedence (`in` only when allowed). -/
def binOpOf (t : Token) (noIn : Bool) : Option (Sum BinOp LogOp × Nat) :=
  match t.kind with
  | .nullish => some (.inr .nullish, 1)
  | .or2 => some (.inr .or, 1)
  | .and2 => some (.inr .and, 2)
  | .pipe => some (.inl .bitOr, 3)
  | .caret => some (.inl .bitXor, 4)
  | .amp => some (.inl .bitAnd, 5)
  | .eq2 => some (.inl .eq, 6) | .ne => some (.inl .ne, 6)
  | .eq3 => some (.inl .seq, 6) | .ne3 => some (.inl .sne, 6)
  | .lt => some (.inl .lt, 7) | .gt => some (.inl .gt, 7)
  | .le => some (.inl .le, 7) | .ge => some (.inl .ge, 7)
  | .shl => some (.inl .shl, 8) | .sar => some (.inl .sar, 8) | .shr => some (.inl .shr, 8)
  | .plus => some (.inl .add, 9) | .minus => some (.inl .sub, 9)
  | .star => some (.inl .mul, 10) | .slash => some (.inl .div, 10) | .percent => some (.inl .mod, 10)
  | .star2 => some (.inl .exp, 11)
  | .name =>
    if t.escaped then none
    else if t.kw == .kInstanceof then some (.inl .instanceof, 7)
    else if t.kw == .kIn && !noIn then some (.inl .in, 7)
    else none
  | _ => none

/-- An operand of the binary operators: a UnaryExpression, or `#x` before `in`. -/
structure Operand where
  e : Expr
  priv : Option JSStr := none
  deriving Inhabited

instance : Inhabited (Sum BinOp LogOp) := ⟨.inl .add⟩

def reduceOp (operands : Array Operand) (op : Sum BinOp LogOp) (pos : Nat) : P (Array Operand) := do
  let rhs := operands.back!
  let operands := operands.pop
  let lhs := operands.back!
  let operands := operands.pop
  if rhs.priv.isSome then fail "unexpected private name" pos
  let e ← match op, lhs.priv with
    | .inl .in, some n => pure (Expr.privIn n rhs.e)
    | _, some _ => fail "unexpected private name" pos
    | .inl b, none => pure (Expr.binary b lhs.e rhs.e)
    | .inr l, none => pure (Expr.logical l lhs.e rhs.e)
  return operands.push { e }

/-- ShortCircuitExpression: the binary operators by precedence (operator-precedence parsing
with explicit stacks; `**` is right-associative; `??` does not mix with `&&`/`||`).
spec: https://tc39.es/ecma262/#sec-binary-logical-operators -/
def parseExprOps (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let b0 := (← get).budget
  let start := (← tok).start
  let readOperand (canPriv : Bool) : P (Operand × Cover × Bool) := do
    let t ← tok
    if t.kind == .priv then
      let p ← peek
      if !canPriv || noIn || !(p.kind == .name && p.kw == .kIn && !p.escaped) then unexpected
      usePrivate t.val t.start
      next
      return ({ e := .this, priv := some t.val }, {}, false)
    let (e, c, u) ← parseMaybeUnary r noIn
    return ({ e }, c, u)
  let (first, c0, u0) ← readOperand true
  if let .func f := first.e then
    if f.kind == .arrow then return (first.e, c0)
  let mut operands : Array Operand := #[first]
  let mut ops : Array (Sum BinOp LogOp × Nat × Nat) := #[]
  let mut lastUnary := u0
  let mut sawNullish := false
  let mut sawLogical := false
  let mut any := false
  for _ in [0:← loopFuel] do
    let t ← tok
    match binOpOf t noIn with
    | none => break
    | some (op, prec) =>
      if !any then checkCover c0
      any := true
      if op matches .inr .nullish then sawNullish := true
      if op matches .inr .and || op matches .inr .or then sawLogical := true
      if sawNullish && sawLogical then fail "cannot mix ?? with && or || without parentheses" t.start
      if prec == 11 && lastUnary then fail "unary operator before ** must be parenthesized" t.start
      -- reduce operators that bind at least as tightly (** is right-associative)
      for _ in [0:ops.size] do
        match ops.back? with
        | some (op', prec', pos') =>
          if prec' > prec || (prec' == prec && prec != 11) then
            operands ← reduceOp operands op' pos'
            ops := ops.pop
          else break
        | none => break
      ops := ops.push (op, prec, t.start)
      next
      let canPriv := match ops.back? with | some (_, p, _) => p < 7 | none => true
      let canPriv := canPriv && (ops.size < 2 || (ops[ops.size - 2]!.2.1 < 7))
      let (o, c, u) ← readOperand canPriv
      if let .func f := o.e then
        if f.kind == .arrow then fail "arrow function in binary expression" f.info.span.start
      checkCover c
      operands := operands.push o
      lastUnary := u
      chainStep
  for _ in [0:ops.size] do
    match ops.back? with
    | some (op', _, pos') => operands ← reduceOp operands op' pos'; ops := ops.pop
    | none => break
  restoreBudget b0
  let res := operands.back!
  if res.priv.isSome then fail "unexpected private name" start
  return (res.e, if any then {} else c0)

/-- ConditionalExpression. spec: https://tc39.es/ecma262/#sec-conditional-operator -/
def parseConditional (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let (e, c) ← parseExprOps r noIn
  if let .func f := e then
    if f.kind == .arrow then return (e, c)
  if (← tokKind) == .question then
    checkCover c
    next
    let cons ← r.assign false
    expect .colon
    let alt ← r.assign noIn
    return (.cond e cons alt, {})
  return (e, c)

/-- YieldExpression. spec: https://tc39.es/ecma262/#sec-generator-function-definitions -/
def parseYield (r : Rec) (noIn : Bool) : P Expr := do
  let t ← tok
  if t.escaped then fail "keyword must not contain escaped characters" t.start
  next
  if (← get).yieldPos == 0 then modify fun s => { s with yieldPos := t.start + 1 }
  let n ← tok
  if n.nl then return .yield none false
  match n.kind with
  | .rparen | .rbracket | .rbrace | .comma | .semi | .colon | .eof | .question =>
    return .yield none false
  | .star =>
    next
    return .yield (some (← r.assign noIn)) true
  | .name =>
    if n.kw == .kIn && !n.escaped then return .yield none false
    return .yield (some (← r.assign noIn)) false
  | _ =>
    if (binOpOf n false).isSome && n.kind != .plus && n.kind != .minus && n.kind != .slash then
      return .yield none false
    return .yield (some (← r.assign noIn)) false

def assignOpOf : T → Option AssignOp
  | .assign => some .assign
  | .plusEq => some (.op .add) | .minusEq => some (.op .sub) | .starEq => some (.op .mul)
  | .slashEq => some (.op .div) | .percentEq => some (.op .mod) | .star2Eq => some (.op .exp)
  | .shlEq => some (.op .shl) | .sarEq => some (.op .sar) | .shrEq => some (.op .shr)
  | .ampEq => some (.op .bitAnd) | .pipeEq => some (.op .bitOr) | .caretEq => some (.op .bitXor)
  | .and2Eq => some (.logical .and) | .or2Eq => some (.logical .or)
  | .nullishEq => some (.logical .nullish)
  | _ => none

/-- AssignmentExpression (with arrow functions, yield, and destructuring assignment).
spec: https://tc39.es/ecma262/#sec-assignment-operators-static-semantics-early-errors -/
def parseMaybeAssign (r : Rec) (noIn : Bool) : P (Expr × Cover) := do
  let t ← tok
  if t.kind == .name && t.kw == .kYield && (← get).fn.yieldExpr then
    return (← parseYield r noIn, {})
  let (left, c) ← parseConditional r noIn
  if let .func f := left then
    if f.kind == .arrow then return (left, c)
  let a ← tok
  match assignOpOf a.kind with
  | none => return (left, c)
  | some op =>
    let target ← match op, left with
      | .assign, .object _ | .assign, .array _ =>
        if c.trailing != 0 then fail "invalid rest element" (c.trailing - 1)
        toPattern astFuel false left t.start
      | .assign, _ => do checkCover c; simpleTarget left true t.start
      | .op _, _ => do checkCover c; simpleTarget left true t.start
      | .logical _, _ => do checkCover c; simpleTarget left false t.start
    next
    let v ← r.assign noIn
    return (.assign op target v, {})

/-- Expression: comma-separated AssignmentExpressions.
spec: https://tc39.es/ecma262/#sec-comma-operator -/
def parseExpression (r : Rec) (noIn : Bool) : P Expr := do
  let e ← r.assign noIn
  if (← tokKind) != .comma then return e
  let mut es := #[e]
  for _ in [0:← loopFuel] do
    if !(← eat .comma) then break
    es := es.push (← r.assign noIn)
  return .seq es

/-! ## Statements
spec: https://tc39.es/ecma262/#sec-ecmascript-language-statements-and-declarations -/

/-- Declares a declaration's bound names: `var` up to the var scope, others in the current
scope (`let` is not a valid lexically bound name).
spec: https://tc39.es/ecma262/#sec-let-and-const-declarations-static-semantics-early-errors -/
def declarePattern (kind : VarKind) (p : Pattern) (pos : Nat) : P Unit := do
  for n in patNames astFuel p #[] do
    match kind with
    | .var => declareVar n pos
    | _ =>
      if n == kLet then fail "'let' is not a valid lexically bound name" pos
      declareLex n pos

/-- A VariableDeclarationList / BindingList (`inFor`: initializers may be missing, checked by
the caller once it knows whether this is a for-in/of head). -/
def parseDeclList (r : Rec) (kind : VarKind) (noIn : Bool) (inFor : Bool) : P (Array VarDeclarator) := do
  let mut decls : Array VarDeclarator := #[]
  for _ in [0:← loopFuel] do
    let start := (← tok).start
    let isUsing := kind == .using || kind == .awaitUsing
    if isUsing && ((← tokKind) == .lbracket || (← tokKind) == .lbrace) then
      fail "using declarations may not have patterns" start
    let target ← parseBindingAtom r
    declarePattern kind target start
    let init ← if ← eat .assign then pure (some (← r.assign noIn)) else pure none
    if init.isNone && !inFor then
      if kind == .const || isUsing then fail "missing initializer in declaration" start
      if !(target matches .ident _) then fail "missing initializer in destructuring declaration" start
    decls := decls.push (.mk target init)
    if !(← eat .comma) then break
  return decls

/-- Whether `let` at the current token starts a LexicalDeclaration. -/
def isLetDecl : P Bool := do
  let t ← tok
  if !(t.kind == .name && t.kw == .kLet && !t.escaped) then return false
  let p ← peek
  match p.kind with
  | .lbracket | .lbrace => return true
  | .name => return !(p.kw == .kIn && !p.escaped) && !(p.kw == .kInstanceof && !p.escaped)
  | _ => return false

/-- Whether `using` / `await using` at the current token starts a declaration. -/
def usingDeclKind (inFor : Bool) : P (Option VarKind) := do
  let t ← tok
  if t.kind != .name || t.escaped then return none
  if t.kw == .kUsing then
    let p ← peek
    if p.kind != .name || p.nl || (p.kw == .kIn && !p.escaped) || (p.kw == .kInstanceof && !p.escaped) then
      return none
    if inFor && p.kw == .kOf && !p.escaped then
      -- `for (using of …)` is an expression head; `for (using of of …)` / `= …` a declaration
      let p2 ← peek2
      if !((p2.kind == .name && p2.kw == .kOf) || p2.kind == .assign || p2.kind == .semi) then
        return none
    return some .using
  if t.kw == .kAwait && (← get).fn.awaitExpr then
    let p ← peek
    if p.kind != .name || p.kw != .kUsing || p.escaped || p.nl then return none
    let p2 ← peek2
    if p2.kind != .name || p2.nl || (p2.kw == .kIn && !p2.escaped) || (p2.kw == .kInstanceof && !p2.escaped) then
      return none
    if inFor && p2.kw == .kOf && !p2.escaped then
      let p3 ← peek3
      if !((p3.kind == .name && p3.kw == .kOf) || p3.kind == .assign || p3.kind == .semi) then
        return none
    return some .awaitUsing
  return none

/-- A block's statements in a new scope, from `{`. -/
def parseBlock (r : Rec) : P (Array Stmt) := do
  expect .lbrace
  enterScope 0
  let (body, _) ← parseBodyList r .item .rbrace false
  expect .rbrace
  exitScope
  return body

/-- The early errors of `break`/`continue` targets.
spec: https://tc39.es/ecma262/#sec-break-statement-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-continue-statement-static-semantics-early-errors -/
def parseBreakContinue (isBreak : Bool) : P Stmt := do
  let start := (← tok).start
  next
  let t ← tok
  let mut label : Option JSStr := none
  if t.kind == .name && !t.nl && !(t.kw.isReserved && !t.escaped) then
    checkIdent t false
    next
    label := some t.val
  semicolon
  let labels := (← get).labels
  match label with
  | some l =>
    match labels.findRev? (·.name == some l) with
    | none => fail s!"undefined label '{l}'" start
    | some lb => if !isBreak && lb.kind != 1 then fail s!"'{l}' does not label an iteration statement" start
  | none =>
    if isBreak then
      if !labels.any (fun lb => lb.name.isNone) then fail "illegal break statement" start
    else
      if !labels.any (fun lb => lb.name.isNone && lb.kind == 1) then fail "illegal continue statement" start
  return if isBreak then .brk label else .cont label

/-- Pushes the anonymous label of an iteration (kind 1) or switch (kind 2) statement and
marks the labels directly on it as iteration labels. -/
def pushLoopLabel (kind : Nat) (start : Nat) : P Unit := do
  modify fun s => { s with labels := (s.labels.map fun lb =>
    if lb.stmtStart == start && lb.name.isSome then { lb with kind } else lb).push { name := none, kind, stmtStart := start } }

def popLabel : P Unit := modify fun s => { s with labels := s.labels.pop }

/-- `for` statements from `for`.
spec: https://tc39.es/ecma262/#sec-for-statement
spec: https://tc39.es/ecma262/#sec-for-in-and-for-of-statements-static-semantics-early-errors
spec: https://tc39.es/ecma262/#sec-initializers-in-forin-statement-heads -/
def parseFor (r : Rec) : P Stmt := do
  let start := (← tok).start
  next
  let mut isAwait := false
  if ← isKeyword .kAwait then
    if !(← get).fn.awaitExpr then fail "for await outside async function" (← tok).start
    next; isAwait := true
  expect .lparen
  pushLoopLabel 1 start
  enterScope 0
  let body (r : Rec) : P Stmt := r.stmt .stmt
  let finishInOf (lhs : ForLhs) (isOf : Bool) : P Stmt := do
    next
    let rhs ← if isOf then r.assign false else parseExpression r false
    expect .rparen
    let b ← body r
    return if isOf then .forOf lhs rhs b isAwait else .forIn lhs rhs b
  let classic (init : Option ForInit) : P Stmt := do
    if isAwait then fail "for await requires of" start
    expect .semi
    let test ← if (← tokKind) == .semi then pure none else pure (some (← parseExpression r false))
    expect .semi
    let update ← if (← tokKind) == .rparen then pure none else pure (some (← parseExpression r false))
    expect .rparen
    let b ← body r
    return .forS init test update b
  let declHead (kind : VarKind) : P Stmt := do
    let declStart := (← tok).start
    let decls ← parseDeclList r kind true true
    let isOf ← isKw .kOf
    let isIn := (← tokKind) == .name && (← tok).kw == .kIn && !(← tok).escaped
    if decls.size == 1 && (isOf || isIn) then
      let .mk target init := decls[0]!
      if isIn && (kind == .using || kind == .awaitUsing) then fail "using declaration in for-in" declStart
      if init.isSome then
        -- Annex B: `for (var x = init in o)` in sloppy mode
        if !(isIn && kind == .var && !(← get).strict && (target matches .ident _)) then
          fail "for-in/of loop variable declaration may not have an initializer" declStart
      if isIn && isAwait then fail "for await requires of" start
      return ← finishInOf (.decl kind target init) isOf
    for d in decls do
      let .mk target init := d
      if init.isNone && (kind == .const || kind == .using || kind == .awaitUsing || !(target matches .ident _)) then
        fail "missing initializer in declaration" declStart
    classic (some (.decl kind decls))
  let t ← tok
  let res ← do
    if t.kind == .semi then classic none
    else if ← isKeyword .kVar then next; declHead .var
    else if ← isLetDecl then
      if (← get).strict || true then pure ()
      next; declHead .let
    else if ← isKeyword .kConst then next; declHead .const
    else match ← usingDeclKind true with
    | some k =>
      next
      if k == .awaitUsing then next
      declHead k
    | none =>
      let t0 ← tok
      let (e, c) ← r.assignC true
      let isOf ← isKw .kOf
      let isIn := (← tokKind) == .name && (← tok).kw == .kIn && !(← tok).escaped
      if isOf || isIn then
        if isOf && t0.kind == .name && t0.kw == .kLet && !t0.escaped then
          fail "for-of left side may not start with 'let'" t0.start
        if isOf && !isAwait && t0.kind == .name && t0.kw == .kAsync && !t0.escaped &&
            (e matches .ident _) && (← get).prevEnd == t0.stop then
          fail "for-of left side may not be 'async'" t0.start
        if isIn && isAwait then fail "for await requires of" start
        let target ← match e with
          | .object _ | .array _ =>
            if c.trailing != 0 then fail "invalid rest element" (c.trailing - 1)
            toPattern astFuel false e t0.start
          | _ => do checkCover c; simpleTarget e true t0.start
        finishInOf (.pattern target) isOf
      else
        checkCover c
        let mut e := e
        if (← tokKind) == .comma then
          let mut es := #[e]
          for _ in [0:← loopFuel] do
            if !(← eat .comma) then break
            es := es.push (← r.assign true)
          e := .seq es
        classic (some (.expr e))
  exitScope
  popLabel
  return res

/-- `switch`. spec: https://tc39.es/ecma262/#sec-switch-statement-static-semantics-early-errors -/
def parseSwitch (r : Rec) : P Stmt := do
  let start := (← tok).start
  next
  expect .lparen
  let disc ← parseExpression r false
  expect .rparen
  expect .lbrace
  pushLoopLabel 2 start
  enterScope 0
  let mut cases : Array SwitchCase := #[]
  let mut sawDefault := false
  for _ in [0:← loopFuel] do
    if (← tokKind) == .rbrace then break
    let test ← if ← isKeyword .kCase then do
        next
        pure (some (← parseExpression r false))
      else if ← isKeyword .kDefault then do
        if sawDefault then fail "multiple default clauses" (← tok).start
        sawDefault := true
        next
        pure none
      else unexpected
    expect .colon
    let mut body : Array Stmt := #[]
    for _ in [0:← loopFuel] do
      let k ← tokKind
      if k == .rbrace || k == .eof || (← isKeyword .kCase) || (← isKeyword .kDefault) then break
      body := body.push (← r.stmt .caseItem)
    cases := cases.push (.mk test body)
  expect .rbrace
  exitScope
  popLabel
  return .switch disc cases

/-- `try`. spec: https://tc39.es/ecma262/#sec-try-statement-static-semantics-early-errors -/
def parseTry (r : Rec) : P Stmt := do
  let start := (← tok).start
  next
  let block ← parseBlock r
  let mut handler : Option CatchClause := none
  if ← isKeyword .kCatch then
    next
    if ← eat .lparen then
      let t ← tok
      let simple := t.kind == .name
      enterScope (if simple then sSimpleCatch else 0)
      let param ← parseBindingAtom r
      match param with
      | .ident n =>
        modify fun s => { s with scopes := s.scopes.modify (s.scopes.size - 1) fun sc =>
          { sc with lexical := sc.lexical.insert n, catchName := some n } }
      | _ => declarePattern .let param t.start
      expect .rparen
      expect .lbrace
      let (body, _) ← parseBodyList r .item .rbrace false
      expect .rbrace
      exitScope
      handler := some (.mk (some param) body)
    else
      handler := some (.mk none (← parseBlock r))
  let mut finalizer : Option (Array Stmt) := none
  if ← isKeyword .kFinally then
    next
    finalizer := some (← parseBlock r)
  if handler.isNone && finalizer.isNone then fail "missing catch or finally after try" start
  return .tryS block handler finalizer

/-- A FunctionDeclaration (or generator/async) from `function` (or `async`). -/
def parseFunctionDecl (r : Rec) (isAsync : Bool) (nameOptional : Bool := false) : P Func := do
  let start := (← tok).start
  if isAsync then next
  next
  let isGen ← eat .star
  let t ← tok
  if t.kind != .name || (t.kw == .kExtends && false) then
    if nameOptional && t.kind == .lparen then
      declareLex kStarDefault start
      return ← parseFunctionRest r { kind := .normal, isAsync, isGen, start }
    unexpected
  let (n, kw, p) ← bindingIdent
  declareFunc n p (!isAsync && !isGen)
  parseFunctionRest r { kind := .normal, isAsync, isGen, start, name := some n, nameKw := kw, namePos := p }

/-- ModuleExportName / the string forms must be well-formed Unicode.
spec: https://tc39.es/ecma262/#sec-module-semantics-static-semantics-early-errors -/
def moduleExportName : P (JSStr × Bool) := do
  let t ← tok
  if t.kind == .str then
    let mut i := 0
    for _ in [0:t.val.length] do
      if i ≥ t.val.length then break
      let (_, n, lone) := t.val.codePointAt i
      if lone then fail "export name must be well-formed Unicode" t.start
      i := i + n
    next
    return (t.val, true)
  if t.kind == .name then next; return (t.val, false)
  unexpected

/-- `with { type: "json" }` (WithClause). spec: https://tc39.es/ecma262/#sec-imports -/
def parseWithClause : P (Array (JSStr × JSStr)) := do
  if !(← isKeyword .kWith) then return #[]
  next
  expect .lbrace
  let mut attrs : Array (JSStr × JSStr) := #[]
  for _ in [0:← loopFuel] do
    if (← tokKind) == .rbrace then break
    let kt ← tok
    if kt.kind != .name && kt.kind != .str then unexpected
    next
    expect .colon
    let vt ← tok
    if vt.kind != .str then unexpected
    next
    if attrs.any (·.1 == kt.val) then fail "duplicate import attribute" kt.start
    attrs := attrs.push (kt.val, vt.val)
    if (← tokKind) != .rbrace then expect .comma
  expect .rbrace
  return attrs

def moduleSpecifier : P JSStr := do
  let t ← tok
  if t.kind != .str then unexpected
  next
  return t.val

/-- ImportDeclaration from `import`.
spec: https://tc39.es/ecma262/#sec-imports-static-semantics-early-errors -/
def parseImportDecl : P Stmt := do
  next
  if (← tokKind) == .str then
    let m ← moduleSpecifier
    let attrs ← parseWithClause
    semicolon
    return .importDecl (.mk none none #[] m attrs none)
  let mut defaultName : Option JSStr := none
  let mut nsName : Option JSStr := none
  let mut named : Array (JSStr × JSStr) := #[]
  if (← tokKind) == .name then
    let t ← tok
    if (t.kw == .kDefer || t.kw == .kSource) && !t.escaped then
      let p ← peek
      if (t.kw == .kDefer && p.kind == .star) || (t.kw == .kSource && p.kind == .name && !(p.kw == .kFrom && !p.escaped)) then
        fail "import phases are not supported" t.start
    let (n, _, p) ← bindingIdent
    declareLex n p
    defaultName := some n
    if (← tokKind) == .comma then
      next
      let k ← tokKind
      if k != .star && k != .lbrace then unexpected
  if (← tokKind) == .star then
    next
    expectKw .kAs
    let (n, _, p) ← bindingIdent
    declareLex n p
    nsName := some n
  else if (← tokKind) == .lbrace then
    next
    for _ in [0:← loopFuel] do
      if (← tokKind) == .rbrace then break
      let t ← tok
      let (imported, isStr) ← moduleExportName
      if ← isKw .kAs then
        next
        let (n, _, p) ← bindingIdent
        declareLex n p
        named := named.push (imported, n)
      else
        if isStr then fail "string import name requires 'as'" t.start
        checkIdent t true
        declareLex t.val t.start
        named := named.push (imported, t.val)
      if (← tokKind) != .rbrace then expect .comma
    expect .rbrace
  else if defaultName.isNone then unexpected
  expectKw .kFrom
  let m ← moduleSpecifier
  let attrs ← parseWithClause
  semicolon
  return .importDecl (.mk defaultName nsName named m attrs none)

def addExport (name : JSStr) (pos : Nat) : P Unit := do
  if (← get).exported.contains name then fail s!"duplicate export '{name}'" pos
  modify fun s => { s with exported := s.exported.insert name }

/-- The names a declaration statement binds (for `export`). -/
def stmtBoundNames : Stmt → Array JSStr
  | .varDecl _ decls => decls.foldl (fun acc d => match d with | .mk t _ => patNames astFuel t acc) #[]
  | .funDecl f => match f.name with | some n => #[n] | none => #[]
  | .classDecl c => match c.name with | some n => #[n] | none => #[]
  | _ => #[]

/-- A function declaration where only a Statement is allowed: Annex B allows plain functions
in sloppy `if` clauses (as if in a block) and as labelled items.
spec: https://tc39.es/ecma262/#sec-functiondeclarations-in-ifstatement-statement-clauses
spec: https://tc39.es/ecma262/#sec-labelled-function-declarations -/
def parseFunctionStmt (r : Rec) (pos : SPos) : P Stmt := do
  let start := (← tok).start
  match pos with
  | .top | .item | .caseItem => return .funDecl (← parseFunctionDecl r false)
  | .ifBody | .label true =>
    if (← get).strict then fail "function declaration not allowed here in strict mode" start
    if (← peek).kind == .star then fail "generator declaration not allowed here" start
    if pos == .ifBody then
      enterScope 0
      let f ← parseFunctionDecl r false
      exitScope
      return .block #[.funDecl f]
    return .funDecl (← parseFunctionDecl r false)
  | _ => fail "function declaration not allowed here" start

/-- ExportDeclaration from `export`.
spec: https://tc39.es/ecma262/#sec-exports-static-semantics-early-errors -/
def parseExport (r : Rec) : P Stmt := do
  next
  let t ← tok
  if t.kind == .star then
    next
    let mut asName : Option JSStr := none
    if ← isKw .kAs then
      next
      let p := (← tok).start
      let (n, _) ← moduleExportName
      addExport n p
      asName := some n
    expectKw .kFrom
    let m ← moduleSpecifier
    let attrs ← parseWithClause
    semicolon
    return .exportDecl (.all asName m attrs)
  if t.kind == .lbrace then
    next
    let mut specs : Array (JSStr × JSStr × Token × Bool) := #[]
    for _ in [0:← loopFuel] do
      if (← tokKind) == .rbrace then break
      let lt ← tok
      let (loc, isStr) ← moduleExportName
      let mut exported := loc
      let ep := (← tok).start
      if ← isKw .kAs then
        next
        let (n, _) ← moduleExportName
        exported := n
      addExport exported (if exported == loc then lt.start else ep)
      specs := specs.push (loc, exported, lt, isStr)
      if (← tokKind) != .rbrace then expect .comma
    expect .rbrace
    if ← isKw .kFrom then
      next
      let m ← moduleSpecifier
      let attrs ← parseWithClause
      semicolon
      return .exportDecl (.namedFrom (specs.map fun (l, e, _, _) => (l, e)) m attrs)
    for (l, _, lt, isStr) in specs do
      if isStr then fail "string export name requires 'from'" lt.start
      if lt.kw.isReserved || lt.kw.isStrictReserved || lt.kw == .kAwait then
        fail s!"unexpected reserved word '{l}'" lt.start
      modify fun s => { s with exportLocals := s.exportLocals.push (l, lt.start) }
    semicolon
    return .exportDecl (.named (specs.map fun (l, e, _, _) => (l, e)))
  if ← isKeyword .kDefault then
    addExport kDefault t.start
    next
    if ← isKeyword .kFunction then
      return .exportDecl (.defaultFunc (← parseFunctionDecl r false true))
    if ← isKw .kAsync then
      let p ← peek
      if p.kind == .name && p.kw == .kFunction && !p.escaped && !p.nl then
        return .exportDecl (.defaultFunc (← parseFunctionDecl r true true))
    if ← isKeyword .kClass then
      let c ← parseClass r true true
      if c.name.isNone then declareLex kStarDefault t.start
      return .exportDecl (.defaultClass c)
    let e ← r.assign false
    semicolon
    declareLex kStarDefault t.start
    return .exportDecl (.defaultExpr e)
  let ok ← do
    if (← isKeyword .kVar) || (← isKeyword .kConst) || (← isKeyword .kFunction) || (← isKeyword .kClass) then pure true
    else if ← isLetDecl then pure true
    else if ← isKw .kAsync then
      let p ← peek
      pure (p.kind == .name && p.kw == .kFunction && !p.escaped && !p.nl)
    else pure false
  if !ok then unexpected
  let st ← r.stmt .top
  for n in stmtBoundNames st do addExport n t.start
  return .exportDecl (.decl st)

/-- Statement / Declaration / module items at `pos`.
spec: https://tc39.es/ecma262/#sec-ecmascript-language-statements-and-declarations -/
def parseStatement (r : Rec) (pos : SPos) : P Stmt := do
  let t ← tok
  let start := t.start
  let s ← get
  match t.kind with
  | .lbrace => return .block (← parseBlock r)
  | .semi => next; return .empty
  | .name =>
    let kw := if t.escaped then Kw.none else t.kw
    match kw with
    | .kVar =>
      next
      let decls ← parseDeclList r .var false false
      semicolon
      return .varDecl .var decls
    | .kConst =>
      if !pos.isItem then fail "lexical declaration not allowed here" start
      next
      let decls ← parseDeclList r .const false false
      semicolon
      return .varDecl .const decls
    | .kIf =>
      next
      expect .lparen
      let test ← parseExpression r false
      expect .rparen
      let cons ← r.stmt .ifBody
      let alt ← if ← isKeyword .kElse then do next; pure (some (← r.stmt .ifBody)) else pure none
      return .ifS test cons alt
    | .kFor => parseFor r
    | .kWhile =>
      next
      expect .lparen
      let test ← parseExpression r false
      expect .rparen
      pushLoopLabel 1 start
      let body ← r.stmt .stmt
      popLabel
      return .whileS test body
    | .kDo =>
      next
      pushLoopLabel 1 start
      let body ← r.stmt .stmt
      popLabel
      if !(← isKeyword .kWhile) then unexpected
      next
      expect .lparen
      let test ← parseExpression r false
      expect .rparen
      discard <| eat .semi
      return .doWhile body test
    | .kContinue => parseBreakContinue false
    | .kBreak => parseBreakContinue true
    | .kReturn =>
      if !s.fn.returnOk then fail "return outside function" start
      next
      if ← canInsertSemi then semicolon; return .ret none
      let e ← parseExpression r false
      semicolon
      return .ret (some e)
    | .kWith =>
      -- spec: https://tc39.es/ecma262/#sec-with-statement-static-semantics-early-errors
      if s.strict then fail "with statement in strict mode" start
      next
      expect .lparen
      let obj ← parseExpression r false
      expect .rparen
      let body ← r.stmt .stmt
      return .with obj body
    | .kSwitch => parseSwitch r
    | .kThrow =>
      next
      if (← tok).nl then fail "line terminator after throw" start
      let e ← parseExpression r false
      semicolon
      return .throw e
    | .kTry => parseTry r
    | .kDebugger => next; semicolon; return .debugger
    | .kFunction => parseFunctionStmt r pos
    | .kClass =>
      if !pos.isItem then fail "class declaration not allowed here" start
      return .classDecl (← parseClass r true false)
    | .kImport =>
      let p ← peek
      if p.kind != .lparen && p.kind != .dot then
        if s.isModule && pos == .top then return ← parseImportDecl
        fail "import declarations may only appear at the top level of a module" start
      parseExprStatement r pos
    | .kExport =>
      if s.isModule && pos == .top then return ← parseExport r
      fail "export declarations may only appear at the top level of a module" start
    | .kAsync =>
      let p ← peek
      if p.kind == .name && p.kw == .kFunction && !p.escaped && !p.nl then
        if !pos.isItem then fail "async function declaration not allowed here" start
        return .funDecl (← parseFunctionDecl r true)
      parseExprStatement r pos
    | .kLet =>
      if pos.isItem then
        if ← isLetDecl then
          next
          let decls ← parseDeclList r .let false false
          semicolon
          return .varDecl .let decls
      else
        let p ← peek
        if p.kind == .lbracket then fail "lexical declaration not allowed here" start
      parseExprStatement r pos
    | .kUsing | .kAwait =>
      match ← usingDeclKind false with
      | some k =>
        if !pos.isItem || pos == .caseItem || (pos == .top && !s.isModule) then
          fail "using declaration not allowed here" start
        next
        if k == .awaitUsing then next
        let decls ← parseDeclList r k false false
        semicolon
        return .varDecl k decls
      | none => parseExprStatement r pos
    | _ => parseExprStatement r pos
  | _ => parseExprStatement r pos
where
  /-- ExpressionStatement or LabelledStatement.
  spec: https://tc39.es/ecma262/#sec-labelled-statements-static-semantics-early-errors -/
  parseExprStatement (r : Rec) (pos : SPos) : P Stmt := do
    let t ← tok
    let isLabel ← if t.kind == .name then pure ((← peek).kind == .colon) else pure false
    if isLabel then
        checkIdent t false
        let n := t.val
        next
        next
        let s ← get
        if s.labels.any (·.name == some n) then fail s!"duplicate label '{n}'" t.start
        let bodyStart := (← tok).start
        let lbl : Label := { name := some n, kind := 0, stmtStart := bodyStart }
        let relabel (lb : Label) : Label :=
          if lb.stmtStart == t.start && lb.name.isSome then { lb with stmtStart := bodyStart } else lb
        modify fun s => { s with labels := (s.labels.map relabel).push lbl }
        let ok := pos.isItem || pos == .label true
        let body ← r.stmt (.label ok)
        popLabel
        return .labeled n body
    let e ← parseExpression r false
    semicolon
    return .expr e

/-! ## The recursion knot -/

/-- One level of the parser over the next level down (`r`). -/
def step (r : Rec) : Rec where
  assignC := fun noIn => nest (parseMaybeAssign r noIn)
  expr := fun noIn => nest (parseExpression r noIn)
  unary := nest do
    let (e, c, _) ← parseMaybeUnary r false
    checkCover c
    if let .func f := e then
      if f.kind == .arrow then fail "arrow function is not a unary operand" f.info.span.start
    return e
  stmt := fun pos => nest (parseStatement r pos)
  binding := nest (parseBindingAtom r)
  member := nest (parseMemberOnly r)
  lhs := nest do
    let (e, c) ← parseExprSubscripts r false
    checkCover c
    if let .func f := e then
      if f.kind == .arrow then fail "arrow function is not a left-hand-side expression" f.info.span.start
    return e

/-- `n` levels of the parser. -/
def tie : Nat → Rec
  | 0 => Rec.bottom
  | n + 1 => step (tie n)

/-- The parser: `maxNesting + 1` levels (the nesting budget runs out before the levels do). -/
def topRec : Rec := tie (maxNesting + 1)

end ES.Parse

namespace ES

open ES.Parse ES.Lex

/-! ## Entry points -/

def runP {α : Type} (p : P α) (s : PState) : Except SyntaxError α :=
  match p.run s with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- The initial state at the start of `src` (after a hashbang when `hashbang`). -/
def initState (src : String) (isModule strict : Bool) (fn : Fn) (hashbang : Bool := true) :
    Except SyntaxError PState := do
  let bytes := src.toUTF8
  let hb := if hashbang then skipHashbang bytes else 0
  let t ← lex bytes hb isModule (lineStart := true)
  return { src := bytes, isModule, strict, fn, tok := t, budget := maxNesting }

/-- Checks that the module's `export { x }` names are declared.
spec: https://tc39.es/ecma262/#sec-module-semantics-static-semantics-early-errors -/
def checkExportLocals : P Unit := do
  let s ← get
  let top := s.scopes[0]!
  for (n, p) in s.exportLocals do
    if !(top.vars.contains n || top.lexical.contains n || top.funcs.contains n) then
      fail s!"export of undeclared name '{n}'" p

def parseProgram (isModule : Bool) : P (Array Stmt × Bool) := do
  enterScope (sVar ||| sTop)
  let (body, _) ← parseBodyList topRec .top .eof (!isModule)
  if (← tokKind) != .eof then unexpected
  if isModule then checkExportLocals
  return (body, (← get).strict)

/-- ParseScript: a Script (`strict`: the code is strict from the start).
spec: https://tc39.es/ecma262/#sec-parse-script -/
def parseScript (src : String) (strict : Bool := false) : Except SyntaxError Program := do
  let s ← initState src false strict {}
  let (body, strict) ← runP (parseProgram false) s
  return { body, isModule := false, strict, source := src }

/-- ParseModule: a Module (strict; top-level `await`).
spec: https://tc39.es/ecma262/#sec-parsemodule -/
def parseModule (src : String) : Except SyntaxError Program := do
  let s ← initState src true true { awaitExpr := true, awaitReserved := true }
  let (body, _) ← runP (parseProgram true) s
  return { body, isModule := true, strict := true, source := src }

/-- What PerformEval's early errors depend on: where the (direct) eval occurs.
spec: https://tc39.es/ecma262/#sec-performeval -/
structure EvalContext where
  /-- A direct eval (otherwise all the following are ignored: an indirect eval is global
  code). -/
  direct : Bool := false
  /-- The caller is strict mode code (direct evals inherit strictness). -/
  strict : Bool := false
  /-- Inside a function: `new.target` allowed. -/
  inFunction : Bool := false
  /-- Inside a method (incl. field initializers, static blocks): `super.x` allowed. -/
  inMethod : Bool := false
  /-- Inside a derived constructor: `super()` allowed. -/
  inDerivedConstructor : Bool := false
  /-- Inside a class field initializer: `arguments` is an error. -/
  inClassFieldInitializer : Bool := false
  /-- The private names of the enclosing classes. -/
  privateNames : Array JSStr := #[]
  deriving Inhabited

/-- PerformEval's parse: `src` as a Script with the early errors of its context (steps 6-11).
spec: https://tc39.es/ecma262/#sec-performeval -/
def parseEval (src : String) (ctx : EvalContext) : Except SyntaxError Program := do
  let d := ctx.direct
  let fn : Fn := { newTarget := d && ctx.inFunction, superProp := d && ctx.inMethod,
                   superCall := d && ctx.inDerivedConstructor,
                   noArguments := d && ctx.inClassFieldInitializer }
  let s ← initState src false (d && ctx.strict) fn
  let s := { s with outerPrivate := if d then ctx.privateNames else #[] }
  let (body, strict) ← runP (parseProgram false) s
  return { body, isModule := false, strict, source := src }

/-- The kind of function a dynamic function constructor makes. -/
inductive DynFnKind where
  | normal | generator | async | asyncGenerator
  deriving BEq, Inhabited, Repr

/-- CreateDynamicFunction's parse (steps 5-20): the parameters and the body must each parse on
their own (as FormalParameters and FunctionBody), then the assembled source text is parsed as
the function expression. Returns the function (its span is the whole assembled text) and that
text (what `toString` returns).
spec: https://tc39.es/ecma262/#sec-createdynamicfunction -/
def parseDynamicFunction (params body : String) (kind : DynFnKind) : Except SyntaxError (Func × String) := do
  let (isAsync, isGen) := match kind with
    | .normal => (false, false) | .generator => (false, true)
    | .async => (true, false) | .asyncGenerator => (true, true)
  let pre := match kind with
    | .normal => "function" | .generator => "function*"
    | .async => "async function" | .asyncGenerator => "async function*"
  let fn : Fn := { awaitExpr := isAsync, awaitReserved := isAsync, yieldExpr := isGen,
                   newTarget := true, returnOk := true }
  -- 9-12. the parameters on their own (as `(P\n)`, the form they take in the source text)
  let s ← initState ("(" ++ params ++ "\n)") false false fn (hashbang := false)
  runP (do
    enterScope (sVar ||| sFunction)
    let _ ← parseParams topRec
    if (← tokKind) != .eof then unexpected
    let st ← get
    if st.yieldPos != 0 then fail "yield expression in formal parameters" (st.yieldPos - 1)
    if st.awaitPos != 0 then fail "await expression in formal parameters" (st.awaitPos - 1)) s
  -- the body on its own
  let s ← initState ("\n" ++ body ++ "\n") false false fn (hashbang := false)
  runP (do
    enterScope (sVar ||| sFunction)
    let _ ← parseBodyList topRec .item .eof true
    if (← tokKind) != .eof then unexpected) s
  -- 13-20. the assembled source text
  let src := pre ++ " anonymous(" ++ params ++ "\n) {\n" ++ body ++ "\n}"
  let s ← initState src false false {} (hashbang := false)
  let f ← runP (do
    enterScope (sVar ||| sTop)
    let start := (← tok).start
    if isAsync then next
    let f ← parseFunctionExpr topRec start isAsync
    if (← tokKind) != .eof then unexpected
    return f) s
  return (f, src)

end ES
