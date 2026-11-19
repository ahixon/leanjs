import ES.Str
import ES.Number

/-!
# ECMAScript syntax trees

The parser's output (`ES/Parser.lean`) and the interpreter's input (`ES/Interp.lean`). The tree
follows the spec's grammar closely enough that the runtime semantics' syntax-directed operations
(Evaluation, BindingInitialization, …) are one case per node; cover grammars are already
refined (arrow parameters and assignment patterns are `Pattern`s). Every node the parser accepts
has passed its early errors (spec: https://tc39.es/ecma262/#sec-static-semantic-rules).
-/

namespace ES

open ES (F64)

/-- A source range: UTF-8 byte offsets into the source text. -/
structure Span where
  start : Nat := 0
  stop : Nat := 0
  deriving Inhabited, Repr, BEq

inductive Lit where
  | null
  | bool (b : Bool)
  | num (n : F64)
  | str (s : JSStr)
  | bigint (i : Int)
  deriving Inhabited

inductive UnOp where
  | neg | pos | not | bitNot | typeof | void | delete
  deriving Inhabited, BEq, Repr

inductive BinOp where
  | add | sub | mul | div | mod | exp
  | shl | sar | shr | bitAnd | bitOr | bitXor
  | eq | ne | seq | sne | lt | gt | le | ge
  | instanceof | in
  deriving Inhabited, BEq, Repr

inductive LogOp where
  | and | or | nullish
  deriving Inhabited, BEq, Repr

/-- `=` is `none`; compound assignment carries its operator. -/
inductive AssignOp where
  | assign
  | op (o : BinOp)
  | logical (o : LogOp)
  deriving Inhabited, BEq

inductive VarKind where
  | var | let | const | using | awaitUsing
  deriving Inhabited, BEq, Repr

/-- Kind of a function-like node: what its [[ThisMode]], [[ConstructorKind]] and allowed
`super` uses are. -/
inductive FuncKind where
  | normal        -- function declarations and expressions
  | arrow
  | method        -- object literal / class methods
  | getter
  | setter
  | classConstructor (derived : Bool)
  | classField    -- the initializer of a class field, as a method-like function
  | classStaticBlock
  deriving Inhabited, BEq, Repr

/-- Static facts about a function computed by the parser (the static semantics the runtime asks
for at each call). -/
structure FuncInfo where
  /-- The function's code is strict (directive or enclosing strict code, class, module). -/
  strict : Bool := false
  /-- The source text matched by the function (for `Function.prototype.toString`). -/
  span : Span := {}
  /-- IsSimpleParameterList -/
  simpleParams : Bool := true
  /-- ExpectedArgumentCount (the `length` property) -/
  expectedArgs : Nat := 0
  /-- Whether the body or parameters contain a direct `eval` call (somewhere a `var` could be
  introduced into the function's scope) — the runtime must then keep a full environment. -/
  hasDirectEval : Bool := false
  /-- Whether `arguments` is referenced (in the parameters or the body, not in nested
  non-arrow functions) or a direct eval may reference it. -/
  usesArguments : Bool := true
  /-- Whether `this`/`super`/`new.target` are referenced from within nested arrow functions or
  direct eval (they then need the function environment). -/
  usesThis : Bool := true
  /-- ContainsExpression of the parameters (parameter expressions get a separate environment). -/
  paramsHaveExpressions : Bool := false
  /-- An id unique within the parsed source (for caches keyed by function code). -/
  id : Nat := 0
  deriving Inhabited

mutual

inductive Expr where
  | this
  | ident (name : JSStr)
  | lit (l : Lit)
  /-- Template literal: cooked strings (`none`: invalid escape, only allowed when tagged) and
  raw strings, and the substitutions between them (`quasis.size = exprs.size + 1`). -/
  | template (cooked : Array (Option JSStr)) (raw : Array JSStr) (exprs : Array Expr)
  /-- `tag`template``; `site` numbers the template within its script/module (the template
  registry's key, with the script). -/
  | tagged (tag : Expr) (cooked : Array (Option JSStr)) (raw : Array JSStr) (exprs : Array Expr) (site : Nat)
  | regex (pattern flags : JSStr)
  | array (elems : Array ArrElem)
  | object (props : Array PropDef)
  | func (f : Func)
  | cls (c : Class)
  | unary (op : UnOp) (e : Expr)
  | update (inc : Bool) (pre : Bool) (target : Expr)
  | binary (op : BinOp) (l r : Expr)
  | logical (op : LogOp) (l r : Expr)
  /-- `#x in obj` -/
  | privIn (name : JSStr) (r : Expr)
  | assign (op : AssignOp) (target : Pattern) (value : Expr)
  | cond (test cons alt : Expr)
  /-- Calls: `optional` is `callee?.(args)`; `directEval`: the callee is the identifier `eval`
  (a direct eval if it is %eval% at runtime, spec: PerformEval). -/
  | call (callee : Expr) (args : Array Arg) (optional : Bool) (directEval : Bool := false)
  | new (callee : Expr) (args : Array Arg)
  /-- Member access; `optional` is `obj?.prop`. -/
  | member (obj : Expr) (key : MemberKey) (optional : Bool)
  /-- The boundary of an optional chain (OptionalExpression): a `?.` short-circuit inside
  makes the whole chain `undefined`. -/
  | chain (e : Expr)
  | superMember (key : MemberKey)
  | superCall (args : Array Arg)
  | newTarget
  | importMeta
  | importCall (spec : Expr) (options : Option Expr)
  | seq (es : Array Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (e : Expr)
  /-- A parenthesized expression, kept only where it matters at runtime: it is not a
  reference to a function name for NamedEvaluation (`(function(){})` still is — see
  IsAnonymousFunctionDefinition, which looks through parentheses), so it is dropped there; it
  is kept so `(a?.b)()` and `delete (x)` behave. -/
  | paren (e : Expr)

inductive MemberKey where
  | name (n : JSStr)
  | computed (e : Expr)
  | priv (n : JSStr)

inductive Arg where
  | expr (e : Expr)
  | spread (e : Expr)

inductive ArrElem where
  | hole
  | expr (e : Expr)
  | spread (e : Expr)

/-- A property name in object literals, classes, and object patterns. -/
inductive PropName where
  | ident (n : JSStr)       -- also keywords; `get`, `set`, …
  | str (s : JSStr)
  | num (n : F64)
  | bigint (i : Int)
  | computed (e : Expr)
  | priv (n : JSStr)        -- classes only

inductive PropDef where
  /-- `key: value`; `protoSetter`: the key is the non-computed `__proto__` (sets the prototype). -/
  | init (key : PropName) (value : Expr) (protoSetter : Bool)
  /-- `{ x }` -/
  | shorthand (name : JSStr)
  | method (key : PropName) (f : Func)   -- `f.kind` is method/getter/setter
  | spread (e : Expr)

/-- Binding and assignment patterns. In assignment patterns a target may be any simple
assignment target (`expr`, a member expression); in binding patterns targets are `ident`s. -/
inductive Pattern where
  | ident (name : JSStr)
  | expr (e : Expr)
  | obj (props : Array PatProp) (rest : Option Pattern)
  | arr (elems : Array (Option PatElem)) (rest : Option Pattern)

/-- `key: target = init` in an object pattern (shorthand `{x = 1}` is key `x`, target `x`). -/
inductive PatProp where
  | mk (key : PropName) (target : Pattern) (init : Option Expr)

inductive PatElem where
  | mk (target : Pattern) (init : Option Expr)

inductive Stmt where
  | expr (e : Expr)
  | varDecl (kind : VarKind) (decls : Array VarDeclarator)
  | funDecl (f : Func)
  | classDecl (c : Class)
  | block (body : Array Stmt)
  | empty
  | ret (e : Option Expr)
  | ifS (test : Expr) (cons : Stmt) (alt : Option Stmt)
  | whileS (test : Expr) (body : Stmt)
  | doWhile (body : Stmt) (test : Expr)
  | forS (init : Option ForInit) (test : Option Expr) (update : Option Expr) (body : Stmt)
  | forIn (lhs : ForLhs) (rhs : Expr) (body : Stmt)
  | forOf (lhs : ForLhs) (rhs : Expr) (body : Stmt) (isAwait : Bool)
  | brk (label : Option JSStr)
  | cont (label : Option JSStr)
  | throw (e : Expr)
  | tryS (block : Array Stmt) (handler : Option CatchClause) (finalizer : Option (Array Stmt))
  | switch (disc : Expr) (cases : Array SwitchCase)
  | labeled (label : JSStr) (body : Stmt)
  | with (obj : Expr) (body : Stmt)
  | debugger
  /-- Module items (only in modules). -/
  | importDecl (d : ImportDecl)
  | exportDecl (d : ExportDecl)

inductive VarDeclarator where
  | mk (target : Pattern) (init : Option Expr)

inductive ForInit where
  | decl (kind : VarKind) (decls : Array VarDeclarator)
  | expr (e : Expr)

/-- The left side of `for-in`/`for-of`: a declaration of one binding (with, for Annex B's
`for (var x = init in o)`, an initializer), or an assignment target. -/
inductive ForLhs where
  | decl (kind : VarKind) (target : Pattern) (init : Option Expr)
  | pattern (target : Pattern)

inductive CatchClause where
  | mk (param : Option Pattern) (body : Array Stmt)

/-- `case test:` (or `default:` when `test` is `none`) and its statements. -/
inductive SwitchCase where
  | mk (test : Option Expr) (body : Array Stmt)

inductive Param where
  | mk (target : Pattern) (init : Option Expr) (rest : Bool)

/-- A function-like node: declarations, expressions, arrows, methods, accessors, class
constructors. -/
inductive Func where
  | mk (name : Option JSStr) (kind : FuncKind) (isAsync isGenerator : Bool)
       (params : Array Param) (body : FuncBody) (info : FuncInfo)

inductive FuncBody where
  | stmts (body : Array Stmt)
  /-- A concise arrow body `x => expr`. -/
  | expr (e : Expr)

inductive Class where
  | mk (name : Option JSStr) (superClass : Option Expr) (elems : Array ClassElem) (span : Span)

inductive ClassElem where
  /-- Methods, getters, setters (`f.kind`); the constructor is a `method` named "constructor"
  with `f.kind = classConstructor _`. -/
  | method (isStatic : Bool) (key : PropName) (f : Func)
  | field (isStatic : Bool) (key : PropName) (init : Option Expr) (span : Span)
  | staticBlock (body : Array Stmt) (span : Span)
  /-- `accessor x = init` (decorators proposal's auto-accessors): not part of ES2025; kept
  for future use. -/
  | accessor (isStatic : Bool) (key : PropName) (init : Option Expr)

inductive ImportDecl where
  /-- `import d, * as ns from "m"` / `import d, { a as b } from "m"` / `import "m"`;
  `attrs` are the `with { type: "json" }` attributes. -/
  | mk (defaultName : Option JSStr) (nsName : Option JSStr)
       (named : Array (JSStr × JSStr))     -- (imported name, local name)
       (module : JSStr) (attrs : Array (JSStr × JSStr)) (phase : Option JSStr)

inductive ExportDecl where
  /-- `export { a as b }` (local, exported) — strings allowed as names. -/
  | named (specs : Array (JSStr × JSStr))
  /-- `export { a as b } from "m"` (imported, exported) -/
  | namedFrom (specs : Array (JSStr × JSStr)) (module : JSStr) (attrs : Array (JSStr × JSStr))
  /-- `export * from "m"` / `export * as ns from "m"` -/
  | all (asName : Option JSStr) (module : JSStr) (attrs : Array (JSStr × JSStr))
  | decl (s : Stmt)                         -- `export var/let/const/function/class …`
  | defaultFunc (f : Func)                  -- `export default function …` (name may be none)
  | defaultClass (c : Class)
  | defaultExpr (e : Expr)

end

instance : Inhabited Func := ⟨.mk none .normal false false #[] (.stmts #[]) {}⟩

/-- A parsed Script or Module. -/
structure Program where
  body : Array Stmt
  isModule : Bool
  /-- The script's code is strict (a `"use strict"` directive; modules always). -/
  strict : Bool
  /-- The source text (the spans index it). -/
  source : String
  deriving Inhabited

/-- An early (or syntax) error with its position. -/
structure SyntaxError where
  msg : String
  pos : Nat := 0
  deriving Inhabited, Repr

instance : Inhabited Expr := ⟨.this⟩
instance : Inhabited Stmt := ⟨.empty⟩
instance : Inhabited Pattern := ⟨.ident JSStr.empty⟩
instance : Inhabited SwitchCase := ⟨.mk none #[]⟩
instance : Inhabited Param := ⟨.mk default none false⟩
instance : Inhabited PropName := ⟨.ident JSStr.empty⟩
instance : Inhabited ClassElem := ⟨.staticBlock #[] {}⟩
instance : Inhabited VarDeclarator := ⟨.mk default none⟩

namespace Func
def name : Func → Option JSStr | .mk n .. => n
def kind : Func → FuncKind | .mk _ k .. => k
def isAsync : Func → Bool | .mk _ _ a .. => a
def isGenerator : Func → Bool | .mk _ _ _ g .. => g
def params : Func → Array Param | .mk _ _ _ _ p .. => p
def body : Func → FuncBody | .mk _ _ _ _ _ b _ => b
def info : Func → FuncInfo | .mk _ _ _ _ _ _ i => i
def strict (f : Func) : Bool := f.info.strict
end Func

namespace Class
def name : Class → Option JSStr | .mk n .. => n
def superClass : Class → Option Expr | .mk _ s .. => s
def elems : Class → Array ClassElem | .mk _ _ e _ => e
def span : Class → Span | .mk _ _ _ s => s
end Class

end ES
