import ES.Promise
import ES.Decls
import ES.Regex
import ES.Parser

/-!
# Function objects, environments for code, and other runtime helpers of the interpreter

spec: https://tc39.es/ecma262/#sec-ecmascript-function-objects (10.2)
-/

namespace ES

open ES (F64)
open Std (HashSet)

/-- The running execution context's parts the evaluation of code needs.
spec: https://tc39.es/ecma262/#table-additional-state-components-for-ecmascript-code-execution-contexts -/
structure Ctx where
  lex : EnvId
  var : EnvId
  priv : Array (JSStr × Nat) := #[]
  strict : Bool
  /-- the active function object (none: script/module/eval code at top level) -/
  fn : Option ObjId := none
  realm : Nat
  script : Nat
  /-- Annex B.3.2 function declarations (by id) whose evaluation also sets the var binding. -/
  annexB : HashSet Nat := {}
  /-- The current label set (for the iteration or switch statement being evaluated). -/
  labels : Array JSStr := #[]
  /-- Inside an async function/generator body (await allowed). -/
  isAsync : Bool := false
  /-- The generator object when evaluating a generator body. -/
  gen : Option ObjId := none
  /-- Evaluating a generator body (with `isAsync`: an async generator). -/
  isGen : Bool := false
  /-- The [[DisposeCapability]] of the innermost scope with `using` declarations. -/
  disposeCap : Option ObjId := none
  deriving Inhabited

/-- A statement's completion (normal with an optional value — `none` is empty —, break,
continue, return); throw completions are the monad's.
spec: https://tc39.es/ecma262/#sec-completion-record-specification-type -/
inductive Compl where
  | normal (v : Option Value)
  | brk (label : Option JSStr) (v : Option Value)
  | cont (label : Option JSStr) (v : Option Value)
  | ret (v : Value)
  deriving Inhabited

namespace Compl
/-- UpdateEmpty(C, V) spec: https://tc39.es/ecma262/#sec-updateempty -/
def updateEmpty (c : Compl) (v : Option Value) : Compl :=
  match c with
  | .normal none => .normal v
  | .brk l none => .brk l v
  | .cont l none => .cont l v
  | c => c
def value? : Compl → Option Value
  | .normal v | .brk _ v | .cont _ v => v
  | .ret v => some v
end Compl

/-- LoopContinues spec: https://tc39.es/ecma262/#sec-loopcontinues -/
def loopContinues (c : Compl) (labels : Array JSStr) : Bool :=
  match c with
  | .normal _ => true
  | .cont none _ => true
  | .cont (some l) _ => labels.contains l
  | _ => false

def sentinelOptional : Value := .sym 16

/-- NewFunctionEnvironment spec: https://tc39.es/ecma262/#sec-newfunctionenvironment -/
def newFunctionEnv (f : ObjId) (d : FuncData) (newTarget : Value) : M EnvId :=
  allocEnv (.func {} (some d.env) (if d.thisMode == .lexical then .lexical else .uninitialized)
    .undefined f newTarget)

/-- The prototype intrinsic of a function kind. -/
def functionProtoName (f : Func) : String :=
  match f.isAsync, f.isGenerator with
  | false, false => "%Function.prototype%"
  | false, true => "%GeneratorFunction.prototype%"
  | true, false => "%AsyncFunction.prototype%"
  | true, true => "%AsyncGeneratorFunction.prototype%"

/-- OrdinaryFunctionCreate spec: https://tc39.es/ecma262/#sec-ordinaryfunctioncreate -/
def ordinaryFunctionCreate (proto : ObjId) (code : Func) (env : EnvId) (priv : Array (JSStr × Nat))
    (ctx : Ctx) (lexicalThis : Bool) : M ObjId := do
  let (source, realm) ← readS fun s => ((s.scripts[ctx.script]?.map (·.prog.source)).getD "", s.realm)
  let strict := code.strict
  let thisMode := if lexicalThis then .lexical else if strict then .strict else .global
  let d : FuncData := { code, env, privEnv := priv, thisMode, realm, script := ctx.script, source }
  let f ← alloc { proto := .obj proto, kind := .func d }
  -- 21. SetFunctionLength
  setOwn f (.str kLength) (.data (numV code.info.expectedArgs) false false true)
  pure f

/-- MakeConstructor spec: https://tc39.es/ecma262/#sec-makeconstructor -/
def makeConstructor (f : ObjId) (writablePrototype : Bool := true) (proto : Option ObjId := none) : M Unit := do
  let proto ← match proto with
    | some p => pure p
    | none => do
      let p ← newObject
      setOwn p (.str kConstructor) (.data (.obj f) writablePrototype false true)
      pure p
  setOwn f (.str kPrototype) (.data (.obj proto) writablePrototype false false)

/-- MakeMethod spec: https://tc39.es/ecma262/#sec-makemethod -/
def makeMethod (f : ObjId) (home : ObjId) : M Unit := modifyObj f fun o => o.withKind fun k =>
  match k with
  | .func d => .func { d with homeObject := some home }
  | k => k

/-- Gives a generator function its `prototype` object. -/
def makeGeneratorPrototype (f : ObjId) (isAsync : Bool) : M Unit := do
  let pp ← intrinsic (if isAsync then "%AsyncGeneratorFunction.prototype.prototype%" else "%GeneratorFunction.prototype.prototype%")
  let p ← ordinaryObjectCreate (.obj pp)
  setOwn f (.str kPrototype) (.data (.obj p) true false false)

/-- Sloppy functions' own `caller` and `arguments` (null), as browsers have them.
DEVIATION (docs/es.md D2) -/
def addLegacyFunctionProps (fo : ObjId) (f : Func) : M Unit := do
  if !f.strict && f.kind == .normal && !f.isAsync && !f.isGenerator then
    setOwn fo (.str "arguments") (.data .null false false false)
    setOwn fo (.str "caller") (.data .null false false false)

/-- Creates the function object of a function declaration or expression (InstantiateOrdinaryFunctionObject
and its generator/async variants), naming it `name`.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-instantiatefunctionobject -/
def instantiateFunction (f : Func) (env : EnvId) (priv : Array (JSStr × Nat)) (ctx : Ctx)
    (name : PropKey) : M ObjId := do
  let proto ← intrinsic (functionProtoName f)
  let fo ← ordinaryFunctionCreate proto f env priv ctx (f.kind == .arrow)
  setFunctionName fo name
  if f.isGenerator then makeGeneratorPrototype fo f.isAsync
  else if !f.isAsync && f.kind == .normal then makeConstructor fo
  addLegacyFunctionProps fo f
  pure fo

/-- The name of an anonymous function's binding: its declared name or "default". -/
def funcNameKey (f : Func) : PropKey := .str (f.name.getD "default")

/-- BlockDeclarationInstantiation spec: https://tc39.es/ecma262/#sec-blockdeclarationinstantiation -/
def blockDeclarationInstantiation (decls : Array LexScoped) (env : EnvId) (ctx : Ctx) : M Unit := do
  M.forArr decls fun d => do
    -- a-b.
    M.forArr d.names fun dn => do
      if d.isConstant then createImmutableBinding env dn true
      else
        -- (Annex B.3.2.6: a repeated function declaration in a sloppy block reuses the binding)
        if !(← hasBinding env dn) then createMutableBinding env dn false
    -- c.
    match d with
    | .func f =>
      let fn := f.name.getD "default"
      let fo ← instantiateFunction f env ctx.priv ctx (.str fn)
      -- (Annex B.3.2.6: a repeated declaration's binding may already be initialized)
      let init ← readEnv env fun e => match e.bindings? with
        | some b => ((b.get? fn).bind (·.value)).isSome
        | none => false
      if init then setMutableBinding env fn (.obj fo) false
      else initializeBinding env fn (.obj fo)
    | _ => pure ()

/-- CreateUnmappedArgumentsObject spec: https://tc39.es/ecma262/#sec-createunmappedargumentsobject -/
def createUnmappedArguments (args : Array Value) : M ObjId := do
  let op ← readS (·.curRealm.objectProto)
  let o ← alloc { proto := .obj op, kind := .arguments none }
  setOwn o (.str kLength) (.data (numV args.size) true false true)
  M.forArr (Array.range args.size) fun i => setOwn o (PropKey.ofNat i) (.data args[i]! true true true)
  let values ← intrinsic "%Array.prototype.values%"
  setOwn o (.sym WK.iterator) (.data (.obj values) true false true)
  let thrower ← intrinsic "%ThrowTypeError%"
  setOwn o (.str "callee") (.accessor (.obj thrower) (.obj thrower) false false)
  pure o

/-- CreateMappedArgumentsObject spec: https://tc39.es/ecma262/#sec-createmappedargumentsobject -/
def createMappedArguments (func : ObjId) (paramNames : Array JSStr) (args : Array Value) (env : EnvId) : M ObjId := do
  let op ← readS (·.curRealm.objectProto)
  -- (17-21: later names win for duplicated parameters)
  let names : Array (Option JSStr) := (Array.range args.size).map fun i =>
    if i < paramNames.size then
      let nm := paramNames[i]!
      -- mapped only if no later parameter has the same name
      if (paramNames.extract (i + 1) paramNames.size).contains nm then none else some nm
    else none
  let o ← alloc { proto := .obj op, kind := .arguments (some (env, names)) }
  M.forArr (Array.range args.size) fun i => setOwn o (PropKey.ofNat i) (.data args[i]! true true true)
  setOwn o (.str kLength) (.data (numV args.size) true false true)
  let values ← intrinsic "%Array.prototype.values%"
  setOwn o (.sym WK.iterator) (.data (.obj values) true false true)
  setOwn o (.str "callee") (.data (.obj func) true false true)
  pure o

/-- PrivateElementFind + PrivateFieldAdd / PrivateMethodOrAccessorAdd
spec: https://tc39.es/ecma262/#sec-privatefieldadd -/
def privateElementAdd (o : Value) (id : Nat) (e : PrivElem) : M Unit := do
  let .obj oid := o | throwType "Cannot add a private member to a non-object"
  let exists_ ← readObj oid fun ob => ob.privates.any (·.1 == id)
  if exists_ then throwType "Cannot initialize a private member twice on the same object"
  modifyObj oid fun ob => { ob with privates := ob.privates.push (id, e) }

/-- DefineField spec: https://tc39.es/ecma262/#sec-definefield -/
def defineField (receiver : Value) (fd : FieldDef) : M Unit := do
  let v ← match fd.init with
    | some f => call (.obj f) receiver #[]
    | none => pure .undefined
  match fd.name with
  | .priv id => privateElementAdd receiver id (.field v)
  | .key k =>
    let .obj r := receiver | throwType "Cannot define a field on a non-object"
    createDataPropertyOrThrow r k v

/-- InitializeInstanceElements spec: https://tc39.es/ecma262/#sec-initializeinstanceelements -/
def initializeInstanceElements (o : Value) (ctor : ObjId) : M Unit := do
  let .func d ← objKind ctor | pure ()
  M.forArr d.privMethods fun (id, e) => privateElementAdd o id e
  M.forArr d.fields fun fd => defineField o fd

/-- GetTemplateObject spec: https://tc39.es/ecma262/#sec-gettemplateobject -/
def getTemplateObject (script site : Nat) (cooked : Array (Option JSStr)) (raw : Array JSStr) : M Value := do
  let t? ← readS (·.curRealm.templates.get? (script, site))
  if let some t := t? then return .obj t
  let template ← createArrayFromList (cooked.map fun c => match c with | some s => .str s | none => .undefined)
  let rawObj ← createArrayFromList (raw.map .str)
  let .obj t := template | M.halt "internal"
  let .obj r := rawObj | M.halt "internal"
  let _ ← setIntegrityLevel r true
  setOwn t (.str "raw") (.data rawObj false false false)
  let _ ← setIntegrityLevel t true
  modify fun s => { s with realms := s.realms.modify s.realm fun rl =>
    { rl with templates := rl.templates.insert (script, site) t } }
  pure template

/-- RegExpCreate for a literal (RegExpAlloc + RegExpInitialize with %RegExp%).
spec: https://tc39.es/ecma262/#sec-regexpcreate -/
def regexpCreateLiteral (pattern flags : JSStr) : M Value := do
  let proto ← intrinsic "%RegExp.prototype%"
  match Regex.compile pattern flags with
  | .error msg => throwError .syntaxError s!"Invalid regular expression: /{pattern}/{flags}: {msg}"
  | .ok prog =>
    let o ← alloc { proto := .obj proto, kind := .regexp pattern flags prog }
    setOwn o (.str "lastIndex") (.data (numV 0) true false false)
    pure (.obj o)

/-! ## Explicit resource management -/

/-- Whether a statement list declares `using`/`await using` bindings directly (and whether any of
them is `await using`). -/
def usingKinds (decls : Array LexScoped) : Bool × Bool :=
  decls.foldl (fun (u, a) d => match d with
    | .binding .using _ => (true, a)
    | .binding .awaitUsing _ => (true, true)
    | _ => (u, a)) (false, false)

/-- The async wrapper GetDisposeMethod makes of a sync `[Symbol.dispose]`. -/
def asyncDisposeFromSync : BuiltinFn := fun self thisV _ _ => do
  let s ← builtinSlots self
  let cap ← newIntrinsicPromise
  match ← M.attempt (call s[0]! thisV #[]) with
  | .error e => let _ ← call cap.reject .undefined #[e]
  | .ok _ => let _ ← call cap.resolve .undefined #[.undefined]
  pure cap.promise

/-- AddDisposableResource (with CreateDisposableResource and GetDisposeMethod).
spec: https://tc39.es/proposal-explicit-resource-management/#sec-adddisposableresource -/
def addDisposableResource (cap : ObjId) (v : Value) (async : Bool) : M Unit := do
  let method ← if v.isNullish then
      if !async then return else pure Value.undefined
    else do
      if !v.isObject then throwType "using declarations need an object, null or undefined"
      let m ← if async then do
          match ← getMethodOf v (.sym WK.asyncDispose) with
          | some m => pure (some m)
          | none => match ← getMethodOf v (.sym WK.dispose) with
            | some sm => pure (some (Value.obj (← makeBuiltinFn "AsyncDisposeFromSync" 0 JSStr.empty #[sm])))
            | none => pure none
        else getMethodOf v (.sym WK.dispose)
      match m with
      | some m => pure m
      | none => throwType "The value of a using declaration has no [Symbol.dispose] method"
  modifyObj cap fun o => o.withKind fun k => match k with
    | .internal t sl => .internal t (sl ++ #[v, method, .bool async])
    | k => k

/-- Creates a SuppressedError. -/
def makeSuppressedError (error suppressed : Value) : M Value := do
  let proto ← intrinsic "%SuppressedError.prototype%"
  let o ← alloc { proto := .obj proto, kind := .error }
  setOwn o (.str "error") (.data error true false true)
  setOwn o (.str "suppressed") (.data suppressed true false true)
  pure (.obj o)

/-- DisposeResources: disposes in reverse order; errors chain as SuppressedErrors.
spec: https://tc39.es/proposal-explicit-resource-management/#sec-disposeresources -/
def disposeResources (cap : ObjId) (completion : Except Value Compl) : M Compl := do
  let sl ← readObj cap fun o => match o.kind with | .internal _ s => s | _ => #[]
  let n := sl.size / 3
  let isThrow (c : Except Value Compl) := match c with
    | .error e => !(match e with | .sym i => i == WK.genReturn | _ => false)
    | .ok _ => false
  let (completion, needsAwait, hasAwaited) ← M.foldArr (Array.range n).reverse (completion, false, false)
    fun (completion, needsAwait, hasAwaited) i => do
      let v := sl[3 * i]!
      let method := sl[3 * i + 1]!
      let async := toBoolean sl[3 * i + 2]!
      let (needsAwait, hasAwaited) ← if !async && needsAwait && !hasAwaited then do
          let _ ← await .undefined; pure (false, true)
        else pure (needsAwait, hasAwaited)
      if method.isUndefined then return (completion, true, hasAwaited)
      let r ← M.attempt do
        let r ← call method v #[]
        if async then let _ ← await r
      let hasAwaited := hasAwaited || async
      match r with
      | .ok _ => pure (completion, needsAwait, hasAwaited)
      | .error e =>
        if isThrow completion then
          let prev := match completion with | .error p => p | .ok _ => .undefined
          pure (.error (← makeSuppressedError e prev), needsAwait, hasAwaited)
        else pure (.error e, needsAwait, hasAwaited)
  if needsAwait && !hasAwaited then let _ ← await .undefined
  modifyObj cap fun o => { o with kind := .internal "DisposeCapability" #[] }
  match completion with
  | .ok c => pure c
  | .error e => M.throwV e

/-- Runs a scope's body with a new DisposeCapability when it declares `using` bindings. -/
def withDisposeScope (needed : Bool) (ctx : Ctx) (body : Ctx → M Compl) : M Compl := do
  if !needed then return ← body ctx
  let cap ← alloc { kind := .internal "DisposeCapability" #[] }
  let r ← M.attempt (body { ctx with disposeCap := some cap })
  let realm := ctx.realm
  let c ← disposeResources cap r
  modify fun s => { s with realm }
  pure c

/-- The FuncData of a function object. -/
def funcData? (f : ObjId) : M (Option FuncData) := do
  match ← objKind f with
  | .func d => pure (some d)
  | _ => pure none

/-- IsAnonymousFunctionDefinition spec: https://tc39.es/ecma262/#sec-isanonymousfunctiondefinition -/
def isAnonymousFn : Expr → Bool
  | .func f => f.name.isNone
  | .cls c => c.name.isNone
  | .paren e => match e with
    | .func f => f.name.isNone
    | .cls c => c.name.isNone
    | _ => false
  | _ => false

/-- The private name id for a description in scope. -/
def resolvePrivate (priv : Array (JSStr × Nat)) (name : JSStr) : M Nat :=
  match priv.reverse.find? (·.1 == name) with
  | some (_, id) => pure id
  | none => M.halt s!"internal: private name #{name} not in scope"

end ES
