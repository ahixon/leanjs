import ES.AsyncGen

/-!
# Evaluation: the runtime semantics of ECMAScript language constructs

spec: https://tc39.es/ecma262/#sec-ecmascript-language-expressions (13), statements (14),
functions and classes (15), and [[Call]]/[[Construct]] of ECMAScript function objects (10.2).

The evaluation functions are one mutual block, structural on a depth parameter `n` (each nested
evaluation takes one): calls of other functions are requests to the driver (`ES/Driver.lean`), so
`n` only bounds the syntactic nesting of one function body, which the parser's nesting limit keeps
far below `evalDepth`.
-/

namespace ES

open ES (F64)
open Std (HashSet)

/-- The depth bound of one function body's evaluation (see the module docstring). -/
def evalDepth : Nat := 1000000

def tooDeep {α} : M α := throwRange "Maximum call stack size exceeded"

def isSentinel (v : Value) (id : Nat) : Bool := match v with | .sym i => i == id | _ => false

/-- The this value of a reference for a call (EvaluateCall step 1).
spec: https://tc39.es/ecma262/#sec-evaluatecall -/
def refThisValue (r : Ref) : M Value := do
  match r with
  | .prop base _ _ thisV => pure (thisV.getD base)
  | .priv base _ => pure base
  | .env (some e) _ _ => readEnv e fun ev => match ev with
    | .object o true _ => .obj o
    | _ => .undefined
  | _ => pure .undefined

/-- A short description of a callee for error messages. -/
def calleeName : Expr → String
  | .ident x => x.toString
  | .member _ (.name k) _ => s!"….{k}"
  | .member _ (.priv k) _ => s!"….#{k}"
  | .member _ (.computed _) _ => "…[…]"
  | .superMember (.name k) => s!"super.{k}"
  | .paren e => calleeName e
  | .chain e => calleeName e
  | _ => "expression"

/-- The literal's value. -/
def litValue : Lit → Value
  | .null => .null
  | .bool b => .bool b
  | .num x => .num x
  | .str s => .str s
  | .bigint i => .bigint i

/-- The property key of a non-computed property name. -/
def staticPropKey : PropName → Option PropKey
  | .ident n | .str n => some (.str n)
  | .num x => some (.str (numberToJSStr x))
  | .bigint i => some (.str (JSStr.ofString (toString i)))
  | _ => none

/-- GetNewTarget spec: https://tc39.es/ecma262/#sec-getnewtarget -/
def getNewTarget (ctx : Ctx) : M Value := do
  let e ← getThisEnvironment ctx.lex
  readEnv e fun ev => match ev with
    | .func _ _ _ _ _ nt => nt
    | _ => .undefined

/-- GetSuperConstructor spec: https://tc39.es/ecma262/#sec-getsuperconstructor -/
def getSuperConstructor (ctx : Ctx) : M Value := do
  let e ← getThisEnvironment ctx.lex
  let f ← readEnv e fun ev => match ev with
    | .func _ _ _ _ f _ => some f
    | _ => none
  match f with
  | some f => Obj'.getPrototypeOf f
  | none => M.halt "internal: super() outside a function"

/-- The [[HomeObject]] of the function whose this environment `ctx` is in. -/
def homeObject (ctx : Ctx) : M (Option ObjId) := do
  let e ← getThisEnvironment ctx.lex
  let f ← readEnv e fun ev => match ev with
    | .func _ _ _ _ f _ => some f
    | _ => none
  match f with
  | some f => do pure ((← funcData? f).bind (·.homeObject))
  | none => pure none

/-- The `realm`/`script` of a context, restored after a suspension. -/
def restoreCtx (ctx : Ctx) : M Unit := modify fun s => { s with realm := ctx.realm, script := ctx.script }

/-- Instantiates a function expression (InstantiateOrdinaryFunctionExpression and its generator,
async and arrow variants); `name` is NamedEvaluation's name.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-instantiateordinaryfunctionexpression -/
def instantiateFunctionExpr (f : Func) (ctx : Ctx) (name : Option PropKey) : M Value := do
  let proto ← intrinsic (functionProtoName f)
  match f.name, f.kind with
  | some fname, .normal =>
    -- (named function expressions bind their name in an environment of their own)
    let funcEnv ← newDeclEnv (some ctx.lex)
    createImmutableBinding funcEnv fname false
    let fo ← ordinaryFunctionCreate proto f funcEnv ctx.priv ctx false
    setFunctionName fo (.str fname)
    if f.isGenerator then makeGeneratorPrototype fo f.isAsync
    else if !f.isAsync then makeConstructor fo
    addLegacyFunctionProps fo f
    initializeBinding funcEnv fname (.obj fo)
    pure (.obj fo)
  | _, _ =>
    let fo ← ordinaryFunctionCreate proto f ctx.lex ctx.priv ctx (f.kind == .arrow)
    setFunctionName fo (name.getD (.str JSStr.empty))
    if f.isGenerator then makeGeneratorPrototype fo f.isAsync
    else if !f.isAsync && f.kind == .normal then makeConstructor fo
    addLegacyFunctionProps fo f
    pure (.obj fo)

/-- How a pattern's targets are bound: assignment (DestructuringAssignmentEvaluation) or
BindingInitialization with an environment (`none`: PutValue to the resolved binding). -/
inductive BindMode where
  | assign
  | init (env : Option EnvId)

/-- Binds an identifier target to a value (the last steps of SingleNameBinding / AssignmentElement). -/
def putTarget (r : Ref) (v : Value) (mode : BindMode) : M Unit :=
  match mode with
  | .init (some _) => initializeRefBinding r v
  | _ => putRefValue r v

/-- HasLexicalDeclaration / HasRestrictedGlobalProperty / CanDeclareGlobalVar /
CanDeclareGlobalFunction / CreateGlobalVarBinding / CreateGlobalFunctionBinding of the global
environment `env` (with global object `g`).
spec: https://tc39.es/ecma262/#sec-global-environment-records -/
def globalDeclRecHas (env : EnvId) (n : JSStr) : M Bool := readEnv env fun e => match e with
  | .global _ b _ => b.contains n
  | _ => false

def hasRestrictedGlobalProperty (g : ObjId) (n : JSStr) : M Bool := do
  match ← Obj'.getOwnProperty g (.str n) with
  | none => pure false
  | some p => pure !p.configurable

def canDeclareGlobalVar (g : ObjId) (n : JSStr) : M Bool := do
  if ← hasOwnProperty g (.str n) then return true
  Obj'.isExtensible g

def canDeclareGlobalFunction (g : ObjId) (n : JSStr) : M Bool := do
  match ← Obj'.getOwnProperty g (.str n) with
  | none => Obj'.isExtensible g
  | some p =>
    if p.configurable then return true
    match p with
    | .data _ true true _ => pure true
    | _ => pure false

def createGlobalVarBinding (g : ObjId) (n : JSStr) (deletable : Bool) : M Unit := do
  let has ← hasOwnProperty g (.str n)
  let ext ← Obj'.isExtensible g
  if !has && ext then
    definePropertyOrThrow g (.str n) (PropDesc.data .undefined true true deletable)
    -- (ObjRec.InitializeBinding(N, undefined): a Set)
    let _ ← Obj'.set g (.str n) .undefined (.obj g)

def createGlobalFunctionBinding (g : ObjId) (n : JSStr) (v : Value) (deletable : Bool) : M Unit := do
  let existing ← Obj'.getOwnProperty g (.str n)
  let desc := match existing with
    | none => PropDesc.data v true true deletable
    | some p => if p.configurable then PropDesc.data v true true deletable else { value := some v }
  definePropertyOrThrow g (.str n) desc
  setProp g (.str n) v false

/-- The private names a class body declares (PrivateBoundIdentifiers). -/
def classPrivateNames (c : Class) : Array JSStr :=
  c.elems.foldl (fun acc e => match e with
    | .method _ (.priv nm) _ | .field _ (.priv nm) _ _ | .accessor _ (.priv nm) _ =>
      if acc.contains nm then acc else acc.push nm
    | _ => acc) #[]

/-- A private method or accessor's PrivateElement.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-methoddefinitionevaluation -/
def privateMethod (ctx : Ctx) (home : ObjId) (f : Func) (nm : JSStr) : M PrivElem := do
  let proto ← intrinsic (functionProtoName f)
  let fo ← ordinaryFunctionCreate proto f ctx.lex ctx.priv ctx false
  makeMethod fo home
  if f.isGenerator then makeGeneratorPrototype fo f.isAsync
  let desc := JSStr.ofString "#" ++ nm
  match f.kind with
  | .getter => setFunctionName fo (.str desc) (some "get"); pure (.accessor (.obj fo) .undefined)
  | .setter => setFunctionName fo (.str desc) (some "set"); pure (.accessor .undefined (.obj fo))
  | _ => setFunctionName fo (.str desc); pure (.method (.obj fo))

/-- MethodDefinitionEvaluation with DefineMethodProperty / accessor definition on `o`.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-methoddefinitionevaluation -/
def defineMethodOn (ctx : Ctx) (o : ObjId) (k : PropKey) (f : Func) (enumerable : Bool) : M Unit := do
  let proto ← intrinsic (functionProtoName f)
  let fo ← ordinaryFunctionCreate proto f ctx.lex ctx.priv ctx false
  makeMethod fo o
  match f.kind with
  | .getter =>
    setFunctionName fo k (some "get")
    definePropertyOrThrow o k { get := some (.obj fo), enumerable := some enumerable, configurable := some true }
  | .setter =>
    setFunctionName fo k (some "set")
    definePropertyOrThrow o k { set := some (.obj fo), enumerable := some enumerable, configurable := some true }
  | _ =>
    setFunctionName fo k
    if f.isGenerator then makeGeneratorPrototype fo f.isAsync
    definePropertyOrThrow o k (PropDesc.data (.obj fo) true enumerable true)

/-- GeneratorYield for a sync generator: the iterator result is made here (in the generator's
realm); a generator `return` unwinds the body as `WK.genReturn`.
spec: https://tc39.es/ecma262/#sec-generatoryield -/
def yieldRaw (ctx : Ctx) (v : Value) : M Outcome := do
  let o ← fun s => Res.req (.yield v) s (fun o s' => Res.ok o s')
  restoreCtx ctx
  pure o

/-- AsyncGeneratorYield + AsyncGeneratorUnwrapYieldResumption: the resumption (a return
completion's value already awaited). `v` is already awaited.
spec: https://tc39.es/ecma262/#sec-asyncgeneratoryield -/
def asyncGenYield (ctx : Ctx) (v : Value) : M Outcome := do
  let some g := ctx.gen | M.halt "internal: yield outside a generator"
  -- 8.
  agCompleteStep g false v false
  -- 9-11.
  let o ← match ← agFirst g with
    | some next => pure (match next.kind with | 0 => Outcome.normal next.value | 1 => .throw next.value | _ => .ret next.value)
    | none =>
      agSetState g .suspendedYield
      yieldRaw ctx .undefined
  -- AsyncGeneratorUnwrapYieldResumption
  match o with
  | .ret rv =>
    let awaited ← await rv
    restoreCtx ctx
    pure (.ret awaited)
  | o => pure o

/-- A resumption as the yield expression's completion. -/
def resumeValue (o : Outcome) : M Value := do
  match o with
  | .normal v => pure v
  | .throw e => M.throwV e
  | .ret v =>
    modify fun s => { s with genReturn := v }
    M.throwV (.sym WK.genReturn)

/-- Yield (for `yield v`). spec: https://tc39.es/ecma262/#sec-yield -/
def generatorYield (ctx : Ctx) (v : Value) : M Value := do
  if ctx.isAsync then
    let v ← await v
    restoreCtx ctx
    resumeValue (← asyncGenYield ctx v)
  else
    let res ← createIterResult v false
    resumeValue (← yieldRaw ctx res)

/-- Whether an environment is a Global Environment Record. -/
def isGlobalEnv (env : EnvId) : M Bool := readEnv env fun e => match e with | .global .. => true | _ => false

/-- EvalDeclarationInstantiation (with Annex B.3.2.3). Returns the Annex B functions' ids.
spec: https://tc39.es/ecma262/#sec-evaldeclarationinstantiation -/
def evalDeclarationInstantiation (body : Array Stmt) (varEnv lexEnv : EnvId) (ctx : Ctx) : M (HashSet Nat) := do
  let strict := ctx.strict
  let varDecls := topLevelVarScoped body
  let varNames := varDecls.foldl (fun (acc : Array JSStr) d => acc ++ d.names) #[]
  let varIsGlobal ← isGlobalEnv varEnv
  let g ← if varIsGlobal then readEnv varEnv (fun e => match e with | .global g _ _ => g | _ => 0) else pure 0
  -- 3.
  if !strict then
    if varIsGlobal then
      M.forArr varNames fun nm => do
        if ← globalDeclRecHas varEnv nm then throwError .syntaxError s!"Identifier '{nm}' has already been declared"
    let outer ← readEnv lexEnv Env.outer
    M.repeatFrom outer fun cur => do
      match cur with
      | none => return .inr ()
      | some e =>
        if e == varEnv then return .inr ()
        match ← readEnv e id with
        | .object .. => pure ()
        | _ => M.forArr varNames fun nm => do
          if ← hasBinding e nm then throwError .syntaxError s!"Identifier '{nm}' has already been declared"
        return .inl (← readEnv e Env.outer)
  -- 8.
  let (fnNames, fnsToInit) ← M.foldArr varDecls.reverse ((#[] : Array JSStr), (#[] : Array Func)) fun (names, fs) d => do
    match d with
    | .func f =>
      let nm := f.name.getD "default"
      if names.contains nm then return (names, fs)
      if varIsGlobal && !(← canDeclareGlobalFunction g nm) then throwType s!"Cannot declare global function {nm}"
      return (names.push nm, #[f] ++ fs)
    | .pat _ => return (names, fs)
  -- 11.
  let declaredVarNames ← M.foldArr varDecls #[] fun acc d => do
    match d with
    | .pat p => M.foldArr (boundNames p) acc fun acc vn => do
      if fnNames.contains vn then return acc
      if varIsGlobal && !(← canDeclareGlobalVar g vn) then throwType s!"Cannot declare global variable {vn}"
      return if acc.contains vn then acc else acc.push vn
    | .func _ => return acc
  -- 12. (Annex B.3.2.3)
  let lexNames := (topLevelLexicallyScoped body).foldl (fun (acc : Array JSStr) d => acc ++ d.names) #[]
  let candidates := if strict then #[] else annexBFunctions body lexNames
  let annexB ← M.foldArr candidates #[] fun acc f => do
    let nm := f.name.getD "default"
    let outer ← readEnv lexEnv Env.outer
    let bindingExists ← M.repeatFrom outer fun cur => do
      match cur with
      | none => return .inr false
      | some e =>
        if e == varEnv then return .inr false
        match ← readEnv e id with
        | .object .. => return .inl (← readEnv e Env.outer)
        | _ => if ← hasBinding e nm then return .inr true else return .inl (← readEnv e Env.outer)
    if bindingExists then return acc
    let definable ← if varIsGlobal then do
        if ← globalDeclRecHas varEnv nm then pure false else canDeclareGlobalVar g nm
      else pure true
    if !definable then return acc
    if !(fnNames.contains nm || declaredVarNames.contains nm || acc.any (·.name == some nm)) then
      if varIsGlobal then createGlobalVarBinding g nm true
      else if !(← hasBinding varEnv nm) then
        createMutableBinding varEnv nm true
        initializeBinding varEnv nm .undefined
    return acc.push f
  -- 15.
  M.forArr (topLevelLexicallyScoped body) fun d =>
    M.forArr d.names fun dn =>
      if d.isConstant then createImmutableBinding lexEnv dn true else createMutableBinding lexEnv dn false
  let ctx' := { ctx with lex := lexEnv, var := varEnv }
  -- 16.
  M.forArr fnsToInit fun f => do
    let nm := f.name.getD "default"
    let fo ← instantiateFunction f lexEnv ctx.priv ctx' (funcNameKey f)
    if varIsGlobal then createGlobalFunctionBinding g nm (.obj fo) true
    else if !(← hasBinding varEnv nm) then
      createMutableBinding varEnv nm true
      initializeBinding varEnv nm (.obj fo)
    else setMutableBinding varEnv nm (.obj fo) false
  -- 17.
  M.forArr declaredVarNames fun vn => do
    if varIsGlobal then createGlobalVarBinding g vn true
    else if !(← hasBinding varEnv vn) then
      createMutableBinding varEnv vn true
      initializeBinding varEnv vn .undefined
  pure (funcIds annexB)

/-- PerformEval's context checks for a direct eval (step 7). -/
def evalParseContext (ctx : Ctx) (direct : Bool) : M EvalContext := do
  if !direct then return {}
  let e ← getThisEnvironment ctx.lex
  let info ← readEnv e fun ev => match ev with
    | .func _ _ ts _ f _ => some (ts, f)
    | _ => none
  let base : EvalContext := {
    direct := true, strict := ctx.strict, privateNames := ctx.priv.map (·.1) }
  match info with
  | none => pure base
  | some (ts, f) =>
    let d ← funcData? f
    let inMethod := ts != .lexical && (d.bind (·.homeObject)).isSome
    let derived := (d.map (·.derived)).getD false
    let field := ((d.bind (·.fieldName)).isSome)
    pure { base with
      inFunction := true, inMethod := inMethod, inDerivedConstructor := derived,
      inClassFieldInitializer := field }

/-! ## Semantic combinators

Each syntax construct's runtime semantics as a combinator over its sub-terms' denotations
(docs/compile.md). The interpreter's cases call these with `(evalExpr n · child)`, so a program's
denotation is a term built from them — which is what `leanjs compile` prints. -/

namespace Sem

/-- An expression's denotation (its value), a reference's, an argument list's. -/
abbrev CExpr := Ctx → M Value
abbrev CRef := Ctx → M Ref
abbrev CArgs := Ctx → M (Array Value)

def this : CExpr := fun ctx => resolveThisBinding ctx.lex
def ident (x : JSStr) : CExpr := fun ctx => identValue ctx.lex x ctx.strict
def lit (l : Lit) : CExpr := fun _ => pure (litValue l)

/-- spec: https://tc39.es/ecma262/#sec-template-literals-runtime-semantics-evaluation -/
def template (cooked : Array (Option JSStr)) (subs : Array CExpr) : CExpr := fun ctx => do
  let first := (cooked[0]?.bind id).getD JSStr.empty
  let r ← M.foldArr (Array.range subs.size) first fun acc i => do
    let v ← subs[i]! ctx
    let s ← toStr v
    pure (acc ++ s ++ (cooked[i + 1]?.bind id).getD JSStr.empty)
  pure (.str r)

/-- A binary operator on two values. spec: https://tc39.es/ecma262/#sec-applystringornumericbinaryoperator -/
def binaryOp (op : BinOp) (lv rv : Value) : M Value := do
  match op with
  | .eq => pure (.bool (← isLooselyEqual lv rv))
  | .ne => pure (.bool !(← isLooselyEqual lv rv))
  | .seq => pure (.bool (isStrictlyEqual lv rv))
  | .sne => pure (.bool !(isStrictlyEqual lv rv))
  | .lt => pure (.bool ((← isLessThan lv rv true) == some true))
  | .gt => pure (.bool ((← isLessThan rv lv false) == some true))
  | .le => pure (.bool ((← isLessThan rv lv false) == some false))
  | .ge => pure (.bool ((← isLessThan lv rv true) == some false))
  | .instanceof => pure (.bool (← instanceofOperator lv rv))
  | .in =>
    let .obj o := rv | throwType "Cannot use 'in' operator to search for a key in a non-object"
    pure (.bool (← Obj'.hasProperty o (← toPropertyKey lv)))
  | op => applyBinaryOp op lv rv

/-- `l op r`: left, then right. -/
def binary (op : BinOp) (l r : CExpr) : CExpr := fun ctx => do
  let lv ← l ctx
  let rv ← r ctx
  binaryOp op lv rv

/-- spec: https://tc39.es/ecma262/#sec-binary-logical-operators-runtime-semantics-evaluation -/
def logical (op : LogOp) (l r : CExpr) : CExpr := fun ctx => do
  let lv ← l ctx
  match op with
  | .and => if !toBoolean lv then pure lv else r ctx
  | .or => if toBoolean lv then pure lv else r ctx
  | .nullish => if lv.isNullish then r ctx else pure lv

/-- spec: https://tc39.es/ecma262/#sec-conditional-operator-runtime-semantics-evaluation -/
def cond (t c a : CExpr) : CExpr := fun ctx => do
  if toBoolean (← t ctx) then c ctx else a ctx

/-- The unary operators other than `delete` and `typeof`, on a value.
spec: https://tc39.es/ecma262/#sec-unary-operators -/
def unaryOp (op : UnOp) (v : Value) : M Value := do
  match op with
  | .not => pure (.bool !(toBoolean v))
  | .pos => pure (.num (← toNum v))
  | .neg =>
    match ← toNumeric v with
    | .bigint i => pure (.bigint (-i))
    | .num x => pure (.num x.neg)
    | v => pure v
  | .bitNot =>
    match ← toNumeric v with
    | .bigint i => pure (.bigint (Conv.intNot i))
    | .num x => pure (intV (Conv.intNot (Conv.toInt32 x)))
    | v => pure v
  | _ => pure .undefined

def unary (op : UnOp) (e : CExpr) : CExpr := fun ctx => do unaryOp op (← e ctx)

/-- spec: https://tc39.es/ecma262/#sec-typeof-operator-runtime-semantics-evaluation -/
def typeofRef (r : CRef) : CExpr := fun ctx => do
  match ← r ctx with
  | .env none _ _ => pure (.str "undefined")
  | r => pure (.str (← typeOf (← getRefValue r)))

/-- spec: https://tc39.es/ecma262/#sec-delete-operator-runtime-semantics-evaluation -/
def deleteRef (r : CRef) : CExpr := fun ctx => do
  match ← r ctx with
  | .value _ => pure (.bool true)
  | .env none _ _ => pure (.bool true)
  | .env (some env) nm _ => pure (.bool (← deleteBinding env nm))
  | .prop base kv strict thisV =>
    if thisV.isSome then throwError .referenceError "Unsupported reference to 'super'"
    let o ← toObject base
    let k ← toPropertyKey kv
    let ok ← Obj'.delete o k
    if !ok && strict then throwType "Cannot delete property"
    pure (.bool ok)
  | .priv .. => M.halt "internal: delete of a private reference"

/-- GetValue of a reference. -/
def getValue (r : CRef) : CExpr := fun ctx => do getRefValue (← r ctx)

def identRef (x : JSStr) : CRef := fun ctx => resolveBinding ctx.lex x ctx.strict

/-- A non-reference expression as a reference. -/
def valueRef (e : CExpr) : CRef := fun ctx => do pure (.value (← e ctx))

/-- A property access's key. -/
inductive Key where
  | name (k : JSStr)
  | computed (e : CExpr)
  | priv (nm : JSStr)

/-- spec: https://tc39.es/ecma262/#sec-property-accessors-runtime-semantics-evaluation -/
def memberRef (obj : CExpr) (key : Key) (optional : Bool) : CRef := fun ctx => do
  let base ← obj ctx
  if optional && base.isNullish then M.throwV sentinelOptional
  match key with
  | .name k => pure (.prop base (.str k) ctx.strict none)
  | .computed ke => do
    let kv ← ke ctx
    pure (.prop base kv ctx.strict none)
  | .priv nm => do pure (.priv base (← resolvePrivate ctx.priv nm))

/-- An optional chain's boundary. -/
def chain (e : CExpr) : CExpr := fun ctx =>
  M.tryCatch (e ctx) fun err => if isSentinel err 16 then pure .undefined else M.throwV err

def chainRef (r : CRef) : CRef := fun ctx =>
  M.tryCatch (r ctx) fun err => if isSentinel err 16 then pure (.value .undefined) else M.throwV err

/-- A call expression used as an assignment target (sloppy web compat): evaluated, then a
ReferenceError. -/
def callTargetRef (e : CExpr) : CRef := fun ctx => do
  let _ ← e ctx
  throwError .referenceError "Invalid left-hand side in assignment"

/-- An argument. -/
inductive ArgD where
  | expr (e : CExpr)
  | spread (e : CExpr)

/-- ArgumentListEvaluation spec: https://tc39.es/ecma262/#sec-runtime-semantics-argumentlistevaluation -/
def args (as : Array ArgD) : CArgs := fun ctx => M.foldArr as #[] fun acc a => do
  match a with
  | .expr e => pure (acc.push (← e ctx))
  | .spread e => do
    let v ← e ctx
    let xs ← iterableToList v
    pure (acc ++ xs)

/-- EvaluateCall (callees other than a possible direct `eval`).
spec: https://tc39.es/ecma262/#sec-evaluatecall -/
def call (callee : CRef) (argList : CArgs) (optional : Bool) (name : String) : CExpr := fun ctx => do
  let ref ← callee ctx
  let func ← getRefValue ref
  if optional && func.isNullish then M.throwV sentinelOptional
  let thisV ← refThisValue ref
  let as ← argList ctx
  if !(← isCallable func) then throwType s!"{name} is not a function"
  ES.call func thisV as

/-- spec: https://tc39.es/ecma262/#sec-evaluatenew -/
def new (c : CExpr) (argList : CArgs) : CExpr := fun ctx => do
  let cv ← c ctx
  let as ← argList ctx
  if !(← isConstructor cv) then throwType "is not a constructor"
  construct cv as

/-- The comma operator. -/
def seq (es : Array CExpr) : CExpr := fun ctx => M.foldArr es .undefined fun _ e => e ctx

/-- A function expression (`name`: NamedEvaluation's name). -/
def func (f : Func) (name : Option PropKey) : CExpr := fun ctx => instantiateFunctionExpr f ctx name

/-- spec: https://tc39.es/ecma262/#sec-postfix-increment-operator-runtime-semantics-evaluation -/
def update (inc pre : Bool) (target : CRef) : CExpr := fun ctx => do
  let (oldV, r) ← getRefValueOnce (← target ctx)
  let old ← toNumeric oldV
  let nv : Value := match old with
    | .bigint i => .bigint (if inc then i + 1 else i - 1)
    | .num x => .num (if inc then Conv.addF x F64.one else Conv.subF x F64.one)
    | v => v
  putRefValue r nv
  pure (if pre then nv else old)

/-- `target = value` (a reference target).
spec: https://tc39.es/ecma262/#sec-assignment-operators-runtime-semantics-evaluation -/
def assign (target : CRef) (value : CExpr) : CExpr := fun ctx => do
  let lref ← target ctx
  let rv ← value ctx
  putRefValue lref rv
  pure rv

/-- `target op= value` -/
def assignOp (o : BinOp) (target : CRef) (value : CExpr) : CExpr := fun ctx => do
  let (lv, lref) ← getRefValueOnce (← target ctx)
  let rv ← value ctx
  let r ← applyBinaryOp o lv rv
  putRefValue lref r
  pure r

/-- `target &&= value` etc. -/
def assignLogical (o : LogOp) (target : CRef) (value : CExpr) : CExpr := fun ctx => do
  let (lv, lref) ← getRefValueOnce (← target ctx)
  let short := match o with
    | .and => !toBoolean lv
    | .or => toBoolean lv
    | .nullish => !lv.isNullish
  if short then return lv
  let rv ← value ctx
  putRefValue lref rv
  pure rv

def newTarget : CExpr := fun ctx => getNewTarget ctx

/-- spec: https://tc39.es/ecma262/#await -/
def await (e : CExpr) : CExpr := fun ctx => do
  let v ← e ctx
  let r ← ES.await v
  restoreCtx ctx
  pure r

/-! ### Statements -/

/-- A statement's denotation. -/
abbrev CStmt := Ctx → M Compl

/-- A declarator's effect. -/
abbrev CDecl := Ctx → M Unit

/-- A loop's or switch's `break` without a label completes it normally. -/
def breakToNormal : Compl → Compl
  | .brk none v => .normal (some (v.getD .undefined))
  | c => c

/-- (a statement's own label set; its parts see none) -/
@[inline] def inner (ctx : Ctx) : Ctx := { ctx with labels := #[] }

/-- spec: https://tc39.es/ecma262/#sec-expression-statement-runtime-semantics-evaluation -/
def exprStmt (e : CExpr) : CStmt := fun ctx => do pure (.normal (some (← e (inner ctx))))

/-- `var x = v` spec: https://tc39.es/ecma262/#sec-variable-statement-runtime-semantics-evaluation -/
def declVar (x : JSStr) (v : CExpr) : CDecl := fun ctx => do
  let lhs ← resolveBinding ctx.lex x ctx.strict
  let val ← v ctx
  putRefValue lhs val

/-- `let x`, `let x = v`, `const x = v`, `using x = v`
spec: https://tc39.es/ecma262/#sec-let-and-const-declarations-runtime-semantics-evaluation -/
def declLex (kind : VarKind) (x : JSStr) (v : Option CExpr) : CDecl := fun ctx => do
  let lhs ← resolveBinding ctx.lex x ctx.strict
  match v with
  | none => initializeRefBinding lhs .undefined
  | some v =>
    let val ← v ctx
    initializeRefBinding lhs val
    if kind == .using || kind == .awaitUsing then
      match ctx.disposeCap with
      | some cap => addDisposableResource cap val (kind == .awaitUsing)
      | none => M.halt "internal: using declaration outside a disposal scope"

def varDecl (ds : Array CDecl) : CStmt := fun ctx => do
  let ctx := inner ctx
  M.forArr ds fun d => d ctx
  pure (.normal none)

/-- A statement list: UpdateEmpty of each statement's completion with the last value.
spec: https://tc39.es/ecma262/#sec-block-runtime-semantics-evaluation -/
def stmts (ss : Array CStmt) : CStmt := fun ctx =>
  M.repeatFrom ((0 : Nat), (none : Option Value)) fun (i, v) => do
    if h : i < ss.size then
      let r ← ss[i] ctx
      match r with
      | .normal rv => return .inl (i + 1, rv <|> v)
      | r => return .inr (r.updateEmpty v)
    else return .inr (.normal v)

/-- A block (its lexical declarations instantiated in a new environment).
spec: https://tc39.es/ecma262/#sec-block-runtime-semantics-evaluation -/
def block (decls : Array LexScoped) (body : Array CStmt) : CStmt := fun ctx => do
  let ctx := inner ctx
  if decls.isEmpty then stmts body ctx
  else
    let env ← newDeclEnv (some ctx.lex)
    blockDeclarationInstantiation decls env ctx
    withDisposeScope (usingKinds decls).1 { ctx with lex := env } fun c => stmts body c

def empty : CStmt := fun _ => pure (.normal none)

/-- spec: https://tc39.es/ecma262/#sec-return-statement-runtime-semantics-evaluation -/
def ret (e : Option CExpr) : CStmt := fun ctx => do
  let ctx := inner ctx
  let v ← match e with
    | some e => e ctx
    | none => pure .undefined
  if ctx.isAsync && ctx.isGen && e.isSome then
    let v ← ES.await v
    restoreCtx ctx
    return .ret v
  pure (.ret v)

/-- spec: https://tc39.es/ecma262/#sec-if-statement-runtime-semantics-evaluation -/
def ifS (t : CExpr) (c : CStmt) (a : Option CStmt) : CStmt := fun ctx => do
  let ctx := inner ctx
  let r ← if toBoolean (← t ctx) then c ctx
    else match a with
      | some a => a ctx
      | none => pure (.normal none)
  pure (r.updateEmpty (some .undefined))

/-- spec: https://tc39.es/ecma262/#sec-runtime-semantics-whileloopevaluation -/
def whileS (t : CExpr) (body : CStmt) : CStmt := fun ctx => do
  let labels := ctx.labels
  let ctx := inner ctx
  let r ← M.repeatFrom (Value.undefined) fun v => do
    M.tick
    if !toBoolean (← t ctx) then return .inr (Compl.normal (some v))
    let r ← body ctx
    if !loopContinues r labels then return .inr (r.updateEmpty (some v))
    return .inl ((r.value?).getD v)
  pure (breakToNormal r)

/-- spec: https://tc39.es/ecma262/#sec-runtime-semantics-dowhileloopevaluation -/
def doWhile (body : CStmt) (t : CExpr) : CStmt := fun ctx => do
  let labels := ctx.labels
  let ctx := inner ctx
  let r ← M.repeatFrom (Value.undefined) fun v => do
    M.tick
    let r ← body ctx
    if !loopContinues r labels then return .inr (r.updateEmpty (some v))
    let v := (r.value?).getD v
    if !toBoolean (← t ctx) then return .inr (Compl.normal (some v))
    return .inl v
  pure (breakToNormal r)

def brk (l : Option JSStr) : CStmt := fun _ => pure (.brk l none)
def cont (l : Option JSStr) : CStmt := fun _ => pure (.cont l none)

/-- spec: https://tc39.es/ecma262/#sec-throw-statement-runtime-semantics-evaluation -/
def throw (e : CExpr) : CStmt := fun ctx => do M.throwV (← e (inner ctx))

/-- A function declaration's evaluation (Annex B.3.2.1: copy a block function to its var binding). -/
def funDecl (f : Func) : CStmt := fun ctx => do
  if ctx.annexB.contains f.info.id then
    if let some nm := f.name then
      let v ← getBindingValue ctx.lex nm false
      setMutableBinding ctx.var nm v false
  pure (.normal none)

/-- spec: https://tc39.es/ecma262/#sec-runtime-semantics-labelledevaluation (`isBreakable`: the
body is an iteration/switch/labelled statement, which sees the label set) -/
def labeled (l : JSStr) (isBreakable : Bool) (body : CStmt) : CStmt := fun ctx => do
  let labels := ctx.labels
  let r ← body { ctx with labels := if isBreakable then labels.push l else #[] }
  match r with
  | .brk (some l') v => if l' == l then pure (.normal (some (v.getD .undefined))) else pure r
  | r => pure r

end Sem

mutual

/-- Evaluation of an expression to a value (with GetValue applied).
spec: https://tc39.es/ecma262/#sec-ecmascript-language-expressions -/
def evalExpr : Nat → Ctx → Expr → M Value
  | 0, _, _ => tooDeep
  | n + 1, ctx, e => do
    match e with
    | .this => Sem.this ctx
    | .ident x => Sem.ident x ctx
    | .lit l => Sem.lit l ctx
    | .paren e => evalExpr n ctx e
    | .template cooked _ exprs => Sem.template cooked (exprs.map fun e c => evalExpr n c e) ctx
    | .tagged tag cooked raw exprs site =>
      -- spec: https://tc39.es/ecma262/#sec-tagged-templates-runtime-semantics-evaluation
      let ref ← evalRef n ctx tag
      let f ← getRefValue ref
      let thisV ← refThisValue ref
      let tmpl ← getTemplateObject ctx.script site cooked raw
      let subs ← M.mapArr exprs (evalExpr n ctx)
      if !(← isCallable f) then throwType "tag is not a function"
      call f thisV (#[tmpl] ++ subs)
    | .regex p fl => regexpCreateLiteral p fl
    | .array elems => evalArrayLit n ctx elems
    | .object props => evalObjectLit n ctx props
    | .func f => Sem.func f none ctx
    | .cls c => evalClass n ctx c c.name (c.name.map (.str ·))
    | .unary op e => match op with
      | .delete => Sem.deleteRef (evalRef n · e) ctx
      | .typeof => Sem.typeofRef (evalRef n · e) ctx
      | op => Sem.unary op (evalExpr n · e) ctx
    | .update inc pre target => Sem.update inc pre (evalTargetRef n · target) ctx
    | .binary op l r => Sem.binary op (evalExpr n · l) (evalExpr n · r) ctx
    | .logical op l r => Sem.logical op (evalExpr n · l) (evalExpr n · r) ctx
    | .privIn name r =>
      -- spec: https://tc39.es/ecma262/#sec-relational-operators-runtime-semantics-evaluation
      let rv ← evalExpr n ctx r
      let .obj o := rv | throwType "Cannot use 'in' operator to search for a private field in a non-object"
      let id ← resolvePrivate ctx.priv name
      readObj o fun ob => .bool (ob.privates.any (·.1 == id))
    | .assign op target value => evalAssign n ctx op target value
    | .cond t c a => Sem.cond (evalExpr n · t) (evalExpr n · c) (evalExpr n · a) ctx
    | .call callee args optional =>
      match callee with
      | .ident nm =>
        if nm == JSStr.ofString "eval" then evalCall n ctx callee args optional
        else Sem.call (evalRef n · callee) (Sem.args (args.map (argD n))) optional (calleeName callee) ctx
      | _ => Sem.call (evalRef n · callee) (Sem.args (args.map (argD n))) optional (calleeName callee) ctx
    | .new callee args => Sem.new (evalExpr n · callee) (Sem.args (args.map (argD n))) ctx
    | .member .. | .superMember _ => Sem.getValue (evalRef n · e) ctx
    | .chain inner => Sem.chain (evalExpr n · inner) ctx
    | .superCall args =>
      -- spec: https://tc39.es/ecma262/#sec-super-keyword-runtime-semantics-evaluation
      let nt ← getNewTarget ctx
      let func ← getSuperConstructor ctx
      let argList ← evalArgs n ctx args
      if !(← isConstructor func) then throwType "Super constructor is not a constructor"
      let result ← construct func argList (some nt)
      let thisEnv ← getThisEnvironment ctx.lex
      bindThisValue thisEnv result
      let f ← readEnv thisEnv fun ev => match ev with | .func _ _ _ _ f _ => some f | _ => none
      if let some f := f then initializeInstanceElements result f
      pure result
    | .newTarget => Sem.newTarget ctx
    | .importMeta => call (← intrinsicV "%ImportMeta%") .undefined #[]
    | .importCall spec opts =>
      -- spec: https://tc39.es/ecma262/#sec-import-call-runtime-semantics-evaluation
      let sv ← evalExpr n ctx spec
      let ov ← match opts with
        | some o => evalExpr n ctx o
        | none => pure .undefined
      call (← intrinsicV "%DynamicImport%") .undefined #[sv, ov]
    | .seq es => Sem.seq (es.map fun e c => evalExpr n c e) ctx
    | .yield arg delegate =>
      if delegate then evalYieldStar n ctx (arg.getD (.lit .null))
      else
        let v ← match arg with
          | some a => evalExpr n ctx a
          | none => pure .undefined
        generatorYield ctx v
    | .await e => Sem.await (evalExpr n · e) ctx

/-- An argument's denotation. -/
def argD : Nat → Arg → Sem.ArgD
  | 0, _ => .expr fun _ => tooDeep
  | n + 1, a => match a with
    | .expr e => .expr (evalExpr n · e)
    | .spread e => .spread (evalExpr n · e)

/-- Evaluation of an expression to a Reference (identifiers, property accesses; other
expressions evaluate to `Ref.value`). -/
def evalRef : Nat → Ctx → Expr → M Ref
  | 0, _, _ => tooDeep
  | n + 1, ctx, e => do
    match e with
    | .ident x => Sem.identRef x ctx
    | .paren e => evalRef n ctx e
    | .member obj key optional =>
      let k : Sem.Key := match key with
        | .name k => .name k
        | .computed ke => .computed (evalExpr n · ke)
        | .priv nm => .priv nm
      Sem.memberRef (evalExpr n · obj) k optional ctx
    | .superMember key =>
      -- spec: https://tc39.es/ecma262/#sec-super-keyword-runtime-semantics-evaluation
      let env ← getThisEnvironment ctx.lex
      let actualThis ← resolveThisBinding ctx.lex
      let kv ← match key with
        | .name k => pure (Value.str k)
        | .computed ke => evalExpr n ctx ke
        | .priv _ => M.halt "internal: super.#x"
      let _ := env
      -- MakeSuperPropertyReference: GetSuperBase
      let home ← homeObject ctx
      let base ← match home with
        | some h => Obj'.getPrototypeOf h
        | none => pure .undefined
      pure (.prop base kv true (some actualThis))
    | .chain inner => Sem.chainRef (evalRef n · inner) ctx
    | e => Sem.valueRef (evalExpr n · e) ctx

/-- An assignment target's reference: a call expression (allowed as a target in sloppy code
for web compatibility) is evaluated, then a ReferenceError thrown.
spec: https://tc39.es/ecma262/#sec-static-semantics-assignmenttargettype (web-compat) -/
def evalTargetRef : Nat → Ctx → Expr → M Ref
  | 0, _, _ => tooDeep
  | n + 1, ctx, e => do
    let rec isCall : Nat → Expr → Bool
      | 0, _ => false
      | k + 1, e => match e with | .call .. => true | .paren e => isCall k e | _ => false
    if isCall 64 e then Sem.callTargetRef (evalExpr n · e) ctx
    else evalRef n ctx e

/-- ArgumentListEvaluation spec: https://tc39.es/ecma262/#sec-runtime-semantics-argumentlistevaluation -/
def evalArgs : Nat → Ctx → Array Arg → M (Array Value)
  | 0, _, _ => tooDeep
  | n + 1, ctx, args => M.foldArr args #[] fun acc a => do
    match a with
    | .expr e => pure (acc.push (← evalExpr n ctx e))
    | .spread e => do
      let v ← evalExpr n ctx e
      let xs ← iterableToList v
      pure (acc ++ xs)

/-- EvaluateCall and the CallExpression forms. -/
def evalCall : Nat → Ctx → Expr → Array Arg → Bool → M Value
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, callee, args, optional => do
    let ref ← evalRef n ctx callee
    let func ← getRefValue ref
    if optional && func.isNullish then M.throwV sentinelOptional
    -- (direct eval: PerformEval)
    if let .ident nm := callee then
      if nm == JSStr.ofString "eval" then
        let ev ← intrinsic "%eval%"
        if sameValue func (.obj ev) then
          let argList ← evalArgs n ctx args
          if argList.isEmpty then return .undefined
          return ← performEval n ctx argList[0]! true
    let thisV ← refThisValue ref
    let argList ← evalArgs n ctx args
    if !(← isCallable func) then throwType s!"{calleeName callee} is not a function"
    call func thisV argList

/-- PerformEval for direct calls (the interpreter's part: parsing is the parser's).
spec: https://tc39.es/ecma262/#sec-performeval -/
def performEval : Nat → Ctx → Value → Bool → M Value
  | 0, _, _, _ => tooDeep
  | n + 1, ctx, x, direct => do
    -- 2.
    let .str src := x | return x
    -- 6-11.
    let pctx ← evalParseContext ctx direct
    let prog ← match parseEval src.toString pctx with
      | .ok p => pure p
      | .error e => throwError .syntaxError e.msg
    let (curGlobal, scriptsSize, realmIdx) ← readS fun s => (s.curRealm.globalEnv, s.scripts.size, s.realm)
    -- 13.
    let strictEval := (direct && ctx.strict) || prog.strict
    -- 16-18.
    let (lexOuter, varEnv, priv) := if direct then (ctx.lex, ctx.var, ctx.priv)
      else (curGlobal, curGlobal, #[])
    let lexEnv ← newDeclEnv (some lexOuter)
    let varEnv := if strictEval then lexEnv else varEnv
    let script := scriptsSize
    modify fun s => { s with scripts := s.scripts.push { prog, realm := s.realm } }
    let ectx : Ctx := {
      lex := lexEnv, var := varEnv, priv := priv, strict := strictEval,
      fn := if direct then ctx.fn else none, realm := realmIdx, script := script,
      isAsync := false }
    -- 28.
    let annexB ← evalDeclarationInstantiation prog.body varEnv lexEnv ectx
    -- 29-30.
    match ← evalStmts n { ectx with annexB } prog.body with
    | .normal v => pure (v.getD .undefined)
    | .ret v => pure v
    | _ => pure .undefined

/-- NamedEvaluation of an expression (anonymous functions and classes get `name`).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-namedevaluation -/
def namedEval : Nat → Ctx → Expr → PropKey → M Value
  | 0, _, _, _ => tooDeep
  | n + 1, ctx, e, name => do
    match e with
    | .func f => if f.name.isNone then instantiateFunctionExpr f ctx (some name) else evalExpr n ctx e
    | .cls c => if c.name.isNone then evalClass n ctx c none (some name) else evalExpr n ctx e
    | .paren e => namedEval n ctx e name
    | e => evalExpr n ctx e

/-- Assignment. spec: https://tc39.es/ecma262/#sec-assignment-operators-runtime-semantics-evaluation -/
def evalAssign : Nat → Ctx → AssignOp → Pattern → Expr → M Value
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, op, target, value => do
    let targetRef : M Ref := match target with
      | .ident x => resolveBinding ctx.lex x ctx.strict
      | .expr e => evalTargetRef n ctx e
      | _ => pure (.value .undefined)
    let nameOf : Option PropKey := match target with
      | .ident x => some (.str x)
      | _ => none
    let rhs : M Value := match nameOf with
      | some nm => if isAnonymousFn value then namedEval n ctx value nm else evalExpr n ctx value
      | none => evalExpr n ctx value
    let _ := (targetRef, rhs)
    -- (the target and the right side as denotations)
    let tD : Sem.CRef := match target with
      | .ident x => Sem.identRef x
      | .expr e => (evalTargetRef n · e)
      | _ => fun _ => pure (.value .undefined)
    let rD : Sem.CExpr := match target with
      | .ident x => if isAnonymousFn value then (namedEval n · value (.str x)) else (evalExpr n · value)
      | _ => (evalExpr n · value)
    match op with
    | .assign =>
      match target with
      | .obj .. | .arr .. =>
        let rv ← evalExpr n ctx value
        bindPattern n ctx target rv .assign
        pure rv
      | _ => Sem.assign tD rD ctx
    | .op o => Sem.assignOp o tD (evalExpr n · value) ctx
    | .logical o => Sem.assignLogical o tD rD ctx

/-- BindingInitialization / DestructuringAssignmentEvaluation of a pattern with a value.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-bindinginitialization,
https://tc39.es/ecma262/#sec-runtime-semantics-destructuringassignmentevaluation -/
def bindPattern : Nat → Ctx → Pattern → Value → BindMode → M Unit
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, p, v, mode => do
    match p with
    | .ident x =>
      let env := match mode with | .init (some e) => e | _ => ctx.lex
      let r ← resolveBinding env x ctx.strict
      putTarget r v mode
    | .expr e =>
      let r ← evalTargetRef n ctx e
      putRefValue r v
    | .obj props rest =>
      -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-propertybindinginitialization
      let _ ← requireObjectCoercible v
      let excluded ← M.foldArr props #[] fun acc pp => do
        let .mk key target init := pp
        let k ← evalPropName n ctx key
        bindElement n ctx target init mode (getVProp v k)
        pure (acc.push k)
      if let some r := rest then
        -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-restbindinginitialization
        let lref ← targetRefOf n ctx r mode
        let restObj ← newObject
        copyDataProperties restObj v excluded
        match lref with
        | some lr => putTarget lr (.obj restObj) mode
        | none => bindPattern n ctx r (.obj restObj) mode
    | .arr elems rest =>
      -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-iteratorbindinginitialization
      let rec_ ← getIterator v
      let rec_ ← M.foldArr elems rec_ fun r el => bindIterElement n ctx el r mode
      let rec_ ← match rest with
        | none => pure rec_
        | some rp => bindIterRest n ctx rp rec_ mode
      if !rec_.done then iteratorClose rec_

/-- The reference of a non-pattern target (evaluated before the value is read); `none` for
nested patterns. -/
def targetRefOf : Nat → Ctx → Pattern → BindMode → M (Option Ref)
  | 0, _, _, _ => tooDeep
  | n + 1, ctx, p, mode => do
    match p with
    | .ident x =>
      let env := match mode with | .init (some e) => e | _ => ctx.lex
      pure (some (← resolveBinding env x ctx.strict))
    | .expr e => pure (some (← evalTargetRef n ctx e))
    | _ => pure none

/-- One keyed element: the target's reference first, then the value, its default, the binding.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-keyeddestructuringassignmentevaluation -/
def bindElement : Nat → Ctx → Pattern → Option Expr → BindMode → M Value → M Unit
  | 0, _, _, _, _, _ => tooDeep
  | n + 1, ctx, target, init, mode, getVal => do
    let lref ← targetRefOf n ctx target mode
    let v ← getVal
    let v ← match init with
      | some ie =>
        if v.isUndefined then
          (match target with
           | .ident x => if isAnonymousFn ie then namedEval n ctx ie (.str x) else evalExpr n ctx ie
           | _ => evalExpr n ctx ie)
        else pure v
      | none => pure v
    match lref with
    | some r => putTarget r v mode
    | none => bindPattern n ctx target v mode

/-- One element of an array pattern (closing the iterator if binding throws).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-iteratordestructuringassignmentevaluation -/
def bindIterElement : Nat → Ctx → Option PatElem → IterRecord → BindMode → M IterRecord
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, el, r, mode => do
    match el with
    | none =>
      -- Elision
      if r.done then return r
      let (r, v) ← iteratorStepValue r
      pure (if v.isNone then { r with done := true } else r)
    | some (.mk target init) =>
      let lref ← withIterClose r (targetRefOf n ctx target mode)
      let (r, v) ← if r.done then pure (r, none) else iteratorStepValue r
      let v := v.getD .undefined
      withIterClose r do
        let v ← match init with
          | some ie =>
            if v.isUndefined then
              (match target with
               | .ident x => if isAnonymousFn ie then namedEval n ctx ie (.str x) else evalExpr n ctx ie
               | _ => evalExpr n ctx ie)
            else pure v
          | none => pure v
        match lref with
        | some lr => putTarget lr v mode
        | none => bindPattern n ctx target v mode
      pure r

/-- The rest element of an array pattern. -/
def bindIterRest : Nat → Ctx → Pattern → IterRecord → BindMode → M IterRecord
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, target, r, mode => do
    let lref ← withIterClose r (targetRefOf n ctx target mode)
    let (r, xs) ← M.repeatFrom (r, (#[] : Array Value)) fun (r, acc) => do
      if r.done then return .inr (r, acc)
      let (r, v) ← iteratorStepValue r
      match v with
      | some v => return .inl (r, acc.push v)
      | none => return .inr ({ r with done := true }, acc)
    let arr ← createArrayFromList xs
    withIterClose r do
      match lref with
      | some lr => putTarget lr arr mode
      | none => bindPattern n ctx target arr mode
    pure r

/-- The property key of a property name (computed keys evaluated and converted).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-propertydefinitionevaluation -/
def evalPropName : Nat → Ctx → PropName → M PropKey
  | 0, _, _ => tooDeep
  | n + 1, ctx, pn => do
    match pn with
    | .computed e => toPropertyKey (← evalExpr n ctx e)
    | .priv nm => M.halt s!"internal: private name #{nm} as a property key"
    | pn => pure ((staticPropKey pn).getD (.str JSStr.empty))

/-- ArrayLiteral evaluation. spec: https://tc39.es/ecma262/#sec-runtime-semantics-arrayaccumulation -/
def evalArrayLit : Nat → Ctx → Array ArrElem → M Value
  | 0, _, _ => tooDeep
  | n + 1, ctx, elems => do
    let a ← arrayCreate 0
    let len ← M.foldArr elems 0 fun i el => do
      match el with
      | .hole => pure (i + 1)
      | .expr e =>
        let v ← evalExpr n ctx e
        createDataPropertyOrThrow a (PropKey.ofNat i) v
        pure (i + 1)
      | .spread e =>
        let v ← evalExpr n ctx e
        let xs ← iterableToList v
        M.foldArr xs i fun j x => do
          createDataPropertyOrThrow a (PropKey.ofNat j) x
          pure (j + 1)
    setProp a (.str kLength) (numV len)
    pure (.obj a)

/-- ObjectLiteral evaluation. spec: https://tc39.es/ecma262/#sec-object-initializer-runtime-semantics-evaluation -/
def evalObjectLit : Nat → Ctx → Array PropDef → M Value
  | 0, _, _ => tooDeep
  | n + 1, ctx, props => do
    let o ← newObject
    M.forArr props fun pd => do
      match pd with
      | .init key value protoSetter =>
        if protoSetter then
          let v ← evalExpr n ctx value
          match v with
          | .obj _ | .null => let _ ← Obj'.setPrototypeOf o v
          | _ => pure ()
        else
          let k ← evalPropName n ctx key
          let v ← if isAnonymousFn value then namedEval n ctx value k else evalExpr n ctx value
          createDataPropertyOrThrow o k v
      | .shorthand nm =>
        let v ← getRefValue (← resolveBinding ctx.lex nm ctx.strict)
        createDataPropertyOrThrow o (.str nm) v
      | .spread e =>
        let v ← evalExpr n ctx e
        copyDataProperties o v #[]
      | .method key f =>
        let k ← evalPropName n ctx key
        defineMethodOn ctx o k f true
    pure (.obj o)

/-- ClassDefinitionEvaluation (`binding`: the class binding; `name`: the function's name).
spec: https://tc39.es/ecma262/#sec-runtime-semantics-classdefinitionevaluation -/
def evalClass : Nat → Ctx → Class → Option JSStr → Option PropKey → M Value
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, c, binding, name => do
    -- 1-3.
    let classEnv ← newDeclEnv (some ctx.lex)
    if let some b := binding then createImmutableBinding classEnv b true
    -- 4-6.
    let privNames ← M.foldArr (classPrivateNames c) #[] fun acc nm => do
      let id ← readS (·.nextPrivId)
      modify fun s => { s with nextPrivId := s.nextPrivId + 1, privNames := s.privNames.push nm }
      pure (acc.push (nm, id))
    let classPriv := ctx.priv ++ privNames
    -- 7-8.
    let (protoParent, ctorParent) ← match c.superClass with
      | none => do pure (Value.obj (← intrinsic "%Object.prototype%"), ← intrinsic "%Function.prototype%")
      | some sc => do
        let superclass ← evalExpr n { ctx with lex := classEnv } sc
        match superclass with
        | .null => pure (Value.null, ← intrinsic "%Function.prototype%")
        | _ =>
          if !(← isConstructor superclass) then throwType "Class extends value is not a constructor or null"
          let .obj sco := superclass | throwType "Class extends value is not a constructor"
          let pp ← getProp sco (.str kPrototype)
          match pp with
          | .obj _ | .null => pure (pp, sco)
          | _ => throwType "Class extends value does not have valid prototype property"
    -- 9.
    let proto ← ordinaryObjectCreate protoParent
    -- 10-14.
    let cctx : Ctx := { ctx with lex := classEnv, priv := classPriv, strict := true }
    let derived := c.superClass.isSome
    let ctorFunc : Option Func := c.elems.findSome? fun e => match e with
      | .method false (.ident k) f => if k == kConstructor && (match f.kind with | .classConstructor _ => true | _ => false) then some f else none
      | .method false (.str k) f => if k == kConstructor && (match f.kind with | .classConstructor _ => true | _ => false) then some f else none
      | _ => none
    let (source, realmIdx) ← readS fun s => ((s.scripts[ctx.script]?.map (·.prog.source)).getD "", s.realm)
    let code : Func := match ctorFunc with
      | some (.mk n k a g p b i) => .mk n k a g p b { i with span := c.span }
      | none => .mk (some kConstructor) (.classConstructor derived) false false #[] (.stmts #[])
          { strict := true, span := c.span }
    let fd : FuncData := {
      code := code, env := classEnv, privEnv := classPriv, thisMode := .strict,
      homeObject := some proto, derived := derived, isClassCtor := true, isDefaultCtor := ctorFunc.isNone,
      realm := realmIdx, script := ctx.script, source := source }
    let f ← alloc { proto := .obj ctorParent, kind := .func fd }
    setOwn f (.str kLength) (.data (numV (if ctorFunc.isSome then code.info.expectedArgs else 0)) false false true)
    setFunctionName f (name.getD (.str JSStr.empty))
    -- 15. MakeConstructor(F, false, proto)
    makeConstructor f false (some proto)
    -- 17.
    setOwn proto (.str kConstructor) (.data (.obj f) true false true)
    -- 18-20.
    let (instPriv, staticPriv, instFields, staticElems) ← M.foldArr c.elems
        ((#[] : Array (Nat × PrivElem)), (#[] : Array (Nat × PrivElem)), (#[] : Array FieldDef),
         (#[] : Array (Sum FieldDef ObjId))) fun (ip, sp, inf, se) el => do
      match el with
      | .method isStatic key mf =>
        if (match mf.kind with | .classConstructor _ => true | _ => false) && !isStatic then
          return (ip, sp, inf, se)
        let home := if isStatic then f else proto
        match key with
        | .priv nm =>
          let id ← resolvePrivate classPriv nm
          let pe ← privateMethod cctx home mf nm
          let merge (xs : Array (Nat × PrivElem)) : Array (Nat × PrivElem) :=
            match xs.findIdx? (·.1 == id) with
            | some i => xs.modify i fun (_, old) => (id, match old, pe with
                | .accessor g _, .accessor .undefined s => .accessor g s
                | .accessor _ s, .accessor g .undefined => .accessor g s
                | _, pe => pe)
            | none => xs.push (id, pe)
          if isStatic then pure (ip, merge sp, inf, se) else pure (merge ip, sp, inf, se)
        | key =>
          let k ← evalPropName n cctx key
          defineMethodOn cctx home k mf false
          pure (ip, sp, inf, se)
      | .field isStatic key init span =>
        let home := if isStatic then f else proto
        let nm : ElemName ← match key with
          | .priv p => do pure (.priv (← resolvePrivate classPriv p))
          | key => do pure (.key (← evalPropName n cctx key))
        let initF ← match init with
          | none => pure none
          | some ie => do
            let code : Func := .mk none .classField false false #[] (.expr ie) { strict := true, span }
            let fp ← intrinsic "%Function.prototype%"
            let fo ← ordinaryFunctionCreate fp code classEnv classPriv cctx false
            makeMethod fo home
            modifyObj fo fun o => o.withKind fun k => match k with
              | .func d => .func { d with fieldName := some nm }
              | k => k
            pure (some fo)
        let fdef : FieldDef := { name := nm, init := initF }
        if isStatic then pure (ip, sp, inf, se.push (.inl fdef)) else pure (ip, sp, inf.push fdef, se)
      | .staticBlock body span =>
        let code : Func := .mk none .classStaticBlock false false #[] (.stmts body) { strict := true, span }
        let fp ← intrinsic "%Function.prototype%"
        let fo ← ordinaryFunctionCreate fp code classEnv classPriv cctx false
        makeMethod fo f
        pure (ip, sp, inf, se.push (.inr fo))
      | .accessor .. => M.halt "class auto-accessors are not implemented"
    -- 22.
    if let some b := binding then initializeBinding classEnv b (.obj f)
    -- 23-24.
    modifyObj f fun o => o.withKind fun k => match k with
      | .func d => .func { d with privMethods := instPriv, fields := instFields }
      | k => k
    -- 25.
    M.forArr staticPriv fun (id, pe) => privateElementAdd (.obj f) id pe
    -- 26.
    M.forArr staticElems fun el => do
      match el with
      | .inl fdef => defineField (.obj f) fdef
      | .inr blk => let _ ← call (.obj blk) (.obj f) #[]
    pure (.obj f)

/-- `yield*` (sync and async generators).
spec: https://tc39.es/ecma262/#sec-generator-function-definitions-runtime-semantics-evaluation -/
def evalYieldStar : Nat → Ctx → Expr → M Value
  | 0, _, _ => tooDeep
  | n + 1, ctx, e => do
    let async := ctx.isAsync
    let value ← evalExpr n ctx e
    let r ← if async then getAsyncIterator value else getIterator value
    let awaitIf (v : Value) : M Value := do
      if async then let x ← await v; restoreCtx ctx; pure x else pure v
    -- (yields an inner result: async generators yield its value, sync ones the result object)
    let yieldInner (inner : Value) : M Outcome := do
      if async then asyncGenYield ctx (← iteratorValue inner) else yieldRaw ctx inner
    let received ← M.repeatFrom (Outcome.normal .undefined) fun received => do
      match received with
      | .normal v =>
        let inner ← awaitIf (← call r.next r.iter #[v])
        if !inner.isObject then throwType "Iterator result is not an object"
        if ← iteratorComplete inner then return .inr (Outcome.normal (← iteratorValue inner))
        return .inl (← yieldInner inner)
      | .throw t =>
        match ← getMethodOf r.iter (.str "throw") with
        | some th =>
          let inner ← awaitIf (← call th r.iter #[t])
          if !inner.isObject then throwType "Iterator result is not an object"
          if ← iteratorComplete inner then return .inr (Outcome.normal (← iteratorValue inner))
          return .inl (← yieldInner inner)
        | none =>
          if async then asyncIteratorClose r else iteratorClose r
          throwType "The iterator does not provide a 'throw' method"
      | .ret v =>
        match ← getMethodOf r.iter (.str "return") with
        | none => return .inr (Outcome.ret (← awaitIf v))
        | some rf =>
          let inner ← awaitIf (← call rf r.iter #[v])
          if !inner.isObject then throwType "Iterator result is not an object"
          if ← iteratorComplete inner then
            let rv ← iteratorValue inner
            return .inr (Outcome.ret (← awaitIf rv))
          return .inl (← yieldInner inner)
    resumeValue received

-- Statements

/-- Evaluation of a statement. spec: https://tc39.es/ecma262/#sec-ecmascript-language-statements-and-declarations -/
def evalStmt : Nat → Ctx → Stmt → M Compl
  | 0, _, _ => tooDeep
  | n + 1, ctx, st => do
    let labels := ctx.labels
    match st with
    | .expr e => Sem.exprStmt (evalExpr n · e) ctx
    | .varDecl kind ds =>
      Sem.varDecl (ds.map (declD n kind)) ctx
    | .funDecl f => Sem.funDecl f ctx
    | .classDecl c =>
      let ctx := Sem.inner ctx
      let nm := c.name.getD "default"
      let v ← evalClass n ctx c (some nm) (some (.str nm))
      initializeBinding ctx.lex nm v
      pure (.normal none)
    | .block body => Sem.block (lexicallyScoped body) (body.map fun s c => evalStmt n c s) ctx
    | .empty | .debugger => Sem.empty ctx
    | .ret e => Sem.ret (e.map fun e c => evalExpr n c e) ctx
    | .ifS t c a => Sem.ifS (evalExpr n · t) (evalStmt n · c) (a.map fun a c => evalStmt n c a) ctx
    | .whileS t body => Sem.whileS (evalExpr n · t) (evalStmt n · body) ctx
    | .doWhile body t => Sem.doWhile (evalStmt n · body) (evalExpr n · t) ctx
    | .forS init test update body => do
      let ctx := Sem.inner ctx
      let r ← evalFor n ctx init test update body labels
      pure (Sem.breakToNormal r)
    | .forIn lhs rhs body => do
      let ctx := Sem.inner ctx
      let r ← evalForIn n ctx lhs rhs body labels
      pure (Sem.breakToNormal r)
    | .forOf lhs rhs body isAwait => do
      let ctx := Sem.inner ctx
      let r ← evalForOf n ctx lhs rhs body isAwait labels
      pure (Sem.breakToNormal r)
    | .brk l => Sem.brk l ctx
    | .cont l => Sem.cont l ctx
    | .throw e => Sem.throw (evalExpr n · e) ctx
    | .tryS blk handler fin => evalTry n (Sem.inner ctx) blk handler fin
    | .switch disc cases =>
      -- spec: https://tc39.es/ecma262/#sec-switch-statement-runtime-semantics-evaluation
      let ctx := Sem.inner ctx
      let sv ← evalExpr n ctx disc
      let env ← newDeclEnv (some ctx.lex)
      blockDeclarationInstantiation (lexicallyScoped (caseBodies cases)) env ctx
      let needDispose := (usingKinds (lexicallyScoped (caseBodies cases))).1
      withDisposeScope needDispose { ctx with lex := env } fun cctx => do
        -- (CaseBlockEvaluation: the first selected case, in source order without the default,
        -- else the default; statements run from there to the end)
        let start ← M.foldArr (Array.range cases.size) none fun found i => do
          if found.isSome then return found
          match cases[i]! with
          | .mk (some t) _ =>
            let cv ← evalExpr n cctx t
            if isStrictlyEqual sv cv then return some i else return none
          | .mk none _ => return none
        let start := start <|> cases.findIdx? (fun c => match c with | .mk none _ => true | _ => false)
        let r ← match start with
          | none => pure (Compl.normal (some .undefined))
          | some st =>
            let r ← M.foldArr ((Array.range cases.size).extract st cases.size) (Compl.normal none) fun acc i => do
              match acc with
              | .normal v =>
                let .mk _ body := cases[i]!
                let r ← evalStmts n cctx body
                pure (r.updateEmpty v)
              | acc => pure acc
            pure (r.updateEmpty (some .undefined))
        pure (Sem.breakToNormal r)
    | .labeled l body =>
      let breakable := match body with
        | .labeled .. | .whileS .. | .doWhile .. | .forS .. | .forIn .. | .forOf .. | .switch .. => true
        | _ => false
      Sem.labeled l breakable (evalStmt n · body) ctx
    | .with obj body =>
      -- spec: https://tc39.es/ecma262/#sec-with-statement-runtime-semantics-evaluation
      let ctx := Sem.inner ctx
      let v ← evalExpr n ctx obj
      let o ← toObject v
      let env ← allocEnv (.object o true (some ctx.lex))
      let r ← evalStmt n { ctx with lex := env } body
      pure (r.updateEmpty (some .undefined))
    | .importDecl _ => pure (.normal none)
    | .exportDecl d =>
      let ctx := Sem.inner ctx
      match d with
      | .decl s => evalStmt n ctx s
      | .defaultFunc _ => pure (.normal none)
      | .defaultClass c =>
        let v ← evalClass n ctx c c.name (some (.str (c.name.getD "default")))
        initializeBinding ctx.lex (c.name.getD "*default*") v
        pure (.normal none)
      | .defaultExpr e =>
        let v ← if isAnonymousFn e then namedEval n ctx e (.str "default") else evalExpr n ctx e
        initializeBinding ctx.lex "*default*" v
        pure (.normal none)
      | _ => pure (.normal none)

/-- A declarator's denotation. -/
def declD : Nat → VarKind → VarDeclarator → Sem.CDecl
  | 0, _, _ => fun _ => tooDeep
  | n + 1, kind, .mk target init =>
    let rhs (x : JSStr) (ie : Expr) : Sem.CExpr :=
      if isAnonymousFn ie then (namedEval n · ie (.str x)) else (evalExpr n · ie)
    match kind, target, init with
    | .var, _, none => fun _ => pure ()
    | .var, .ident x, some ie => Sem.declVar x (rhs x ie)
    | .var, p, some ie => fun ctx => do
      let v ← evalExpr n ctx ie
      bindPattern n ctx p v (.init none)
    | k, .ident x, none => Sem.declLex k x none
    | k, .ident x, some ie => Sem.declLex k x (some (rhs x ie))
    | _, p, some ie => fun ctx => do
      let v ← evalExpr n ctx ie
      bindPattern n ctx p v (.init (some ctx.lex))
    | _, _, none => fun _ => pure ()

/-- A statement list: UpdateEmpty of each statement's completion with the last value.
spec: https://tc39.es/ecma262/#sec-block-runtime-semantics-evaluation -/
def evalStmts : Nat → Ctx → Array Stmt → M Compl
  | 0, _, _ => tooDeep
  | n + 1, ctx, ss => Sem.stmts (ss.map fun s c => evalStmt n c s) ctx

/-- ForLoopEvaluation and ForBodyEvaluation (with CreatePerIterationEnvironment).
spec: https://tc39.es/ecma262/#sec-forbodyevaluation -/
def evalFor : Nat → Ctx → Option ForInit → Option Expr → Option Expr → Stmt → Array JSStr → M Compl
  | 0, _, _, _, _, _, _ => tooDeep
  | n + 1, ctx, init, test, update, body, labels => do
    let needDispose := match init with
      | some (.decl k _) => k == .using || k == .awaitUsing
      | _ => false
    withDisposeScope needDispose ctx fun ctx => do
      -- (the loop's environment and its per-iteration bindings)
      let (lex, perIter) ← match init with
        | some (.decl k ds) =>
          if k == .var then
            let _ ← evalStmt n ctx (.varDecl .var ds)
            pure (ctx.lex, #[])
          else
            let loopEnv ← newDeclEnv (some ctx.lex)
            let names := ds.foldl (fun acc (d : VarDeclarator) => match d with | .mk p _ => acc ++ boundNames p) #[]
            let isConst := k == .const || k == .using || k == .awaitUsing
            M.forArr names fun dn => if isConst then createImmutableBinding loopEnv dn true else createMutableBinding loopEnv dn false
            let _ ← evalStmt n { ctx with lex := loopEnv } (.varDecl k ds)
            pure (loopEnv, if isConst then #[] else names)
        | some (.expr e) => let _ ← evalExpr n ctx e; pure (ctx.lex, #[])
        | none => pure (ctx.lex, #[])
      let perIteration (cur : EnvId) : M EnvId := do
        if perIter.isEmpty then return cur
        let outer ← readEnv cur Env.outer
        let env ← newDeclEnv outer
        M.forArr perIter fun bn => do
          createMutableBinding env bn false
          let v ← getBindingValue cur bn true
          initializeBinding env bn v
        pure env
      let lex ← perIteration lex
      M.repeatFrom (lex, Value.undefined) fun (lex, v) => do
        M.tick
        let ictx := { ctx with lex }
        if let some t := test then
          if !toBoolean (← evalExpr n ictx t) then return .inr (.normal (some v))
        let r ← evalStmt n ictx body
        if !loopContinues r labels then return .inr (r.updateEmpty (some v))
        let v := (r.value?).getD v
        let lex ← perIteration lex
        if let some u := update then let _ ← evalExpr n { ctx with lex } u
        return .inl (lex, v)

/-- The left side's binding for one iteration of for-in/of (ForIn/OfBodyEvaluation steps g-h). -/
def bindForLhs : Nat → Ctx → ForLhs → Value → M Ctx
  | 0, _, _, _ => tooDeep
  | n + 1, ctx, lhs, v => do
    match lhs with
    | .pattern p =>
      match p with
      | .obj .. | .arr .. => bindPattern n ctx p v .assign
      | .ident x => putRefValue (← resolveBinding ctx.lex x ctx.strict) v
      | .expr e => putRefValue (← evalTargetRef n ctx e) v
      pure ctx
    | .decl .var p _ =>
      match p with
      | .ident x => putRefValue (← resolveBinding ctx.lex x ctx.strict) v
      | p => bindPattern n ctx p v (.init none)
      pure ctx
    | .decl k p _ =>
      let env ← newDeclEnv (some ctx.lex)
      M.forArr (boundNames p) fun dn =>
        if k == .const || k == .using || k == .awaitUsing then createImmutableBinding env dn true
        else createMutableBinding env dn false
      let ctx' := { ctx with lex := env }
      bindPattern n ctx' p v (.init (some env))
      if k == .using || k == .awaitUsing then
        if let some cap := ctx.disposeCap then addDisposableResource cap v (k == .awaitUsing)
      pure ctx'

/-- ForIn/OfHeadEvaluation's expression (with a TDZ environment for lexical bindings). -/
def evalForHead : Nat → Ctx → ForLhs → Expr → M Value
  | 0, _, _, _ => tooDeep
  | n + 1, ctx, lhs, rhs => do
    match lhs with
    | .decl k p _ =>
      if k == .var then evalExpr n ctx rhs
      else
        let tdz ← newDeclEnv (some ctx.lex)
        M.forArr (boundNames p) fun dn => createMutableBinding tdz dn false
        evalExpr n { ctx with lex := tdz } rhs
    | _ => evalExpr n ctx rhs

/-- for-in. spec: https://tc39.es/ecma262/#sec-for-in-and-for-of-statements -/
def evalForIn : Nat → Ctx → ForLhs → Expr → Stmt → Array JSStr → M Compl
  | 0, _, _, _, _, _ => tooDeep
  | n + 1, ctx, lhs, rhs, body, labels => do
    -- (Annex B.3.5: `for (var x = init in o)`)
    if let .decl .var (.ident x) (some ie) := lhs then
      let v ← if isAnonymousFn ie then namedEval n ctx ie (.str x) else evalExpr n ctx ie
      putRefValue (← resolveBinding ctx.lex x ctx.strict) v
    let ov ← evalForHead n ctx lhs rhs
    if ov.isNullish then return .brk none none
    let o ← toObject ov
    -- EnumerateObjectProperties as %ForInIteratorPrototype%.next does it
    -- spec: https://tc39.es/ecma262/#sec-%foriniteratorprototype%.next
    let st : (Value × HashSet PropKey × Array PropKey × Nat × Bool × Value) :=
      (.obj o, {}, #[], 0, false, .undefined)
    M.repeatFrom st fun (cur, visited, keys, i, wasVisited, v) => do
      M.tick
      let .obj co := cur | return .inr (.normal (some v))
      if !wasVisited then
        let ks ← Obj'.ownPropertyKeys co
        let ks := ks.filter fun k => match k with | .str _ => true | _ => false
        return .inl (cur, visited, ks, 0, true, v)
      if h : i < keys.size then
        let k := keys[i]
        if visited.contains k then return .inl (cur, visited, keys, i + 1, true, v)
        match ← Obj'.getOwnProperty co k with
        | none => return .inl (cur, visited, keys, i + 1, true, v)
        | some p =>
          let visited := visited.insert k
          if !p.enumerable then return .inl (cur, visited, keys, i + 1, true, v)
          let .str ks := k | return .inl (cur, visited, keys, i + 1, true, v)
          let ictx ← bindForLhs n ctx lhs (.str ks)
          let r ← evalStmt n ictx body
          if !loopContinues r labels then return .inr (r.updateEmpty (some v))
          return .inl (cur, visited, keys, i + 1, true, (r.value?).getD v)
      else
        let p ← Obj'.getPrototypeOf co
        return .inl (p, visited, #[], 0, false, v)

/-- for-of / for-await-of. spec: https://tc39.es/ecma262/#sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset -/
def evalForOf : Nat → Ctx → ForLhs → Expr → Stmt → Bool → Array JSStr → M Compl
  | 0, _, _, _, _, _, _ => tooDeep
  | n + 1, ctx, lhs, rhs, body, isAwait, labels => do
    let ov ← evalForHead n ctx lhs rhs
    let r ← if isAwait then getAsyncIterator ov else getIterator ov
    let close : M Unit := if isAwait then asyncIteratorClose r else iteratorClose r
    M.repeatFrom Value.undefined fun v => do
      M.tick
      let res ← call r.next r.iter #[]
      let res ← if isAwait then do let x ← await res; restoreCtx ctx; pure x else pure res
      if !res.isObject then throwType "Iterator result is not an object"
      if ← iteratorComplete res then return .inr (.normal (some v))
      let x ← iteratorValue res
      -- (an abrupt binding or body closes the iterator; a generator return too)
      let usingLhs := match lhs with
        | .decl k _ _ => k == .using || k == .awaitUsing
        | _ => false
      let step ← M.attempt do
        withDisposeScope usingLhs ctx fun ctx => do
          let ictx ← bindForLhs n ctx lhs x
          evalStmt n ictx body
      match step with
      | .error e =>
        if isSentinel e WK.genReturn then close; M.throwV e
        else if isAwait then asyncIteratorCloseOnThrow r e
        else iteratorCloseOnThrow r e
      | .ok r' =>
        if loopContinues r' labels then return .inl ((r'.value?).getD v)
        close
        return .inr (r'.updateEmpty (some v))

/-- try statements. spec: https://tc39.es/ecma262/#sec-try-statement-runtime-semantics-evaluation -/
def evalTry : Nat → Ctx → Array Stmt → Option CatchClause → Option (Array Stmt) → M Compl
  | 0, _, _, _, _ => tooDeep
  | n + 1, ctx, blk, handler, fin => do
    let b ← M.attempt (evalStmt n ctx (.block blk))
    -- catch
    let c ← match b, handler with
      | .error e, some (.mk param body) =>
        if isSentinel e WK.genReturn then pure b
        else M.attempt do
          -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-catchclauseevaluation
          match param with
          | none => evalStmt n ctx (.block body)
          | some p =>
            let env ← newDeclEnv (some ctx.lex)
            M.forArr (boundNames p) fun nm => createMutableBinding env nm false
            let cctx := { ctx with lex := env }
            bindPattern n cctx p e (.init (some env))
            evalStmt n cctx (.block body)
      | b, _ => pure b
    match fin with
    | none => match c with
      | .ok r => pure (r.updateEmpty (some .undefined))
      | .error e => M.throwV e
    | some f =>
      let fr ← evalStmt n ctx (.block f)
      match fr with
      | .normal _ => match c with
        | .ok r => pure (r.updateEmpty (some .undefined))
        | .error e => M.throwV e
      | fr => pure (fr.updateEmpty (some .undefined))

-- Function bodies

/-- FunctionDeclarationInstantiation, then the body. Returns the body's return value (normal
completion: undefined). `env` is the function's environment (from PrepareForOrdinaryCall).
spec: https://tc39.es/ecma262/#sec-functiondeclarationinstantiation -/
def functionDeclarationInstantiation : Nat → ObjId → FuncData → EnvId → Array Value → M Ctx
  | 0, _, _, _, _ => tooDeep
  | n + 1, f, d, env, args => do
    let code := d.code
    let strict := code.strict
    let formals := code.params
    -- 5.
    let paramNames := formals.foldl (fun acc (p : Param) => match p with | .mk t _ _ => acc ++ boundNames t) #[]
    -- 6-8.
    let hasDuplicates := (paramNames.foldl (fun (acc : HashSet JSStr × Bool) nm =>
      (acc.1.insert nm, acc.2 || acc.1.contains nm)) ({}, false)).2
    let simple := code.info.simpleParams
    let hasParamExprs := code.info.paramsHaveExpressions
    let body := match code.body with | .stmts b => b | .expr _ => #[]
    -- 9-11.
    let varDecls := topLevelVarScoped body
    let varNames := varDecls.foldl (fun (acc : Array JSStr) dd => acc ++ dd.names) #[]
    let lexDecls := topLevelLexicallyScoped body
    let lexNames := lexDecls.foldl (fun (acc : Array JSStr) dd => acc ++ dd.names) #[]
    -- 12-14.
    let (functionNames, functionsToInit) := varDecls.reverse.foldl (fun (names, fs) dd =>
      match dd with
      | .func fn => match fn.name with
        | some nm => if names.contains nm then (names, fs) else (#[nm] ++ names, #[fn] ++ fs)
        | none => (names, fs)
      | .pat _ => (names, fs)) ((#[] : Array JSStr), (#[] : Array Func))
    -- 15-18.
    let argumentsNeeded :=
      d.thisMode != .lexical && !paramNames.contains "arguments" &&
      !(!hasParamExprs && (functionNames.contains "arguments" || lexNames.contains "arguments"))
    let argumentsNeeded := argumentsNeeded && code.kind != .classField && code.kind != .classStaticBlock
    -- 19-20.
    let paramEnv ← if strict || !hasParamExprs then pure env else newDeclEnv (some env)
    -- 21.
    M.forArr paramNames fun pn => do
      if !(← hasBinding paramEnv pn) then
        createMutableBinding paramEnv pn false
        if hasDuplicates then initializeBinding paramEnv pn .undefined
    -- 22-23.
    let paramBindings ← if argumentsNeeded then do
        let ao ← if strict || !simple then createUnmappedArguments args
          else createMappedArguments f paramNames args paramEnv
        if strict then createImmutableBinding paramEnv "arguments" false
        else createMutableBinding paramEnv "arguments" false
        initializeBinding paramEnv "arguments" (.obj ao)
        pure (paramNames.push "arguments")
      else pure paramNames
    -- 24-25. IteratorBindingInitialization of the formals over the arguments list
    let pctx : Ctx := {
      lex := paramEnv, var := env, priv := d.privEnv, strict := strict, fn := some f,
      realm := d.realm, script := d.script, isAsync := code.isAsync }
    let mode : BindMode := if hasDuplicates then .init none else .init (some paramEnv)
    M.forArr (Array.range formals.size) fun i => do
      let .mk target init rest := formals[i]!
      if rest then
        let xs ← createArrayFromList (args.extract i args.size)
        bindPattern n pctx target xs mode
      else
        bindElement n pctx target init mode (pure (args[i]?.getD .undefined))
    -- 26-27.
    let varEnv ← if !hasParamExprs then do
        M.forArr varNames fun vn => do
          if !(paramBindings.contains vn) && !(← hasBinding paramEnv vn) then
            createMutableBinding paramEnv vn false
            initializeBinding paramEnv vn .undefined
        pure paramEnv
      else do
        let varEnv ← newDeclEnv (some paramEnv)
        M.forArr varNames fun vn => do
          if !(← hasBinding varEnv vn) then
            createMutableBinding varEnv vn false
            let iv ← if !(paramBindings.contains vn) || functionNames.contains vn then pure .undefined
              else getBindingValue paramEnv vn false
            initializeBinding varEnv vn iv
        pure varEnv
    -- 28. (Annex B.3.2.1)
    let annexB := if strict then #[] else annexBFunctions body (paramNames ++ lexNames)
    M.forArr annexB fun af => do
      let some fname := af.name | pure ()
      if fname != JSStr.ofString "arguments" && !(← hasBinding varEnv fname) then
        createMutableBinding varEnv fname false
        initializeBinding varEnv fname .undefined
    -- 29-30.
    let lexEnv ← if !strict then newDeclEnv (some varEnv) else pure varEnv
    -- 31-32.
    M.forArr lexDecls fun dd => M.forArr dd.names fun dn =>
      if dd.isConstant then createImmutableBinding lexEnv dn true else createMutableBinding lexEnv dn false
    let ctx : Ctx := {
      pctx with lex := lexEnv, var := varEnv, annexB := funcIds annexB }
    -- 34.
    M.forArr functionsToInit fun fn => do
      let fo ← instantiateFunction fn lexEnv d.privEnv ctx (funcNameKey fn)
      setMutableBinding varEnv (fn.name.getD "default") (.obj fo) false
    pure ctx

/-- Evaluates a function's body after FunctionDeclarationInstantiation; the return value
(`undefined` for a normal completion). -/
def evalFunctionBody : Nat → ObjId → FuncData → EnvId → Array Value → M Value
  | 0, _, _, _, _ => tooDeep
  | n + 1, f, d, env, args => do
    let ctx ← functionDeclarationInstantiation n f d env args
    match d.code.body with
    | .expr e =>
      match d.code.kind, d.fieldName with
      | .classField, some (.key k) => if isAnonymousFn e then namedEval n ctx e k else evalExpr n ctx e
      | .classField, some (.priv id) =>
        if isAnonymousFn e then
          let desc ← readS fun s => (s.privNames[id]?).getD JSStr.empty
          namedEval n ctx e (.str (JSStr.ofString "#" ++ desc))
        else evalExpr n ctx e
      | _, _ => evalExpr n ctx e
    | .stmts body =>
      let r ← withDisposeScope (usingKinds (topLevelLexicallyScoped body)).1 ctx fun c => evalStmts n c body
      match r with
      | .ret v => pure v
      | _ => pure .undefined

/-- The body of a generator or async function, run by the driver when the coroutine starts. -/
def evalCoroutineBody : Nat → ObjId → FuncData → EnvId → EnvId → ObjId → M Value
  | 0, _, _, _, _, _ => tooDeep
  | n + 1, f, d, lexEnv, varEnv, co => do
    let body := match d.code.body with | .stmts b => b | .expr _ => #[]
    let paramNames := d.code.params.foldl (fun acc (p : Param) => match p with | .mk t _ _ => acc ++ boundNames t) #[]
    let lexNames := (topLevelLexicallyScoped body).foldl (fun (acc : Array JSStr) dd => acc ++ dd.names) #[]
    let annexB := if d.code.strict then #[] else annexBFunctions body (paramNames ++ lexNames)
    let ctx : Ctx := {
      lex := lexEnv, var := varEnv, priv := d.privEnv, strict := d.code.strict,
      fn := some f, realm := d.realm, script := d.script, annexB := funcIds annexB,
      isAsync := d.code.isAsync, isGen := d.code.isGenerator, gen := some co }
    match d.code.body with
    | .expr e => evalExpr n ctx e
    | .stmts body =>
      let r ← withDisposeScope (usingKinds (topLevelLexicallyScoped body)).1 ctx fun c => evalStmts n c body
      match r with
      | .ret v => pure v
      | _ => pure .undefined

end

end ES
