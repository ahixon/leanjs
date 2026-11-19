import ES.Interp

/-!
# The driver: calls, constructs, coroutines, scripts, jobs

The driver answers the requests computations make (`Res.req`): [[Call]] and [[Construct]] of
every kind of function object, resuming generators and async functions (whose continuations it
keeps, `Conts`), and the setup of an `await`. Its recursion is structural on the call depth `d`:
a call runs its function one level deeper; at depth 0 a call throws a RangeError (as engines do
on stack overflow). Continuations are heap closures, so the C stack holds a few frames per JS
call level, not the evaluation's.
-/

namespace ES

open ES (F64)
open Std (HashMap)

/-- Suspended coroutine bodies by coroutine object id. -/
abbrev Conts := HashMap ObjId (Outcome → State → Res Value)

/-- The call depth limit (nested JS calls). -/
def callDepth : Nat := 4000

/-- The engine's built-in behaviours, by id. -/
structure Engine where
  builtins : Array BuiltinFn

/-! ## [[Call]] and [[Construct]] -/

/-- OrdinaryCallBindThis spec: https://tc39.es/ecma262/#sec-ordinarycallbindthis -/
def ordinaryCallBindThis (d : FuncData) (env : EnvId) (thisArg : Value) : M Unit := do
  if d.thisMode == .lexical then return
  let thisValue ← if d.thisMode == .strict then pure thisArg
    else if thisArg.isNullish then do
      let ge ← readS fun s => (s.realms[d.realm]!).globalEnv
      readEnv ge fun e => match e with | .global _ _ tv => tv | _ => .undefined
    else pure (Value.obj (← toObject thisArg))
  bindThisValue env thisValue

/-- Runs `body` in the realm/script of a function and restores the caller's afterwards. -/
def inCallee {α} (realm script : Nat) (body : M α) : M α := do
  let (r0, s0) ← readS fun s => (s.realm, s.script)
  modify fun s => { s with realm, script }
  let r ← M.attempt body
  modify fun s => { s with realm := r0, script := s0 }
  match r with
  | .ok v => pure v
  | .error e => M.throwV e

/-- The [[Call]] of an ECMAScript function object.
spec: https://tc39.es/ecma262/#sec-ecmascript-function-objects-call-thisargument-argumentslist -/
def callECMA (f : ObjId) (d : FuncData) (thisArg : Value) (args : Array Value) : M Value := do
  -- 2.
  if d.isClassCtor then
    inCallee d.realm d.script (throwType "Class constructor cannot be invoked without 'new'")
  inCallee d.realm d.script do
    -- 3-4.
    let env ← newFunctionEnv f d .undefined
    ordinaryCallBindThis d env thisArg
    let code := d.code
    match code.isAsync, code.isGenerator with
    | false, false => evalFunctionBody evalDepth f d env args
    | false, true =>
      -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-evaluategeneratorbody
      let ctx ← functionDeclarationInstantiation evalDepth f d env args
      let g ← ordinaryCreateFromConstructor (.obj f) "%GeneratorFunction.prototype.prototype%"
        (.coroutine .suspendedStart f ctx.lex ctx.var false true #[])
      pure (.obj g)
    | true, false =>
      -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-evaluateasyncfunctionbody
      let cap ← newIntrinsicPromise
      match ← M.attempt (functionDeclarationInstantiation evalDepth f d env args) with
      | .error e => let _ ← call cap.reject .undefined #[e]
      | .ok ctx =>
        -- AsyncFunctionStart: the body runs now, until its first await
        let kd : Kind := .coroutine .suspendedStart f ctx.lex ctx.var true false
          #[cap.promise, cap.resolve, cap.reject]
        let co ← alloc { kind := kd }
        let _ ← M.request (.resume co (.normal .undefined))
      pure cap.promise
    | true, true =>
      -- spec: https://tc39.es/ecma262/#sec-runtime-semantics-evaluateasyncgeneratorbody
      let ctx ← functionDeclarationInstantiation evalDepth f d env args
      let q ← alloc { kind := .internal "AsyncGeneratorQueue" #[] }
      let g ← ordinaryCreateFromConstructor (.obj f) "%AsyncGeneratorFunction.prototype.prototype%"
        (.coroutine .suspendedStart f ctx.lex ctx.var true true #[.obj q])
      pure (.obj g)

/-- The [[Construct]] of an ECMAScript function object.
spec: https://tc39.es/ecma262/#sec-ecmascript-function-objects-construct-argumentslist-newtarget -/
def constructECMA (f : ObjId) (d : FuncData) (args : Array Value) (newTarget : Value) : M Value := do
  if d.isDefaultCtor then
    -- (the default constructor's built-in steps, ClassDefinitionEvaluation 14.a)
    return ← inCallee d.realm d.script do
      let result ← if d.derived then do
          let func ← Obj'.getPrototypeOf f
          if !(← isConstructor func) then throwType "Super constructor is not a constructor"
          construct func args (some newTarget)
        else pure (.obj (← ordinaryCreateFromConstructor newTarget "%Object.prototype%"))
      initializeInstanceElements result f
      pure result
  -- 3.
  let thisArgument ← if d.derived then pure none
    else pure (some (← inCallee d.realm d.script (ordinaryCreateFromConstructor newTarget "%Object.prototype%")))
  let (rv, env) ← inCallee d.realm d.script do
    let env ← newFunctionEnv f d newTarget
    -- 6.
    if let some t := thisArgument then
      ordinaryCallBindThis d env (.obj t)
      initializeInstanceElements (.obj t) f
    -- 8.
    let rv ← evalFunctionBody evalDepth f d env args
    pure (rv, env)
  -- (9: the caller's context is restored: the errors below are the caller realm's)
  -- 10-11. (a body without `return` gives undefined, treated like `return;`)
  if rv.isObject then return rv
  if let some t := thisArgument then return .obj t
  if !rv.isUndefined then throwType "Derived constructors may only return object or undefined"
  -- 12.
  resolveThisBinding env

/-- [[Call]] of any function object (Call(F, V, args) step 2 included). -/
def callImpl (eng : Engine) (f thisV : Value) (args : Array Value) : M Value := do
  M.tick
  let .obj fo := f | throwType "is not a function"
  match ← objKind fo with
  | .func d => callECMA fo d thisV args
  | .builtin b =>
    match eng.builtins[b.id]? with
    | some fn => inCallee b.realm (← readS (·.script)) (fn fo thisV args .undefined)
    | none => M.halt "internal: unknown built-in"
  | .bound t bthis bargs =>
    -- spec: https://tc39.es/ecma262/#sec-bound-function-exotic-objects-call-thisargument-argumentslist
    call (.obj t) bthis (bargs ++ args)
  | .proxy .. =>
    -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-call-thisargument-argumentslist
    let (target, handler) ← proxyParts fo
    match ← getMethodOf (.obj handler) (.str "apply") with
    | none => call (.obj target) thisV args
    | some trap =>
      let arr ← createArrayFromList args
      call trap (.obj handler) #[.obj target, thisV, arr]
  | _ => throwType "is not a function"

/-- [[Construct]] of any constructor. -/
def constructImpl (eng : Engine) (f : Value) (args : Array Value) (newTarget : Value) : M Value := do
  M.tick
  let .obj fo := f | throwType "is not a constructor"
  match ← objKind fo with
  | .func d => constructECMA fo d args newTarget
  | .builtin b =>
    if !b.isCtor then throwType "is not a constructor"
    match eng.builtins[b.id]? with
    | some fn => inCallee b.realm (← readS (·.script)) (fn fo .undefined args newTarget)
    | none => M.halt "internal: unknown built-in"
  | .bound t _ bargs =>
    -- spec: https://tc39.es/ecma262/#sec-bound-function-exotic-objects-construct-argumentslist-newtarget
    let nt := if sameValue f newTarget then Value.obj t else newTarget
    construct (.obj t) (bargs ++ args) (some nt)
  | .proxy .. =>
    -- spec: https://tc39.es/ecma262/#sec-proxy-object-internal-methods-and-internal-slots-construct-argumentslist-newtarget
    let (target, handler) ← proxyParts fo
    match ← getMethodOf (.obj handler) (.str "construct") with
    | none => construct (.obj target) args (some newTarget)
    | some trap =>
      let arr ← createArrayFromList args
      let r ← call trap (.obj handler) #[.obj target, arr, newTarget]
      if !r.isObject then throwType "proxy [[Construct]] must return an object"
      pure r
  | _ => throwType "is not a constructor"

/-! ## Coroutines -/

/-- Starts a coroutine's body (the first resume). -/
def startCoroutine (co : ObjId) : M Value := do
  let .coroutine _ f lexEnv varEnv isAsync isGen slots ← objKind co | M.halt "internal: not a coroutine"
  let some d ← funcData? f | M.halt "internal: coroutine without function"
  modify fun s => { s with realm := d.realm, script := d.script }
  match isAsync, isGen with
  | false, true =>
    -- (GeneratorStart's body: the completion becomes a done iterator result; a `return`
    -- request unwinds as WK.genReturn)
    let r ← M.attempt (evalCoroutineBody evalDepth f d lexEnv varEnv co)
    match r with
    | .ok v => createIterResult v true
    | .error e =>
      if isSentinel e WK.genReturn then createIterResult (← readS (·.genReturn)) true
      else M.throwV e
  | true, false =>
    -- (AsyncBlockStart: resolve or reject the function's promise)
    let r ← M.attempt (evalCoroutineBody evalDepth f d lexEnv varEnv co)
    match r with
    | .ok v => let _ ← call slots[1]! .undefined #[v]
    | .error e => let _ ← call slots[2]! .undefined #[e]
    pure .undefined
  | true, true =>
    -- (AsyncGeneratorStart's completion steps)
    let r ← M.attempt (evalCoroutineBody evalDepth f d lexEnv varEnv co)
    agSetState co .drainingQueue
    match r with
    | .ok v => agCompleteStep co false v true
    | .error e =>
      if isSentinel e WK.genReturn then agCompleteStep co false (← readS (·.genReturn)) true
      else agCompleteStep co true e true
    agDrainQueue co
    pure .undefined
  | _, _ => M.halt "internal: not a coroutine body"

/-- An await's reactions: resume the coroutine with the settled value or reason.
spec: https://tc39.es/ecma262/#await (steps 2-9) -/
def awaitSetup (co : ObjId) (v : Value) : M Unit := do
  let pc ← intrinsicV "%Promise%"
  let promise ← promiseResolve pc v
  let onF ← makeBuiltinFn "AwaitResume" 1 JSStr.empty #[.obj co, .bool false]
  let onR ← makeBuiltinFn "AwaitResume" 1 JSStr.empty #[.obj co, .bool true]
  let .obj p := promise | M.halt "internal: PromiseResolve gave a non-object"
  let _ ← performPromiseThen p (.obj onF) (.obj onR) none

/-- The AwaitResume closures: resume the coroutine. -/
def awaitResume : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let .obj co := s[0]! | M.halt "internal: AwaitResume slots"
  let o := if toBoolean s[1]! then Outcome.throw (arg args 0) else .normal (arg args 0)
  let _ ← M.request (.resume co o)
  pure .undefined

/-! ## The driver -/

/-- The result of running a nested call: its outcome, or a halt. -/
def outcomeOf : Res Value → Sum (Outcome × State) (String × State)
  | .ok v s => .inl (.normal v, s)
  | .err e s => .inl (.throw e, s)
  | .halt m s => .inr (m, s)
  | .req _ s _ => .inr ("internal: a suspension escaped a function call", s)

/-- Answers the requests of `r` with `sub` running nested computations one call level deeper
(`canCall = false`: at the depth limit, calls throw RangeError). Structural on `r`. -/
def driveWith (eng : Engine) (canCall : Bool)
    (sub : ∀ {β : Type}, Res β → Conts → Res β × Conts) {α : Type} : Res α → Conts → Res α × Conts
  | .ok a s, cs => (.ok a s, cs)
  | .err e s, cs => (.err e s, cs)
  | .halt m s, cs => (.halt m s, cs)
  | .req r s k, cs =>
    let overflow (_ : Unit) : Res α × Conts :=
      match makeError .rangeError "Maximum call stack size exceeded" s with
      | .ok e s' => driveWith eng canCall sub (k (.throw e) s') cs
      | _ => (.halt "internal: could not create RangeError" s, cs)
    match r with
    | .call f t args =>
      if !canCall then overflow () else
      let (r', cs) := sub (callImpl eng f t args s) cs
      match outcomeOf r' with
      | .inl (o, s') => driveWith eng canCall sub (k o s') cs
      | .inr (m, s') => (.halt m s', cs)
    | .construct f args nt =>
      if !canCall then overflow () else
      let (r', cs) := sub (constructImpl eng f args nt s) cs
      match outcomeOf r' with
      | .inl (o, s') => driveWith eng canCall sub (k o s') cs
      | .inr (m, s') => (.halt m s', cs)
    | .resume co o =>
      if !canCall then overflow () else
      let r0 : Res Value := match cs.get? co with
        | some c => c o s
        | none => startCoroutine co s
      let cs := cs.erase co
      let (r', cs) := sub r0 cs
      match r' with
      | .ok v s' => driveWith eng canCall sub (k (.ret v) s') cs
      | .err e s' => driveWith eng canCall sub (k (.throw e) s') cs
      | .halt m s' => (.halt m s', cs)
      | .req (.yield v) s' kc => driveWith eng canCall sub (k (.normal v) s') (cs.insert co kc)
      | .req (.await v) s' kc =>
        let cs := cs.insert co kc
        let (r2, cs) := sub (awaitSetup co v s') cs
        match r2 with
        | .ok _ s2 => driveWith eng canCall sub (k (.normal .undefined) s2) cs
        | .err _ s2 => (.halt "await on a value whose PromiseResolve throws is not implemented" s2, cs)
        | .halt m s2 => (.halt m s2, cs)
        | .req _ s2 _ => (.halt "internal: request escaped" s2, cs)
      | .req _ s' _ => (.halt "internal: request escaped a coroutine" s', cs)
    | .yield _ | .await _ => (.req r s k, cs)

/-- Runs `r` to completion (or to a suspension of the coroutine it belongs to) with `d` levels
of calls available. -/
def drive (eng : Engine) : Nat → {α : Type} → Res α → Conts → Res α × Conts
  | 0, _, r, cs => driveWith eng false (fun r cs => (r, cs)) r cs
  | d + 1, _, r, cs => driveWith eng true (drive eng d) r cs

/-! ## Scripts -/

/-- GlobalDeclarationInstantiation spec: https://tc39.es/ecma262/#sec-globaldeclarationinstantiation -/
def globalDeclarationInstantiation (body : Array Stmt) (env : EnvId) (g : ObjId) (ctx : Ctx) : M Ctx := do
  let lexDecls := topLevelLexicallyScoped body
  let lexNames := lexDecls.foldl (fun (acc : Array JSStr) d => acc ++ d.names) #[]
  let varDecls := topLevelVarScoped body
  let varNames := varDecls.foldl (fun (acc : Array JSStr) d => acc ++ d.names) #[]
  -- 3.
  M.forArr lexNames fun nm => do
    if ← globalDeclRecHas env nm then throwError .syntaxError s!"Identifier '{nm}' has already been declared"
    if ← hasRestrictedGlobalProperty g nm then throwError .syntaxError s!"Identifier '{nm}' has already been declared"
  -- 4.
  M.forArr varNames fun nm => do
    if ← globalDeclRecHas env nm then throwError .syntaxError s!"Identifier '{nm}' has already been declared"
  -- 5-8.
  let (fnNames, fnsToInit) ← M.foldArr varDecls.reverse ((#[] : Array JSStr), (#[] : Array Func)) fun (names, fs) d => do
    match d with
    | .func f =>
      let nm := f.name.getD "default"
      if names.contains nm then return (names, fs)
      if !(← canDeclareGlobalFunction g nm) then throwType s!"Cannot declare global function {nm}"
      return (names.push nm, #[f] ++ fs)
    | .pat _ => return (names, fs)
  -- 9-10.
  let declaredVarNames ← M.foldArr varDecls #[] fun acc d => do
    match d with
    | .pat p => M.foldArr (boundNames p) acc fun acc vn => do
      if fnNames.contains vn then return acc
      if !(← canDeclareGlobalVar g vn) then throwType s!"Cannot declare global variable {vn}"
      return if acc.contains vn then acc else acc.push vn
    | .func _ => return acc
  -- 12. (Annex B.3.2.2)
  let candidates := if ctx.strict then #[] else annexBFunctions body lexNames
  let annexB ← M.foldArr candidates #[] fun acc f => do
    let nm := f.name.getD "default"
    if ← globalDeclRecHas env nm then return acc
    if !(← canDeclareGlobalVar g nm) then return acc
    if !(fnNames.contains nm || declaredVarNames.contains nm || acc.any (·.name == some nm)) then
      createGlobalVarBinding g nm false
    return acc.push f
  -- 15.
  M.forArr lexDecls fun d => M.forArr d.names fun dn =>
    if d.isConstant then createImmutableBinding env dn true else createMutableBinding env dn false
  let ctx := { ctx with annexB := funcIds annexB }
  -- 16.
  M.forArr fnsToInit fun f => do
    let fo ← instantiateFunction f env #[] ctx (funcNameKey f)
    createGlobalFunctionBinding g (f.name.getD "default") (.obj fo) false
  -- 17.
  M.forArr declaredVarNames fun vn => createGlobalVarBinding g vn false
  pure ctx

/-- ScriptEvaluation: the completion value of a parsed script in the current realm.
spec: https://tc39.es/ecma262/#sec-runtime-semantics-scriptevaluation -/
def scriptEvaluation (prog : Program) (path : String := "") : M Value := do
  let (script, realmIdx, rl) ← readS fun s => (s.scripts.size, s.realm, s.curRealm)
  modify fun s => { s with scripts := s.scripts.push { prog, realm := s.realm, path }, script }
  let ctx : Ctx := {
    lex := rl.globalEnv, var := rl.globalEnv, strict := prog.strict, realm := realmIdx, script := script }
  let ctx ← globalDeclarationInstantiation prog.body rl.globalEnv rl.globalObj ctx
  match ← evalStmts evalDepth ctx prog.body with
  | .normal v => pure (v.getD .undefined)
  | .ret v => pure v
  | _ => pure .undefined

/-- Runs a computation to completion: its requests answered, no suspension left. -/
def runM {α} (eng : Engine) (m : M α) (s : State) (cs : Conts) : Res α × Conts :=
  drive eng callDepth (m s) cs

/-- Runs the job queue until empty (or a halt). Each job is a call; a job's throw is reported
(HostReportErrors) and does not stop the queue. -/
def runJobs (eng : Engine) (s : State) (cs : Conts) : Except String State × Conts :=
  let rec go : Nat → State → Conts → Except String State × Conts
    | 0, s, cs => (.error "out of fuel (jobs)", cs)
    | k + 1, s, cs =>
      if h : s.jobHead < s.jobs.size then
        let (f, args) := s.jobs[s.jobHead]
        let s := { s with jobHead := s.jobHead + 1 }
        match runM eng (call f .undefined args) s cs with
        | (.ok _ s, cs) => go k s cs
        | (.err e s, cs) =>
          let msg := match e with | .str m => m.toString | _ => "uncaught exception in a job"
          let s := { s with output := s.output.push s!"Uncaught (in job): {msg}" }
          go k s cs
        | (.halt m _, cs) => (.error m, cs)
        | (.req _ s _, cs) => go k s cs
      else
        let s := { s with jobs := #[], jobHead := 0 }
        (.ok s, cs)
  go s.fuel s cs

def interpBuiltins : Array BuiltinDef := #[⟨"AwaitResume", awaitResume⟩]

end ES
