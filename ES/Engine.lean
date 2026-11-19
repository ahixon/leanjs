import ES.Builtins.Core
import ES.Module
import ES.Builtins.Text
import ES.Builtins.Collections
import ES.Builtins.Library

/-!
# The engine: the table of built-in behaviours, realms, sessions

`Session` is a running engine (state + suspended coroutines): `newSession` creates the first
realm; `runScript` parses and evaluates a script, then runs the job queue.
-/

namespace ES

open ES (F64)

/-! ## Behaviours that parse code (eval, the Function constructors) -/

/-- The context an indirect eval or a dynamic function runs in: the current realm's global
environment. -/
def globalCtx : M Ctx := do
  let (ge, realm, script) ← readS fun s => (s.curRealm.globalEnv, s.realm, s.script)
  pure { lex := ge, var := ge, strict := false, realm, script }

/-- %eval%(x): an indirect eval. spec: https://tc39.es/ecma262/#sec-eval-x -/
def evalBuiltin : BuiltinFn := fun _ _ args _ => do
  performEval evalDepth (← globalCtx) (arg args 0) false

/-- CreateDynamicFunction spec: https://tc39.es/ecma262/#sec-createdynamicfunction -/
def createDynamicFunction (ctor : ObjId) (nt : Value) (kind : DynFnKind) (args : Array Value) : M Value := do
  -- 1.
  let nt := if nt.isUndefined then Value.obj ctor else nt
  -- 2-5.
  let fallback := match kind with
    | .normal => "%Function.prototype%" | .generator => "%GeneratorFunction.prototype%"
    | .async => "%AsyncFunction.prototype%" | .asyncGenerator => "%AsyncGeneratorFunction.prototype%"
  -- 6-12.
  let argCount := args.size
  let paramStrings ← M.mapArr (args.extract 0 (argCount - min 1 argCount)) toStr
  let bodyString ← if argCount == 0 then pure JSStr.empty else toStr args[argCount - 1]!
  let P := JSStr.join paramStrings (JSStr.ofString ",")
  -- 13-27.
  let (code, source) ← match parseDynamicFunction P.toString bodyString.toString kind with
    | .ok r => pure r
    | .error e => throwError .syntaxError e.msg
  -- 28.
  let proto ← getPrototypeFromConstructor nt fallback
  -- 29-31. (the function's source is a script record of its own: its template sites are its own)
  let ctx ← globalCtx
  let script ← readS (·.scripts.size)
  let prog : Program := { body := #[], isModule := false, strict := code.strict, source }
  modify fun s => { s with scripts := s.scripts.push { prog, realm := s.realm } }
  let ctx := { ctx with script }
  let f ← ordinaryFunctionCreate proto code ctx.lex #[] ctx false
  modifyObj f fun o => o.withKind fun k => match k with
    | .func d => .func { d with source }
    | k => k
  -- 32.
  setFunctionName f (.str "anonymous")
  -- 33-35.
  match kind with
  | .generator | .asyncGenerator => makeGeneratorPrototype f (kind == .asyncGenerator)
  | .normal => makeConstructor f
  | .async => pure ()
  pure (.obj f)

def functionCtor (kind : DynFnKind) : BuiltinFn := fun self _ args nt => createDynamicFunction self nt kind args

def engineBuiltins : Array BuiltinDef := #[
  ⟨"AsyncDisposeFromSync", asyncDisposeFromSync⟩,
  ⟨"eval", evalBuiltin⟩,
  ⟨"Function", functionCtor .normal⟩, ⟨"GeneratorFunction", functionCtor .generator⟩,
  ⟨"AsyncFunction", functionCtor .async⟩, ⟨"AsyncGeneratorFunction", functionCtor .asyncGenerator⟩]

def engineSetup : M Unit := do
  let fp ← intrinsic "%Function.prototype%"
  let (fc, _) ← defConstructor "Function" 1 "Function" fp
  let _ := fc
  for (nm, protoName) in [("GeneratorFunction", "%GeneratorFunction.prototype%"),
      ("AsyncFunction", "%AsyncFunction.prototype%"),
      ("AsyncGeneratorFunction", "%AsyncGeneratorFunction.prototype%")] do
    let p ← intrinsic protoName
    let c ← makeBuiltinFn nm 1 (JSStr.ofString nm) #[] true
    modifyObj c fun o => { o with proto := .obj fc }
    setOwn c (.str kPrototype) (.data (.obj p) false false false)
    setOwn p (.str kConstructor) (.data (.obj c) false false true)
    regIntrinsic s!"%{nm}%" c
  -- (hidden built-ins the interpreter calls for import() and import.meta)
  regIntrinsic "%DynamicImport%" (← makeBuiltinFn "%DynamicImport%" 2 JSStr.empty)
  regIntrinsic "%ImportMeta%" (← makeBuiltinFn "%ImportMeta%" 0 JSStr.empty)
  -- async generators and async iteration
  let agp ← intrinsic "%AsyncGeneratorPrototype%"
  for (nm, len) in [("next", 1), ("return", 1), ("throw", 1)] do
    let _ ← defMethod agp (.str (JSStr.ofString nm)) s!"AsyncGenerator.prototype.{nm}" len
  let aip ← intrinsic "%AsyncIteratorPrototype%"
  if !(← hasOwnProperty aip (.sym WK.asyncIterator)) then
    let _ ← defMethod aip (.sym WK.asyncIterator) "returnThis" 0 (some "[Symbol.asyncIterator]")
  let afs ← newIntrinsicObject "%AsyncFromSyncIteratorPrototype%" (some aip)
  for (nm, len) in [("next", 1), ("return", 1), ("throw", 1)] do
    let _ ← defMethod afs (.str (JSStr.ofString nm)) s!"%AsyncFromSyncIteratorPrototype%.{nm}" len

/-! ## Sessions -/

/-- A running engine. -/
structure Session where
  eng : Engine
  state : State
  conts : Conts := {}

/-- The outcome of running code. -/
inductive Outcome' where
  | value (v : Value)
  | threw (v : Value)
  | halted (msg : String)
  deriving Inhabited

/-- Runs a computation in a session (requests answered). -/
def Session.run {α} (sess : Session) (m : M α) : Except String (Except Value α) × Session :=
  match runM sess.eng m sess.state sess.conts with
  | (.ok a s, cs) => (.ok (.ok a), { sess with state := s, conts := cs })
  | (.err e s, cs) => (.ok (.error e), { sess with state := s, conts := cs })
  | (.halt m s, cs) => (.error m, { sess with state := s, conts := cs })
  | (.req _ s _, cs) => (.error "internal: unanswered request at top level", { sess with state := s, conts := cs })

/-- Runs the job queue. -/
def Session.drainJobs (sess : Session) : Except String Session :=
  match runJobs sess.eng sess.state sess.conts with
  | (.ok s, cs) => .ok { sess with state := s, conts := cs }
  | (.error m, _) => .error m

/-- Parses a script and evaluates it (a SyntaxError is thrown as an error object of the
current realm). -/
def evalScriptSource (src : String) (path : String := "") : M Value := do
  match parseScript src with
  | .ok prog => scriptEvaluation prog path
  | .error e => throwError .syntaxError e.msg

/-- Runs a script, then the jobs it queued. -/
def Session.runScript (sess : Session) (src : String) (path : String := "") : Outcome' × Session :=
  match sess.run (evalScriptSource src path) with
  | (.error m, sess) => (.halted m, sess)
  | (.ok r, sess) =>
    match sess.drainJobs with
    | .error m => (.halted m, sess)
    | .ok sess => match r with
      | .ok v => (.value v, sess)
      | .error e => (.threw e, sess)

/-- Loads, links and evaluates a module graph (sources by path in `sources`), then runs the jobs;
the outcome is the evaluation promise's: its rejection reason is thrown. -/
def Session.runModule (sess : Session) (path : String) (sources : Std.HashMap String String) : Outcome' × Session :=
  let sess := { sess with state := { sess.state with moduleSources := sess.state.moduleSources.insertMany sources.toList } }
  match sess.run (runModuleGraph path) with
  | (.error m, sess) => (.halted m, sess)
  | (.ok (.error e), sess) => (.threw e, sess)
  | (.ok (.ok p), sess) =>
    match sess.drainJobs with
    | .error m => (.halted m, sess)
    | .ok sess =>
      let st := match p with
        | .obj o => match sess.state.heap[o]? with
          | some { kind := .promise st r .., .. } => some (st, r)
          | _ => none
        | _ => none
      match st with
      | some (.rejected, r) => (.threw r, sess)
      | _ => (.value .undefined, sess)

/-- Adds module sources (for `import()` from scripts). -/
def Session.addSources (sess : Session) (sources : Std.HashMap String String) : Session :=
  { sess with state := { sess.state with moduleSources := sess.state.moduleSources.insertMany sources.toList } }

/-- A readable description of a thrown value: `Name: message`. -/
def describeThrown (v : Value) : M String := do
  match v with
  | .obj o =>
    let c ← M.attempt (getProp o (.str kConstructor))
    let nm ← match c with
      | .ok (.obj c) => do
        match ← M.attempt (getProp c (.str kName)) with
        | .ok (.str s) => pure s.toString
        | _ => pure "?"
      | _ => pure "?"
    let msg ← match ← M.attempt (getProp o (.str kMessage)) with
      | .ok (.str s) => pure s.toString
      | _ => pure ""
    pure s!"{nm}: {msg}"
  | v => match ← M.attempt (toStr v) with
    | .ok s => pure s.toString
    | .error _ => pure "(unprintable)"

/-- The constructor name of a thrown value (for test262's negative tests). -/
def thrownName (v : Value) : M String := do
  let .obj o := v | return ""
  let c ← M.attempt (getProp o (.str kConstructor))
  match c with
  | .ok (.obj c) => match ← M.attempt (getProp c (.str kName)) with
    | .ok (.str s) => pure s.toString
    | _ => pure ""
  | _ => pure ""

/-- All behaviours: the engine's and the host's. -/
def allBuiltins (host : Array BuiltinDef) : Array BuiltinDef :=
  promiseBuiltins ++ interpBuiltins ++ asyncGenBuiltins ++ moduleBuiltins ++ coreBuiltins ++ engineBuiltins ++
    Builtins.Text.defs ++ Builtins.Collections.defs ++ Builtins.Library.defs ++ host

/-- A new session with one realm (the host's setup runs last in each realm). -/
def newSession (hostDefs : Array BuiltinDef) (hostSetup : M Unit) (fuel : Nat := 100000000) : Except String Session :=
  let defs := allBuiltins hostDefs
  let eng : Engine := { builtins := defs.map (·.fn) }
  let s : State := { initialState defs with fuel }
  let sess : Session := { eng, state := s }
  match sess.run (createRealm #[coreSetup, engineSetup, Builtins.Text.setup, Builtins.Collections.setup,
    Builtins.Library.setup, hostSetup]) with
  | (.ok (.ok idx), sess) => .ok { sess with state := { sess.state with realm := idx } }
  | (.ok (.error _), _) => .error "realm creation threw"
  | (.error m, _) => .error m

/-! ## The test262 host ($262, print) -/

/-- The realm setups (for `$262.createRealm`). -/
def test262Setups (host : M Unit) : Array (M Unit) := #[coreSetup, engineSetup, Builtins.Text.setup,
  Builtins.Collections.setup, Builtins.Library.setup, host]

def printBuiltin : BuiltinFn := fun _ _ args _ => do
  let s ← toStr (arg args 0)
  modify fun st => { st with output := st.output.push s.toString }
  pure .undefined

/-- `$262.evalScript(src)` in the $262 object's realm. -/
def evalScriptBuiltin : BuiltinFn := fun self _ args _ => do
  let sl ← builtinSlots self
  let realm := match (sl[0]? : Option Value) with | some (.num x) => (Conv.toNat? x).getD 0 | _ => 0
  let src ← toStr (arg args 0)
  let prev ← readS (·.realm)
  modify fun s => { s with realm }
  let r ← M.attempt (evalScriptSource src.toString)
  modify fun s => { s with realm := prev }
  match r with
  | .ok v => pure v
  | .error e => M.throwV e

def detachArrayBufferBuiltin : BuiltinFn := fun _ _ args _ => do
  let .obj b := arg args 0 | throwType "not an ArrayBuffer"
  match ← objKind b with
  | .buffer _ _ ml sh =>
    if sh then throwType "Cannot detach a SharedArrayBuffer"
    modifyObj b fun o => { o with kind := .buffer ByteArray.empty true ml sh }
    pure .null
  | _ => throwType "not an ArrayBuffer"

/-- Defines `$262` and `print` in the current realm.
(test262 INTERPRETING.md: Test262-Defined Bindings) -/
def test262HostSetup : M Unit := do
  let (g, realmIdx) ← readS fun s => (s.curRealm.globalObj, s.realm)
  let pr ← makeBuiltinFn "print" 1 "print"
  defGlobal "print" (.obj pr)
  let o ← newObject
  let _ ← defMethod o (.str "createRealm") "$262.createRealm" 0
  let es ← makeBuiltinFn "$262.evalScript" 1 "evalScript" #[numV realmIdx]
  setOwn o (.str "evalScript") (.data (.obj es) true false true)
  let _ ← defMethod o (.str "detachArrayBuffer") "$262.detachArrayBuffer" 1
  let _ ← defMethod o (.str "gc") "returnThis" 0
  setOwn o (.str "global") (.data (.obj g) true false true)
  let agent ← newObject
  setOwn o (.str "agent") (.data (.obj agent) true false true)
  defGlobal "$262" (.obj o)

def createRealmBuiltin : BuiltinFn := fun _ _ _ _ => do
  let idx ← createRealm (test262Setups test262HostSetup)
  let g ← readS fun s => (s.realms[idx]!).globalObj
  getProp g (.str "$262")

def test262Builtins : Array BuiltinDef := #[
  ⟨"print", printBuiltin⟩, ⟨"$262.createRealm", createRealmBuiltin⟩,
  ⟨"$262.evalScript", evalScriptBuiltin⟩, ⟨"$262.detachArrayBuffer", detachArrayBufferBuiltin⟩]

end ES
