import Std.Data.HashMap
import ES.AST
import ES.Regex

/-!
# The engine's state: values, objects, environments, realms, and the evaluation monad

- Values (spec: https://tc39.es/ecma262/#sec-ecmascript-language-types) and objects in an arena
  (`State.heap`, object = index). There is no garbage collector yet: LIMITATION (docs/es.md).
- Environment Records (spec: https://tc39.es/ecma262/#sec-environment-records), also an arena.
- Realms (spec: https://tc39.es/ecma262/#sec-code-realms): intrinsics by their spec names.
- `M`, the monad all runtime semantics are written in: a state monad whose results may be
  *requests* with a continuation (`Res.req`). A request asks the driver (`ES/Interp.lean`,
  `drive`) to call or construct a function, or suspends a generator or async function
  (`yield`/`await`) until the driver resumes it. Built-ins call functions through requests, so
  they are not mutually recursive with the interpreter, generators are ordinary code that
  suspends, and every function here stays total: recursion through calls is bounded by the
  driver's call depth (a `RangeError` past it, as engines do on stack overflow).
-/

namespace ES

open ES (F64)
open Std (HashMap)

abbrev ObjId := Nat
abbrev EnvId := Nat
abbrev SymId := Nat

inductive Value where
  | undefined
  | null
  | bool (b : Bool)
  | num (n : F64)
  | str (s : JSStr)
  | sym (id : SymId)
  | bigint (i : Int)
  | obj (id : ObjId)
  deriving Inhabited

instance : Coe JSStr Value := ⟨.str⟩
instance : Coe Bool Value := ⟨.bool⟩

/-- A property key: a String or a Symbol.
spec: https://tc39.es/ecma262/#sec-object-type -/
inductive PropKey where
  | str (s : JSStr)
  | sym (id : SymId)
  deriving Inhabited, BEq, Hashable

instance : Coe JSStr PropKey := ⟨.str⟩

/-- A property's attributes and value.
spec: https://tc39.es/ecma262/#sec-property-attributes -/
inductive Property where
  | data (value : Value) (writable enumerable configurable : Bool)
  | accessor (get set : Value) (enumerable configurable : Bool)
  deriving Inhabited

namespace Property
def enumerable : Property → Bool | .data _ _ e _ | .accessor _ _ e _ => e
def configurable : Property → Bool | .data _ _ _ c | .accessor _ _ _ c => c
end Property

/-- A Property Descriptor (fields may be absent).
spec: https://tc39.es/ecma262/#sec-property-descriptor-specification-type -/
structure PropDesc where
  value : Option Value := none
  writable : Option Bool := none
  get : Option Value := none
  set : Option Value := none
  enumerable : Option Bool := none
  configurable : Option Bool := none
  deriving Inhabited

namespace PropDesc
/-- spec: https://tc39.es/ecma262/#sec-isaccessordescriptor -/
def isAccessor (d : PropDesc) : Bool := d.get.isSome || d.set.isSome
/-- spec: https://tc39.es/ecma262/#sec-isdatadescriptor -/
def isData (d : PropDesc) : Bool := d.value.isSome || d.writable.isSome
/-- spec: https://tc39.es/ecma262/#sec-isgenericdescriptor -/
def isGeneric (d : PropDesc) : Bool := !d.isAccessor && !d.isData
def ofProp : Property → PropDesc
  | .data v w e c => { value := v, writable := w, enumerable := e, configurable := c }
  | .accessor g s e c => { get := g, set := s, enumerable := e, configurable := c }
def data (v : Value) (w e c : Bool := true) : PropDesc :=
  { value := v, writable := w, enumerable := e, configurable := c }
end PropDesc

/-- An object's own properties in insertion order (OrdinaryOwnPropertyKeys sorts the integer
indices first when asked). Deleting leaves a tombstone in `order` (a key whose recorded position
is elsewhere or absent), so deletion is O(1); `order` is compacted when tombstones dominate. -/
structure PropMap where
  /-- each key's property and its position in `order` -/
  map : HashMap PropKey (Nat × Property) := {}
  order : Array PropKey := #[]
  deriving Inhabited

namespace PropMap
@[inline] def get? (m : PropMap) (k : PropKey) : Option Property := (m.map.get? k).map (·.2)
@[inline] def contains (m : PropMap) (k : PropKey) : Bool := m.map.contains k
def insert (m : PropMap) (k : PropKey) (p : Property) : PropMap :=
  match m.map.get? k with
  | some (i, _) => { m with map := m.map.insert k (i, p) }
  | none => { map := m.map.insert k (m.order.size, p), order := m.order.push k }
/-- The live keys in insertion order. -/
def keys (m : PropMap) : Array PropKey :=
  if m.order.size == m.map.size then m.order else
  (m.order.zipIdx).filterMap fun (k, i) => match m.map.get? k with
    | some (j, _) => if i == j then some k else none
    | none => none
def size (m : PropMap) : Nat := m.map.size
def erase (m : PropMap) (k : PropKey) : PropMap :=
  if !m.map.contains k then m else
  let m := { m with map := m.map.erase k }
  -- (compact when more than half of `order` is tombstones)
  if m.order.size > 32 && 2 * m.map.size < m.order.size then
    let ks := m.keys
    let map := (ks.zipIdx).foldl (fun mp (k, i) => match mp.get? k with
      | some (_, p) => mp.insert k (i, p)
      | none => mp) m.map
    { map, order := ks }
  else m
end PropMap

inductive ThisMode where
  | lexical | strict | global
  deriving Inhabited, BEq

/-- A class element's name: a property key or a Private Name (by id). -/
inductive ElemName where
  | key (k : PropKey)
  | priv (id : Nat)
  deriving Inhabited, BEq

/-- ClassFieldDefinition Record (the initializer is a method-like function object).
spec: https://tc39.es/ecma262/#sec-classfielddefinition-record-specification-type -/
structure FieldDef where
  name : ElemName
  init : Option ObjId
  deriving Inhabited

/-- PrivateElement
spec: https://tc39.es/ecma262/#sec-privateelement-specification-type -/
inductive PrivElem where
  | field (v : Value)
  | method (f : Value)
  | accessor (get set : Value)
  deriving Inhabited

/-- The internal slots of an ECMAScript function object.
spec: https://tc39.es/ecma262/#table-internal-slots-of-ecmascript-function-objects -/
structure FuncData where
  code : Func
  env : EnvId
  /-- [[PrivateEnvironment]]: the private names in scope (description, id); later ones shadow. -/
  privEnv : Array (JSStr × Nat) := #[]
  thisMode : ThisMode
  homeObject : Option ObjId := none
  derived : Bool := false
  isClassCtor : Bool := false
  /-- A class's default constructor (spec: the built-in closure of ClassDefinitionEvaluation
  step 14.a). -/
  isDefaultCtor : Bool := false
  /-- [[ClassFieldInitializerName]] (for field initializers: the field's name). -/
  fieldName : Option ElemName := none
  /-- The source text (for `Function.prototype.toString`), shared with the script. -/
  source : String := ""
  fields : Array FieldDef := #[]
  privMethods : Array (Nat × PrivElem) := #[]
  /-- [[ClassFieldInitializerName]] -/
  realm : Nat
  /-- [[ScriptOrModule]]: an index into `State.scripts`. -/
  script : Nat
  deriving Inhabited

/-- A built-in function object's slots: its behaviour (an index into the engine's table of
built-ins) and captured values (e.g. a promise resolving function's promise). -/
structure BuiltinData where
  id : Nat
  realm : Nat
  isCtor : Bool := false
  slots : Array Value := #[]
  deriving Inhabited

inductive PromiseState where
  | pending | fulfilled | rejected
  deriving Inhabited, BEq

/-- PromiseReaction Record
spec: https://tc39.es/ecma262/#sec-promisereaction-records -/
structure Reaction where
  /-- the capability's promise, resolve, reject (absent for await's reactions) -/
  capability : Option (Value × Value × Value)
  isFulfill : Bool
  handler : Value   -- undefined: the default (identity / thrower)
  deriving Inhabited

inductive GenState where
  | suspendedStart | suspendedYield | executing | completed
  /-- (async generators) -/
  | drainingQueue
  deriving Inhabited, BEq

/-- Typed array element types.
spec: https://tc39.es/ecma262/#table-the-typedarray-constructors -/
inductive TAKind where
  | int8 | uint8 | uint8c | int16 | uint16 | int32 | uint32 | float16 | float32 | float64
  | bigInt64 | bigUint64
  deriving Inhabited, BEq, Repr

/-- The kinds of objects: ordinary, and every exotic or slot-carrying object. -/
inductive Kind where
  | ordinary
  | array
  | func (d : FuncData)
  | builtin (b : BuiltinData)
  | bound (target : ObjId) (thisV : Value) (args : Array Value)
  /-- `target`/`handler` are `none` once revoked. -/
  | proxy (target handler : Option ObjId) (callable ctor : Bool)
  /-- Primitive wrappers: [[BooleanData]], [[NumberData]], [[StringData]] (a String exotic
  object), [[SymbolData]], [[BigIntData]]. -/
  | primitive (v : Value)
  /-- Arguments objects; mapped ones map index i to the binding `names[i]` (`none`: unmapped
  index) of environment `env`. -/
  | arguments (mapped : Option (EnvId × Array (Option JSStr)))
  | error
  | date (tv : F64)
  | regexp (source flags : JSStr) (prog : Regex.Program)
  /-- Map/Set entries in insertion order; deleted entries are `none` so live iterators keep
  their positions. `index` maps a SameValueZero key to its entry. -/
  | mapData (entries : Array (Option (Value × Value))) (index : HashMap PropKey Nat) (isSet : Bool) (weak : Bool)
  | promise (state : PromiseState) (result : Value) (fulfill reject : Array Reaction) (handled : Bool)
  /-- Generators and async functions/generators in progress: the driver keeps their
  continuations by this object's id. `start` is what the driver runs first: the function
  object and its prepared environment. -/
  | coroutine (state : GenState) (fn : ObjId) (lexEnv varEnv : EnvId) (isAsync : Bool) (isGenerator : Bool)
      (slots : Array Value)
  /-- ArrayBuffer/SharedArrayBuffer: `maxLen` for resizable buffers. -/
  | buffer (data : ByteArray) (detached : Bool) (maxLen : Option Nat) (shared : Bool)
  /-- Typed arrays: `length = none` tracks a resizable buffer's length. -/
  | typedArray (k : TAKind) (buf : ObjId) (byteOffset : Nat) (length : Option Nat)
  | dataView (buf : ObjId) (byteOffset : Nat) (byteLength : Option Nat)
  /-- Module namespace exotic objects (module index, sorted export names). -/
  | moduleNS (module : Nat) (exports : Array JSStr)
  /-- Other built-in objects with internal slots (iterators, records, …): a tag naming the
  kind (e.g. "Array Iterator") and its slots. -/
  | internal (tag : String) (slots : Array Value)
  deriving Inhabited

/-- An object.
spec: https://tc39.es/ecma262/#sec-object-type -/
structure Obj where
  proto : Value := .null
  extensible : Bool := true
  props : PropMap := {}
  kind : Kind := .ordinary
  /-- [[PrivateElements]] -/
  privates : Array (Nat × PrivElem) := #[]
  /-- The object's class for `Object.prototype.toString`'s builtinTag and error checks
  (e.g. "Error", "Arguments") is in `kind`; `immutableProto` marks immutable prototype exotic
  objects (%Object.prototype%). -/
  immutableProto : Bool := false
  deriving Inhabited

/-- A binding in a Declarative Environment Record (`value = none`: uninitialized). -/
structure Binding where
  value : Option Value := none
  mutable : Bool := true
  strict : Bool := false
  deletable : Bool := false
  deriving Inhabited

inductive ThisStatus where
  | lexical | initialized | uninitialized
  deriving Inhabited, BEq

/-- Environment Records.
spec: https://tc39.es/ecma262/#sec-environment-records -/
inductive Env where
  | decl (b : HashMap JSStr Binding) (outer : Option EnvId)
  /-- Function Environment Records -/
  | func (b : HashMap JSStr Binding) (outer : Option EnvId) (thisStatus : ThisStatus)
      (thisValue : Value) (funcObj : ObjId) (newTarget : Value)
  /-- Object Environment Records (`with` and the global object's part) -/
  | object (o : ObjId) (isWith : Bool) (outer : Option EnvId)
  /-- Global Environment Records: the object record's object, the declarative record, the
  [[GlobalThisValue]] (and, before ES2025, [[VarNames]]). -/
  | global (objRec : ObjId) (declRec : HashMap JSStr Binding) (thisValue : Value)
  /-- Module Environment Records: bindings, and imports as indirect bindings to (module,
  binding name) — `none` name: the namespace object. -/
  | module (b : HashMap JSStr Binding) (imports : HashMap JSStr (Nat × Option JSStr)) (outer : Option EnvId)
  deriving Inhabited

/-- A Realm Record: intrinsics by name (e.g. "%Array.prototype%"), the global object and
environment, the template registry.
spec: https://tc39.es/ecma262/#sec-code-realms -/
structure Realm where
  intrinsics : HashMap String ObjId := {}
  globalObj : ObjId := 0
  globalEnv : EnvId := 0
  templates : HashMap (Nat × Nat) ObjId := {}
  /-- The Object.prototype, Function.prototype, Array.prototype ids (used on every object
  creation). -/
  objectProto : ObjId := 0
  functionProto : ObjId := 0
  arrayProto : ObjId := 0
  deriving Inhabited

/-- A parsed Script or Module record. -/
structure ScriptRec where
  prog : Program
  realm : Nat
  /-- The host's name for the script/module (a path), for resolving `import()` specifiers. -/
  path : String := ""
  /-- (modules) the index in `State.modules` -/
  module : Option Nat := none
  hostDefined : Value := .undefined
  deriving Inhabited

/-- An ExportEntry Record (`importName`: "*" is `all`, "*-but-default" is `all-but-default`).
spec: https://tc39.es/ecma262/#table-exportentry-records -/
structure ExportEntry where
  exportName : Option JSStr
  moduleRequest : Option JSStr
  importName : Option JSStr
  localName : Option JSStr
  deriving Inhabited

/-- An ImportEntry Record (`importName` none: namespace-object).
spec: https://tc39.es/ecma262/#table-importentry-record-fields -/
structure ImportEntry where
  moduleRequest : JSStr
  importName : Option JSStr
  localName : JSStr
  deriving Inhabited

/-- A Source Text Module Record (the fields its algorithms use).
spec: https://tc39.es/ecma262/#sec-source-text-module-records -/
structure ModuleRec where
  script : Nat
  path : String
  env : Option EnvId := none
  ns : Option ObjId := none
  /-- the namespace's exports with their resolutions (module, binding name; none: namespace) -/
  nsBindings : Array (JSStr × Nat × Option JSStr) := #[]
  /-- "new" | "unlinked" | "linking" | "linked" | "evaluating" | "evaluating-async" | "evaluated" -/
  status : String := "unlinked"
  error : Option Value := none
  /-- RequestedModules with their loaded modules -/
  requested : Array (JSStr × Nat) := #[]
  importEntries : Array ImportEntry := #[]
  localExports : Array ExportEntry := #[]
  indirectExports : Array ExportEntry := #[]
  starExports : Array ExportEntry := #[]
  hasTLA : Bool := false
  dfsIndex : Nat := 0
  dfsAncestorIndex : Nat := 0
  cycleRoot : Option Nat := none
  /-- [[AsyncEvaluationOrder]]: none (unset), some 0 (done), some k (order) -/
  asyncOrder : Option Nat := none
  pendingAsyncDeps : Nat := 0
  asyncParents : Array Nat := #[]
  topCapability : Option (Value × Value × Value) := none
  importMeta : Option ObjId := none
  /-- (synthetic modules: JSON modules) the value of the `default` export -/
  syntheticDefault : Option Value := none
  deriving Inhabited

/-- The engine's whole state. -/
structure State where
  heap : Array Obj := #[]
  envs : Array Env := #[]
  realms : Array Realm := #[]
  /-- The current Realm Record (of the running execution context). -/
  realm : Nat := 0
  /-- The running execution context's ScriptOrModule (index into `scripts`). -/
  script : Nat := 0
  scripts : Array ScriptRec := #[]
  modules : Array ModuleRec := #[]
  /-- Symbols' [[Description]] (`none`: undefined). The well-known symbols come first. -/
  symbols : Array (Option JSStr) := #[]
  /-- GlobalSymbolRegistry -/
  symRegistry : HashMap JSStr SymId := {}
  /-- The job queue: functions to call with arguments, in order (promise jobs are built-in
  closures). spec: https://tc39.es/ecma262/#sec-jobs -/
  jobs : Array (Value × Array Value) := #[]
  jobHead : Nat := 0
  /-- Steps left (each loop iteration and call takes one): exhausting it halts evaluation
  (a resource limit, like an engine's watchdog). -/
  fuel : Nat := 100000000
  /-- Built-in behaviours by name → id in the engine's table. -/
  builtinIds : HashMap String Nat := {}
  nextPrivId : Nat := 0
  privNames : Array JSStr := #[]
  /-- Host output (`print`, `console.log`). -/
  output : Array String := #[]
  /-- Promise rejections without handlers (HostPromiseRejectionTracker). -/
  rejections : Array ObjId := #[]
  /-- The current function's call depth (see `drive`). -/
  depth : Nat := 0
  /-- Host hooks' data (e.g. the test harness's `$262.agent`). -/
  hostData : HashMap String Value := {}
  /-- Module sources the host provides, by path (HostLoadImportedModule reads them). -/
  moduleSources : HashMap String String := {}
  /-- The next [[AsyncEvaluationOrder]]. -/
  asyncOrderCounter : Nat := 1
  /-- The value of a generator `return` unwinding its body (see `WK.genReturn`). -/
  genReturn : Value := .undefined
  deriving Inhabited

/-- How a suspended computation is resumed: normally with a value, with a throw, or (a
generator's `return`) with a return. -/
inductive Outcome where
  | normal (v : Value)
  | throw (v : Value)
  | ret (v : Value)
  deriving Inhabited

/-- What a computation can ask of the driver. -/
inductive Req where
  /-- [[Call]] spec: https://tc39.es/ecma262/#sec-call -/
  | call (f thisV : Value) (args : Array Value)
  /-- [[Construct]] spec: https://tc39.es/ecma262/#sec-construct -/
  | construct (f : Value) (args : Array Value) (newTarget : Value)
  /-- A generator body suspends (GeneratorYield); resumed with the generator's next/throw/return. -/
  | yield (v : Value)
  /-- An async body suspends until `v` settles (Await); resumed with its value or reason. -/
  | await (v : Value)
  /-- Resume the coroutine (generator or async body) `co`: the continuation gets
  `normal v` when it yields `v`, `ret v` when it completes with `v`, `throw e` when it throws. -/
  | resume (co : ObjId) (o : Outcome)
  /-- A call of a host operation (a host-provided built-in, e.g. a DOM member `name` with its `this` value and
  arguments): answered by the embedder outside the engine, which resumes with its result or exception. -/
  | host (name : String) (thisV : Value) (args : Array Value)
  /-- Continue the innermost frame suspended at a host request with the host's answer `o` (the driver's frame
  stack, `Conts.frames`). -/
  | resumeFrame (o : Outcome)
  deriving Inhabited

/-- The result of running a computation. -/
inductive Res (α : Type) where
  | ok (a : α) (s : State)
  /-- A thrown exception (a throw completion). -/
  | err (e : Value) (s : State)
  /-- An engine failure, not catchable by scripts: out of fuel, an internal error, or an
  unimplemented feature. -/
  | halt (msg : String) (s : State)
  | req (r : Req) (s : State) (k : Outcome → State → Res α)

instance {α} : Inhabited (Res α) := ⟨.halt "" default⟩

/-- The evaluation monad. -/
abbrev M (α : Type) := State → Res α

namespace M

@[inline] def pure {α} (a : α) : M α := fun s => .ok a s

/-- Continues `r` with `f` (and, through requests, every continuation of `r`). -/
def bindRes {α β} (f : α → M β) : Res α → Res β
  | .ok a s => f a s
  | .err e s => .err e s
  | .halt m s => .halt m s
  | .req r s k => .req r s (fun o s' => bindRes f (k o s'))

@[inline] def bind {α β} (x : M α) (f : α → M β) : M β := fun s => bindRes f (x s)

instance : Monad M where
  pure := M.pure
  bind := M.bind

instance : MonadStateOf State M where
  get := fun s => .ok s s
  set := fun s _ => .ok () s
  modifyGet := fun f s => let (a, s) := f s; .ok a s

/-- Throws a value. -/
@[inline] def throwV {α} (v : Value) : M α := fun s => .err v s

/-- Halts evaluation (an engine limitation or failure, not a JS exception). -/
@[inline] def halt {α} (msg : String) : M α := fun s => .halt msg s

/-- Runs `x`, handling a thrown exception with `h`. -/
def tryCatchRes {α} (h : Value → M α) : Res α → Res α
  | .ok a s => .ok a s
  | .err e s => h e s
  | .halt m s => .halt m s
  | .req r s k => .req r s (fun o s' => tryCatchRes h (k o s'))

@[inline] def tryCatch {α} (x : M α) (h : Value → M α) : M α := fun s => tryCatchRes h (x s)

/-- Runs `x` and returns its completion (normal or throw) as data. -/
def attempt {α} (x : M α) : M (Except Value α) :=
  tryCatch (Except.ok <$> x) (fun e => M.pure (.error e))

instance : MonadExceptOf Value M where
  throw := throwV
  tryCatch := tryCatch

/-- Issues a request and continues with its outcome. -/
@[inline] def request (r : Req) : M Outcome := fun s => .req r s (fun o s' => .ok o s')

/-- Takes one step of fuel. -/
@[inline] def tick : M Unit := fun s =>
  if s.fuel == 0 then .halt "out of fuel" s else .ok () { s with fuel := s.fuel - 1 }

/-- Continues a loop's step result: `next` runs the next iteration. Structural on the result. -/
def loopRes {σ α} (next : σ → State → Res α) : Res (σ ⊕ α) → Res α
  | .ok (.inl st) s => next st s
  | .ok (.inr a) s => .ok a s
  | .err e s => .err e s
  | .halt m s => .halt m s
  | .req r s k => .req r s (fun o s' => loopRes next (k o s'))

/-- Runs `body` from `st` until it returns `inr`, at most `bound` iterations (then halts: out
of fuel). The recursive call is a tail call (through `loopRes`'s first case), so long loops
run in constant stack. -/
def loop {σ α} (body : σ → M (σ ⊕ α)) : (bound : Nat) → σ → State → Res α
  | 0, _, s => .halt "out of fuel" s
  | n + 1, st, s => loopRes (loop body n) (body st s)

/-- `loop` bounded by the state's fuel. -/
@[inline] def repeatFrom {σ α} (st : σ) (body : σ → M (σ ⊕ α)) : M α := fun s => loop body s.fuel st s

/-- Folds `f` over an array, in order. -/
def foldArr {α β} (xs : Array α) (init : β) (f : β → α → M β) : M β := fun s =>
  loop (fun (st : Nat × β) =>
      if h : st.1 < xs.size then
        fun s => bindRes (fun acc' s => .ok (.inl (st.1 + 1, acc')) s) (f st.2 xs[st.1] s)
      else M.pure (.inr st.2))
    (xs.size + 1) (0, init) s

/-- Runs `f` on each element, in order. -/
def forArr {α} (xs : Array α) (f : α → M Unit) : M Unit := foldArr xs () (fun _ x => f x)

/-- Maps `f` over an array, in order. -/
def mapArr {α β} (xs : Array α) (f : α → M β) : M (Array β) :=
  foldArr xs (Array.mkEmpty xs.size) (fun acc x => do let y ← f x; M.pure (acc.push y))

end M

end ES
