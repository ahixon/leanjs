import ES.Value

/-!
# State access: objects, environments, symbols, intrinsics, errors

Updates go through `State.withHeap`/`withEnvs`, which take the arena out of the state before
changing it so that it is updated in place (see CLAUDE.md: never keep an old copy alive).
-/

namespace ES

open ES (F64)

-- The well-known symbols' ids (`State.symbols` starts with them).
-- spec: https://tc39.es/ecma262/#sec-well-known-symbols
namespace WK
def asyncIterator : SymId := 0
def hasInstance : SymId := 1
def isConcatSpreadable : SymId := 2
def iterator : SymId := 3
def «match» : SymId := 4
def matchAll : SymId := 5
def replace : SymId := 6
def search : SymId := 7
def species : SymId := 8
def split : SymId := 9
def toPrimitive : SymId := 10
def toStringTag : SymId := 11
def unscopables : SymId := 12
def dispose : SymId := 13
def asyncDispose : SymId := 14
/-- (internal, never exposed) the value a generator's `return` throws through its body's
`finally` blocks; the return value is in `State.genReturn`. -/
def genReturn : SymId := 15
def names : Array String := #["Symbol.asyncIterator", "Symbol.hasInstance",
  "Symbol.isConcatSpreadable", "Symbol.iterator", "Symbol.match", "Symbol.matchAll",
  "Symbol.replace", "Symbol.search", "Symbol.species", "Symbol.split", "Symbol.toPrimitive",
  "Symbol.toStringTag", "Symbol.unscopables", "Symbol.dispose", "Symbol.asyncDispose",
  "(generator return)"]
end WK

namespace State

@[inline] def withHeap (s : State) (f : Array Obj → Array Obj) : State :=
  let h := s.heap
  let s := { s with heap := #[] }
  { s with heap := f h }

@[inline] def withEnvs (s : State) (f : Array Env → Array Env) : State :=
  let e := s.envs
  let s := { s with envs := #[] }
  { s with envs := f e }

@[inline] def curRealm (s : State) : Realm := s.realms[s.realm]!

end State

namespace Obj
@[inline] def withProps (o : Obj) (f : PropMap → PropMap) : Obj :=
  let p := o.props
  let o := { o with props := {} }
  { o with props := f p }
@[inline] def withKind (o : Obj) (f : Kind → Kind) : Obj :=
  let k := o.kind
  let o := { o with kind := .ordinary }
  { o with kind := f k }
end Obj

/-- Reads a projection of the state. (Never return the whole state as a value: holding it keeps
a second reference to the arenas, and the next update would copy them.) -/
@[inline] def readS {α} (f : State → α) : M α := fun s => .ok (f s) s

/-! ## Objects -/

/-- Allocates an object. -/
def alloc (o : Obj) : M ObjId := fun s =>
  let id := s.heap.size
  .ok id (s.withHeap (·.push o))

/-- Reads part of an object (without keeping a copy of the whole object). -/
@[inline] def readObj {α} (id : ObjId) (f : Obj → α) : M α := fun s =>
  if h : id < s.heap.size then .ok (f s.heap[id]) s else .halt s!"internal: bad object id {id}" s

@[inline] def modifyObj (id : ObjId) (f : Obj → Obj) : M Unit := fun s =>
  .ok () (s.withHeap (·.modify id f))

@[inline] def objKind (id : ObjId) : M Kind := readObj id (·.kind)
@[inline] def objProto (id : ObjId) : M Value := readObj id (·.proto)
@[inline] def ownProp (id : ObjId) (k : PropKey) : M (Option Property) := readObj id (·.props.get? k)

/-- Sets an own property directly (no checks; for building intrinsics and fresh objects). -/
@[inline] def setOwn (id : ObjId) (k : PropKey) (p : Property) : M Unit :=
  modifyObj id (·.withProps (·.insert k p))

/-! ## Environments -/

def allocEnv (e : Env) : M EnvId := fun s =>
  let id := s.envs.size
  .ok id (s.withEnvs (·.push e))

@[inline] def readEnv {α} (id : EnvId) (f : Env → α) : M α := fun s =>
  if h : id < s.envs.size then .ok (f s.envs[id]) s else .halt s!"internal: bad environment id {id}" s

@[inline] def modifyEnv (id : EnvId) (f : Env → Env) : M Unit := fun s =>
  .ok () (s.withEnvs (·.modify id f))

/-! ## Realms and intrinsics -/

/-- The current realm's intrinsic `%name%` (e.g. `"%Array.prototype%"`). -/
def intrinsic (name : String) : M ObjId := fun s =>
  match s.curRealm.intrinsics.get? name with
  | some id => .ok id s
  | none => .halt s!"internal: no intrinsic {name}" s

/-- An intrinsic of a given realm. -/
def intrinsicOf (realm : Nat) (name : String) : M ObjId := fun s =>
  match s.realms[realm]? >>= (·.intrinsics.get? name) with
  | some id => .ok id s
  | none => .halt s!"internal: no intrinsic {name} in realm {realm}" s

/-- OrdinaryObjectCreate(proto) with no slots.
spec: https://tc39.es/ecma262/#sec-ordinaryobjectcreate -/
def ordinaryObjectCreate (proto : Value) (kind : Kind := .ordinary) : M ObjId :=
  alloc { proto, kind }

/-- A new ordinary object inheriting from the current realm's %Object.prototype%. -/
def newObject : M ObjId := fun s =>
  let p := s.curRealm.objectProto
  alloc { proto := .obj p } s

/-! ## Symbols -/

def newSymbol (desc : Option JSStr) : M SymId := fun s =>
  .ok s.symbols.size { s with symbols := s.symbols.push desc }

/-! ## Errors -/

inductive ErrorKind where
  | error | typeError | rangeError | referenceError | syntaxError | evalError | uriError
  | aggregateError
  deriving Inhabited, BEq

def ErrorKind.name : ErrorKind → String
  | .error => "Error" | .typeError => "TypeError" | .rangeError => "RangeError"
  | .referenceError => "ReferenceError" | .syntaxError => "SyntaxError"
  | .evalError => "EvalError" | .uriError => "URIError" | .aggregateError => "AggregateError"

def kMessage : JSStr := "message"

/-- A new error object of the current realm with a message. -/
def makeError (k : ErrorKind) (msg : String) : M Value := do
  let proto ← intrinsic s!"%{k.name}.prototype%"
  let o ← alloc { proto := .obj proto, kind := .error }
  setOwn o kMessage (.data (.str (JSStr.ofString msg)) true false true)
  pure (.obj o)

/-- Throws a new error object of the current realm. -/
def throwError {α} (k : ErrorKind) (msg : String) : M α := do
  let e ← makeError k msg
  M.throwV e

def throwType {α} (msg : String) : M α := throwError .typeError msg
def throwRange {α} (msg : String) : M α := throwError .rangeError msg

/-! ## Requests -/

/-- Call(F, V, argumentsList): asks the driver to call `f`.
spec: https://tc39.es/ecma262/#sec-call -/
def call (f thisV : Value) (args : Array Value := #[]) : M Value := fun s =>
  .req (.call f thisV args) s fun o s' => match o with
    | .normal v | .ret v => .ok v s'
    | .throw e => .err e s'

/-- Construct(F, argumentsList, newTarget)
spec: https://tc39.es/ecma262/#sec-construct -/
def construct (f : Value) (args : Array Value := #[]) (newTarget : Option Value := none) : M Value :=
  fun s => .req (.construct f args (newTarget.getD f)) s fun o s' => match o with
    | .normal v | .ret v => .ok v s'
    | .throw e => .err e s'

/-- Await(value): suspends the running async body until `v` settles.
spec: https://tc39.es/ecma262/#await -/
def await (v : Value) : M Value := fun s =>
  .req (.await v) s fun o s' => match o with
    | .normal v | .ret v => .ok v s'
    | .throw e => .err e s'

/-- Looks up a built-in behaviour's id by name. -/
def builtinId (name : String) : M Nat := fun s =>
  match s.builtinIds.get? name with
  | some i => .ok i s
  | none => .halt s!"internal: no built-in {name}" s

/-- CreateBuiltinFunction for a closure-like built-in (a behaviour with captured slots): a new
function object of the current realm.
spec: https://tc39.es/ecma262/#sec-createbuiltinfunction -/
def makeBuiltinFn (name : String) (length : Nat) (fnName : JSStr := JSStr.empty)
    (slots : Array Value := #[]) (isCtor := false) : M ObjId := do
  let id ← builtinId name
  let (proto, realm) ← readS fun s => (s.curRealm.functionProto, s.realm)
  let o ← alloc { proto := .obj proto, kind := .builtin { id, realm, slots, isCtor } }
  setOwn o "length" (.data (.num (F64.ofInt length)) false false true)
  setOwn o "name" (.data (.str fnName) false false true)
  pure o

/-- Queues a job: a call of `f` with `args` (HostEnqueuePromiseJob and friends).
spec: https://tc39.es/ecma262/#sec-hostenqueuepromisejob -/
def enqueueJob (f : Value) (args : Array Value) : M Unit := modify fun s =>
  { s with jobs := s.jobs.push (f, args) }

end ES
