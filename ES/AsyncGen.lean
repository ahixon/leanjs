import ES.Function

/-!
# Async generators and async iteration

spec: https://tc39.es/ecma262/#sec-asyncgenerator-objects (27.6),
https://tc39.es/ecma262/#sec-async-from-sync-iterator-objects (27.1.6),
https://tc39.es/ecma262/#sec-asynciteratorclose

An async generator is a coroutine object (`Kind.coroutine … isAsync true isGenerator true`) whose
`slots[0]` is its [[AsyncGeneratorQueue]]: an internal object holding the requests, five slots
each (completion kind 0 normal / 1 throw / 2 return, value, and the capability's promise,
resolve, reject).
-/

namespace ES

/-- An AsyncGeneratorRequest Record. -/
structure AGRequest where
  kind : Nat
  value : Value
  cap : Capability

def agQueueObj (g : ObjId) : M ObjId := do
  let .coroutine _ _ _ _ _ _ sl ← objKind g | M.halt "internal: not an async generator"
  let .obj q := sl[0]! | M.halt "internal: async generator without queue"
  pure q

def agQueue (g : ObjId) : M (Array Value) := do
  let q ← agQueueObj g
  readObj q fun o => match o.kind with | .internal _ s => s | _ => #[]

def agSetQueue (g : ObjId) (xs : Array Value) : M Unit := do
  let q ← agQueueObj g
  modifyObj q fun o => { o with kind := .internal "AsyncGeneratorQueue" xs }

def agState (g : ObjId) : M GenState := do
  match ← objKind g with
  | .coroutine st .. => pure st
  | _ => M.halt "internal: not an async generator"

def agSetState (g : ObjId) (st : GenState) : M Unit := modifyObj g fun o => o.withKind fun k => match k with
  | .coroutine _ f l v a gn sl => .coroutine st f l v a gn sl
  | k => k

def agFirst (g : ObjId) : M (Option AGRequest) := do
  let q ← agQueue g
  if q.size < 5 then return none
  let kind := match q[0]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  pure (some { kind, value := q[1]!, cap := { promise := q[2]!, resolve := q[3]!, reject := q[4]! } })

/-- AsyncGeneratorEnqueue spec: https://tc39.es/ecma262/#sec-asyncgeneratorenqueue -/
def agEnqueue (g : ObjId) (kind : Nat) (v : Value) (cap : Capability) : M Unit := do
  let q ← agQueue g
  agSetQueue g (q ++ #[numV kind, v, cap.promise, cap.resolve, cap.reject])

/-- AsyncGeneratorCompleteStep spec: https://tc39.es/ecma262/#sec-asyncgeneratorcompletestep -/
def agCompleteStep (g : ObjId) (isThrow : Bool) (v : Value) (done : Bool) : M Unit := do
  -- 2-3.
  let some next ← agFirst g | M.halt "internal: async generator queue empty"
  let q ← agQueue g
  agSetQueue g (q.extract 5 q.size)
  -- 5-8.
  if isThrow then let _ ← call next.cap.reject .undefined #[v]
  else
    let r ← createIterResult v done
    let _ ← call next.cap.resolve .undefined #[r]

/-- AsyncGeneratorAwaitReturn and AsyncGeneratorDrainQueue.
spec: https://tc39.es/ecma262/#sec-asyncgeneratorawaitreturn,
https://tc39.es/ecma262/#sec-asyncgeneratordrainqueue -/
def agDrainQueue (g : ObjId) : M Unit := do
  M.repeatFrom () fun _ => do
    match ← agFirst g with
    | none => agSetState g .completed; return .inr ()
    | some next =>
      if next.kind == 2 then
        agAwaitReturn g
        return .inr ()
      if next.kind == 1 then agCompleteStep g true next.value true
      else agCompleteStep g false .undefined true
      return .inl ()
where
  agAwaitReturn (g : ObjId) : M Unit := do
    let some next ← agFirst g | M.halt "internal: async generator queue empty"
    let pc ← intrinsicV "%Promise%"
    match ← M.attempt (promiseResolve pc next.value) with
    | .error e =>
      agCompleteStep g true e true
      -- (drain the rest: a recursive drain is a job away; queue the remaining work)
      let f ← makeBuiltinFn "AsyncGeneratorDrain" 0 JSStr.empty #[.obj g]
      enqueueJob (.obj f) #[]
    | .ok (.obj p) =>
      let onF ← makeBuiltinFn "AsyncGeneratorReturnSettled" 1 JSStr.empty #[.obj g, .bool false]
      let onR ← makeBuiltinFn "AsyncGeneratorReturnSettled" 1 JSStr.empty #[.obj g, .bool true]
      let _ ← performPromiseThen p (.obj onF) (.obj onR) none
    | .ok _ => M.halt "internal: PromiseResolve gave a non-object"

/-- The closures of AsyncGeneratorAwaitReturn. -/
def agReturnSettled : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let .obj g := s[0]! | M.halt "internal"
  agSetState g .drainingQueue
  agCompleteStep g (toBoolean s[1]!) (arg args 0) true
  agDrainQueue g
  pure .undefined

def agDrainBuiltin : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  let .obj g := s[0]! | M.halt "internal"
  agDrainQueue g
  pure .undefined

/-- AsyncGeneratorResume: resumes the body with a request's completion. -/
def agResume (g : ObjId) (kind : Nat) (v : Value) : M Unit := do
  agSetState g .executing
  let o := match kind with | 0 => Outcome.normal v | 1 => .throw v | _ => .ret v
  let realm ← readS (·.realm)
  let _ ← M.request (.resume g o)
  modify fun s => { s with realm }

/-- AsyncGenerator.prototype.next/return/throw (`kind` 0/1/2 as in the queue: 0 next, 1 throw,
2 return). spec: https://tc39.es/ecma262/#sec-asyncgenerator-prototype-next -/
def asyncGenMethod (kind : Nat) : BuiltinFn := fun _ thisV args _ => do
  let cap ← newIntrinsicPromise
  let v := arg args 0
  -- AsyncGeneratorValidate
  let valid ← match thisV with
    | .obj g => do match ← objKind g with
      | .coroutine _ _ _ _ true true _ => pure (some g)
      | _ => pure none
    | _ => pure none
  let some g := valid | do
    let e ← makeError .typeError "AsyncGenerator method called on incompatible receiver"
    let _ ← call cap.reject .undefined #[e]
    return cap.promise
  let st ← agState g
  match kind with
  | 0 =>
    if st == .completed then
      let r ← createIterResult .undefined true
      let _ ← call cap.resolve .undefined #[r]
      return cap.promise
    agEnqueue g 0 v cap
    if st == .suspendedStart || st == .suspendedYield then agResume g 0 v
    pure cap.promise
  | 2 =>
    agEnqueue g 2 v cap
    if st == .suspendedStart || st == .completed then
      agSetState g .drainingQueue
      agDrainQueue.agAwaitReturn g
    else if st == .suspendedYield then agResume g 2 v
    pure cap.promise
  | _ =>
    let st ← if st == .suspendedStart then do agSetState g .completed; pure GenState.completed else pure st
    if st == .completed then
      let _ ← call cap.reject .undefined #[v]
      return cap.promise
    agEnqueue g 1 v cap
    if st == .suspendedYield then agResume g 1 v
    pure cap.promise

/-! ## Async iteration -/

/-- CreateAsyncFromSyncIterator spec: https://tc39.es/ecma262/#sec-createasyncfromsynciterator -/
def createAsyncFromSyncIterator (r : IterRecord) : M IterRecord := do
  let proto ← intrinsic "%AsyncFromSyncIteratorPrototype%"
  let o ← alloc { proto := .obj proto, kind := .internal "AsyncFromSyncIterator" #[r.iter, r.next] }
  let next ← getProp proto (.str kNext)
  pure { iter := .obj o, next }

/-- GetIterator(obj, async) spec: https://tc39.es/ecma262/#sec-getiterator -/
def getAsyncIterator (o : Value) : M IterRecord := do
  match ← getMethodOf o (.sym WK.asyncIterator) with
  | some m => getIteratorFromMethod o m
  | none =>
    match ← getMethodOf o (.sym WK.iterator) with
    | none => throwType "object is not async iterable"
    | some sm =>
      let sr ← getIteratorFromMethod o sm
      createAsyncFromSyncIterator sr

/-- AsyncIteratorClose with a normal completion (or a return-like one): the `return` result is
awaited and must be an object. spec: https://tc39.es/ecma262/#sec-asynciteratorclose -/
def asyncIteratorClose (r : IterRecord) : M Unit := do
  match ← getMethodOf r.iter (.str "return") with
  | none => pure ()
  | some f =>
    let inner ← call f r.iter #[]
    let inner ← await inner
    if !inner.isObject then throwType "Iterator result is not an object"

/-- AsyncIteratorClose with a throw completion: the original exception wins. -/
def asyncIteratorCloseOnThrow {α} (r : IterRecord) (e : Value) : M α := do
  let _ ← M.attempt do
    match ← getMethodOf r.iter (.str "return") with
    | some f => let inner ← call f r.iter #[]; let _ ← await inner; pure ()
    | none => pure ()
  M.throwV e

/-- AsyncFromSyncIteratorContinuation
spec: https://tc39.es/ecma262/#sec-asyncfromsynciteratorcontinuation -/
def asyncFromSyncContinuation (result : Value) (cap : Capability) (sync : IterRecord) (closeOnRejection : Bool) : M Value := do
  let reject (e : Value) : M Value := do let _ ← call cap.reject .undefined #[e]; pure cap.promise
  -- 1-4.
  let done ← match ← M.attempt (iteratorComplete result) with
    | .ok d => pure d
    | .error e => return ← reject e
  let value ← match ← M.attempt (iteratorValue result) with
    | .ok v => pure v
    | .error e => return ← reject e
  -- 5-7.
  let pc ← intrinsicV "%Promise%"
  let wrapper ← match ← M.attempt (promiseResolve pc value) with
    | .ok w => pure w
    | .error e =>
      if !done && closeOnRejection then
        let _ ← M.attempt (iteratorClose sync)
      return ← reject e
  -- 8-13.
  let onF ← makeBuiltinFn "AsyncFromSyncUnwrap" 1 JSStr.empty #[.bool done]
  let onR ← if done || !closeOnRejection then pure Value.undefined else do
    pure (.obj (← makeBuiltinFn "AsyncFromSyncClose" 1 JSStr.empty #[sync.iter, sync.next]))
  let .obj p := wrapper | M.halt "internal"
  performPromiseThen p (.obj onF) onR (some cap)

def asyncFromSyncUnwrap : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  createIterResult (arg args 0) (toBoolean s[0]!)

def asyncFromSyncClose : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  iteratorCloseOnThrow { iter := s[0]!, next := s[1]! } (arg args 0)

def asyncFromSyncRecord (thisV : Value) : M IterRecord := do
  let .obj o := thisV | M.halt "internal"
  match ← objKind o with
  | .internal "AsyncFromSyncIterator" s => pure { iter := s[0]!, next := s[1]! }
  | _ => M.halt "internal: not an async-from-sync iterator"

/-- %AsyncFromSyncIteratorPrototype%.next/return/throw (`kind` 0/1/2: next/throw/return).
spec: https://tc39.es/ecma262/#sec-%asyncfromsynciteratorprototype%.next -/
def asyncFromSyncMethod (kind : Nat) : BuiltinFn := fun _ thisV args _ => do
  let cap ← newIntrinsicPromise
  let sync ← asyncFromSyncRecord thisV
  let reject (e : Value) : M Value := do let _ ← call cap.reject .undefined #[e]; pure cap.promise
  match kind with
  | 0 =>
    match ← M.attempt (iteratorNext sync (if args.size > 0 then some args[0]! else none)) with
    | .error e => reject e
    | .ok r => asyncFromSyncContinuation r cap sync true
  | 2 =>
    match ← M.attempt (getMethodOf sync.iter (.str "return")) with
    | .error e => reject e
    | .ok none =>
      let r ← createIterResult (arg args 0) true
      let _ ← call cap.resolve .undefined #[r]
      pure cap.promise
    | .ok (some f) =>
      match ← M.attempt (call f sync.iter (if args.size > 0 then #[args[0]!] else #[])) with
      | .error e => reject e
      | .ok r =>
        if !r.isObject then return ← reject (← makeError .typeError "iterator result is not an object")
        asyncFromSyncContinuation r cap sync false
  | _ =>
    match ← M.attempt (getMethodOf sync.iter (.str "throw")) with
    | .error e => reject e
    | .ok none =>
      match ← M.attempt (iteratorClose sync) with
      | .error e => reject e
      | .ok _ => reject (← makeError .typeError "The iterator does not provide a 'throw' method")
    | .ok (some f) =>
      match ← M.attempt (call f sync.iter #[arg args 0]) with
      | .error e => reject e
      | .ok r =>
        if !r.isObject then return ← reject (← makeError .typeError "iterator result is not an object")
        asyncFromSyncContinuation r cap sync true

def asyncGenBuiltins : Array BuiltinDef := #[
  ⟨"AsyncGenerator.prototype.next", asyncGenMethod 0⟩,
  ⟨"AsyncGenerator.prototype.throw", asyncGenMethod 1⟩,
  ⟨"AsyncGenerator.prototype.return", asyncGenMethod 2⟩,
  ⟨"AsyncGeneratorReturnSettled", agReturnSettled⟩, ⟨"AsyncGeneratorDrain", agDrainBuiltin⟩,
  ⟨"%AsyncFromSyncIteratorPrototype%.next", asyncFromSyncMethod 0⟩,
  ⟨"%AsyncFromSyncIteratorPrototype%.throw", asyncFromSyncMethod 1⟩,
  ⟨"%AsyncFromSyncIteratorPrototype%.return", asyncFromSyncMethod 2⟩,
  ⟨"AsyncFromSyncUnwrap", asyncFromSyncUnwrap⟩, ⟨"AsyncFromSyncClose", asyncFromSyncClose⟩]

end ES
