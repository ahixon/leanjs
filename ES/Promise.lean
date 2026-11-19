import ES.Builtin

/-!
# Promise abstract operations

spec: https://tc39.es/ecma262/#sec-promise-abstract-operations (27.2.1, 27.2.2)

Closures (resolving functions, reaction jobs, capability executors) are built-in function
objects with slots; jobs are queued as calls (`enqueueJob`).
-/

namespace ES

/-- A PromiseCapability Record. spec: https://tc39.es/ecma262/#sec-promisecapability-records -/
structure Capability where
  promise : Value
  resolve : Value
  reject : Value
  deriving Inhabited

def IsPromise (v : Value) : M Bool := do
  match v with
  | .obj o => match ← objKind o with
    | .promise .. => pure true
    | _ => pure false
  | _ => pure false

/-- CreateResolvingFunctions spec: https://tc39.es/ecma262/#sec-createresolvingfunctions -/
def createResolvingFunctions (promise : ObjId) : M (Value × Value) := do
  -- 1. (the shared alreadyResolved record)
  let rec_ ← alloc { kind := .internal "AlreadyResolved" #[.bool false] }
  let resolve ← makeBuiltinFn "PromiseResolveFunction" 1 JSStr.empty #[.obj promise, .obj rec_]
  let reject ← makeBuiltinFn "PromiseRejectFunction" 1 JSStr.empty #[.obj promise, .obj rec_]
  pure (.obj resolve, .obj reject)

/-- TriggerPromiseReactions spec: https://tc39.es/ecma262/#sec-triggerpromisereactions -/
def triggerPromiseReactions (reactions : Array Reaction) (argument : Value) : M Unit :=
  M.forArr reactions fun r => newPromiseReactionJob r argument
where
  /-- NewPromiseReactionJob spec: https://tc39.es/ecma262/#sec-newpromisereactionjob -/
  newPromiseReactionJob (r : Reaction) (argument : Value) : M Unit := do
    let (p, res, rej) := match r.capability with
      | some (p, res, rej) => (p, res, rej)
      | none => (.undefined, .undefined, .undefined)
    -- (the handler's realm decides the job's realm; the job is a built-in closure)
    let job ← makeBuiltinFn "PromiseReactionJob" 0 JSStr.empty
      #[p, res, rej, .bool r.isFulfill, r.handler, argument, .bool r.capability.isSome]
    enqueueJob (.obj job) #[]

/-- FulfillPromise spec: https://tc39.es/ecma262/#sec-fulfillpromise -/
def fulfillPromise (p : ObjId) (v : Value) : M Unit := do
  let .promise _ _ fulfill _ handled ← objKind p | M.halt "internal: FulfillPromise on a non-promise"
  modifyObj p fun o => { o with kind := .promise .fulfilled v #[] #[] handled }
  triggerPromiseReactions fulfill v

/-- HostPromiseRejectionTracker spec: https://tc39.es/ecma262/#sec-host-promise-rejection-tracker -/
def promiseRejectionTracker (p : ObjId) (isReject : Bool) : M Unit := modify fun s =>
  if isReject then { s with rejections := s.rejections.push p }
  else { s with rejections := s.rejections.filter (· != p) }

/-- RejectPromise spec: https://tc39.es/ecma262/#sec-rejectpromise -/
def rejectPromise (p : ObjId) (reason : Value) : M Unit := do
  let .promise _ _ _ reject handled ← objKind p | M.halt "internal: RejectPromise on a non-promise"
  modifyObj p fun o => { o with kind := .promise .rejected reason #[] #[] handled }
  if !handled then promiseRejectionTracker p true
  triggerPromiseReactions reject reason

/-- The behaviour of a promise's resolve function.
spec: https://tc39.es/ecma262/#sec-promise-resolve-functions -/
def promiseResolveFunction : BuiltinFn := fun self _ args _ => do
  let slots ← builtinSlots self
  let (.obj promise, .obj rec_) := (slots[0]!, slots[1]!) | M.halt "internal: resolve function slots"
  let resolution := arg args 0
  -- 5-6.
  if toBoolean ((← readObj rec_ (fun o => match o.kind with
      | .internal _ s => s[0]! | _ => .bool true))) then return .undefined
  -- 6.
  modifyObj rec_ fun o => { o with kind := .internal "AlreadyResolved" #[.bool true] }
  -- 7.
  if sameValue resolution (.obj promise) then
    let e ← makeError .typeError "Chaining cycle detected for promise"
    rejectPromise promise e
    return .undefined
  -- 8.
  let .obj ro := resolution | fulfillPromise promise resolution; return .undefined
  -- 9.
  let thenAction ← M.attempt (getProp ro (.str "then"))
  match thenAction with
  -- 10.
  | .error e => rejectPromise promise e; return .undefined
  | .ok thenV =>
    -- 12.
    if !(← isCallable thenV) then fulfillPromise promise resolution; return .undefined
    -- 13-16. NewPromiseResolveThenableJob
    let job ← makeBuiltinFn "PromiseResolveThenableJob" 0 JSStr.empty #[.obj promise, resolution, thenV]
    enqueueJob (.obj job) #[]
    return .undefined

/-- The behaviour of a promise's reject function.
spec: https://tc39.es/ecma262/#sec-promise-reject-functions -/
def promiseRejectFunction : BuiltinFn := fun self _ args _ => do
  let slots ← builtinSlots self
  let (.obj promise, .obj rec_) := (slots[0]!, slots[1]!) | M.halt "internal: reject function slots"
  if toBoolean ((← readObj rec_ (fun o => match o.kind with
      | .internal _ s => s[0]! | _ => .bool true))) then return .undefined
  modifyObj rec_ fun o => { o with kind := .internal "AlreadyResolved" #[.bool true] }
  rejectPromise promise (arg args 0)
  return .undefined

/-- The PromiseReactionJob closure. spec: https://tc39.es/ecma262/#sec-newpromisereactionjob -/
def promiseReactionJob : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  let (cp, cres, crej, isFulfill, handler, argument, hasCap) :=
    (s[0]!, s[1]!, s[2]!, toBoolean s[3]!, s[4]!, s[5]!, toBoolean s[6]!)
  -- c-f.
  let handlerResult : Except Value Value ←
    if handler.isUndefined then
      pure (if isFulfill then .ok argument else .error argument)
    else M.attempt (call handler .undefined #[argument])
  let _ := cp
  -- g.
  if !hasCap then return .undefined
  -- h-i.
  match handlerResult with
  | .error e => call crej .undefined #[e]
  | .ok v => call cres .undefined #[v]

/-- The PromiseResolveThenableJob closure.
spec: https://tc39.es/ecma262/#sec-newpromiseresolvethenablejob -/
def promiseResolveThenableJob : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  let (.obj promise, thenable, thenV) := (s[0]!, s[1]!, s[2]!) | M.halt "internal: thenable job slots"
  let (res, rej) ← createResolvingFunctions promise
  match ← M.attempt (call thenV thenable #[res, rej]) with
  | .error e => call rej .undefined #[e]
  | .ok v => pure v

/-- The GetCapabilitiesExecutor closure. spec: https://tc39.es/ecma262/#sec-newpromisecapability -/
def capabilitiesExecutor : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let .obj rec_ := s[0]! | M.halt "internal: executor slots"
  let (res, rej) ← readObj rec_ fun o => match o.kind with
    | .internal _ s => (s[0]!, s[1]!) | _ => (.undefined, .undefined)
  if !res.isUndefined then throwType "Promise executor has already been invoked with non-undefined arguments"
  if !rej.isUndefined then throwType "Promise executor has already been invoked with non-undefined arguments"
  modifyObj rec_ fun o => { o with kind := .internal "Capability" #[arg args 0, arg args 1] }
  return .undefined

/-- NewPromiseCapability(C) spec: https://tc39.es/ecma262/#sec-newpromisecapability -/
def newPromiseCapability (c : Value) : M Capability := do
  -- 1.
  if !(← isConstructor c) then throwType "Promise resolve or reject function is not callable"
  -- 3-5.
  let rec_ ← alloc { kind := .internal "Capability" #[.undefined, .undefined] }
  let executor ← makeBuiltinFn "GetCapabilitiesExecutor" 2 JSStr.empty #[.obj rec_]
  -- 6.
  let promise ← construct c #[.obj executor]
  -- 7-8.
  let (res, rej) ← readObj rec_ fun o => match o.kind with
    | .internal _ s => (s[0]!, s[1]!) | _ => (.undefined, .undefined)
  if !(← isCallable res) then throwType "Promise resolve function is not callable"
  if !(← isCallable rej) then throwType "Promise reject function is not callable"
  pure { promise, resolve := res, reject := rej }

/-- A new pending promise of the current realm with its resolving functions (NewPromiseCapability
of %Promise%, without observable steps). -/
def newIntrinsicPromise : M Capability := do
  let proto ← intrinsic "%Promise.prototype%"
  let p ← alloc { proto := .obj proto, kind := .promise .pending .undefined #[] #[] false }
  let (res, rej) ← createResolvingFunctions p
  pure { promise := .obj p, resolve := res, reject := rej }

/-- PromiseResolve(C, x) spec: https://tc39.es/ecma262/#sec-promise-resolve -/
def promiseResolve (c : Value) (x : Value) : M Value := do
  -- 1.
  if ← IsPromise x then
    let .obj xo := x | pure ()
    let xc ← getProp xo (.str kConstructor)
    if sameValue xc c then return x
  -- 2-4.
  let cap ← newPromiseCapability c
  let _ ← call cap.resolve .undefined #[x]
  pure cap.promise

/-- PerformPromiseThen spec: https://tc39.es/ecma262/#sec-performpromisethen -/
def performPromiseThen (p : ObjId) (onFulfilled onRejected : Value) (cap : Option Capability) : M Value := do
  -- 3-6.
  let onF := if ← isCallable onFulfilled then onFulfilled else .undefined
  let onR := if ← isCallable onRejected then onRejected else .undefined
  let capT := cap.map fun c => (c.promise, c.resolve, c.reject)
  let fr : Reaction := { capability := capT, isFulfill := true, handler := onF }
  let rr : Reaction := { capability := capT, isFulfill := false, handler := onR }
  let .promise st result fl rl handled ← objKind p | M.halt "internal: PerformPromiseThen on a non-promise"
  match st with
  -- 9.
  | .pending => modifyObj p fun o => { o with kind := .promise .pending result (fl.push fr) (rl.push rr) true }
  -- 10.
  | .fulfilled =>
    modifyObj p fun o => { o with kind := .promise st result fl rl true }
    triggerPromiseReactions.newPromiseReactionJob fr result
  -- 11.
  | .rejected =>
    if !handled then promiseRejectionTracker p false
    modifyObj p fun o => { o with kind := .promise st result fl rl true }
    triggerPromiseReactions.newPromiseReactionJob rr result
  -- 13-14.
  pure (match cap with | some c => c.promise | none => .undefined)

def promiseBuiltins : Array BuiltinDef := #[
  ⟨"PromiseResolveFunction", promiseResolveFunction⟩,
  ⟨"PromiseRejectFunction", promiseRejectFunction⟩,
  ⟨"PromiseReactionJob", promiseReactionJob⟩,
  ⟨"PromiseResolveThenableJob", promiseResolveThenableJob⟩,
  ⟨"GetCapabilitiesExecutor", capabilitiesExecutor⟩]

end ES
