import ES.Driver

/-!
# Realms: creating the intrinsics and the global object

spec: https://tc39.es/ecma262/#sec-createrealm (CreateRealm, CreateIntrinsics,
SetRealmGlobalObject, SetDefaultGlobalBindings)

Each built-ins module contributes behaviours (`BuiltinDef`s) and a setup (`M Unit`) that creates
its intrinsics in the realm being created (the current realm while setups run), registering
them by name (`regIntrinsic`) and defining its global properties (`defGlobal`). The fundamental
objects (%Object.prototype%, %Function.prototype%) exist before any setup runs.
-/

namespace ES

open ES (F64)

/-- Registers `%name%` in the current realm. -/
def regIntrinsic (name : String) (id : ObjId) : M Unit := modify fun s =>
  { s with realms := s.realms.modify s.realm fun r => { r with intrinsics := r.intrinsics.insert name id } }

/-- Defines a global property (writable, non-enumerable, configurable; the default of
SetDefaultGlobalBindings). -/
def defGlobal (name : String) (v : Value) : M Unit := do
  let g ← readS (·.curRealm.globalObj)
  setOwn g (.str (JSStr.ofString name)) (.data v true false true)

/-- Creates a built-in constructor `%Name%` with its prototype object `%Name.prototype%` (which
must already be registered, or `protoKind` makes a fresh one), defines the global binding, and
returns (constructor, prototype). -/
def defConstructor (name : String) (length : Nat) (behaviour : String) (proto : ObjId)
    (ctorProto : Option ObjId := none) (global := true) : M (ObjId × ObjId) := do
  let c ← makeBuiltinFn behaviour length (JSStr.ofString name) #[] true
  if let some cp := ctorProto then modifyObj c fun o => { o with proto := .obj cp }
  setOwn c (.str kPrototype) (.data (.obj proto) false false false)
  setOwn proto (.str kConstructor) (.data (.obj c) true false true)
  regIntrinsic s!"%{name}%" c
  regIntrinsic s!"%{name}.prototype%" proto
  if global then defGlobal name (.obj c)
  pure (c, proto)

/-- A new ordinary object inheriting from %Object.prototype%, registered as `%name%`. -/
def newIntrinsicObject (name : String) (proto : Option ObjId := none) (kind : Kind := .ordinary) : M ObjId := do
  let p ← match proto with
    | some p => pure p
    | none => readS (·.curRealm.objectProto)
  let o ← alloc { proto := .obj p, kind }
  regIntrinsic name o
  pure o

/-- The initial symbol table: the well-known symbols, then the internal sentinels. -/
def initialSymbols : Array (Option JSStr) :=
  WK.names.map (fun n => some (JSStr.ofString n)) |>.push (some "(optional chain)")

/-- CreateRealm + SetRealmGlobalObject + SetDefaultGlobalBindings: a new realm with the
intrinsics the setups create; returns its index (the current realm is unchanged). -/
def createRealm (setups : Array (M Unit)) : M Nat := do
  let (prev, idx) ← readS fun s => (s.realm, s.realms.size)
  modify fun s => { s with realms := s.realms.push {}, realm := idx }
  -- %Object.prototype%: an immutable prototype exotic object
  let op ← alloc { proto := .null, immutableProto := true }
  -- %Function.prototype%: a built-in function that returns undefined
  let fpId ← builtinId "FunctionPrototype"
  let fp ← alloc { proto := .obj op, kind := .builtin { id := fpId, realm := idx } }
  setOwn fp (.str kLength) (.data (numV 0) false false true)
  setOwn fp (.str kName) (.data (.str JSStr.empty) false false true)
  -- the global object and environment
  let g ← alloc { proto := .obj op }
  let genv ← allocEnv (.global g {} (.obj g))
  modify fun s => { s with realms := s.realms.modify idx fun r =>
    { r with objectProto := op, functionProto := fp, globalObj := g, globalEnv := genv } }
  regIntrinsic "%Object.prototype%" op
  regIntrinsic "%Function.prototype%" fp
  M.forArr setups id
  -- SetDefaultGlobalBindings: the value properties of the global object
  setOwn g (.str "globalThis") (.data (.obj g) true false true)
  setOwn g (.str "NaN") (.data (.num .nan) false false false)
  setOwn g (.str "Infinity") (.data (.num (.inf false)) false false false)
  setOwn g (.str "undefined") (.data .undefined false false false)
  let ap ← intrinsic "%Array.prototype%"
  modify fun s => { s with realms := s.realms.modify idx fun r => { r with arrayProto := ap } }
  modify fun s => { s with realm := prev }
  pure idx

/-- A fresh engine state: the symbol table and the built-in ids. -/
def initialState (defs : Array BuiltinDef) : State :=
  { symbols := initialSymbols,
    builtinIds := (defs.zipIdx).foldl (fun m (d, i) => m.insert d.name i) {} }

end ES
