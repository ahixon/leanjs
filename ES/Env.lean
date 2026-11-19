import ES.Ops

/-!
# Environment Records and References

spec: https://tc39.es/ecma262/#sec-environment-records (9.1),
https://tc39.es/ecma262/#sec-reference-record-specification-type (6.2.5)
-/

namespace ES

open Std (HashMap)

/-- A Reference Record: a binding of an Environment Record (`env = none`: unresolvable), a
property of a value (with the key not yet converted — ToPropertyKey happens at GetValue/PutValue
— and, for `super` references, the this value), or a private name.
spec: https://tc39.es/ecma262/#sec-reference-record-specification-type -/
inductive Ref where
  | env (env : Option EnvId) (name : JSStr) (strict : Bool)
  | prop (base : Value) (key : Value) (strict : Bool) (thisValue : Option Value)
  | priv (base : Value) (id : Nat)
  /-- Not a reference: the value of an expression that is not a reference (assigning to it is a
  ReferenceError; `delete` of it is true). -/
  | value (v : Value)
  deriving Inhabited

def Env.outer : Env → Option EnvId
  | .decl _ o | .func _ o .. | .object _ _ o | .module _ _ o => o
  | .global .. => none

def Env.bindings? : Env → Option (HashMap JSStr Binding)
  | .decl b _ | .func b .. | .module b .. => some b
  | .global _ b _ => some b
  | .object .. => none

/-- Updates the declarative bindings of an environment (the global record's declarative part). -/
def Env.withBindings (e : Env) (f : HashMap JSStr Binding → HashMap JSStr Binding) : Env :=
  match e with
  | .decl b o => .decl (f b) o
  | .func b o ts tv fo nt => .func (f b) o ts tv fo nt
  | .module b i o => .module (f b) i o
  | .global g b t => .global g (f b) t
  | e => e

def newDeclEnv (outer : Option EnvId) : M EnvId := allocEnv (.decl {} outer)

def kUnscopables : PropKey := .sym WK.unscopables

/-- HasBinding(N) spec: https://tc39.es/ecma262/#sec-declarative-environment-records-hasbinding-n
(and the object, global and module records' versions) -/
def hasBinding (env : EnvId) (n : JSStr) : M Bool := do
  match ← readEnv env id with
  | .decl b _ | .func b .. => pure (b.contains n)
  | .module b imps _ => pure (b.contains n || imps.contains n)
  | .object o isWith _ =>
    -- spec: https://tc39.es/ecma262/#sec-object-environment-records-hasbinding-n
    if !(← Obj'.hasProperty o (.str n)) then return false
    if !isWith then return true
    let unscopables ← getProp o kUnscopables
    match unscopables with
    | .obj u => pure !(toBoolean (← getProp u (.str n)))
    | _ => pure true
  | .global g b _ =>
    if b.contains n then return true
    Obj'.hasProperty g (.str n)

/-- CreateMutableBinding(N, D) -/
def createMutableBinding (env : EnvId) (n : JSStr) (deletable : Bool) : M Unit := do
  match ← readEnv env id with
  | .object o _ _ =>
    -- spec: https://tc39.es/ecma262/#sec-object-environment-records-createmutablebinding-n-d
    definePropertyOrThrow o (.str n) (PropDesc.data .undefined true true deletable)
  | _ => modifyEnv env (·.withBindings (·.insert n { deletable }))

/-- CreateImmutableBinding(N, S) -/
def createImmutableBinding (env : EnvId) (n : JSStr) (strict : Bool) : M Unit :=
  modifyEnv env (·.withBindings (·.insert n { mutable := false, strict }))

/-- InitializeBinding(N, V) -/
def initializeBinding (env : EnvId) (n : JSStr) (v : Value) : M Unit := do
  match ← readEnv env id with
  | .object o _ _ =>
    -- spec: https://tc39.es/ecma262/#sec-object-environment-records-initializebinding-n-v
    let _ ← Obj'.set o (.str n) v (.obj o)
  | .global g b _ =>
    if b.contains n then modifyEnv env (·.withBindings (·.modify n fun bd => { bd with value := some v }))
    else let _ ← Obj'.set g (.str n) v (.obj g)
  | _ => modifyEnv env (·.withBindings (·.modify n fun bd => { bd with value := some v }))

def refError {α} (n : JSStr) : M α := throwError .referenceError s!"{n} is not defined"
def tdzError {α} (n : JSStr) : M α := throwError .referenceError s!"Cannot access '{n}' before initialization"

/-- SetMutableBinding(N, V, S) of a declarative record (the bindings map `b`).
spec: https://tc39.es/ecma262/#sec-declarative-environment-records-setmutablebinding-n-v-s -/
def declSetMutable (env : EnvId) (b : HashMap JSStr Binding) (n : JSStr) (v : Value) (strict : Bool) : M Unit := do
  match b.get? n with
  -- 1.
  | none =>
    if strict then refError n
    modifyEnv env (·.withBindings (·.insert n { value := some v, deletable := true }))
  | some bd =>
    -- 2.
    let strict := strict || bd.strict
    -- 3.
    if bd.value.isNone then tdzError n
    -- 4.
    else if bd.mutable then modifyEnv env (·.withBindings (·.modify n fun bd => { bd with value := some v }))
    -- 5.
    else if strict then throwType "Assignment to constant variable."

/-- SetMutableBinding(N, V, S) -/
def setMutableBinding (env : EnvId) (n : JSStr) (v : Value) (strict : Bool) : M Unit := do
  match ← readEnv env id with
  | .decl b _ | .func b .. => declSetMutable env b n v strict
  | .module b imps _ =>
    if imps.contains n then throwType "Assignment to constant variable."
    declSetMutable env b n v strict
  | .object o _ _ =>
    -- spec: https://tc39.es/ecma262/#sec-object-environment-records-setmutablebinding-n-v-s
    let still ← Obj'.hasProperty o (.str n)
    if !still && strict then refError n
    setProp o (.str n) v strict
  | .global g b _ =>
    if b.contains n then declSetMutable env b n v strict
    else
      let still ← Obj'.hasProperty g (.str n)
      if !still && strict then refError n
      setProp g (.str n) v strict

/-- The value of a module's binding (following imports to the exporting module's environment).
`resolveImport` gives the target environment and binding name for an imported binding. -/
def moduleBindingValue (b : HashMap JSStr Binding) (n : JSStr) : M Value :=
  match (b.get? n).bind (·.value) with
  | some v => pure v
  | none => tdzError n

/-- GetBindingValue(N, S) -/
def getBindingValue (env : EnvId) (n : JSStr) (strict : Bool) : M Value := do
  match ← readEnv env id with
  | .decl b _ | .func b .. =>
    match b.get? n with
    | some { value := some v, .. } => pure v
    | some _ => tdzError n
    | none => refError n
  | .module b imps _ =>
    match imps.get? n with
    | some (m, name) => do
      let mr? ← readS (·.modules[m]?)
      let some mr := mr? | M.halt "internal: bad module"
      match name with
      | none => match mr.ns with
        | some ns => pure (.obj ns)
        | none => M.halt "internal: namespace not created"
      | some name =>
        let some e := mr.env | tdzError n
        match ← readEnv e id with
        | .module tb _ _ => moduleBindingValue tb name
        | _ => M.halt "internal: bad module environment"
    | none => moduleBindingValue b n
  | .object o _ _ =>
    -- spec: https://tc39.es/ecma262/#sec-object-environment-records-getbindingvalue-n-s
    if !(← Obj'.hasProperty o (.str n)) then
      if strict then refError n else return .undefined
    getProp o (.str n)
  | .global g b _ =>
    match b.get? n with
    | some { value := some v, .. } => pure v
    | some _ => tdzError n
    | none =>
      if !(← Obj'.hasProperty g (.str n)) then
        if strict then refError n else return .undefined
      getProp g (.str n)

/-- DeleteBinding(N) -/
def deleteBinding (env : EnvId) (n : JSStr) : M Bool := do
  match ← readEnv env id with
  | .decl b _ | .func b .. =>
    match b.get? n with
    | some bd => if bd.deletable then modifyEnv env (·.withBindings (·.erase n)); pure true else pure false
    | none => pure true
  | .module .. => pure false
  | .object o _ _ => Obj'.delete o (.str n)
  | .global g b _ =>
    if b.contains n then
      match b.get? n with
      | some bd => if bd.deletable then modifyEnv env (·.withBindings (·.erase n)); pure true else pure false
      | none => pure true
    else Obj'.delete g (.str n)

/-- GetIdentifierReference spec: https://tc39.es/ecma262/#sec-getidentifierreference -/
def resolveBinding (env : EnvId) (n : JSStr) (strict : Bool) : M Ref :=
  M.repeatFrom (some env) fun e => do
    match e with
    | none => return .inr (.env none n strict)
    | some e =>
      if ← hasBinding e n then return .inr (.env (some e) n strict)
      return .inl (← readEnv e Env.outer)

/-- GetThisEnvironment spec: https://tc39.es/ecma262/#sec-getthisenvironment -/
def getThisEnvironment (env : EnvId) : M EnvId :=
  M.repeatFrom env fun e => do
    match ← readEnv e id with
    | .func _ o ts .. =>
      if ts == .lexical then
        match o with
        | some o => return .inl o
        | none => M.halt "internal: arrow environment without outer"
      else return .inr e
    | .global .. | .module .. => return .inr e
    | ev => match ev.outer with
      | some o => return .inl o
      | none => return .inr e

/-- ResolveThisBinding spec: https://tc39.es/ecma262/#sec-resolvethisbinding -/
def resolveThisBinding (env : EnvId) : M Value := do
  let e ← getThisEnvironment env
  match ← readEnv e id with
  | .func _ _ ts tv .. =>
    if ts == .uninitialized then
      throwError .referenceError "Must call super constructor in derived class before accessing 'this' or returning from derived constructor"
    pure tv
  | .global _ _ tv => pure tv
  | _ => pure .undefined

/-- BindThisValue spec: https://tc39.es/ecma262/#sec-bindthisvalue -/
def bindThisValue (env : EnvId) (v : Value) : M Unit := do
  match ← readEnv env id with
  | .func b o ts _ fo nt =>
    if ts == .initialized then
      throwError .referenceError "Super constructor may only be called once"
    modifyEnv env fun _ => .func b o .initialized v fo nt
  | _ => M.halt "internal: BindThisValue on a non-function environment"

/-- GetValue for references.
spec: https://tc39.es/ecma262/#sec-getvalue -/
def getRefValue (r : Ref) : M Value := do
  match r with
  | .env none n _ => refError n
  | .env (some e) n strict => getBindingValue e n strict
  | .prop base key _ thisV => do
    -- 3.a (ToObject's TypeError comes before ToPropertyKey)
    if base.isNullish then
      throwType s!"Cannot read properties of {if base.isUndefined then "undefined" else "null"}"
    let k ← toPropertyKey key
    match base with
    | .obj o => Obj'.get o k (thisV.getD base)
    | _ =>
      -- (primitive base: the wrapper's [[Get]] with the primitive as receiver)
      match base, k with
      | .str s, .str ks =>
        if ks == kLength then return .num (Conv.ofNat s.length)
        match ks.toIndex? with
        | some i => if i < s.length then return .str (s.slice i (i + 1)) else pure ()
        | none => pure ()
      | _, _ => pure ()
      let o ← toObject base
      Obj'.get o k (thisV.getD base)
  | .priv base id => privateGet base id
  | .value v => pure v
where
  /-- PrivateGet spec: https://tc39.es/ecma262/#sec-privateget -/
  privateGet (base : Value) (id : Nat) : M Value := do
    let .obj o := base | throwType "Cannot read private member from a non-object"
    let elems ← readObj o (·.privates)
    match elems.find? (·.1 == id) with
    | none => throwType "Cannot read private member from an object whose class did not declare it"
    | some (_, .field v) | some (_, .method v) => pure v
    | some (_, .accessor g _) =>
      if g.isUndefined then throwType "'#' accessor was defined without a getter"
      call g base #[]

/-- GetValue that also returns the reference with its key converted (GetValue sets
[[ReferencedName]] to the property key, so a later PutValue does not convert it again).
spec: https://tc39.es/ecma262/#sec-getvalue -/
def getRefValueOnce (r : Ref) : M (Value × Ref) := do
  match r with
  | .prop base key strict thisV =>
    if base.isNullish then
      throwType s!"Cannot read properties of {if base.isUndefined then "undefined" else "null"}"
    let k ← toPropertyKey key
    let r' := Ref.prop base (keyToValue k) strict thisV
    pure (← getRefValue r', r')
  | r => pure (← getRefValue r, r)

/-- ResolveBinding then GetValue for an identifier, in one walk: declarative records answer
directly; the first object/global/module record goes through the general path (same results).
spec: https://tc39.es/ecma262/#sec-getidentifierreference -/
def identValue (env : EnvId) (n : JSStr) (strict : Bool) : M Value :=
  M.repeatFrom env fun e => do
    let r ← readEnv e fun ev => match ev with
      | .decl b o | .func b o .. => match b.get? n with
        | some bd => Sum.inr (Sum.inl bd.value)
        | none => match o with
          | some o => Sum.inl o
          | none => Sum.inr (Sum.inr ())
      | _ => Sum.inr (Sum.inr ())
    match r with
    | .inl o => return .inl o
    | .inr (.inl (some v)) => return .inr v
    | .inr (.inl none) => tdzError n
    | .inr (.inr ()) => return .inr (← getRefValue (← resolveBinding e n strict))

/-- PrivateSet spec: https://tc39.es/ecma262/#sec-privateset -/
def privateSet (base : Value) (id : Nat) (v : Value) : M Unit := do
  let .obj o := base | throwType "Cannot write private member to a non-object"
  let elems ← readObj o (·.privates)
  match elems.findIdx? (·.1 == id) with
  | none => throwType "Cannot write private member to an object whose class did not declare it"
  | some i => match elems[i]! with
    | (_, .field _) => modifyObj o fun ob => { ob with privates := ob.privates.set! i (id, .field v) }
    | (_, .method _) => throwType "Private method is not writable"
    | (_, .accessor _ s) =>
      if s.isUndefined then throwType "'#' accessor was defined without a setter"
      let _ ← call s base #[v]

/-- PutValue spec: https://tc39.es/ecma262/#sec-putvalue -/
def putRefValue (r : Ref) (v : Value) : M Unit := do
  match r with
  | .env none n strict =>
    if strict then refError n
    let g ← readS (·.curRealm.globalObj)
    let _ ← Obj'.set g (.str n) v (.obj g)
  | .env (some e) n strict => setMutableBinding e n v strict
  | .prop base key strict thisV => do
    let k ← toPropertyKey key
    match base with
    | .obj o =>
      let ok ← Obj'.set o k v (thisV.getD base)
      if !ok && strict then throwType s!"Cannot assign to read only property"
    | _ =>
      let o ← toObject base
      let ok ← Obj'.set o k v (thisV.getD base)
      if !ok && strict then throwType s!"Cannot create property on primitive value"
  | .priv base id => privateSet base id v
  | .value _ => throwError .referenceError "Invalid left-hand side in assignment"

/-- InitializeReferencedBinding spec: https://tc39.es/ecma262/#sec-initializereferencedbinding -/
def initializeRefBinding (r : Ref) (v : Value) : M Unit := do
  match r with
  | .env (some e) n _ => initializeBinding e n v
  | _ => M.halt "internal: InitializeReferencedBinding on a non-binding reference"

end ES
