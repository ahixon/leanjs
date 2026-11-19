import ES.Env

/-!
# Built-in functions: the behaviour table and helpers for defining intrinsics

A built-in function object (`Kind.builtin`) names its behaviour by an index into the engine's
table of behaviours (`State.builtinIds` maps names to indices). A behaviour gets the function
object itself (for its slots: closures such as promise resolving functions), the this value,
the arguments, and the NewTarget (`undefined` for [[Call]]).
spec: https://tc39.es/ecma262/#sec-built-in-function-objects
-/

namespace ES

open ES (F64)

abbrev BuiltinFn := (self : ObjId) → (thisV : Value) → (args : Array Value) → (newTarget : Value) → M Value

/-- A named behaviour. -/
structure BuiltinDef where
  name : String
  fn : BuiltinFn

@[inline] def arg (args : Array Value) (i : Nat) : Value := args[i]?.getD .undefined

/-- The slots of a built-in function object. -/
def builtinSlots (self : ObjId) : M (Array Value) := do
  match ← objKind self with
  | .builtin b => pure b.slots
  | _ => pure #[]

def setBuiltinSlots (self : ObjId) (slots : Array Value) : M Unit := modifyObj self fun o =>
  o.withKind fun k => match k with
    | .builtin b => .builtin { b with slots }
    | k => k

/-- Defines a built-in method `key` on `o` (writable, non-enumerable, configurable). -/
def defMethod (o : ObjId) (key : PropKey) (behaviour : String) (length : Nat)
    (fnName : Option JSStr := none) : M ObjId := do
  let nm : JSStr ← match fnName, key with
    | some n, _ => pure n
    | none, .str s => pure s
    | none, .sym id => do
      let d ← readS fun s => (s.symbols[id]?).bind (fun x => x)
      pure (JSStr.ofString "[" ++ d.getD JSStr.empty ++ JSStr.ofString "]")
  let f ← makeBuiltinFn behaviour length nm
  setOwn o key (.data (.obj f) true false true)
  pure f

/-- Defines an accessor with a built-in getter (and optional setter). -/
def defGetter (o : ObjId) (key : PropKey) (getter : String) (setter : Option String := none) : M Unit := do
  let nm : JSStr ← match key with
    | .str s => pure s
    | .sym id => do
      let d ← readS fun s => (s.symbols[id]?).bind (fun x => x)
      pure (JSStr.ofString "[" ++ d.getD JSStr.empty ++ JSStr.ofString "]")
  let g ← makeBuiltinFn getter 0 (JSStr.ofString "get " ++ nm)
  let s ← match setter with
    | some st => do pure (Value.obj (← makeBuiltinFn st 1 (JSStr.ofString "set " ++ nm)))
    | none => pure .undefined
  setOwn o key (.accessor (.obj g) s false true)

/-- Defines a data property with the given attributes. -/
def defValue (o : ObjId) (key : PropKey) (v : Value) (w e c : Bool := false) : M Unit :=
  setOwn o key (.data v w e c)

/-- The current realm's intrinsic as a Value. -/
def intrinsicV (name : String) : M Value := do pure (.obj (← intrinsic name))

/-- Checks a this value is an object with a given internal kind (RequireInternalSlot). -/
def thisObj (thisV : Value) (what : String) : M ObjId := do
  match thisV with
  | .obj o => pure o
  | _ => throwType s!"{what} called on non-object"

def numV (n : Nat) : Value := .num (Conv.ofNat n)
def intV (i : Int) : Value := .num (F64.ofInt i)

end ES
