import JSProofs.Env

/-!
# Objects: property maps and the heap as rewriting rules

`PropKey` equality is lawful (so `Std.HashMap` lemmas apply to property maps), property-map reads
after inserts, and heap reads after allocations and updates (`State.objEntry`).
-/

namespace ES

open Std (HashMap)

instance : LawfulBEq PropKey where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqPropKey.beq] <;>
      first
      | exact eq_of_beq (α := JSStr) h
      | exact h
  rfl {a} := by
    cases a <;> simp [BEq.beq, instBEqPropKey.beq] <;>
      first
      | exact beq_self_eq_true (α := JSStr) _
      | rfl

instance : DecidableEq PropKey := fun a b =>
  if h : (a == b) = true then isTrue (eq_of_beq h) else isFalse (fun e => h (e ▸ beq_self_eq_true a))

theorem PropMap.get?_insert (m : PropMap) (k k' : PropKey) (p : Property) :
    (m.insert k p).get? k' = if k = k' then some p else m.get? k' := by
  unfold PropMap.insert PropMap.get?
  split <;> simp [Std.HashMap.getElem?_insert] <;> split <;> simp_all

@[simp] theorem PropMap.get?_insert_self (m : PropMap) (k : PropKey) (p : Property) :
    (m.insert k p).get? k = some p := by
  simp [PropMap.get?_insert]

/-- Reading another key (the inequality is a proved fact, so the kernel never compares keys by
evaluating them). -/
theorem PropMap.get?_insert_ne (m : PropMap) (k k' : PropKey) (p : Property) (h : k ≠ k') :
    (m.insert k p).get? k' = m.get? k' := by
  simp [PropMap.get?_insert, h]

@[simp] theorem PropMap.get?_empty (k : PropKey) : ({} : PropMap).get? k = none := by
  simp [PropMap.get?]

/-- The object at an index (`default` when out of range). -/
def State.objEntry (s : State) (o : ObjId) : Obj := (s.heap[o]?).getD default

theorem State.objEntry_of (s : State) (o : ObjId) (h : o < s.heap.size) : s.objEntry o = s.heap[o] := by
  simp [State.objEntry, Array.getElem?_eq_getElem h]

theorem readObj_entry {α : Type} (o : ObjId) (f : Obj → α) (s : State) (h : o < s.heap.size) :
    readObj o f s = .ok (f (s.objEntry o)) s := by
  simp [readObj, h, State.objEntry_of s o h]

/-- Ordinary objects and ECMAScript function objects: every essential internal method is the
ordinary one. -/
def Kind.isPlain : Kind → Bool
  | .ordinary | .func _ => true
  | _ => false

@[simp] theorem Kind.isPlain_ordinary : Kind.ordinary.isPlain = true := by simp only [Kind.isPlain]
@[simp] theorem Kind.isPlain_func (d : FuncData) : (Kind.func d).isPlain = true := by simp only [Kind.isPlain]

theorem readObj_some {α : Type} (o : ObjId) (f : Obj → α) (s : State) (ob : Obj) (h : s.heap[o]? = some ob) :
    readObj o f s = .ok (f ob) s := by
  have hlt : o < s.heap.size := by
    rcases Nat.lt_or_ge o s.heap.size with hl | hl
    · exact hl
    · simp [Array.getElem?_eq_none hl] at h
  have : s.heap[o] = ob := by simpa [Array.getElem?_eq_getElem hlt] using h
  simp [readObj, hlt, this]

theorem objKind_some (o : ObjId) (s : State) (ob : Obj) (h : s.heap[o]? = some ob) :
    objKind o s = .ok ob.kind s := readObj_some o _ s ob h

/-- The method bodies after reading the kind: the `_` branch for plain kinds. -/
private theorem plain_cases {β : Type} (k : Kind) (hk : k.isPlain = true) (P : Kind → β) (x : β)
    (h : ∀ k, k.isPlain = true → P k = x) : P k = x := h k hk

theorem getOwnProperty_plain (n : Nat) (o : ObjId) (k : PropKey) (s : State) (ob : Obj)
    (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true) :
    ES.getOwnProperty (n + 1) o k s = .ok (ob.props.get? k) s := by
  simp only [ES.getOwnProperty, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;> simp [ownProp, readObj_some o _ s ob h]

theorem isExtensible_plain (n : Nat) (o : ObjId) (s : State) (ob : Obj)
    (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true) :
    ES.isExtensible (n + 1) o s = .ok ob.extensible s := by
  simp only [ES.isExtensible, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;> simp [readObj_some o _ s ob h]

theorem defineOwnProperty_plain (n : Nat) (o : ObjId) (k : PropKey) (desc : PropDesc) (s : State) (ob : Obj)
    (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true) :
    ES.defineOwnProperty (n + 1) o k desc s = ordinaryDefineOwnProperty o k desc s := by
  simp only [ES.defineOwnProperty, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;> rfl

/-- OrdinaryDefineOwnProperty: ValidateAndApplyPropertyDescriptor's decision, and the property stored. -/
theorem ordinaryDefineOwnProperty_some (o : ObjId) (k : PropKey) (desc : PropDesc) (s : State) (ob : Obj)
    (h : s.heap[o]? = some ob) :
    ordinaryDefineOwnProperty o k desc s =
      match validateAndApply ob.extensible desc (ob.props.get? k) with
      | (ok, none) => .ok ok s
      | (ok, some p) => .ok ok { s with heap := s.heap.modify o (·.withProps (·.insert k p)) } := by
  simp only [ordinaryDefineOwnProperty, M.bind_eq, M.bind_apply, readObj_some o _ s ob h, M.bindRes_ok]
  split <;> next heq => simp [heq, setOwn, modifyObj, pure, M.pure]

theorem hasProperty_plain_own (n : Nat) (o : ObjId) (k : PropKey) (s : State) (ob : Obj) (p : Property)
    (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true) (hp : ob.props.get? k = some p) :
    ES.hasProperty (n + 2) o k s = .ok true s := by
  simp only [ES.hasProperty, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;>
    simp [M.bind_apply, getOwnProperty_plain n o k s ob h (by simp [hkd]), hp, pure, M.pure]

theorem get_plain_data (n : Nat) (o : ObjId) (k : PropKey) (r : Value) (s : State) (ob : Obj) (v : Value)
    (w e c : Bool) (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true)
    (hp : ob.props.get? k = some (.data v w e c)) :
    ES.get (n + 3) o k r s = .ok v s := by
  simp only [ES.get, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;>
    simp [ES.ordinaryGet, M.bind_apply, getOwnProperty_plain n o k s ob h (by simp [hkd]), hp, pure, M.pure]

/-- [[Set]] on an own writable data property, with the object itself as receiver: redefines the value. -/
theorem set_plain_own (n : Nat) (o : ObjId) (k : PropKey) (v : Value) (s : State) (ob : Obj) (v0 : Value)
    (e c : Bool) (h : s.heap[o]? = some ob) (hk : ob.kind.isPlain = true)
    (hp : ob.props.get? k = some (.data v0 true e c)) :
    ES.set (n + 3) o k v (.obj o) s = ordinaryDefineOwnProperty o k { value := some v } s := by
  simp only [ES.set, M.bind_eq, M.bind_apply, objKind_some o s ob h, M.bindRes_ok]
  cases hkd : ob.kind <;> simp [hkd, Kind.isPlain] at hk <;>
    simp [ES.ordinarySet, M.bind_apply, getOwnProperty_plain n o k s ob h (by simp [hkd]), hp, pure, M.pure,
      defineOwnProperty_plain n o k _ s ob h (by simp [hkd])]

/-! ## The same, over `State.objEntry` (for `simp`: no variable only in a hypothesis) -/

theorem heap_get?_entry (s : State) (o : ObjId) (h : o < s.heap.size) : s.heap[o]? = some (s.objEntry o) := by
  simp [State.objEntry, h]

theorem readObj_entry' {α : Type} (o : ObjId) (f : Obj → α) (s : State) (h : o < s.heap.size) :
    readObj o f s = .ok (f (s.objEntry o)) s := readObj_some o f s _ (heap_get?_entry s o h)

theorem getOwnProperty_entry (n : Nat) (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    ES.getOwnProperty (n + 1) o k s = .ok ((s.objEntry o).props.get? k) s :=
  getOwnProperty_plain n o k s _ (heap_get?_entry s o h) hk

theorem isExtensible_entry (n : Nat) (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    ES.isExtensible (n + 1) o s = .ok (s.objEntry o).extensible s :=
  isExtensible_plain n o s _ (heap_get?_entry s o h) hk

theorem defineOwnProperty_entry (n : Nat) (o : ObjId) (k : PropKey) (desc : PropDesc) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true) :
    ES.defineOwnProperty (n + 1) o k desc s = ordinaryDefineOwnProperty o k desc s :=
  defineOwnProperty_plain n o k desc s _ (heap_get?_entry s o h) hk

theorem ordinaryDefineOwnProperty_entry (o : ObjId) (k : PropKey) (desc : PropDesc) (s : State)
    (h : o < s.heap.size) :
    ordinaryDefineOwnProperty o k desc s =
      match validateAndApply (s.objEntry o).extensible desc ((s.objEntry o).props.get? k) with
      | (ok, none) => .ok ok s
      | (ok, some p) => .ok ok { s with heap := s.heap.modify o (·.withProps (·.insert k p)) } :=
  ordinaryDefineOwnProperty_some o k desc s _ (heap_get?_entry s o h)

theorem hasProperty_entry_own (n : Nat) (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) (hp : ((s.objEntry o).props.get? k).isSome = true) :
    ES.hasProperty (n + 2) o k s = .ok true s := by
  obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.mp hp
  exact hasProperty_plain_own n o k s _ p (heap_get?_entry s o h) hk hp'

/-- A looked-up own property's value if it is a data property. -/
def ownDataValue : Option Property → Value
  | some (.data v ..) => v
  | _ => .undefined

def isOwnData : Option Property → Bool
  | some (.data ..) => true
  | _ => false

def isOwnWritableData : Option Property → Bool
  | some (.data _ true _ _) => true
  | _ => false

@[simp] theorem ownDataValue_data (v : Value) (w e c : Bool) : ownDataValue (some (.data v w e c)) = v := by
  simp only [ownDataValue]
@[simp] theorem isOwnData_data (v : Value) (w e c : Bool) : isOwnData (some (.data v w e c)) = true := by
  simp only [isOwnData]
@[simp] theorem isOwnWritableData_data (v : Value) (e c : Bool) :
    isOwnWritableData (some (.data v true e c)) = true := by
  simp only [isOwnWritableData]

theorem get_entry_data (n : Nat) (o : ObjId) (k : PropKey) (r : Value) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true)
    (hp : isOwnData ((s.objEntry o).props.get? k) = true) :
    ES.get (n + 3) o k r s = .ok (ownDataValue ((s.objEntry o).props.get? k)) s := by
  cases hq : (s.objEntry o).props.get? k with
  | none => simp [hq, isOwnData] at hp
  | some p =>
    cases p with
    | accessor => simp [hq, isOwnData] at hp
    | data v w e c => simpa using get_plain_data n o k r s _ v w e c (heap_get?_entry s o h) hk hq

theorem set_entry_own (n : Nat) (o : ObjId) (k : PropKey) (v : Value) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true)
    (hp : isOwnWritableData ((s.objEntry o).props.get? k) = true) :
    ES.set (n + 3) o k v (.obj o) s = ordinaryDefineOwnProperty o k { value := some v } s := by
  cases hq : (s.objEntry o).props.get? k with
  | none => simp [hq, isOwnWritableData] at hp
  | some p =>
    cases p with
    | accessor => simp [hq, isOwnWritableData] at hp
    | data v0 w e c =>
      cases w
      · simp [hq, isOwnWritableData] at hp
      · exact set_plain_own n o k v s _ v0 e c (heap_get?_entry s o h) hk hq

/-! ## Named state updates

`{ s with heap := … }` elaborates to a literal of all of `State`'s fields; nested updates make terms
that grow with every step and that the kernel checks slowly. Proofs keep updates as these named
definitions, which `simp` does not unfold, and use the lemmas below to read them. -/

/-- The state with own property `k` of object `o` set to `p` (`setOwn`). -/
def State.setProp (s : State) (o : ObjId) (k : PropKey) (p : Property) : State :=
  { s with heap := s.heap.modify o (·.withProps (·.insert k p)) }

/-- The state with object `ob` allocated (at index `s.heap.size`). -/
def State.allocObj (s : State) (ob : Obj) : State := { s with heap := s.heap.push ob }

section
variable (s : State) (o i : ObjId) (k : PropKey) (p : Property) (ob : Obj)

@[simp] theorem State.setProp_envs : (s.setProp o k p).envs = s.envs := by simp only [State.setProp]
@[simp] theorem State.setProp_realms : (s.setProp o k p).realms = s.realms := by simp only [State.setProp]
@[simp] theorem State.setProp_realm : (s.setProp o k p).realm = s.realm := by simp only [State.setProp]
@[simp] theorem State.setProp_fuel : (s.setProp o k p).fuel = s.fuel := by simp only [State.setProp]
@[simp] theorem State.setProp_scripts : (s.setProp o k p).scripts = s.scripts := by simp only [State.setProp]
@[simp] theorem State.setProp_script : (s.setProp o k p).script = s.script := by simp only [State.setProp]
@[simp] theorem State.setProp_size : (s.setProp o k p).heap.size = s.heap.size := by simp [State.setProp]
@[simp] theorem State.allocObj_envs : (s.allocObj ob).envs = s.envs := by simp only [State.allocObj]
@[simp] theorem State.allocObj_realms : (s.allocObj ob).realms = s.realms := by simp only [State.allocObj]
@[simp] theorem State.allocObj_realm : (s.allocObj ob).realm = s.realm := by simp only [State.allocObj]
@[simp] theorem State.allocObj_fuel : (s.allocObj ob).fuel = s.fuel := by simp only [State.allocObj]
@[simp] theorem State.allocObj_scripts : (s.allocObj ob).scripts = s.scripts := by simp only [State.allocObj]
@[simp] theorem State.allocObj_script : (s.allocObj ob).script = s.script := by simp only [State.allocObj]
@[simp] theorem State.allocObj_size : (s.allocObj ob).heap.size = s.heap.size + 1 := by simp [State.allocObj]

@[simp] theorem State.setProp_curRealm : (s.setProp o k p).curRealm = s.curRealm := by
  simp only [State.curRealm, State.setProp_realms, State.setProp_realm]
@[simp] theorem State.allocObj_curRealm : (s.allocObj ob).curRealm = s.curRealm := by
  simp only [State.curRealm, State.allocObj_realms, State.allocObj_realm]

theorem State.setProp_entry_self (h : o < s.heap.size) :
    (s.setProp o k p).objEntry o = (s.objEntry o).withProps (·.insert k p) := by
  simp [State.setProp, State.objEntry, h, Array.getElem_modify]

theorem State.setProp_entry_ne (h : o ≠ i) : (s.setProp o k p).objEntry i = s.objEntry i := by
  simp [State.setProp, State.objEntry, Array.getElem?_modify, h]

theorem State.allocObj_entry_new : (s.allocObj ob).objEntry s.heap.size = ob := by
  simp [State.allocObj, State.objEntry]

theorem State.allocObj_entry_lt (h : i < s.heap.size) : (s.allocObj ob).objEntry i = s.objEntry i := by
  simp [State.allocObj, State.objEntry, Array.getElem?_push, Nat.ne_of_lt h, h]

theorem State.setProp_get?_lt (hne : o ≠ i) : (s.setProp o k p).heap[i]? = s.heap[i]? := by
  simp [State.setProp, Array.getElem?_modify, hne]

theorem State.allocObj_get?_lt (h : i < s.heap.size) : (s.allocObj ob).heap[i]? = s.heap[i]? := by
  simp [State.allocObj, Array.getElem?_push, Nat.ne_of_lt h]
end

@[simp] theorem Obj.withProps_kind (ob : Obj) (f : PropMap → PropMap) : (ob.withProps f).kind = ob.kind := by
  simp only [Obj.withProps]
@[simp] theorem Obj.withProps_extensible (ob : Obj) (f : PropMap → PropMap) :
    (ob.withProps f).extensible = ob.extensible := by simp only [Obj.withProps]
@[simp] theorem Obj.withProps_props (ob : Obj) (f : PropMap → PropMap) : (ob.withProps f).props = f ob.props := by
  simp only [Obj.withProps]

/-! ### The operations, in terms of the named updates -/

theorem alloc_eq (ob : Obj) (s : State) : alloc ob s = .ok s.heap.size (s.allocObj ob) := by
  simp only [alloc, State.allocObj, State.withHeap_eq]

theorem newObject_eq (s : State) :
    newObject s = .ok s.heap.size (s.allocObj { proto := .obj s.curRealm.objectProto }) := by
  simp only [newObject, alloc, State.allocObj, State.withHeap_eq]

theorem setOwn_eq (o : ObjId) (k : PropKey) (p : Property) (s : State) :
    setOwn o k p s = .ok () (s.setProp o k p) := by
  simp only [setOwn, modifyObj, State.setProp, State.withHeap_eq]

/-- OrdinaryDefineOwnProperty of a new data property on an extensible object. -/
theorem ordinaryDefineOwnProperty_new (o : ObjId) (k : PropKey) (v : Value) (w e c : Bool) (s : State)
    (h : o < s.heap.size) (hx : (s.objEntry o).extensible = true) (hn : (s.objEntry o).props.get? k = none) :
    ordinaryDefineOwnProperty o k (PropDesc.data v w e c) s = .ok true (s.setProp o k (.data v w e c)) := by
  rw [ordinaryDefineOwnProperty_entry o k _ s h, hx, hn]
  simp [validateAndApply, PropDesc.data, PropDesc.isAccessor, State.setProp]

/-- OrdinaryDefineOwnProperty of a new value for a writable data property. -/
theorem ordinaryDefineOwnProperty_value (o : ObjId) (k : PropKey) (v v0 : Value) (e c : Bool) (s : State)
    (h : o < s.heap.size) (hp : (s.objEntry o).props.get? k = some (.data v0 true e c)) :
    ordinaryDefineOwnProperty o k { value := some v } s = .ok true (s.setProp o k (.data v true e c)) := by
  rw [ordinaryDefineOwnProperty_entry o k _ s h, hp]
  simp [validateAndApply, PropDesc.isAccessor, PropDesc.isData, PropDesc.isGeneric, Property.configurable,
    Property.enumerable, State.setProp]

/-! ### The `Obj'` wrappers (at `maxDepth`), so proofs never unfold `maxDepth` -/

theorem maxDepth_eq : maxDepth = 19997 + 3 := by decide

theorem Obj'.getOwnProperty_entry (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    Obj'.getOwnProperty o k s = .ok ((s.objEntry o).props.get? k) s := by
  unfold Obj'.getOwnProperty; rw [maxDepth_eq]; exact ES.getOwnProperty_entry _ o k s h hk

theorem Obj'.isExtensible_entry (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    Obj'.isExtensible o s = .ok (s.objEntry o).extensible s := by
  unfold Obj'.isExtensible; rw [maxDepth_eq]; exact ES.isExtensible_entry _ o s h hk

theorem Obj'.defineOwnProperty_entry (o : ObjId) (k : PropKey) (desc : PropDesc) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true) :
    Obj'.defineOwnProperty o k desc s = ordinaryDefineOwnProperty o k desc s := by
  unfold Obj'.defineOwnProperty; rw [maxDepth_eq]; exact ES.defineOwnProperty_entry _ o k desc s h hk

theorem Obj'.hasProperty_entry_own (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) (hp : ((s.objEntry o).props.get? k).isSome = true) :
    Obj'.hasProperty o k s = .ok true s := by
  unfold Obj'.hasProperty; rw [maxDepth_eq]; exact ES.hasProperty_entry_own _ o k s h hk hp

theorem Obj'.get_entry_data (o : ObjId) (k : PropKey) (r : Value) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true)
    (hp : isOwnData ((s.objEntry o).props.get? k) = true) :
    Obj'.get o k r s = .ok (ownDataValue ((s.objEntry o).props.get? k)) s := by
  unfold Obj'.get; rw [maxDepth_eq]; exact ES.get_entry_data _ o k r s h hk hp

theorem Obj'.set_entry_own (o : ObjId) (k : PropKey) (v : Value) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true)
    (hp : isOwnWritableData ((s.objEntry o).props.get? k) = true) :
    Obj'.set o k v (.obj o) s = ordinaryDefineOwnProperty o k { value := some v } s := by
  unfold Obj'.set; rw [maxDepth_eq]; exact ES.set_entry_own _ o k v s h hk hp

end ES
