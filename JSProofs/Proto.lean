import JSProofs.Object

/-!
# Property lookup through prototype chains

For chains of plain objects (ordinary and ECMAScript function objects), the essential internal
methods [[Get]], [[HasProperty]] and [[Set]] agree with a pure walk of the chain, `ordLookup`:
the first own property met, starting at the object and following `proto`.

Each method's depth parameter drops per prototype step ([[HasProperty]] by one, [[Get]] and [[Set]]
by two); `Obj'.*` run at `maxDepth` (20000), enough for chains of up to 9999 objects.
-/

namespace ES

open Std (HashMap)

/-- The property `k` of `o`, own or inherited, looking at no more than `n` objects of the chain. -/
def ordLookup (s : State) : Nat → ObjId → PropKey → Option Property
  | 0, _, _ => none
  | n + 1, o, k =>
    match (s.objEntry o).props.get? k with
    | some p => some p
    | none =>
      match (s.objEntry o).proto with
      | .obj p => ordLookup s n p k
      | _ => none

/-- The chain from `o` consists of plain objects in the heap, and the lookup of `k` ends (at the
property or at a non-object prototype) within `n` objects. -/
def PlainChain (s : State) : Nat → ObjId → PropKey → Prop
  | 0, _, _ => False
  | n + 1, o, k =>
    o < s.heap.size ∧ (s.objEntry o).kind.isPlain = true ∧
      ((s.objEntry o).props.get? k = none →
        match (s.objEntry o).proto with
        | .obj p => PlainChain s n p k
        | _ => True)

/-- No accessor property was found (a getter or setter would be a call). -/
def noAccessor : Option Property → Bool
  | some (.accessor ..) => false
  | _ => true

/-- Absent, or a writable data property: [[Set]] then creates or updates the receiver's own property. -/
def writableOrAbsent : Option Property → Bool
  | none => true
  | some (.data _ true _ _) => true
  | _ => false

theorem getPrototypeOf_plain (n : Nat) (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    ES.getPrototypeOf (n + 1) o s = .ok (s.objEntry o).proto s := by
  simp only [ES.getPrototypeOf, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, M.bindRes_ok]
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk <;> simp [objProto, readObj_entry' _ _ _ h]

/-- [[HasProperty]] is whether the lookup finds the property. -/
theorem hasProperty_chain (s : State) (k : PropKey) :
    ∀ (n : Nat) (o : ObjId) (m : Nat), PlainChain s n o k → n + 1 ≤ m →
      ES.hasProperty m o k s = .ok (ordLookup s n o k).isSome s := by
  intro n
  induction n with
  | zero => intro o m h; simp [PlainChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hrest⟩ hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [ES.hasProperty]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk <;>
    · simp only [M.bind_apply, getOwnProperty_entry _ o k s hlt (by simp [hkd]), M.bindRes_ok]
      cases hp : (s.objEntry o).props.get? k with
      | some p => simp [ordLookup, hp, pure, M.pure]
      | none =>
        have hr := hrest hp
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, M.bind_apply,
          getPrototypeOf_plain _ o s hlt (by simp [hkd]), M.bindRes_ok]
        cases hpr : (s.objEntry o).proto with
        | obj p =>
          rw [hpr] at hr
          simp only [hpr]
          rw [ih p (j + 1) hr (by omega)]
          simp [ordLookup, hp, hpr]
        | _ => simp [ordLookup, hp, hpr, pure, M.pure]

/-- [[Get]] is the value of the data property the lookup finds (`undefined` if none). -/
theorem get_chain (s : State) (k : PropKey) (r : Value) :
    ∀ (n : Nat) (o : ObjId) (m : Nat), PlainChain s n o k → 2 * n + 1 ≤ m →
      noAccessor (ordLookup s n o k) = true →
      ES.get m o k r s = .ok (ownDataValue (ordLookup s n o k)) s := by
  intro n
  induction n with
  | zero => intro o m h; simp [PlainChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hrest⟩ hm hna
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [ES.get]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk <;>
    · rw [ES.ordinaryGet]
      simp only [M.bind_eq, M.bind_apply, getOwnProperty_entry _ o k s hlt (by simp [hkd]), M.bindRes_ok]
      cases hp : (s.objEntry o).props.get? k with
      | some p =>
        cases p with
        | data v w e c => simp [ordLookup, hp, pure, M.pure]
        | accessor => simp [ordLookup, hp, noAccessor] at hna
      | none =>
        have hr := hrest hp
        simp only [M.bind_apply, getPrototypeOf_plain _ o s hlt (by simp [hkd]), M.bindRes_ok]
        cases hpr : (s.objEntry o).proto with
        | obj p =>
          rw [hpr] at hr
          simp only [hpr]
          have hna' : noAccessor (ordLookup s n p k) = true := by simpa [ordLookup, hp, hpr] using hna
          rw [ih p (j + 1) hr (by omega) hna']
          simp [ordLookup, hp, hpr]
        | _ => simp [ordLookup, hp, hpr, pure, M.pure, ownDataValue]

/-- [[Set]] with a receiver that has no own property `k`: if the lookup from `o` finds nothing or a
writable data property, the receiver gets an own data property (writable, enumerable, configurable)
with the value; if it finds a read-only one, nothing changes and the result is `false`. -/
theorem set_chain (s : State) (k : PropKey) (v : Value) (recv : ObjId)
    (hr : recv < s.heap.size) (hrk : (s.objEntry recv).kind.isPlain = true)
    (hrn : (s.objEntry recv).props.get? k = none) (hrx : (s.objEntry recv).extensible = true) :
    ∀ (n : Nat) (o : ObjId) (m : Nat), PlainChain s n o k → 2 * n + 1 ≤ m →
      noAccessor (ordLookup s n o k) = true →
      ES.set m o k v (.obj recv) s =
        if writableOrAbsent (ordLookup s n o k) then .ok true (s.setProp recv k (.data v true true true))
        else .ok false s := by
  intro n
  induction n with
  | zero => intro o m h; simp [PlainChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hrest⟩ hm hna
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hdef : ES.defineOwnProperty (j + 1) recv k (PropDesc.data v) s =
        .ok true (s.setProp recv k (.data v true true true)) := by
      rw [defineOwnProperty_entry _ _ _ _ _ hr hrk]
      exact ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ hr hrx hrn
    rw [ES.set]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk <;>
    · rw [ES.ordinarySet]
      simp only [M.bind_eq, M.bind_apply, getOwnProperty_entry _ o k s hlt (by simp [hkd]), M.bindRes_ok]
      cases hp : (s.objEntry o).props.get? k with
      | some p =>
        cases p with
        | data v0 w e c =>
          cases w <;> simp [ordLookup, hp, writableOrAbsent, pure, M.pure,
            getOwnProperty_entry _ recv k s hr hrk, hrn, hdef]
        | accessor => simp [ordLookup, hp, noAccessor] at hna
      | none =>
        have hr' := hrest hp
        simp only [M.bind_apply, getPrototypeOf_plain _ o s hlt (by simp [hkd]), M.bindRes_ok]
        cases hpr : (s.objEntry o).proto with
        | obj p =>
          rw [hpr] at hr'
          have hna' : noAccessor (ordLookup s n p k) = true := by simpa [ordLookup, hp, hpr] using hna
          have := ih p (j + 1) hr' (by omega) hna'
          simp [hpr, this, ordLookup, hp]
        | _ =>
          simp [ordLookup, hp, hpr, writableOrAbsent, pure, M.pure, getOwnProperty_entry _ recv k s hr hrk, hrn, hdef]

/-! ## At `maxDepth` (`Obj'.*`), and through references -/

theorem Obj'.hasProperty_chain (s : State) (k : PropKey) (n : Nat) (o : ObjId) (hc : PlainChain s n o k)
    (hn : n ≤ 9999) : Obj'.hasProperty o k s = .ok (ordLookup s n o k).isSome s := by
  unfold Obj'.hasProperty
  exact ES.hasProperty_chain s k n o maxDepth hc (by simp only [maxDepth]; omega)

theorem Obj'.get_chain (s : State) (k : PropKey) (r : Value) (n : Nat) (o : ObjId) (hc : PlainChain s n o k)
    (hn : n ≤ 9999) (hna : noAccessor (ordLookup s n o k) = true) :
    Obj'.get o k r s = .ok (ownDataValue (ordLookup s n o k)) s := by
  unfold Obj'.get
  exact ES.get_chain s k r n o maxDepth hc (by simp only [maxDepth]; omega) hna

theorem Obj'.set_chain (s : State) (k : PropKey) (v : Value) (recv : ObjId)
    (hr : recv < s.heap.size) (hrk : (s.objEntry recv).kind.isPlain = true)
    (hrn : (s.objEntry recv).props.get? k = none) (hrx : (s.objEntry recv).extensible = true)
    (n : Nat) (o : ObjId) (hc : PlainChain s n o k) (hn : n ≤ 9999) (hna : noAccessor (ordLookup s n o k) = true) :
    Obj'.set o k v (.obj recv) s =
      if writableOrAbsent (ordLookup s n o k) then .ok true (s.setProp recv k (.data v true true true))
      else .ok false s := by
  unfold Obj'.set
  exact ES.set_chain s k v recv hr hrk hrn hrx n o maxDepth hc (by simp only [maxDepth]; omega) hna

/-- GetValue of `o.key` (a property reference with a string key). -/
theorem getRefValue_prop (o : ObjId) (key : JSStr) (strict : Bool) (s : State) :
    getRefValue (.prop (.obj o) (.str key) strict none) s = Obj'.get o (.str key) (.obj o) s := by
  simp [getRefValue, Value.isNullish, toPropertyKey, M.bind_eq, M.bind_apply, pure, M.pure]

/-- PutValue of `o.key = v` when `o` has no own `key` and the chain does not make it read-only:
`o` gets an own data property. -/
theorem putRefValue_prop (o : ObjId) (key : JSStr) (strict : Bool) (v : Value) (s : State) (n : Nat)
    (hr : o < s.heap.size) (hrk : (s.objEntry o).kind.isPlain = true)
    (hrn : (s.objEntry o).props.get? (.str key) = none) (hrx : (s.objEntry o).extensible = true)
    (hc : PlainChain s n o (.str key)) (hn : n ≤ 9999)
    (hw : writableOrAbsent (ordLookup s n o (.str key)) = true) :
    putRefValue (.prop (.obj o) (.str key) strict none) v s =
      .ok () (s.setProp o (.str key) (.data v true true true)) := by
  have hna : noAccessor (ordLookup s n o (.str key)) = true := by
    revert hw; cases ordLookup s n o (.str key) with
    | none => simp [noAccessor]
    | some p => cases p <;> simp [noAccessor, writableOrAbsent]
  simp [putRefValue, toPropertyKey, M.bind_eq, M.bind_apply, pure, M.pure,
    Obj'.set_chain s _ v o hr hrk hrn hrx n o hc hn hna, hw]

/-! ## Example: assignment shadows an inherited property -/

/-- `o` inherits `key` (a writable data property with value `v0`) from its prototype `p`. Reading
`o.key` gives `v0`; assigning `o.key = v` gives `o` its own property and leaves `p` unchanged; then
`o.key` reads `v`. -/
theorem shadowing (s : State) (o p : ObjId) (key : JSStr) (strict : Bool) (v0 v : Value) (e c : Bool)
    (ho : o < s.heap.size) (hp : p < s.heap.size) (hop : o ≠ p)
    (hok : (s.objEntry o).kind.isPlain = true) (hpk : (s.objEntry p).kind.isPlain = true)
    (hox : (s.objEntry o).extensible = true) (hon : (s.objEntry o).props.get? (.str key) = none)
    (hproto : (s.objEntry o).proto = .obj p) (hpv : (s.objEntry p).props.get? (.str key) = some (.data v0 true e c)) :
    let s' := s.setProp o (.str key) (.data v true true true)
    getRefValue (.prop (.obj o) (.str key) strict none) s = .ok v0 s ∧
      putRefValue (.prop (.obj o) (.str key) strict none) v s = .ok () s' ∧
      getRefValue (.prop (.obj o) (.str key) strict none) s' = .ok v s' ∧
      s'.objEntry p = s.objEntry p := by
  intro s'
  have hc : PlainChain s 2 o (.str key) := by simp [PlainChain, ho, hok, hproto, hp, hpk, hpv]
  have hl : ordLookup s 2 o (.str key) = some (.data v0 true e c) := by simp [ordLookup, hon, hproto, hpv]
  have ho' : o < s'.heap.size := by simp [s', ho]
  have hok' : (s'.objEntry o).kind.isPlain = true := by simp [s', State.setProp_entry_self _ _ _ _ ho, hok]
  have hov' : (s'.objEntry o).props.get? (.str key) = some (.data v true true true) := by
    simp [s', State.setProp_entry_self _ _ _ _ ho]
  have hc' : PlainChain s' 1 o (.str key) := by simp [PlainChain, ho', hok', hov']
  have hl' : ordLookup s' 1 o (.str key) = some (.data v true true true) := by simp [ordLookup, hov']
  refine ⟨?_, ?_, ?_, State.setProp_entry_ne _ _ _ _ _ hop⟩
  · rw [getRefValue_prop, Obj'.get_chain s _ _ 2 o hc (by omega) (by simp [hl, noAccessor]), hl]; rfl
  · exact putRefValue_prop o key strict v s 2 ho hok hon hox hc (by omega) (by simp [hl, writableOrAbsent])
  · rw [getRefValue_prop, Obj'.get_chain s' _ _ 1 o hc' (by omega) (by simp [hl', noAccessor]), hl']; rfl

end ES
