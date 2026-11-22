import JSProofs.Proto

/-!
# Property reads through chains that include arrays and built-in functions (zippy docs/react-proofs.md)

`Kind.isPlain` covers the objects whose every internal method is ordinary. For reads it is enough that
[[GetOwnProperty]], [[GetPrototypeOf]] and [[Get]] are: also Array exotic objects (only [[DefineOwnProperty]] is
special) and built-in function objects. React's render reads through them: `const [n, setN] = useState(0)` looks up
`@@iterator` on an array and `Array.prototype`.
-/

open Std (HashMap)

namespace ES

/-- Objects whose read-side internal methods are the ordinary ones. -/
def Kind.isReadPlain : Kind → Bool
  | .ordinary | .func _ | .internal _ _ | .array | .builtin _ => true
  | _ => false

theorem Kind.isReadPlain_of_isPlain {k : Kind} (h : k.isPlain = true) : k.isReadPlain = true := by
  cases k <;> simp_all [Kind.isPlain, Kind.isReadPlain]

/-- The chain from `o` consists of read-plain objects, and the lookup of `k` ends within `n` objects. -/
def ReadChain (s : State) : Nat → ObjId → PropKey → Prop
  | 0, _, _ => False
  | n + 1, o, k =>
    o < s.heap.size ∧ (s.objEntry o).kind.isReadPlain = true ∧
      ((s.objEntry o).props.get? k = none →
        match (s.objEntry o).proto with
        | .obj p => ReadChain s n p k
        | _ => True)


theorem getOwnProperty_read (n : Nat) (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isReadPlain = true) :
    ES.getOwnProperty (n + 1) o k s = .ok ((s.objEntry o).props.get? k) s := by
  have hg := heap_get?_entry s o h
  simp only [ES.getOwnProperty, M.bind_eq, M.bind_apply, objKind_some o s _ hg, M.bindRes_ok]
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isReadPlain] at hk <;> simp [ownProp, readObj_some o _ s _ hg]

theorem getPrototypeOf_read (n : Nat) (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isReadPlain = true) :
    ES.getPrototypeOf (n + 1) o s = .ok (s.objEntry o).proto s := by
  simp only [ES.getPrototypeOf, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, M.bindRes_ok]
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isReadPlain] at hk <;> simp [objProto, readObj_entry' _ _ _ h]

/-- [[Get]] through a read-plain chain is the value of the data property the lookup finds. -/
theorem get_readChain (s : State) (k : PropKey) (r : Value) :
    ∀ (n : Nat) (o : ObjId) (m : Nat), ReadChain s n o k → 2 * n + 1 ≤ m →
      noAccessor (ordLookup s n o k) = true →
      ES.get m o k r s = .ok (ownDataValue (ordLookup s n o k)) s := by
  intro n
  induction n with
  | zero => intro o m h; simp [ReadChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hrest⟩ hm hna
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [ES.get]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isReadPlain] at hk <;>
    · rw [ES.ordinaryGet]
      simp only [M.bind_eq, M.bind_apply, getOwnProperty_read _ o k s hlt (by simp [hkd, Kind.isReadPlain]), M.bindRes_ok]
      cases hp : (s.objEntry o).props.get? k with
      | some p =>
        cases p with
        | data v w e c => simp [ordLookup, hp, pure, M.pure]
        | accessor => simp [ordLookup, hp, noAccessor] at hna
      | none =>
        have hr := hrest hp
        simp only [M.bind_apply, getPrototypeOf_read _ o s hlt (by simp [hkd, Kind.isReadPlain]), M.bindRes_ok]
        cases hpr : (s.objEntry o).proto with
        | obj p =>
          rw [hpr] at hr
          simp only [hpr]
          have hna' : noAccessor (ordLookup s n p k) = true := by simpa [ordLookup, hp, hpr] using hna
          rw [ih p (j + 1) hr (by omega) hna']
          simp [ordLookup, hp, hpr]
        | _ => simp [ordLookup, hp, hpr, pure, M.pure, ownDataValue]

end ES
