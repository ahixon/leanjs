import Proofs.ArrayWrite
import Proofs.Proto

/-!
# Writes past the end: `a[len] = v`

The array has no own element `len`, so OrdinarySet walks the prototype chain (`Array.prototype`, itself
an array, then `Object.prototype`); when no object on it has the key, the value is defined on the
array as a new data property, and the array's [[DefineOwnProperty]] moves `length` to `len + 1`.
-/

namespace ES

open Conv

/-- Objects whose [[GetOwnProperty]], [[GetPrototypeOf]] and [[Set]] are the ordinary ones. -/
def Kind.isOrd : Kind → Bool
  | .ordinary | .func _ | .array => true
  | _ => false

theorem getOwnProperty_ord (n : Nat) (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isOrd = true) :
    ES.getOwnProperty (n + 1) o k s = .ok ((s.objEntry o).props.get? k) s := by
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isOrd] at hk <;>
    first | exact getOwnProperty_array n o k s h hkd | exact getOwnProperty_entry n o k s h (by simp [hkd])

theorem getPrototypeOf_ord (n : Nat) (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isOrd = true) :
    ES.getPrototypeOf (n + 1) o s = .ok (s.objEntry o).proto s := by
  simp only [ES.getPrototypeOf, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, M.bindRes_ok]
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isOrd] at hk <;> simp [objProto, readObj_entry' _ _ _ h]

/-- A prototype chain (at most `n` objects, starting at `o`) of ordinary objects, functions and arrays,
none of which has the key `k`. -/
def AbsentChain (s : State) : Nat → ObjId → PropKey → Prop
  | 0, _, _ => False
  | n + 1, o, k =>
    o < s.heap.size ∧ (s.objEntry o).kind.isOrd = true ∧ (s.objEntry o).props.get? k = none ∧
      match (s.objEntry o).proto with
      | .obj p => AbsentChain s n p k
      | _ => True

/-- [[Set]] of a key no object on the chain has: the receiver's [[DefineOwnProperty]] of a new data
property. -/
theorem set_absent (s : State) (k : PropKey) (v : Value) (recv : ObjId) (s' : State)
    (hrn : ∀ j, ES.getOwnProperty (j + 1) recv k s = .ok none s)
    (hdef : ∀ j, ES.defineOwnProperty (j + 1) recv k (PropDesc.data v) s = .ok true s') :
    ∀ (n : Nat) (o : ObjId) (m : Nat), AbsentChain s n o k → 2 * n + 1 ≤ m →
      ES.set m o k v (.obj recv) s = .ok true s' := by
  intro n
  induction n with
  | zero => intro o m h; simp [AbsentChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hp, hrest⟩ hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [ES.set]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isOrd] at hk <;>
    · rw [ES.ordinarySet]
      simp only [M.bind_eq, M.bind_apply, getOwnProperty_ord _ o k s hlt (by simp [hkd, Kind.isOrd]), hp,
        M.bindRes_ok, getPrototypeOf_ord _ o s hlt (by simp [hkd, Kind.isOrd])]
      cases hpr : (s.objEntry o).proto with
      | obj p =>
        rw [hpr] at hrest
        simp [ih p (j + 1) hrest (by omega)]
      | _ => simp [pure, M.pure, hrn, hdef]

theorem Obj'.set_absent (s : State) (k : PropKey) (v : Value) (recv : ObjId) (s' : State)
    (hrn : ∀ j, ES.getOwnProperty (j + 1) recv k s = .ok none s)
    (hdef : ∀ j, ES.defineOwnProperty (j + 1) recv k (PropDesc.data v) s = .ok true s')
    (n : Nat) (o : ObjId) (hc : AbsentChain s n o k) (hn : n ≤ 9999) :
    Obj'.set o k v (.obj recv) s = .ok true s' := by
  unfold Obj'.set
  exact ES.set_absent s k v recv s' hrn hdef n o maxDepth hc (by simp only [maxDepth]; omega)

/-- The state after appending `v` at index `len`. -/
def appendState (A : ObjId) (len : Nat) (v : Value) (t : State) : State :=
  (t.setProp A (PropKey.ofNat len) (.data v true true true)).setProp A (.str kLength)
    (.data (.num (Conv.ofNat (len + 1))) true false false)

/-- **`a[len] = v`**: no object on the array's prototype chain has the index, so the element is
appended and `length` becomes `len + 1`. -/
theorem putRefValue_append (A : ObjId) (len : Nat) (xs : Nat → Value) (v : Value) (strict : Bool) (t : State)
    (n : Nat) (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) (hc : AbsentChain t n A (PropKey.ofNat len))
    (hn : n ≤ 9999) :
    putRefValue (.prop (.obj A) (.num (ofSmallInt len)) strict none) v t = .ok () (appendState A len v t) := by
  have hkb : len < intBound := by simp only [intBound]; omega
  have hA' := hA
  obtain ⟨hs, hk, -, -, -, hnone⟩ := hA
  have hset := Obj'.set_absent t (PropKey.ofNat len) v A (appendState A len v t)
    (fun j => by rw [getOwnProperty_array j A _ t hs hk, hnone len (Nat.le_refl _) (by omega)])
    (fun j => defineOwnProperty_append j A len xs v t hA' hlen) n A hc hn
  simp only [putRefValue, M.bind_eq, M.bind_apply, toPropertyKey_int len hkb, M.bindRes_ok, Option.getD_none,
    key_eq, hset]
  simp [pure, M.pure]

theorem arrayObj_appendState (A : ObjId) (len : Nat) (xs : Nat → Value) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    ArrayObj A (len + 1) (fun i => if i = len then v else xs i) (appendState A len v t) :=
  arrayObj_append A len xs v t hA hlen

end ES
