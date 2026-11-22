import JSProofs.Builtins
import JSProofs.ReadChain

/-!
# The array iterator built-ins (zippy docs/react-proofs.md)

`%Array.prototype.values%` (`Array.prototype[@@iterator]`) and `%ArrayIteratorPrototype%.next` on an array: what
`const [a, b] = arr` runs. Each call's state is given exactly (the allocations and the iterator's index).
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The iterator `values()` allocates: over `A`, at index 0, of values. -/
def iterObj (AIP A : ObjId) : Obj :=
  { proto := .obj AIP, kind := .internal "Array Iterator" #[.obj A, numV 0, numV 1] }

theorem values_eq (fV A AIP : ObjId) (s : State) (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hI : s.curRealm.intrinsics["%ArrayIteratorPrototype%"]? = some AIP) :
    ES.arrayProtoValues 1 fV (.obj A) #[] .undefined s =
      .ok (.obj s.heap.size) (s.withHeap (·.push (iterObj AIP A))) := by
  simp only [ES.arrayProtoValues, ES.createArrayIterator, toObj, M.bind_eq, M.bind_apply]
  simp [toObject, intrinsic, hI, alloc, iterObj, Pure.pure, M.pure, M.bindRes_ok]

/-- **`Array.prototype[@@iterator]` called on an array** (the built-in `values`): a new array iterator. -/
theorem values_spec {n : Nat} {h : σ} {fV A AIP : ObjId} {bd : BuiltinData} {s : State}
    (hlt : fV < s.heap.size) (hk : (s.objEntry fV).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some (ES.arrayProtoValues 1)) (hf : s.fuel ≠ 0) (hrl : bd.realm = s.realm)
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hI : s.curRealm.intrinsics["%ArrayIteratorPrototype%"]? = some AIP) :
    WP eng answer n h (callImpl eng (.obj fV) (.obj A) #[]) s fun v w h' =>
      v = .obj s.heap.size ∧ w = { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fV bd _ _ _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  rw [hrl]
  refine wp_of_eq (values_eq fV A AIP _ hA hAk hI) ⟨rfl, rfl, rfl⟩


/-- ToLength of a Number. -/
def lenOf (L : F64) : Nat := match Conv.toIntegerOrInf L with
  | .inl true => 0
  | .inl false => 9007199254740991
  | .inr i => if i ≤ 0 then 0 else min i.toNat 9007199254740991

/-- `lengthOf` of an array with its own `length` data property. -/
theorem lengthOf_array (A : ObjId) (s : State) (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    {L : F64} {w e c : Bool} (hL : (s.objEntry A).props.get? (.str kLength) = some (.data (.num L) w e c)) :
    lengthOf A s = .ok (lenOf L) s := by
  have hc : ReadChain s 1 A (.str kLength) := ⟨hA, by simp [hAk, Kind.isReadPlain], fun h => by simp [hL] at h⟩
  have hg := get_readChain s (.str kLength) (.obj A) 1 A 19999 hc (by omega) (by simp [ordLookup, hL, noAccessor])
  simp only [ordLookup, hL, ownDataValue] at hg
  unfold lengthOf
  rw [show maxDepth = 19999 + 1 from rfl]
  simp only [lengthOfArrayLike, M.bind_eq, M.bind_apply, hg, M.bindRes_ok]
  rw [show (19999 : Nat) = 19998 + 1 from rfl]
  simp [toLength, toNumber, M.bind_eq, M.bind_apply, M.bindRes_ok, Pure.pure, M.pure, lenOf]
  rfl

/-- [[Get]] of an array's own data property. -/
theorem getProp_own_read (A : ObjId) (k : PropKey) (s : State) (hA : A < s.heap.size)
    (hAk : (s.objEntry A).kind.isReadPlain = true) {v : Value} {w e c : Bool}
    (hv : (s.objEntry A).props.get? k = some (.data v w e c)) :
    getProp A k s = .ok v s := by
  have hc : ReadChain s 1 A k := ⟨hA, hAk, fun h => by simp [hv] at h⟩
  have hg := get_readChain s k (.obj A) 1 A maxDepth hc (by rw [show maxDepth = 20000 from rfl]; omega)
    (by simp [ordLookup, hv, noAccessor])
  simp only [ordLookup, hv, ownDataValue] at hg
  exact hg

theorem taRecord_array (A : ObjId) (s : State) (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array) :
    taRecord? A s = .ok none s := by
  simp [taRecord?, objKind, readObj_entry' _ _ _ hA, hAk, M.bind_eq, M.bind_apply, Pure.pure, M.pure]

/-- The state after `next()` on an array iterator at index `i` with element `v`: the index bumped, the result object
`{value: v, done: false}` allocated. -/
def nextState (s : State) (It A : ObjId) (i : Nat) (v : Value) : State :=
  ((((s.withHeap (·.modify It fun ob => { ob with kind := .internal "Array Iterator" #[.obj A, .num (Conv.ofNat (i + 1)), .num (Conv.ofNat 1)] })).withHeap
    (·.push { proto := .obj s.curRealm.objectProto })).withHeap
    (·.modify s.heap.size (·.withProps (·.insert (.str kValue) (.data v true true true))))).withHeap
    (·.modify s.heap.size (·.withProps (·.insert (.str kDone) (.data (.bool false) true true true)))))

set_option maxRecDepth 10000 in
theorem next_eq (fN It A : ObjId) (i : Nat) (v : Value) (s : State) {L : F64} {lw le lc w e c : Bool}
    (hIt : It < s.heap.size) (hItk : (s.objEntry It).kind = .internal "Array Iterator" #[.obj A, numV i, numV 1])
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hL : (s.objEntry A).props.get? (.str kLength) = some (.data (.num L) lw le lc))
    (hi : i < lenOf L)
    (hidx : (Conv.toNat? (Conv.ofNat i)).getD 0 = i)
    (hv : (s.objEntry A).props.get? (PropKey.ofNat i) = some (.data v w e c)) (hItA : It ≠ A) :
    ES.arrayIteratorNext fN (.obj It) #[] .undefined s = .ok (.obj s.heap.size) (nextState s It A i v) := by
  have hlen := lengthOf_array A s hA hAk hL
  have hgv := getProp_own_read A (PropKey.ofNat i) _ hA (by simp [hAk, Kind.isReadPlain]) hv
  simp only [ES.arrayIteratorNext, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hIt, M.bindRes_ok, hItk]
  have hk1 : (Conv.toNat? (Conv.ofNat 1)).getD 1 = 1 := by decide
  simp [taRecord_array A s hA hAk, M.tryCatch, hlen, M.bindRes_ok, hidx, hk1, numV, Nat.not_le.mpr hi]
  simp only [modifyObj, M.bindRes_ok, M.bind_eq, M.bind_apply]
  rw [getProp_own_read A (PropKey.ofNat i) _ (v := v) (w := w) (e := e) (c := c) ?h1 ?h2 ?h3]
  case h1 => simpa [State.withHeap] using hA
  case h2 =>
    simp only [State.objEntry, State.withHeap, Array.getElem?_modify, hItA, ite_false]
    simp only [State.objEntry] at hAk; simp [hAk, Kind.isReadPlain]
  case h3 => simp only [State.objEntry, State.withHeap, Array.getElem?_modify, hItA, ite_false]; simpa [State.objEntry] using hv
  simp [createIterResult, newObject, alloc, setOwn, modifyObj, M.bind_eq, M.bind_apply, M.bindRes_ok,
    Pure.pure, M.pure, nextState]
  simp [State.curRealm, State.withHeap, Array.size_modify]


/-- **`%ArrayIteratorPrototype%.next` called on an array iterator** below the array's length: the result object. -/
theorem next_spec {n : Nat} {h : σ} {fN It A : ObjId} {bd : BuiltinData} {i : Nat} {v : Value} {s : State}
    {L : F64} {lw le lc w e c : Bool}
    (hlt : fN < s.heap.size) (hk : (s.objEntry fN).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some ES.arrayIteratorNext) (hf : s.fuel ≠ 0) (hrl : bd.realm = s.realm)
    (hIt : It < s.heap.size) (hItk : (s.objEntry It).kind = .internal "Array Iterator" #[.obj A, numV i, numV 1])
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hL : (s.objEntry A).props.get? (.str kLength) = some (.data (.num L) lw le lc))
    (hi : i < lenOf L)
    (hidx : (Conv.toNat? (Conv.ofNat i)).getD 0 = i)
    (hv : (s.objEntry A).props.get? (PropKey.ofNat i) = some (.data v w e c)) (hItA : It ≠ A) :
    WP eng answer n h (callImpl eng (.obj fN) (.obj It) #[]) s fun r w' h' =>
      r = .obj s.heap.size ∧ w' = { nextState { s with fuel := s.fuel - 1 } It A i v with realm := s.realm, script := s.script } ∧
      h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fN bd _ _ _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  rw [hrl]
  refine wp_of_eq (next_eq fN It A i v _ hIt hItk hA hAk hL hi hidx hv hItA) ⟨rfl, rfl, rfl⟩

end

end Logic
