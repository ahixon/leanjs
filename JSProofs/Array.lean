import JSProofs.Proto
import JSProofs.NumInt

/-!
# Arrays: reading elements and `length`

An array object's [[Get]] is the ordinary one (only [[DefineOwnProperty]] is exotic), and `a[i]` with
an integer Number `i` reads the property named by `i`'s decimal digits: integers below 2^53 convert
to their own digits (`toStr_int`).
-/

namespace ES

open Conv

/-- The integer path of Number::toString: a natural below 2^53 converts to its decimal digits. -/
theorem toStr_int (k : Nat) (hk : k < intBound) (s : State) :
    toStr (.num (ofSmallInt k)) s = .ok (JSStr.ofString (toString k)) s := by
  have hd : maxDepth = 19999 + 1 := by decide
  simp only [toStr, hd, toJSString, numberToJSStr, Num.toJSStr, Num.toStringRadix, pure, M.pure]
  simp only [beq_self_eq_true, ↓reduceIte]
  by_cases hk0 : k = 0
  · subst hk0; simp [ofSmallInt_zero, Num.toStringDec]; rfl
  · have hi : ((k : Int)) ≠ 0 := by omega
    have hb : ((k : Int)).natAbs < intBound := by simpa using hk
    rw [ofSmallInt_ne_zero _ hi hb]
    have hl := log2_le_52 _ (by simpa using hi) hb
    have hm := ofSmallInt_m_ne_zero _ hi
    simp only [Int.natAbs_natCast] at hl hm ⊢
    have hneg : decide ((k : Int) < 0) = false := by simp
    rw [hneg]
    by_cases h52 : Nat.log2 k = 52
    · simp [Num.toStringDec, hm, h52]
    · have he : ((Nat.log2 k : Int) - 52) ≠ 0 := by omega
      have hk' : (-((Nat.log2 k : Int) - 52)).toNat = 52 - Nat.log2 k := by omega
      simp [Num.toStringDec, hm, he, hk', Num.intMag, Nat.shiftLeft_shiftRight,
        show (Nat.log2 k : Int) - 52 < 0 by omega, show (Nat.log2 k : Int) - 52 > -53 by omega]

/-- [[Get]] of an own data property of an array object (ordinary for arrays). -/
theorem Obj'.get_array (o : ObjId) (k : PropKey) (r : Value) (s : State) (v : Value) (w e c : Bool)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind = .array)
    (hp : (s.objEntry o).props.get? k = some (.data v w e c)) :
    Obj'.get o k r s = .ok v s := by
  have hd : maxDepth = 19997 + 3 := by decide
  unfold Obj'.get; rw [hd, ES.get]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, hk, M.bindRes_ok]
  rw [ES.ordinaryGet]
  simp only [M.bind_eq, M.bind_apply]
  rw [ES.getOwnProperty]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, hk, M.bindRes_ok, ownProp, hp]
  rfl

theorem toPropertyKey_int (k : Nat) (hk : k < intBound) (s : State) :
    toPropertyKey (.num (ofSmallInt k)) s = .ok (.str (JSStr.ofString (toString k))) s := by
  simp [toPropertyKey, M.bind_eq, M.bind_apply, toStr_int k hk, pure, M.pure]

/-- GetValue of `a[k]`: the own data property named by `k`'s digits. -/
theorem getRefValue_index (o : ObjId) (k : Nat) (strict : Bool) (s : State) (v : Value) (w e c : Bool)
    (hk : k < intBound) (h : o < s.heap.size) (hkind : (s.objEntry o).kind = .array)
    (hp : (s.objEntry o).props.get? (.str (JSStr.ofString (toString k))) = some (.data v w e c)) :
    getRefValue (.prop (.obj o) (.num (ofSmallInt k)) strict none) s = .ok v s := by
  simp only [getRefValue, Value.isNullish, M.bind_eq, M.bind_apply, toPropertyKey_int k hk, M.bindRes_ok,
    Bool.false_eq_true, ↓reduceIte, Obj'.get_array o _ _ s v w e c h hkind hp]

/-- GetValue of `a.key` (e.g. `a.length`). -/
theorem getRefValue_name (o : ObjId) (key : JSStr) (strict : Bool) (s : State) (v : Value) (w e c : Bool)
    (h : o < s.heap.size) (hkind : (s.objEntry o).kind = .array)
    (hp : (s.objEntry o).props.get? (.str key) = some (.data v w e c)) :
    getRefValue (.prop (.obj o) (.str key) strict none) s = .ok v s := by
  simp [getRefValue, Value.isNullish, M.bind_eq, M.bind_apply, toPropertyKey, pure, M.pure,
    Obj'.get_array o _ _ s v w e c h hkind hp]

@[simp] theorem State.setEnv_objEntry (s : State) (env : EnvId) (e : Env) (o : ObjId) :
    (s.setEnv env e).objEntry o = s.objEntry o := by simp only [State.setEnv, State.objEntry]
@[simp] theorem State.setEnv_heap_size (s : State) (env : EnvId) (e : Env) :
    (s.setEnv env e).heap.size = s.heap.size := by simp only [State.setEnv]
@[simp] theorem State.pushEnv_objEntry (s : State) (e : Env) (o : ObjId) :
    (s.pushEnv e).objEntry o = s.objEntry o := by simp only [State.pushEnv, State.objEntry]
@[simp] theorem State.pushEnv_heap_size (s : State) (e : Env) :
    (s.pushEnv e).heap.size = s.heap.size := by simp only [State.pushEnv]

end ES
