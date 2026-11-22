import JSProofs.ArrayWrite
import JSProofs.Destructure

/-!
# Two-element array literals whose elements are reads (zippy docs/react-proofs.md)

`[e1, e2]` where each element evaluates without changing the state (React's `return [hook.memoizedState,
queue.dispatch]` in `updateReducerImpl`): a new array with the two values. `array_literal` needs elements whose
value does not depend on the state; here each element has its own WP, at the state it runs in.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace ES
open Conv

/-- Setting an array's `length` to what it is: the property rewritten with the same value. -/
theorem setProp_length_eq (A : ObjId) (len : Nat) (xs : Nat → Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    setProp A (.str kLength) (numV len) true t =
      .ok () (t.setProp A (.str kLength) (.data (.num (ofSmallInt len)) true false false)) := by
  obtain ⟨hs, hk, hx, hl, hel, hnone⟩ := hA
  have hlb : len < intBound := by simp only [intBound]; omega
  have hnv : numV len = .num (ofSmallInt len) := by simp [numV, ofNat_eq_ofSmallInt len hlb]
  have hd : maxDepth = 19996 + 4 := by decide
  have hlk : (PropKey.str kLength == PropKey.str kLength) = true := by simp
  simp only [setProp, M.bind_eq, M.bind_apply, hnv]
  unfold Obj'.set; rw [hd, set_array_own _ A _ _ t _ _ _ hs hk hl, ES.defineOwnProperty]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok, hlk, ↓reduceIte]
  rw [ES.arraySetLength]
  simp only [M.bind_eq, M.bind_apply, toNumber_num, M.bindRes_ok]
  simp only [Pure.pure, M.pure, M.bindRes_ok, toUint32_ofSmallInt len (by omega), toNat?_ofSmallInt len hlb,
    readObj_entry' _ _ _ hs, hl, Option.getD_some, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    ge_iff_le, Nat.le_refl, decide_true, ofNat_eq_ofSmallInt len hlb]
  simp [M.bind_eq, M.bind_apply, readObj_entry' _ _ _ hs, hl, toNat?_ofSmallInt len hlb,
    ordinaryDefineOwnProperty_value _ _ _ _ _ _ _ hs hl, Pure.pure, M.pure]

end ES

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The array literal's state after its first element `v1`. -/
def arr1State (s : State) (v1 : Value) : State :=
  ((emptyArrayState s).setProp s.heap.size (PropKey.ofNat 0) (.data v1 true true true)).setProp s.heap.size
    (.str kLength) (.data (.num (Conv.ofNat 1)) true false false)

theorem wp_array2 {n : Nat} {h : σ} {e1 e2 : Sem.CExpr} {v1 v2 : Value} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (h1 : WP eng answer n h (e1 ctx) (emptyArrayState s) fun v w h' => v = v1 ∧ w = emptyArrayState s ∧ h' = h)
    (h2 : WP eng answer n h (e2 ctx) (arr1State s v1) fun v w h' => v = v2 ∧ w = arr1State s v1 ∧ h' = h)
    (hQ : ∀ t', ArrayObj s.heap.size 2 (fun j => if j = 1 then v2 else if j = 0 then v1 else .undefined) t' →
      t'.envs = s.envs → t'.fuel = s.fuel → t'.heap.size = s.heap.size + 1 → Frame {} s t' →
      (t'.objEntry s.heap.size).props.get? (.sym WK.iterator) = none →
      (∀ o, o < s.heap.size → t'.objEntry o = s.objEntry o) → t'.realms = s.realms →
      (t'.objEntry s.heap.size).proto = .obj s.curRealm.arrayProto → Q (.obj s.heap.size) t' h) :
    WP eng answer n h (Sem.array #[.expr e1, .expr e2] ctx) s Q := by
  rw [array_eq]
  simp only [M.bind_eq]
  apply wp_mbind
  refine wp_of_eq (arrayCreate_zero s) ?_
  apply wp_mbind
  simp only [M.foldArr_toArray]
  rw [foldList_cons_bind]
  apply wp_mbind
  simp only [arrayStep, M.bind_eq]
  apply wp_mbind
  refine wp_mono h1 ?_
  intro v w h' ⟨hv, hw, hh⟩
  subst v w h'
  apply wp_mbind
  refine wp_of_eq (createDataPropertyOrThrow_append s.heap.size 0 (fun _ => .undefined) v1 _ (arrayObj_empty s _) (by decide)) ?_
  refine wp_of_eq rfl ?_
  rw [foldList_cons_bind]
  apply wp_mbind
  simp only [arrayStep, M.bind_eq]
  apply wp_mbind
  refine wp_mono h2 ?_
  intro v w h' ⟨hv, hw, hh⟩
  subst v w h'
  have hA1 : ArrayObj s.heap.size 1 (fun i => if i = 0 then v1 else .undefined) (arr1State s v1) :=
    arrayObj_append s.heap.size 0 (fun _ => .undefined) v1 _ (arrayObj_empty s _) (by decide)
  apply wp_mbind
  refine wp_of_eq (createDataPropertyOrThrow_append s.heap.size 1 _ v2 _ hA1 (by decide)) ?_
  refine wp_of_eq rfl ?_
  rw [foldList_nil_pure]
  refine wp_of_eq rfl ?_
  have hA2 := arrayObj_append s.heap.size 1 _ v2 _ hA1 (by decide)
  obtain ⟨t', hs', hA', he', hfu', hz', ho', hr', hp'⟩ := setProp_length_same s.heap.size 2 _ _ hA2 (by decide)
  have ht' : (((arr1State s v1).setProp s.heap.size (PropKey.ofNat 1) (.data v2 true true true)).setProp s.heap.size
      (.str kLength) (.data (.num (Conv.ofNat (1 + 1))) true false false)).setProp s.heap.size (.str kLength)
      (.data (.num (Conv.ofSmallInt ((2 : Nat) : Int))) true false false) = t' := by
    have h2 := hs'
    rw [setProp_length_eq s.heap.size 2 _ _ hA2 (by decide)] at h2
    exact (Res.ok.inj h2).2
  have hsz : s.heap.size < (s.allocObj { proto := .obj s.curRealm.arrayProto, kind := .array }).heap.size := by simp
  have hsym : (t'.objEntry s.heap.size).props.get? (.sym WK.iterator) = none := by
    rw [← ht']
    simp only [arr1State, emptyArrayState]
    repeat rw [State.setProp_entry_self _ _ _ _ (by simp)]
    rw [State.allocObj_entry_new]
    simp [PropKey.ofNat, PropMap.get?_insert_ne, PropMap.get?_empty]
  have hFr : Frame {} s t' := by
    rw [← ht']
    simp only [arr1State, emptyArrayState]
    repeat (first | with_reducible refine frame_setProp_new ?_ (Nat.le_refl _) _ _ | with_reducible exact frame_allocObj (frame_refl _ s) _)
  apply wp_mbind
  refine wp_of_eq hs' ?_
  have hsz : s.heap.size < (emptyArrayState s).heap.size := by simp [emptyArrayState]
  refine wp_of_eq rfl (hQ t' hA' ?_ ?_ ?_ hFr hsym ?_ ?_ ?_)
  · rw [he']; simp [arr1State, emptyArrayState]
  · rw [hfu']; simp [arr1State, emptyArrayState]
  · rw [hz']; simp [arr1State, emptyArrayState]
  · intro o ho
    have hne : o ≠ s.heap.size := Nat.ne_of_lt ho
    rw [ho' o hne]
    simp only [arr1State, emptyArrayState]
    rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne), State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne),
      State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne), State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne),
      State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne), State.allocObj_entry_lt _ _ _ ho]
  · rw [hr']; simp [arr1State, emptyArrayState]
  · rw [hp']; simp only [arr1State, emptyArrayState]
    rw [setProp_proto, setProp_proto, setProp_proto, setProp_proto, setProp_proto, State.allocObj_entry_new]

end

end Logic
