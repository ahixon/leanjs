import JSProofs.Array
import JSProofs.StrIndex

/-!
# Arrays: creating and writing elements

The array exotic [[DefineOwnProperty]] on index keys (`PropKey.ofNat j`): appending at `length`
(which grows `length`) and redefining an existing element; [[Set]] of an element; ArraySetLength to
the current length.
-/

namespace ES

open Conv

theorem kLength_eq : kLength = JSStr.ofString "length" := rfl

/-- An array object with elements `xs 0, …, xs (len − 1)` (writable, enumerable, configurable data
properties), a writable `length`, nothing at other indices; extensible. -/
def ArrayObj (A : ObjId) (len : Nat) (xs : Nat → Value) (t : State) : Prop :=
  A < t.heap.size ∧ (t.objEntry A).kind = .array ∧ (t.objEntry A).extensible = true ∧
  (t.objEntry A).props.get? (.str kLength) = some (.data (.num (ofSmallInt len)) true false false) ∧
  (∀ j < len, (t.objEntry A).props.get? (PropKey.ofNat j) = some (.data (xs j) true true true)) ∧
  (∀ j, len ≤ j → j < 4294967295 → (t.objEntry A).props.get? (PropKey.ofNat j) = none)

@[simp] theorem Obj.withProps_proto (ob : Obj) (f : PropMap → PropMap) : (ob.withProps f).proto = ob.proto := by
  simp only [Obj.withProps]

theorem setProp_proto (s : State) (o : ObjId) (k : PropKey) (p : Property) (x : ObjId) :
    ((s.setProp o k p).objEntry x).proto = (s.objEntry x).proto := by
  by_cases h : o = x
  · subst h
    by_cases hs : o < s.heap.size
    · rw [State.setProp_entry_self _ _ _ _ hs, Obj.withProps_proto]
    · simp [State.setProp, State.objEntry, Array.getElem?_modify, hs]
  · rw [State.setProp_entry_ne _ _ _ _ _ h]

theorem ofNat_key_ne_length (j : Nat) (hj : j < 10 ^ 10) : (PropKey.ofNat j == .str kLength) = false := by
  have h := JSStr.ofNat_ne_length j hj
  simp only [PropKey.ofNat, kLength_eq]
  simpa using h

theorem arrayIndex_ofNat (j : Nat) (hj : j < 4294967295) : (PropKey.ofNat j).arrayIndex? = some j := by
  simp only [PropKey.ofNat, PropKey.arrayIndex?]; exact JSStr.toArrayIndex_ofNat j hj

theorem toNumber_num (n : Nat) (x : F64) (s : State) : ES.toNumber (n + 1) (.num x) s = .ok x s := by
  rw [ES.toNumber]; rfl

theorem getOwnProperty_array (n : Nat) (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind = .array) :
    ES.getOwnProperty (n + 1) o k s = .ok ((s.objEntry o).props.get? k) s := by
  rw [ES.getOwnProperty]
  simp [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, hk, ownProp]

/-- [[Set]] on an array's own writable data property, the array the receiver: [[DefineOwnProperty]]
with the value. -/
theorem set_array_own (n : Nat) (o : ObjId) (k : PropKey) (v : Value) (s : State) (v0 : Value) (e c : Bool)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind = .array)
    (hp : (s.objEntry o).props.get? k = some (.data v0 true e c)) :
    ES.set (n + 3) o k v (.obj o) s = ES.defineOwnProperty (n + 1) o k { value := some v } s := by
  rw [ES.set]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, hk, M.bindRes_ok]
  rw [ES.ordinarySet]
  simp [M.bind_eq, M.bind_apply, getOwnProperty_array n o k s h hk, hp, pure, M.pure]

/-- Appending an element at `length`: the property, then `length + 1`. -/
theorem defineOwnProperty_append (m : Nat) (A : ObjId) (len : Nat) (xs : Nat → Value) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    ES.defineOwnProperty (m + 1) A (PropKey.ofNat len) (PropDesc.data v) t =
      .ok true ((t.setProp A (PropKey.ofNat len) (.data v true true true)).setProp A (.str kLength)
        (.data (.num (Conv.ofNat (len + 1))) true false false)) := by
  obtain ⟨hs, hk, hx, hl, -, hnone⟩ := hA
  have hlb : len < intBound := by simp only [intBound]; omega
  rw [ES.defineOwnProperty]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok,
    ofNat_key_ne_length len (by omega), Bool.false_eq_true, ↓reduceIte, arrayIndex_ofNat len (by omega), ownProp, hl,
    toNat?_ofSmallInt len hlb, Option.getD_some]
  simp [ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ hs hx (hnone len (Nat.le_refl _) (by omega)), pure, M.pure, setOwn_eq]

/-- Redefining an existing element's value. -/
theorem defineOwnProperty_element (m : Nat) (A : ObjId) (len : Nat) (xs : Nat → Value) (j : Nat) (v : Value)
    (t : State) (hA : ArrayObj A len xs t) (hj : j < len) (hlen : len < 2 ^ 26) :
    ES.defineOwnProperty (m + 1) A (PropKey.ofNat j) { value := some v } t =
      .ok true (t.setProp A (PropKey.ofNat j) (.data v true true true)) := by
  obtain ⟨hs, hk, -, hl, hel, -⟩ := hA
  have hlb : len < intBound := by simp only [intBound]; omega
  rw [ES.defineOwnProperty]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok,
    ofNat_key_ne_length j (by omega), Bool.false_eq_true, ↓reduceIte, arrayIndex_ofNat j (by omega), ownProp, hl,
    toNat?_ofSmallInt len hlb, Option.getD_some, show ¬ (len ≤ j) by omega, decide_false, Bool.false_and]
  simp [ordinaryDefineOwnProperty_value _ _ _ _ _ _ _ hs (hel j hj), pure, M.pure, show ¬ (len ≤ j) by omega]

/-- [[Set]] of an existing element, the array itself the receiver. -/
theorem set_element (A : ObjId) (len : Nat) (xs : Nat → Value) (j : Nat) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hj : j < len) (hlen : len < 2 ^ 26) :
    Obj'.set A (PropKey.ofNat j) v (.obj A) t = .ok true (t.setProp A (PropKey.ofNat j) (.data v true true true)) := by
  have hA' := hA
  obtain ⟨hs, hk, -, -, hel, -⟩ := hA
  have hd : maxDepth = 19997 + 3 := by decide
  unfold Obj'.set; rw [hd, ES.set]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok]
  rw [ES.ordinarySet]
  simp only [M.bind_eq, M.bind_apply]
  rw [ES.getOwnProperty]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok, ownProp, hel j hj]
  simp [pure, M.pure, ES.getOwnProperty, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, ownProp,
    hel j hj, defineOwnProperty_element _ A len xs j v t hA' hj hlen]

/-- The array after writing element `j < len`. -/
theorem arrayObj_set (A : ObjId) (len : Nat) (xs : Nat → Value) (j : Nat) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hj : j < len) (hlen : len < 2 ^ 26) :
    ArrayObj A len (fun i => if i = j then v else xs i) (t.setProp A (PropKey.ofNat j) (.data v true true true)) := by
  obtain ⟨hs, hk, hx, hl, hel, hnone⟩ := hA
  have hne : ∀ i, i ≠ j → i < 4294967295 → j < 4294967295 → PropKey.ofNat j ≠ PropKey.ofNat i := by
    intro i hij hi hj' h
    have := congrArg PropKey.arrayIndex? h
    rw [arrayIndex_ofNat j (by omega), arrayIndex_ofNat i (by omega)] at this
    exact hij (Option.some.inj this).symm
  have hlk : PropKey.ofNat j ≠ .str kLength := by
    have := ofNat_key_ne_length j (by omega); simpa using this
  refine ⟨by simp [hs], by simp [State.setProp_entry_self _ _ _ _ hs, hk],
    by simp [State.setProp_entry_self _ _ _ _ hs, hx], ?_, ?_, ?_⟩
  · simp [State.setProp_entry_self _ _ _ _ hs, PropMap.get?_insert_ne _ _ _ _ hlk, hl]
  · intro i hi
    by_cases hij : i = j
    · subst hij; simp [State.setProp_entry_self _ _ _ _ hs]
    · simp [State.setProp_entry_self _ _ _ _ hs, PropMap.get?_insert_ne _ _ _ _ (hne i hij (by omega) (by omega)),
        hel i hi, hij]
  · intro i hi hib
    have hij : i ≠ j := by omega
    simp [State.setProp_entry_self _ _ _ _ hs, PropMap.get?_insert_ne _ _ _ _ (hne i hij hib (by omega)),
      hnone i hi hib]

/-- The array after appending at `length`. -/
theorem arrayObj_append (A : ObjId) (len : Nat) (xs : Nat → Value) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    ArrayObj A (len + 1) (fun i => if i = len then v else xs i)
      ((t.setProp A (PropKey.ofNat len) (.data v true true true)).setProp A (.str kLength)
        (.data (.num (Conv.ofNat (len + 1))) true false false)) := by
  obtain ⟨hs, hk, hx, hl, hel, hnone⟩ := hA
  have hne : ∀ i, i ≠ len → i < 4294967295 → PropKey.ofNat len ≠ PropKey.ofNat i := by
    intro i hij hi h
    have := congrArg PropKey.arrayIndex? h
    rw [arrayIndex_ofNat len (by omega), arrayIndex_ofNat i (by omega)] at this
    exact hij (Option.some.inj this).symm
  have hlk : PropKey.ofNat len ≠ .str kLength := by
    have := ofNat_key_ne_length len (by omega); simpa using this
  have hlk' : PropKey.str kLength ≠ PropKey.ofNat len := fun h => hlk h.symm
  have hlk2 : ∀ i, i < 4294967295 → PropKey.str kLength ≠ PropKey.ofNat i := by
    intro i hi h; have := ofNat_key_ne_length i (by omega); rw [← h] at this; simp at this
  have hs1 : A < (t.setProp A (PropKey.ofNat len) (.data v true true true)).heap.size := by simp [hs]
  refine ⟨by simp [hs], by simp [State.setProp_entry_self _ _ _ _ hs1, State.setProp_entry_self _ _ _ _ hs, hk],
    by simp [State.setProp_entry_self _ _ _ _ hs1, State.setProp_entry_self _ _ _ _ hs, hx], ?_, ?_, ?_⟩
  · simp [State.setProp_entry_self _ _ _ _ hs1, ofNat_eq_ofSmallInt (len + 1) (by simp only [intBound]; omega)]
  · intro i hi
    rw [State.setProp_entry_self _ _ _ _ hs1, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (hlk2 i (by omega)),
      State.setProp_entry_self _ _ _ _ hs, Obj.withProps_props]
    by_cases hij : i = len
    · subst hij; simp
    · rw [PropMap.get?_insert_ne _ _ _ _ (hne i hij (by omega)), hel i (by omega)]; simp [hij]
  · intro i hi hib
    rw [State.setProp_entry_self _ _ _ _ hs1, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (hlk2 i hib),
      State.setProp_entry_self _ _ _ _ hs, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (hne i (by omega) hib),
      hnone i (by omega) hib]

/-- The state after `arrayCreate 0`. -/
def emptyArrayState (t : State) : State :=
  (t.allocObj { proto := .obj t.curRealm.arrayProto, kind := .array }).setProp t.heap.size (.str kLength)
    (.data (.num (Conv.ofNat 0)) true false false)

theorem arrayCreate_zero (t : State) : arrayCreate 0 none t = .ok t.heap.size (emptyArrayState t) := by
  simp [arrayCreate, M.bind_eq, M.bind_apply, pure, M.pure, alloc_eq, setOwn_eq, emptyArrayState, -alloc_apply]

theorem arrayObj_empty (t : State) (xs : Nat → Value) : ArrayObj t.heap.size 0 xs (emptyArrayState t) := by
  have hs : t.heap.size < (t.allocObj { proto := .obj t.curRealm.arrayProto, kind := .array }).heap.size := by simp
  refine ⟨by simp [emptyArrayState], ?_, ?_, ?_, by intro j hj; omega, ?_⟩
  · simp [emptyArrayState, State.setProp_entry_self _ _ _ _ hs, State.allocObj_entry_new]
  · simp [emptyArrayState, State.setProp_entry_self _ _ _ _ hs, State.allocObj_entry_new]
  · simp [emptyArrayState, State.setProp_entry_self _ _ _ _ hs, State.allocObj_entry_new,
      ofNat_eq_ofSmallInt 0 (by simp [intBound])]
  · intro j _ hj
    have hlk2 : PropKey.str kLength ≠ PropKey.ofNat j := by
      intro h; have := ofNat_key_ne_length j (by omega); rw [← h] at this; simp at this
    simp [emptyArrayState, State.setProp_entry_self _ _ _ _ hs, State.allocObj_entry_new,
      PropMap.get?_insert_ne _ _ _ _ hlk2]

/-- CreateDataPropertyOrThrow at `length`: an append. -/
theorem createDataPropertyOrThrow_append (A : ObjId) (len : Nat) (xs : Nat → Value) (v : Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    createDataPropertyOrThrow A (PropKey.ofNat len) v t =
      .ok () ((t.setProp A (PropKey.ofNat len) (.data v true true true)).setProp A (.str kLength)
        (.data (.num (Conv.ofNat (len + 1))) true false false)) := by
  have hd : maxDepth = 19999 + 1 := by decide
  simp [createDataPropertyOrThrow, createDataProperty, Obj'.defineOwnProperty, hd, M.bind_eq, M.bind_apply,
    defineOwnProperty_append 19999 A len xs v t hA hlen, pure, M.pure]

/-- `a.length = len` with the current length (ArraySetLength, the length unchanged). -/
theorem setProp_length_same (A : ObjId) (len : Nat) (xs : Nat → Value) (t : State)
    (hA : ArrayObj A len xs t) (hlen : len < 2 ^ 26) :
    ∃ t', setProp A (.str kLength) (numV len) true t = .ok () t' ∧ ArrayObj A len xs t' ∧
      t'.envs = t.envs ∧ t'.fuel = t.fuel ∧ t'.heap.size = t.heap.size ∧
      (∀ o, o ≠ A → t'.objEntry o = t.objEntry o) ∧ t'.realms = t.realms ∧
      (t'.objEntry A).proto = (t.objEntry A).proto := by
  have hA' := hA
  obtain ⟨hs, hk, hx, hl, hel, hnone⟩ := hA
  have hlb : len < intBound := by simp only [intBound]; omega
  have hnv : numV len = .num (ofSmallInt len) := by simp [numV, ofNat_eq_ofSmallInt len hlb]
  have hd : maxDepth = 19996 + 4 := by decide
  have hlk : (PropKey.str kLength == PropKey.str kLength) = true := by simp
  refine ⟨t.setProp A (.str kLength) (.data (.num (ofSmallInt len)) true false false), ?_, ?_, by simp, by simp,
    by simp, fun o ho => State.setProp_entry_ne _ _ _ _ _ (Ne.symm ho), by simp, setProp_proto _ _ _ _ _⟩
  · simp only [setProp, M.bind_eq, M.bind_apply, hnv]
    unfold Obj'.set; rw [hd, set_array_own _ A _ _ t _ _ _ hs hk hl, ES.defineOwnProperty]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hs, hk, M.bindRes_ok, hlk, ↓reduceIte]
    rw [ES.arraySetLength]
    simp only [M.bind_eq, M.bind_apply, toNumber_num, M.bindRes_ok]
    simp only [pure, M.pure, M.bindRes_ok, toUint32_ofSmallInt len (by omega), toNat?_ofSmallInt len hlb,
      readObj_entry' _ _ _ hs, hl, Option.getD_some, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ge_iff_le, Nat.le_refl, decide_true, ofNat_eq_ofSmallInt len hlb]
    simp [M.bind_eq, M.bind_apply, readObj_entry' _ _ _ hs, hl, toNat?_ofSmallInt len hlb,
      ordinaryDefineOwnProperty_value _ _ _ _ _ _ _ hs hl, pure, M.pure]
  · have hlk2 : ∀ i, i < 4294967295 → PropKey.str kLength ≠ PropKey.ofNat i := by
      intro i hi h; have := ofNat_key_ne_length i (by omega); rw [← h] at this; simp at this
    refine ⟨by simp [hs], by simp [State.setProp_entry_self _ _ _ _ hs, hk],
      by simp [State.setProp_entry_self _ _ _ _ hs, hx], by simp [State.setProp_entry_self _ _ _ _ hs], ?_, ?_⟩
    · intro j hj
      rw [State.setProp_entry_self _ _ _ _ hs, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (hlk2 j (by omega))]
      exact hel j hj
    · intro j hj hjb
      rw [State.setProp_entry_self _ _ _ _ hs, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (hlk2 j hjb)]
      exact hnone j hj hjb

/-! ## Array literals -/

/-- One element of an array literal, as `Sem.array` handles it. -/
def arrayStep (a : ObjId) (ctx : Ctx) : Nat → Sem.ElemD → M Nat := fun i el => do
  match el with
  | .hole => pure (i + 1)
  | .expr e =>
    let v ← e ctx
    createDataPropertyOrThrow a (PropKey.ofNat i) v
    pure (i + 1)
  | .spread e =>
    let v ← e ctx
    let xs ← iterableToList v
    M.foldArr xs i fun j x => do
      createDataPropertyOrThrow a (PropKey.ofNat j) x
      pure (j + 1)

theorem array_eq (elems : Array Sem.ElemD) (ctx : Ctx) :
    Sem.array elems ctx = (do
      let a ← arrayCreate 0
      let len ← M.foldArr elems 0 (arrayStep a ctx)
      setProp a (.str kLength) (numV len)
      pure (.obj a)) := rfl

/-- The elements of an array literal whose expressions evaluate (without effects) to `ps`'s values. -/
theorem fold_elems (A : ObjId) (ctx : Ctx) :
    ∀ (ps : List (Sem.CExpr × Value)) (i : Nat) (xs : Nat → Value) (t : State),
      (∀ p ∈ ps, ∀ u, p.1 ctx u = .ok p.2 u) → i + ps.length < 2 ^ 26 → ArrayObj A i xs t →
      ∃ t', M.foldList (ps.map fun p => Sem.ElemD.expr p.1) i (arrayStep A ctx) t = .ok (i + ps.length) t' ∧
        ArrayObj A (i + ps.length) (fun j => if j < i then xs j else ((ps.map Prod.snd)[j - i]?).getD .undefined) t' ∧
        t'.envs = t.envs ∧ t'.fuel = t.fuel ∧ t'.heap.size = t.heap.size ∧
        (∀ o, o ≠ A → t'.objEntry o = t.objEntry o) ∧ t'.realms = t.realms ∧
        (t'.objEntry A).proto = (t.objEntry A).proto := by
  intro ps
  induction ps with
  | nil =>
    intro i xs t _ _ hA
    refine ⟨t, by simp, ?_, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
    have : (fun j => if j < i then xs j else (([] : List Value)[j - i]?).getD Value.undefined) = fun j =>
        if j < i then xs j else .undefined := by funext j; simp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
    exact ⟨h1, h2, h3, h4, fun j hj => by simpa [show j < i by simpa using hj] using h5 j (by simpa using hj), h6⟩
  | cons p ps ih =>
    intro i xs t hev hb hA
    have hp := hev p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ ps, ∀ u, q.1 ctx u = .ok q.2 u := fun q h => hev q (List.mem_cons_of_mem _ h)
    have happ := createDataPropertyOrThrow_append A i xs p.2 t hA (by simp at hb; omega)
    have hA1 := arrayObj_append A i xs p.2 t hA (by simp at hb; omega)
    obtain ⟨t', hf, hA', he', hfu', hz', ho', hr', hp'⟩ := ih (i + 1) _ _ hrest (by simp at hb; omega) hA1
    refine ⟨t', ?_, ?_, by rw [he']; simp, by rw [hfu']; simp, by rw [hz']; simp, fun o ho => by
      rw [ho' o ho, State.setProp_entry_ne _ _ _ _ _ (Ne.symm ho), State.setProp_entry_ne _ _ _ _ _ (Ne.symm ho)],
      by rw [hr']; simp, by rw [hp', setProp_proto, setProp_proto]⟩
    · simp only [List.map_cons, M.foldList_cons, arrayStep, M.bind_eq, M.bind_apply, hp, M.bindRes_ok, happ,
        pure, M.pure]
      rw [hf]; simp; omega
    · have hlen : i + 1 + ps.length = i + (p :: ps).length := by simp; omega
      rw [← hlen]
      have hfun : (fun j => if j < i + 1 then (if j = i then p.2 else xs j)
            else ((ps.map Prod.snd)[j - (i + 1)]?).getD Value.undefined) =
          (fun j => if j < i then xs j else (((p :: ps).map Prod.snd)[j - i]?).getD Value.undefined) := by
        funext j
        by_cases hji : j < i
        · simp [hji, show j < i + 1 by omega, show j ≠ i by omega]
        · by_cases hjeq : j = i
          · subst hjeq; simp
          · simp only [hji, hjeq, show ¬ j < i + 1 by omega, ↓reduceIte, List.map_cons]
            rw [show j - i = (j - (i + 1)) + 1 by omega, List.getElem?_cons_succ]
      rw [← hfun]; exact hA'

/-- **An array literal** `[e0, …, e(n−1)]` whose element expressions evaluate (without effects) to
`v0, …, v(n−1)`: a new array object with exactly those elements. -/
theorem array_literal (ctx : Ctx) (ps : List (Sem.CExpr × Value)) (hev : ∀ p ∈ ps, ∀ u, p.1 ctx u = .ok p.2 u)
    (hb : ps.length < 2 ^ 26) (t : State) :
    ∃ t', Sem.array (ps.map fun p => Sem.ElemD.expr p.1).toArray ctx t = .ok (.obj t.heap.size) t' ∧
      ArrayObj t.heap.size ps.length (fun j => ((ps.map Prod.snd)[j]?).getD .undefined) t' ∧
      t'.envs = t.envs ∧ t'.fuel = t.fuel ∧ t'.heap.size = t.heap.size + 1 ∧
      (∀ o, o < t.heap.size → t'.objEntry o = t.objEntry o) ∧ t'.realms = t.realms ∧
      (t'.objEntry t.heap.size).proto = .obj t.curRealm.arrayProto := by
  obtain ⟨t1, hf, hA1, he1, hfu1, hz1, ho1, hr1, hp1⟩ := fold_elems t.heap.size ctx ps 0 (fun _ => .undefined) (emptyArrayState t) hev
    (by simpa using hb) (arrayObj_empty t _)
  have hA1' : ArrayObj t.heap.size ps.length (fun j => ((ps.map Prod.snd)[j]?).getD .undefined) t1 := by
    simpa using hA1
  obtain ⟨t2, hs2, hA2, he2, hfu2, hz2, ho2, hr2, hp2⟩ := setProp_length_same t.heap.size ps.length _ t1 hA1' hb
  have hE : (emptyArrayState t).envs = t.envs := by simp [emptyArrayState]
  have hF : (emptyArrayState t).fuel = t.fuel := by simp [emptyArrayState]
  refine ⟨t2, ?_, hA2, by rw [he2, he1, hE], by rw [hfu2, hfu1, hF], by rw [hz2, hz1]; simp [emptyArrayState],
    fun o ho => by
      have hne : o ≠ t.heap.size := Nat.ne_of_lt ho
      rw [ho2 o hne, ho1 o hne]
      simp only [emptyArrayState]
      rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hne), State.allocObj_entry_lt _ _ _ ho],
    by rw [hr2, hr1]; simp [emptyArrayState],
    by rw [hp2, hp1]; simp only [emptyArrayState]; rw [setProp_proto, State.allocObj_entry_new]⟩
  rw [array_eq]
  simp only [M.bind_eq, M.bind_apply, arrayCreate_zero, M.bindRes_ok, M.foldArr_toArray]
  simp only [Nat.zero_add] at hf
  rw [hf]
  simp [hs2, pure, M.pure]

/-! ## Writes and reads through references -/

theorem key_eq (k : Nat) : PropKey.str (JSStr.ofString (toString k)) = PropKey.ofNat k := rfl

/-- **`a[k] = v`** on an existing element. -/
theorem putRefValue_element (A : ObjId) (len : Nat) (xs : Nat → Value) (k : Nat) (v : Value) (strict : Bool)
    (t : State) (hA : ArrayObj A len xs t) (hk : k < len) (hlen : len < 2 ^ 26) :
    putRefValue (.prop (.obj A) (.num (ofSmallInt k)) strict none) v t =
      .ok () (t.setProp A (PropKey.ofNat k) (.data v true true true)) := by
  have hkb : k < intBound := by simp only [intBound]; omega
  simp only [putRefValue, M.bind_eq, M.bind_apply, toPropertyKey_int k hkb, M.bindRes_ok, Option.getD_none,
    key_eq, set_element A len xs k v t hA hk hlen]
  simp [pure, M.pure]

/-- Reading `a[k]` of an array object. -/
theorem getRefValue_element (A : ObjId) (len : Nat) (xs : Nat → Value) (k : Nat) (strict : Bool) (t : State)
    (hA : ArrayObj A len xs t) (hk : k < len) (hlen : len < 2 ^ 26) :
    getRefValue (.prop (.obj A) (.num (ofSmallInt k)) strict none) t = .ok (xs k) t := by
  obtain ⟨hs, hkd, -, -, hel, -⟩ := hA
  exact getRefValue_index A k strict t (xs k) true true true (by simp only [intBound]; omega) hs hkd
    (by rw [key_eq]; exact hel k hk)

/-- `ArrayObj` depends only on the elements below `len`. -/
theorem arrayObj_congr (A : ObjId) (len : Nat) (xs ys : Nat → Value) (t : State) (h : ∀ j < len, xs j = ys j)
    (hA : ArrayObj A len xs t) : ArrayObj A len ys t := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
  exact ⟨a1, a2, a3, a4, fun j hj => by rw [← h j hj]; exact a5 j hj, a6⟩

end ES
