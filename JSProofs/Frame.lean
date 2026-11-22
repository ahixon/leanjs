import JSProofs.Rules3

/-!
# Frames: what a call leaves unchanged (zippy docs/react-proofs.md)

`Frame fp s w`: from `s` to `w`, nothing that existed in `s` changed outside the footprint `fp` — bindings
`(record, name)` and properties `(object, key)`; records and objects may be created. Declarative and function
records keep their kind and outer record, objects their kind, prototype and extensibility; other records (object,
global, module) are unchanged.

A function's frame follows its proof: `frame_refl`, and one lemma per kind of state change (`frame_setEnv_new`,
`frame_setEnv_bind`, `frame_setProp_new`, `frame_setProp_prop`, `frame_allocObj`, `frame_pushEnv`, …). At a call
site, the caller reads through the callee's frame: `lookup_frame`, `resolve_frame`, `props_frame` — a read outside
the footprint is the read before the call.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- The bindings and properties a computation may change. -/
structure Footprint where
  binds : List (EnvId × JSStr) := []
  props : List (ObjId × PropKey) := []

def Footprint.union (a b : Footprint) : Footprint := ⟨a.binds ++ b.binds, a.props ++ b.props⟩

/-- A record now (`ew`) agrees with the record then (`es`) except at the names `P`. -/
def EnvAgree (P : JSStr → Prop) (ew es : Env) : Prop :=
  match Scope.declLike? es with
  | some (bs, o) => ∃ bw, Scope.declLike? ew = some (bw, o) ∧ ∀ x, ¬ P x → bw[x]? = bs[x]?
  | none => ew = es

/-- An object now agrees with the object then except at the keys `P`. -/
def ObjAgree (P : PropKey → Prop) (ow os : Obj) : Prop :=
  ow.kind = os.kind ∧ ow.proto = os.proto ∧ ow.extensible = os.extensible ∧ ∀ k, ¬ P k → ow.props.get? k = os.props.get? k

/-- **The frame**: from `s` to `w`, only `fp` changed among what existed in `s`; a record or object with nothing in
the footprint is exactly as it was. -/
structure Frame (fp : Footprint) (s w : State) : Prop where
  envs_le : s.envs.size ≤ w.envs.size
  heap_le : s.heap.size ≤ w.heap.size
  env_agree : ∀ e, e < s.envs.size → EnvAgree (fun x => (e, x) ∈ fp.binds) (w.envEntry e) (s.envEntry e)
  obj_agree : ∀ o, o < s.heap.size → ObjAgree (fun k => (o, k) ∈ fp.props) (w.objEntry o) (s.objEntry o)
  env_eq : ∀ e, e < s.envs.size → (∀ x, (e, x) ∉ fp.binds) → w.envEntry e = s.envEntry e
  obj_eq : ∀ o, o < s.heap.size → (∀ k, (o, k) ∉ fp.props) → w.objEntry o = s.objEntry o

/-! ## Composition -/

theorem envAgree_refl (P : JSStr → Prop) (ev : Env) : EnvAgree P ev ev := by
  unfold EnvAgree
  cases h : Scope.declLike? ev with
  | some p => obtain ⟨bs, o⟩ := p; exact ⟨bs, rfl, fun _ _ => rfl⟩
  | none => rfl

theorem envAgree_trans {P R : JSStr → Prop} {a b c : Env} (h1 : EnvAgree P b a) (h2 : EnvAgree R c b) :
    EnvAgree (fun x => P x ∨ R x) c a := by
  unfold EnvAgree at *
  cases ha : Scope.declLike? a with
  | none => rw [ha] at h1; subst h1; rw [ha] at h2; exact h2
  | some p =>
    obtain ⟨bs, o⟩ := p
    rw [ha] at h1
    obtain ⟨bb, hb, hbx⟩ := h1
    rw [hb] at h2
    obtain ⟨bc, hc, hcx⟩ := h2
    exact ⟨bc, hc, fun x hx => by
      rw [hcx x (fun h => hx (Or.inr h)), hbx x (fun h => hx (Or.inl h))]⟩

theorem envAgree_mono {P R : JSStr → Prop} {a b : Env} (h : EnvAgree P a b) (hPR : ∀ x, P x → R x) :
    EnvAgree R a b := by
  unfold EnvAgree at *
  cases hb : Scope.declLike? b with
  | none => rw [hb] at h; exact h
  | some p =>
    obtain ⟨bs, o⟩ := p
    rw [hb] at h
    obtain ⟨bw, hw, hx⟩ := h
    exact ⟨bw, hw, fun x hn => hx x (fun hp => hn (hPR x hp))⟩

theorem objAgree_refl (P : PropKey → Prop) (ob : Obj) : ObjAgree P ob ob := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem objAgree_trans {P R : PropKey → Prop} {a b c : Obj} (h1 : ObjAgree P b a) (h2 : ObjAgree R c b) :
    ObjAgree (fun k => P k ∨ R k) c a :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun k hk => by
    rw [h2.2.2.2 k (fun h => hk (Or.inr h)), h1.2.2.2 k (fun h => hk (Or.inl h))]⟩

theorem frame_refl (fp : Footprint) (s : State) : Frame fp s s :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => envAgree_refl _ _, fun _ _ => objAgree_refl _ _, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- **Frames compose**: the footprints' union. -/
theorem frame_trans {fp1 fp2 : Footprint} {s u w : State} (h1 : Frame fp1 s u) (h2 : Frame fp2 u w) :
    Frame (fp1.union fp2) s w where
  envs_le := Nat.le_trans h1.envs_le h2.envs_le
  heap_le := Nat.le_trans h1.heap_le h2.heap_le
  env_agree e he := envAgree_mono (envAgree_trans (h1.env_agree e he)
      (h2.env_agree e (Nat.lt_of_lt_of_le he h1.envs_le)))
    fun x hx => by simp only [Footprint.union, List.mem_append]; exact hx
  obj_agree o ho :=
    have h := objAgree_trans (h1.obj_agree o ho) (h2.obj_agree o (Nat.lt_of_lt_of_le ho h1.heap_le))
    ⟨h.1, h.2.1, h.2.2.1, fun k hk => h.2.2.2 k (by simpa [Footprint.union, List.mem_append] using hk)⟩
  env_eq e he hn := by
    rw [h2.env_eq e (Nat.lt_of_lt_of_le he h1.envs_le) (fun x hx => hn x (by simp [Footprint.union, hx])),
      h1.env_eq e he (fun x hx => hn x (by simp [Footprint.union, hx]))]
  obj_eq o ho hn := by
    rw [h2.obj_eq o (Nat.lt_of_lt_of_le ho h1.heap_le) (fun k hk => hn k (by simp [Footprint.union, hk])),
      h1.obj_eq o ho (fun k hk => hn k (by simp [Footprint.union, hk]))]

theorem frame_mono {fp fp' : Footprint} {s w : State} (h : Frame fp s w)
    (hb : ∀ p, p ∈ fp.binds → p ∈ fp'.binds) (hp : ∀ p, p ∈ fp.props → p ∈ fp'.props) : Frame fp' s w where
  envs_le := h.envs_le
  heap_le := h.heap_le
  env_agree e hl := envAgree_mono (h.env_agree e hl) fun x hx => hb _ hx
  obj_agree o hl := ⟨(h.obj_agree o hl).1, (h.obj_agree o hl).2.1, (h.obj_agree o hl).2.2.1,
    fun k hk => (h.obj_agree o hl).2.2.2 k (fun h' => hk (hp _ h'))⟩
  env_eq e hl hn := h.env_eq e hl (fun x hx => hn x (hb _ hx))
  obj_eq o hl hn := h.obj_eq o hl (fun k hk => hn k (hp _ hk))

/-! ## Steps -/

section
variable {fp : Footprint} {s u : State}

/-- A record that did not exist at the start may change freely. -/
theorem frame_setEnv_new (hF : Frame fp s u) {e : EnvId} (he : s.envs.size ≤ e) (ev : Env) :
    Frame fp s (u.setEnv e ev) := by
  have hne : ∀ i, i < s.envs.size → e ≠ i := fun i hi h => by subst h; omega
  exact {
    envs_le := by simpa using hF.envs_le
    heap_le := by simpa [State.setEnv] using hF.heap_le
    env_agree := fun i hi => by rw [setEnv_envEntry_ne _ _ _ _ (hne i hi)]; exact hF.env_agree i hi
    obj_agree := fun o ho => by simpa [State.objEntry, State.setEnv] using hF.obj_agree o ho
    env_eq := fun i hi hn => by rw [setEnv_envEntry_ne _ _ _ _ (hne i hi)]; exact hF.env_eq i hi hn
    obj_eq := fun o ho hn => by simpa [State.objEntry, State.setEnv] using hF.obj_eq o ho hn }

/-- **A binding of an existing record** changes: its name joins the footprint. -/
theorem frame_setEnv_bind (hF : Frame fp s u) {e : EnvId} (he : e < s.envs.size) {bm : HashMap JSStr Binding}
    {o : Option EnvId} (hd : Scope.declLike? (u.envEntry e) = some (bm, o)) (x : JSStr) (f : Binding → Binding) :
    Frame ⟨(e, x) :: fp.binds, fp.props⟩ s (u.setEnv e ((u.envEntry e).withBindings (·.modify x f))) := by
  have heu : e < u.envs.size := Nat.lt_of_lt_of_le he hF.envs_le
  refine {
    envs_le := by simpa using hF.envs_le
    heap_le := by simpa [State.setEnv] using hF.heap_le
    env_agree := fun i hi => ?_
    obj_agree := fun o' ho => by simpa [State.objEntry, State.setEnv] using hF.obj_agree o' ho
    env_eq := fun i hi hn => ?_
    obj_eq := fun o' ho hn => by simpa [State.objEntry, State.setEnv] using hF.obj_eq o' ho hn }
  · by_cases hei : e = i
    · subst hei
      rw [State.setEnv_envEntry_self _ _ _ heu]
      have hag := hF.env_agree e hi
      unfold EnvAgree at hag ⊢
      cases hs : Scope.declLike? (s.envEntry e) with
      | none =>
        rw [hs] at hag
        rw [hag] at hd; rw [hd] at hs; simp at hs
      | some p =>
        obtain ⟨bs, os⟩ := p
        rw [hs] at hag
        obtain ⟨bw, hw, hx⟩ := hag
        rw [hw] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        refine ⟨bw.modify x f, declLike_withBindings hw _, fun y hy => ?_⟩
        have hyx : (x == y) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun h => hy (by simp [h])
        rw [Std.HashMap.getElem?_modify, hyx]
        exact hx y (fun h => hy (List.mem_cons_of_mem _ h))
    · rw [setEnv_envEntry_ne _ _ _ _ hei]
      exact envAgree_mono (hF.env_agree i hi) fun y hy => List.mem_cons_of_mem _ hy
  · by_cases hei : e = i
    · subst hei; exact absurd List.mem_cons_self (hn x)
    · rw [setEnv_envEntry_ne _ _ _ _ hei]
      exact hF.env_eq i hi (fun y hy => hn y (List.mem_cons_of_mem _ hy))

/-- An object that did not exist at the start may change freely. -/
theorem frame_setProp_new (hF : Frame fp s u) {o : ObjId} (ho : s.heap.size ≤ o) (k : PropKey) (p : Property) :
    Frame fp s (u.setProp o k p) := by
  have hne : ∀ i, i < s.heap.size → o ≠ i := fun i hi h => by subst h; omega
  exact {
    envs_le := by simpa using hF.envs_le
    heap_le := by simpa using hF.heap_le
    env_agree := fun i hi => by simpa using hF.env_agree i hi
    obj_agree := fun i hi => by rw [State.setProp_entry_ne _ _ _ _ _ (hne i hi)]; exact hF.obj_agree i hi
    env_eq := fun i hi hn => by simpa using hF.env_eq i hi hn
    obj_eq := fun i hi hn => by rw [State.setProp_entry_ne _ _ _ _ _ (hne i hi)]; exact hF.obj_eq i hi hn }

/-- **A property of an existing object** changes: the key joins the footprint. -/
theorem frame_setProp_prop (hF : Frame fp s u) {o : ObjId} (ho : o < s.heap.size) (k : PropKey) (p : Property) :
    Frame ⟨fp.binds, (o, k) :: fp.props⟩ s (u.setProp o k p) := by
  have hou : o < u.heap.size := Nat.lt_of_lt_of_le ho hF.heap_le
  refine {
    envs_le := by simpa using hF.envs_le
    heap_le := by simpa using hF.heap_le
    env_agree := fun i hi => by simpa using hF.env_agree i hi
    obj_agree := fun i hi => ?_
    env_eq := fun i hi hn => by simpa using hF.env_eq i hi hn
    obj_eq := fun i hi hn => ?_ }
  · by_cases hoi : o = i
    · subst hoi
      rw [State.setProp_entry_self _ _ _ _ hou]
      obtain ⟨a1, a2, a3, a4⟩ := hF.obj_agree o hi
      refine ⟨by simpa using a1, by simpa [Obj.withProps] using a2, by simpa using a3, fun k' hk' => ?_⟩
      have hkk : k ≠ k' := fun h => hk' (by simp [h])
      rw [Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ hkk]
      exact a4 k' (fun h => hk' (List.mem_cons_of_mem _ h))
    · rw [State.setProp_entry_ne _ _ _ _ _ hoi]
      obtain ⟨a1, a2, a3, a4⟩ := hF.obj_agree i hi
      exact ⟨a1, a2, a3, fun k' hk' => a4 k' (fun h => hk' (List.mem_cons_of_mem _ h))⟩
  · by_cases hoi : o = i
    · subst hoi; exact absurd List.mem_cons_self (hn k)
    · rw [State.setProp_entry_ne _ _ _ _ _ hoi]
      exact hF.obj_eq i hi (fun k' hk' => hn k' (List.mem_cons_of_mem _ hk'))

theorem frame_allocObj (hF : Frame fp s u) (ob : Obj) : Frame fp s (u.allocObj ob) where
  envs_le := by simpa using hF.envs_le
  heap_le := by simp; have := hF.heap_le; omega
  env_agree i hi := by simpa using hF.env_agree i hi
  obj_agree i hi := by rw [State.allocObj_entry_lt _ _ _ (Nat.lt_of_lt_of_le hi hF.heap_le)]; exact hF.obj_agree i hi
  env_eq i hi hn := by simpa using hF.env_eq i hi hn
  obj_eq i hi hn := by rw [State.allocObj_entry_lt _ _ _ (Nat.lt_of_lt_of_le hi hF.heap_le)]; exact hF.obj_eq i hi hn

/-- A function's call: its record pushed and filled (`bodyState`). -/
theorem frame_bodyState (hF : Frame fp s u) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) :
    Frame fp s (bodyState u fo d t args) where
  envs_le := by simp; have := hF.envs_le; omega
  heap_le := by simpa using hF.heap_le
  env_agree i hi := by
    rw [bodyState_envEntry_lt _ _ _ _ _ _ (Nat.lt_of_lt_of_le hi hF.envs_le)]; exact hF.env_agree i hi
  obj_agree i hi := by simpa using hF.obj_agree i hi
  env_eq i hi hn := by
    rw [bodyState_envEntry_lt _ _ _ _ _ _ (Nat.lt_of_lt_of_le hi hF.envs_le)]; exact hF.env_eq i hi hn
  obj_eq i hi hn := by simpa using hF.obj_eq i hi hn

/-- The caller's realm and script back. -/
theorem frame_restore (hF : Frame fp s u) (c : State) : Frame fp s (u.restore c) :=
  ⟨hF.envs_le, hF.heap_le, hF.env_agree, hF.obj_agree, hF.env_eq, hF.obj_eq⟩

end

/-! ## Reading through a frame -/

/-- The chain from `e` in `s` (declarative and function records, existing at the start) reaches `x`'s binding, or its
end, without a record whose `x` is in the footprint. -/
def avoids (s : State) (fp : Footprint) : Nat → EnvId → JSStr → Bool
  | 0, _, _ => false
  | k + 1, e, x =>
    decide (e < s.envs.size) &&
    match Scope.declLike? (s.envEntry e) with
    | some (bm, o) => !(fp.binds.contains (e, x)) &&
      match bm[x]? with
      | some _ => true
      | none => match o with
        | some o => avoids s fp k o x
        | none => true
    | none => false

theorem lookup_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) (x : JSStr) :
    ∀ (k : Nat) (e : EnvId), avoids s fp k e x = true → Scope.lookup w k e x = Scope.lookup s k e x := by
  intro k
  induction k with
  | zero => intro e h; simp [avoids] at h
  | succ k ih =>
    intro e h
    simp only [avoids, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨he, hm⟩ := h
    have hag := hF.env_agree e he
    have hew : e < w.envs.size := Nat.lt_of_lt_of_le he hF.envs_le
    rw [Scope.lookup_succ, Scope.lookup_succ]
    simp only [he, hew, ↓reduceIte]
    unfold EnvAgree at hag
    cases hs : Scope.declLike? (s.envEntry e) with
    | none => rw [hs] at hm; simp at hm
    | some p =>
      obtain ⟨bs, o⟩ := p
      rw [hs] at hm hag
      obtain ⟨bw, hw, hx⟩ := hag
      rw [hw]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hnot, hrest⟩ := hm
      have hnm : ¬ (e, x) ∈ fp.binds := by simpa using hnot
      simp only
      rw [hx x hnm]
      cases hb : bs[x]? with
      | some bd => rfl
      | none =>
        rw [hb] at hrest
        cases o with
        | none => rfl
        | some o => exact ih o hrest

theorem resolve_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) (x : JSStr) :
    ∀ (k : Nat) (e : EnvId), avoids s fp k e x = true → Scope.resolve w k e x = Scope.resolve s k e x := by
  intro k
  induction k with
  | zero => intro e h; simp [avoids] at h
  | succ k ih =>
    intro e h
    simp only [avoids, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨he, hm⟩ := h
    have hag := hF.env_agree e he
    have hew : e < w.envs.size := Nat.lt_of_lt_of_le he hF.envs_le
    simp only [Scope.resolve, he, hew, ↓reduceIte]
    unfold EnvAgree at hag
    cases hs : Scope.declLike? (s.envEntry e) with
    | none => rw [hs] at hm; simp at hm
    | some p =>
      obtain ⟨bs, o⟩ := p
      rw [hs] at hm hag
      obtain ⟨bw, hw, hx⟩ := hag
      rw [hw]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hnot, hrest⟩ := hm
      have hnm : ¬ (e, x) ∈ fp.binds := by simpa using hnot
      have hc : bw.contains x = bs.contains x := by
        simp only [Std.HashMap.contains_eq_isSome_getElem?, hx x hnm]
      simp only [hc]
      cases hb : bs[x]? with
      | some bd =>
        have hct : bs.contains x = true := by simp [Std.HashMap.contains_eq_isSome_getElem?, hb]
        simp only [hct, ↓reduceIte]
      | none =>
        rw [hb] at hrest
        cases o with
        | none => rfl
        | some o =>
          have hcf : bs.contains x = false := by simp [Std.HashMap.contains_eq_isSome_getElem?, hb]
          simp only [hcf, Bool.false_eq_true, ↓reduceIte]
          exact ih o hrest

/-- An existing object's property outside the footprint reads as before the call. -/
theorem props_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {o : ObjId} (ho : o < s.heap.size)
    {k : PropKey} (hk : fp.props.contains (o, k) = false) :
    (w.objEntry o).props.get? k = (s.objEntry o).props.get? k :=
  (hF.obj_agree o ho).2.2.2 k (by simpa using hk)

theorem kind_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {o : ObjId} (ho : o < s.heap.size) :
    (w.objEntry o).kind = (s.objEntry o).kind := (hF.obj_agree o ho).1

theorem extensible_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {o : ObjId} (ho : o < s.heap.size) :
    (w.objEntry o).extensible = (s.objEntry o).extensible := (hF.obj_agree o ho).2.2.1

theorem heap_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {o : ObjId} (ho : o < s.heap.size) :
    o < w.heap.size := Nat.lt_of_lt_of_le ho hF.heap_le

/-- An existing record with no binding in the footprint is exactly as it was. -/
theorem envEntry_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {e : EnvId} (he : e < s.envs.size)
    (hn : fp.binds.all (fun p => p.1 != e) = true) : w.envEntry e = s.envEntry e :=
  hF.env_eq e he fun x hx => by
    have := List.all_eq_true.mp hn _ hx
    simp at this

/-- An existing object with no property in the footprint is exactly as it was. -/
theorem objEntry_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {o : ObjId} (ho : o < s.heap.size)
    (hn : fp.props.all (fun p => p.1 != o) = true) : w.objEntry o = s.objEntry o :=
  hF.obj_eq o ho fun k hk => by
    have := List.all_eq_true.mp hn _ hk
    simp at this

/-- The empty footprint's union with itself. -/
@[simp] theorem union_empty : (({} : Footprint).union {}) = {} := rfl

/-- A frame for an explicit final state, by its last steps: realm restored, record and property writes, a pushed
function record, allocations, down to the start. -/
syntax "frame_tac" : tactic
macro_rules
  | `(tactic| frame_tac) => `(tactic| (repeat' (first
      | exact frame_refl _ _
      | apply frame_restore
      | apply frame_bodyState
      | apply frame_allocObj
      | (apply frame_setEnv_new (he := by simp))
      | (apply frame_setProp_new (ho := by simp)))); done)

end Logic
