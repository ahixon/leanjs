import JSProofs.Frame

/-!
# Facts about a state, as data (zippy docs/react-proofs.md, "Composition in Lean")

A spec's premises about the state it starts from, written as a list of `Fact`s instead of one binder each. Each fact
states the place it reads (`Loc`: an object's property, a binding, a record, …) and that a frame whose footprint
misses that place keeps it (`Loc.Apart`). `Facts.frame` moves a whole list through a call's frame; that is how a
caller gives a callee its premises at the call state, and what a click leaves of its start state for the next.

Whether places lie outside a footprint is decided by reflection (`Facts.apart_refl`): the objects and records both
name are listed as atoms (`Atoms`, distinct: `Atoms.Wf`), places and footprint are written over their indices
(`RLoc`, `SFoot`), and the check is a computation on indices. The tactic in `FactsForm.lean` builds the reflection.
-/

open ES
open Std (HashMap)

namespace Logic

/-! ## Footprints within footprints -/

/-- Every entry of `f` is one of `g`'s, and `f` queues jobs only if `g` may. -/
def Footprint.Sub (f g : Footprint) : Prop :=
  (∀ p, p ∈ f.binds → p ∈ g.binds) ∧ (∀ p, p ∈ f.props → p ∈ g.props) ∧ (g.jobs = false → f.jobs = false)

theorem Footprint.sub_union {f g : Footprint} (h : f.Sub g) : (f.union g).Sub g := by
  obtain ⟨hb, hp, hj⟩ := h
  refine ⟨fun p hq => ?_, fun p hq => ?_, fun hg => ?_⟩
  · simp only [Footprint.union, List.mem_append] at hq; exact hq.elim (hb p) id
  · simp only [Footprint.union, List.mem_append] at hq; exact hq.elim (hp p) id
  · simp [Footprint.union, hg, hj hg]

/-! ## Facts -/

/-- The place a fact reads. -/
inductive Loc where
  /-- Nothing in the state. -/
  | pure
  /-- An object's existence, kind and prototype: no frame changes them. -/
  | obj (o : ObjId)
  /-- An object's own property. -/
  | prop (o : ObjId) (k : PropKey)
  /-- A binding in a declarative or function record. -/
  | bind (e : EnvId) (x : JSStr)
  /-- A record's being declarative or a function's, and its outer record: no frame changes them. -/
  | record (e : EnvId)
  /-- All of a record. -/
  | recordAll (e : EnvId)
  /-- All of an object's own properties (its keys, …). -/
  | objAll (o : ObjId)
  /-- Every state a frame through `f` reaches. -/
  | closed (f : Footprint)

/-- The place lies outside the footprint: a frame through it keeps what the place holds. -/
def Loc.Apart (fp : Footprint) : Loc → Prop
  | .pure | .obj _ | .record _ => True
  | .prop o k => fp.props.contains (o, k) = false
  | .bind e x => (e, x) ∉ fp.binds
  | .recordAll e => fp.binds.all (fun p => p.1 != e) = true
  | .objAll o => fp.props.all (fun p => p.1 != o) = true
  | .closed g => fp.Sub g

/-- **A fact**: a statement about a state, the place it reads, and that a frame missing that place keeps it. -/
structure Fact where
  loc : Loc
  holds : State → Prop
  stable : ∀ (fp : Footprint) {s w : State}, Frame fp s w → loc.Apart fp → holds s → holds w

namespace Fact

/-- A fact about values alone. -/
def pure (P : Prop) : Fact := ⟨.pure, fun _ => P, fun _ _ _ _ _ h => h⟩

/-- Object `o` exists and its kind satisfies `P` (`isPlain`, a function, …). -/
def kindP (o : ObjId) (P : Kind → Prop) : Fact :=
  ⟨.obj o, fun s => o < s.heap.size ∧ P (s.objEntry o).kind,
    fun _ _ _ hF _ ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [kind_frame hF hl]; exact hk⟩⟩

/-- Object `o` exists and its prototype is `p`. -/
def proto (o : ObjId) (p : Value) : Fact :=
  ⟨.obj o, fun s => o < s.heap.size ∧ (s.objEntry o).proto = p,
    fun _ _ _ hF _ ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [(hF.obj_agree _ hl).2.1]; exact hk⟩⟩

/-- Object `o` exists and its own property `k` reads `r` (`none`: it has none). -/
def prop (o : ObjId) (k : PropKey) (r : Option Property) : Fact :=
  ⟨.prop o k, fun s => o < s.heap.size ∧ (s.objEntry o).props.get? k = r,
    fun _ _ _ hF hap ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [props_frame hF hl hap]; exact hk⟩⟩

/-- Object `o` exists and its own property `k` satisfies `P` (`∃ e c, r = some (.data v true e c)`, …). -/
def propP (o : ObjId) (k : PropKey) (P : Option Property → Prop) : Fact :=
  ⟨.prop o k, fun s => o < s.heap.size ∧ P ((s.objEntry o).props.get? k),
    fun _ _ _ hF hap ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [props_frame hF hl hap]; exact hk⟩⟩

/-- Object `o` exists and its entry satisfies `P` (its keys, …: what reads all its own properties). -/
def objP (o : ObjId) (P : Obj → Prop) : Fact :=
  ⟨.objAll o, fun s => o < s.heap.size ∧ P (s.objEntry o),
    fun _ _ _ hF hap ⟨hl, hk⟩ => ⟨heap_frame hF hl, by
      have hn : ∀ k, (o, k) ∉ _ := fun k hm => by
        have := List.all_eq_true.mp hap _ hm
        simp at this
      rw [hF.obj_eq o hl hn]; exact hk⟩⟩

/-- Record `e` is a declarative or function record (outer `oG`) whose binding `x` satisfies `P`. -/
def bind (e : EnvId) (oG : Option EnvId) (x : JSStr) (P : Option Binding → Prop) : Fact :=
  ⟨.bind e x, fun s => e < s.envs.size ∧ ∃ bs, Scope.declLike? (s.envEntry e) = some (bs, oG) ∧ P bs[x]?,
    fun _ _ _ hF hap ⟨hl, bs, hd, hp⟩ => by
      obtain ⟨bw, hdw, hag⟩ := declLike_frame hF hl hd
      exact ⟨envs_frame hF hl, bw, hdw, by rw [hag x hap]; exact hp⟩⟩

/-- Record `e` is a declarative or function record with outer record `oG`. -/
def record (e : EnvId) (oG : Option EnvId) : Fact :=
  ⟨.record e, fun s => e < s.envs.size ∧ ∃ bs, Scope.declLike? (s.envEntry e) = some (bs, oG),
    fun _ _ _ hF _ ⟨hl, bs, hd⟩ => by
      obtain ⟨bw, hdw, -⟩ := declLike_frame hF hl hd
      exact ⟨envs_frame hF hl, bw, hdw⟩⟩

/-- Record `e` is a declarative or function record whose bindings are exactly `bs` (outer `oG`). -/
def recordIs (e : EnvId) (bs : HashMap JSStr Binding) (oG : Option EnvId) : Fact :=
  ⟨.recordAll e, fun s => e < s.envs.size ∧ Scope.declLike? (s.envEntry e) = some (bs, oG),
    fun _ _ _ hF hap ⟨hl, hd⟩ => ⟨envs_frame hF hl, by rw [envEntry_frame hF hl hap]; exact hd⟩⟩

/-- `P` holds at every state a frame through `f` reaches from here (a read of the DOM, a string's method, …). -/
def closed (f : Footprint) (P : State → Prop) : Fact :=
  ⟨.closed f, fun s => ∀ w, Frame f s w → P w,
    fun _ _ _ hF hap h w hw => h w (frame_mono (frame_trans hF hw) (Footprint.sub_union hap).1
      (Footprint.sub_union hap).2.1 (Footprint.sub_union hap).2.2)⟩

/-- A closed fact through a wider footprint gives it through a narrower one. -/
theorem closed_mono {f g : Footprint} {P : State → Prop} {s : State} (h : (closed g P).holds s) (hs : f.Sub g) :
    (closed f P).holds s := fun w hw => h w (frame_mono hw hs.1 hs.2.1 hs.2.2)

/-- A binding fact read in the record's bindings `bs`. -/
theorem bind_get {e : EnvId} {oG : Option EnvId} {x : JSStr} {P : Option Binding → Prop} {s : State}
    {bs : HashMap JSStr Binding} (hd : Scope.declLike? (s.envEntry e) = some (bs, oG))
    (h : (bind e oG x P).holds s) : P bs[x]? := by
  obtain ⟨-, bs', hd', hp⟩ := h
  rw [hd] at hd'
  cases hd'
  exact hp

end Fact

/-- Every fact of the list holds. -/
def Facts.holds (l : List Fact) (s : State) : Prop := ∀ x ∈ l, x.holds s

theorem Facts.holds_nil {s : State} : Facts.holds [] s := fun _ h => nomatch h

theorem Facts.holds_cons {f : Fact} {l : List Fact} {s : State} (hf : f.holds s) (hl : Facts.holds l s) :
    Facts.holds (f :: l) s := by
  intro x hx
  cases List.mem_cons.mp hx with
  | inl h => exact h ▸ hf
  | inr h => exact hl x h

/-- An object with a property exists (a missing object's entry has none). -/
theorem lt_of_props_ne_none {s : State} {o : ObjId} {k : PropKey} (h : (s.objEntry o).props.get? k ≠ none) :
    o < s.heap.size := by
  apply Classical.byContradiction
  intro hn
  apply h
  have : s.heap[o]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hn)
  simp only [State.objEntry, this, Option.getD_none]
  first
  | (simp [PropMap.get?]; done)
  | (show ((default : PropMap).map.get? k).map (·.2) = none; rw [show (default : PropMap).map = ∅ from rfl]; simp)

/-- A record with a binding exists (a missing record's entry has none). -/
theorem lt_of_bind_ne_none {s : State} {e : EnvId} {bs : HashMap JSStr Binding} {oG : Option EnvId} {x : JSStr}
    (hd : Scope.declLike? (s.envEntry e) = some (bs, oG)) (h : bs[x]? ≠ none) : e < s.envs.size := by
  apply Classical.byContradiction
  intro hn
  apply h
  have : s.envs[e]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hn)
  simp only [State.envEntry, this, Option.getD_none] at hd
  have hdef : (default : Env) = .decl ∅ none := rfl
  rw [hdef] at hd
  simp only [Scope.declLike?, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, -⟩ := hd
  simp

theorem lt_of_props_P {s : State} {o : ObjId} {k : PropKey} {P : Option Property → Prop}
    (hp : P ((s.objEntry o).props.get? k)) (hn : ¬ P none) : o < s.heap.size :=
  lt_of_props_ne_none fun h => hn (h ▸ hp)

theorem lt_of_bind_P {s : State} {e : EnvId} {bs : HashMap JSStr Binding} {oG : Option EnvId} {x : JSStr}
    {P : Option Binding → Prop} (hd : Scope.declLike? (s.envEntry e) = some (bs, oG)) (hp : P bs[x]?) (hn : ¬ P none) :
    e < s.envs.size :=
  lt_of_bind_ne_none hd fun h => hn (h ▸ hp)

/-- Every fact of the list lies outside the footprint. -/
def Facts.Apart (fp : Footprint) (l : List Fact) : Prop := ∀ x ∈ l, x.loc.Apart fp

/-- **Facts through a frame**: those outside its footprint hold after it as before. -/
theorem Facts.frame {fp : Footprint} {s w : State} (hF : Frame fp s w) {l : List Fact} (hap : Facts.Apart fp l)
    (h : Facts.holds l s) : Facts.holds l w :=
  fun x hx => x.stable fp hF (hap x hx) (h x hx)

theorem Facts.holds_append {l m : List Fact} {s : State} :
    Facts.holds (l ++ m) s ↔ Facts.holds l s ∧ Facts.holds m s := by
  simp only [Facts.holds, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x)⟩

theorem Facts.holds_sub {l m : List Fact} {s : State} (hs : ∀ x ∈ l, x ∈ m) (h : Facts.holds m s) :
    Facts.holds l s := fun x hx => h x (hs x hx)

/-- A member's statement, from the list's. -/
theorem Facts.get {l : List Fact} {s : State} (h : Facts.holds l s) (i : Nat) (hi : i < l.length) :
    (l[i]).holds s := h _ (List.getElem_mem hi)

/-! ## Deciding `Apart` by reflection -/

/-- The objects and records named, by index. -/
structure Atoms where
  objs : List ObjId := []
  envs : List EnvId := []

namespace Atoms

def obj (a : Atoms) (i : Nat) : ObjId := a.objs.getD i 0
def env (a : Atoms) (i : Nat) : EnvId := a.envs.getD i 0

/-- The atoms name different objects and different records. -/
structure Wf (a : Atoms) : Prop where
  objs : a.objs.Nodup
  envs : a.envs.Nodup

theorem getD_inj {l : List Nat} (hl : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i 0 = l.getD j 0) : i = j := by
  simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact (List.Nodup.getElem_inj hl).mp h

end Atoms

/-- A footprint over atoms. -/
structure SFoot where
  binds : List (Nat × JSStr) := []
  props : List (Nat × PropKey) := []
  jobs : Bool := false

namespace SFoot

def eval (a : Atoms) (f : SFoot) : Footprint :=
  ⟨f.binds.map (fun p => (a.env p.1, p.2)), f.props.map (fun p => (a.obj p.1, p.2)), f.jobs⟩

def union (f g : SFoot) : SFoot := ⟨f.binds ++ g.binds, f.props ++ g.props, f.jobs || g.jobs⟩

/-- Every atom it names is one of `a`'s. -/
def inRange (a : Atoms) (f : SFoot) : Bool :=
  f.binds.all (fun p => decide (p.1 < a.envs.length)) && f.props.all (fun p => decide (p.1 < a.objs.length))

/-- Every entry of `f` is one of `g`'s (and `f` queues jobs only if `g` may). -/
def sub (f g : SFoot) : Bool :=
  f.binds.all (fun p => g.binds.contains p) && f.props.all (fun p => g.props.contains p) && (!f.jobs || g.jobs)

theorem sub_sound {a : Atoms} {f g : SFoot} (h : f.sub g = true) : (f.eval a).Sub (g.eval a) := by
  simp only [sub, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hb, hp⟩, hj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp only [eval, List.mem_map] at hq ⊢
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨r, List.contains_iff_mem.mp (hb r hr), rfl⟩
  · intro q hq
    simp only [eval, List.mem_map] at hq ⊢
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨r, List.contains_iff_mem.mp (hp r hr), rfl⟩
  · intro hg
    simp only [eval] at hg ⊢
    cases hj with
    | inl h => exact h
    | inr h => rw [hg] at h; cases h

end SFoot

/-- A place over atoms. -/
inductive RLoc where
  | pure
  /-- (kept by every frame: the object itself, not an atom) -/
  | obj (o : ObjId)
  | prop (o : Nat) (k : PropKey)
  | bind (e : Nat) (x : JSStr)
  /-- (kept by every frame: the record itself, not an atom) -/
  | record (e : EnvId)
  | recordAll (e : Nat)
  | objAll (o : Nat)
  | closed (f : SFoot)

def RLoc.eval (a : Atoms) : RLoc → Loc
  | .pure => .pure
  | .obj o => .obj o
  | .prop o k => .prop (a.obj o) k
  | .bind e x => .bind (a.env e) x
  | .record e => .record e
  | .recordAll e => .recordAll (a.env e)
  | .objAll o => .objAll (a.obj o)
  | .closed f => .closed (f.eval a)

/-- The place lies outside the footprint, decided on indices. -/
def RLoc.apart (a : Atoms) (f : SFoot) : RLoc → Bool
  | .pure | .obj _ | .record _ => true
  | .prop o k => f.inRange a && decide (o < a.objs.length) && !f.props.contains (o, k)
  | .bind e x => f.inRange a && decide (e < a.envs.length) && !f.binds.contains (e, x)
  | .recordAll e => f.inRange a && decide (e < a.envs.length) && f.binds.all (fun p => p.1 != e)
  | .objAll o => f.inRange a && decide (o < a.objs.length) && f.props.all (fun p => p.1 != o)
  | .closed g => f.sub g

theorem RLoc.apart_sound {a : Atoms} (hw : a.Wf) {f : SFoot} (r : RLoc) (h : r.apart a f = true) :
    (r.eval a).Apart (f.eval a) := by
  cases r with
  | pure | obj _ | record _ => trivial
  | prop o k =>
    simp only [RLoc.apart, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hr, ho⟩, hn⟩ := h
    simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    have hn' : (o, k) ∉ f.props := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
    show (f.eval a).props.contains (a.obj o, k) = false
    apply Bool.eq_false_iff.mpr
    intro hc
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    apply hn'
    have := Atoms.getD_inj hw.objs (hr.2 p hp) ho (congrArg Prod.fst he)
    have h2 : p.2 = k := by simpa using congrArg Prod.snd he
    rw [← this, ← h2]
    exact hp
  | bind e x =>
    simp only [RLoc.apart, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hr, he⟩, hn⟩ := h
    simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    have hn' : (e, x) ∉ f.binds := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
    show (a.env e, x) ∉ (f.eval a).binds
    intro hm
    obtain ⟨p, hp, hq⟩ := List.mem_map.mp hm
    apply hn'
    have := Atoms.getD_inj hw.envs (hr.1 p hp) he (congrArg Prod.fst hq)
    have h2 : p.2 = x := by simpa using congrArg Prod.snd hq
    rw [← this, ← h2]
    exact hp
  | recordAll e =>
    simp only [RLoc.apart, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hr, he⟩, hn⟩ := h
    simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    show (f.eval a).binds.all (fun p => p.1 != a.env e) = true
    simp only [SFoot.eval, List.all_eq_true, List.mem_map, bne_iff_ne, ne_eq]
    rintro _ ⟨p, hp, rfl⟩ hq
    exact hn p hp (Atoms.getD_inj hw.envs (hr.1 p hp) he hq)
  | objAll o =>
    simp only [RLoc.apart, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hr, ho⟩, hn⟩ := h
    simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
    show (f.eval a).props.all (fun p => p.1 != a.obj o) = true
    simp only [SFoot.eval, List.all_eq_true, List.mem_map, bne_iff_ne, ne_eq]
    rintro _ ⟨p, hp, rfl⟩ hq
    exact hn p hp (Atoms.getD_inj hw.objs (hr.2 p hp) ho hq)
  | closed g => exact SFoot.sub_sound h

/-- **`Apart` by reflection**: the facts' places written over distinct atoms (`hl`, by `rfl`), the footprint too, and
the check on indices. -/
theorem Facts.apart_refl {a : Atoms} (hw : a.Wf) (f : SFoot) {l : List Fact} (rs : List RLoc)
    (hl : l.map Fact.loc = rs.map (RLoc.eval a)) (h : rs.all (RLoc.apart a f) = true) : Facts.Apart (f.eval a) l := by
  intro x hx
  have : x.loc ∈ rs.map (RLoc.eval a) := hl ▸ List.mem_map_of_mem hx
  obtain ⟨r, hr, he⟩ := List.mem_map.mp this
  rw [← he]
  exact RLoc.apart_sound hw r (List.all_eq_true.mp h r hr)

end Logic
