import JSProofs.Frame

/-!
# Facts about a state, as data (zippy docs/react-proofs.md, "Composition in Lean")

A spec's premises about the state it starts from, written as a list of `Fact`s instead of one binder each. Each fact
names the place it reads (`Loc`) by *atoms*: indices into a list of the objects (and records) the spec talks about,
`Atoms`. A footprint written over the same atoms (`SFoot`) is compared with those places by computation: whether a
fact lies outside a footprint is `decide`, and with the atoms distinct (`Atoms.Wf`) a fact outside a call's footprint
holds after the call as before (`Facts.frame`). The values facts state are any Lean terms; only places are compared.

Specs are stated for any atoms `a` and take their objects as indices into them, so a caller instantiates a callee's
facts and footprint over its own atoms: every comparison in a composition is between literal indices.

This replaces restating each callee premise at the caller's start state and moving it to the call state by a
generated tactic (`tools/react_commit/*.py`, `rebase_tac`): one lemma moves a whole list. It is also the invariant's
step from one click to the next: what a click leaves of its start state is `Facts.keep` of the facts there.
-/

open ES
open Std (HashMap)

namespace Logic

/-- The objects and records a spec's facts and footprints name, by index. -/
structure Atoms where
  objs : List ObjId := []
  envs : List EnvId := []

namespace Atoms

/-- Object atom `i`. -/
def obj (a : Atoms) (i : Nat) : ObjId := a.objs.getD i 0

/-- Record atom `i`. -/
def env (a : Atoms) (i : Nat) : EnvId := a.envs.getD i 0

/-- The atoms name different objects and different records. -/
structure Wf (a : Atoms) : Prop where
  objs : a.objs.Nodup
  envs : a.envs.Nodup

theorem getD_inj {l : List Nat} (hl : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i 0 = l.getD j 0) : i = j := by
  simp only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact (List.Nodup.getElem_inj hl).mp h

theorem obj_inj {a : Atoms} (hw : a.Wf) {i j : Nat} (hi : i < a.objs.length) (hj : j < a.objs.length)
    (h : a.obj i = a.obj j) : i = j := getD_inj hw.objs hi hj h

theorem env_inj {a : Atoms} (hw : a.Wf) {i j : Nat} (hi : i < a.envs.length) (hj : j < a.envs.length)
    (h : a.env i = a.env j) : i = j := getD_inj hw.envs hi hj h

end Atoms

/-- A footprint over atoms. -/
structure SFoot where
  binds : List (Nat × JSStr) := []
  props : List (Nat × PropKey) := []
  jobs : Bool := false

namespace SFoot

/-- The footprint it names. -/
def eval (a : Atoms) (f : SFoot) : Footprint :=
  ⟨f.binds.map (fun p => (a.env p.1, p.2)), f.props.map (fun p => (a.obj p.1, p.2)), f.jobs⟩

def union (f g : SFoot) : SFoot := ⟨f.binds ++ g.binds, f.props ++ g.props, f.jobs || g.jobs⟩

theorem eval_union (a : Atoms) (f g : SFoot) : (f.union g).eval a = (f.eval a).union (g.eval a) := by
  simp [eval, union, Footprint.union]

/-- Every atom it names is one of `a`'s. -/
def inRange (a : Atoms) (f : SFoot) : Bool :=
  f.binds.all (fun p => decide (p.1 < a.envs.length)) && f.props.all (fun p => decide (p.1 < a.objs.length))

/-- Every entry of `f` is one of `g`'s (and `f` queues jobs only if `g` may). -/
def sub (f g : SFoot) : Bool :=
  f.binds.all (fun p => g.binds.contains p) && f.props.all (fun p => g.props.contains p) && (!f.jobs || g.jobs)

/-- A frame through a footprint within another's is one through the other's. -/
theorem frame_sub {a : Atoms} {f g : SFoot} {s w : State} (hF : Frame (f.eval a) s w) (h : f.sub g = true) :
    Frame (g.eval a) s w := by
  simp only [sub, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hb, hp⟩, hj⟩ := h
  refine frame_mono hF ?_ ?_ ?_
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

/-- The place a fact reads. -/
inductive Loc where
  /-- Nothing in the state (a fact about the spec's values alone). -/
  | pure
  /-- An object's existence, kind and prototype: no footprint changes them. -/
  | obj (o : Nat)
  /-- An object's own property. -/
  | prop (o : Nat) (k : PropKey)
  /-- A binding in a declarative or function record. -/
  | bind (e : Nat) (x : JSStr)
  /-- A record's being declarative or a function's, and its outer record: no footprint changes them. -/
  | record (e : Nat)
  /-- All of a record: kept by a frame that changes none of its bindings. -/
  | recordAll (e : Nat)
  /-- Every state a frame through `f` reaches: kept by a frame within `f`. -/
  | closed (f : SFoot)

/-- The place lies outside the footprint (decided on atoms). -/
def Loc.apart (a : Atoms) (f : SFoot) : Loc → Bool
  | .pure | .obj _ | .record _ => true
  | .prop o k => f.inRange a && decide (o < a.objs.length) && !f.props.contains (o, k)
  | .bind e x => f.inRange a && decide (e < a.envs.length) && !f.binds.contains (e, x)
  | .recordAll e => f.inRange a && decide (e < a.envs.length) && f.binds.all (fun p => p.1 != e)
  | .closed g => f.sub g

theorem Loc.apart_prop {a : Atoms} {f : SFoot} {o : Nat} {k : PropKey} (hw : a.Wf)
    (h : (Loc.prop o k).apart a f = true) : (f.eval a).props.contains (a.obj o, k) = false := by
  simp only [Loc.apart, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hr, ho⟩, hn⟩ := h
  simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
  have hn' : (o, k) ∉ f.props := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
  apply Bool.eq_false_iff.mpr
  intro hc
  have hm := List.contains_iff_mem.mp hc
  simp only [SFoot.eval, List.mem_map] at hm
  obtain ⟨p, hp, he⟩ := hm
  apply hn'
  have h1 : a.obj p.1 = a.obj o := congrArg Prod.fst he
  have h2 : p.2 = k := congrArg Prod.snd he
  have := Atoms.obj_inj hw (hr.2 p hp) ho h1
  rw [← this, ← h2]
  exact hp

theorem Loc.apart_bind {a : Atoms} {f : SFoot} {e : Nat} {x : JSStr} (hw : a.Wf)
    (h : (Loc.bind e x).apart a f = true) : (a.env e, x) ∉ (f.eval a).binds := by
  simp only [Loc.apart, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hr, he⟩, hn⟩ := h
  simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
  have hn' : (e, x) ∉ f.binds := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
  simp only [SFoot.eval, List.mem_map, not_exists, not_and]
  intro p hp hq
  apply hn'
  have h1 : a.env p.1 = a.env e := congrArg Prod.fst hq
  have h2 : p.2 = x := congrArg Prod.snd hq
  have := Atoms.env_inj hw (hr.1 p hp) he h1
  rw [← this, ← h2]
  exact hp

/-- **A fact**: a statement about a state, the place it reads, and that a frame missing that place keeps it. -/
structure Fact (a : Atoms) where
  loc : Loc
  holds : State → Prop
  stable : ∀ (f : SFoot) {s w : State}, a.Wf → Frame (f.eval a) s w → loc.apart a f = true → holds s → holds w

namespace Fact

variable {a : Atoms}

/-- A fact about the spec's values alone. -/
def pure (P : Prop) : Fact a := ⟨.pure, fun _ => P, fun _ _ _ _ _ _ h => h⟩

/-- Object atom `o` exists and its kind satisfies `P` (`isPlain`, a function, …). -/
def kindP (o : Nat) (P : Kind → Prop) : Fact a :=
  ⟨.obj o, fun s => a.obj o < s.heap.size ∧ P (s.objEntry (a.obj o)).kind,
    fun _ _ _ _ hF _ ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [kind_frame hF hl]; exact hk⟩⟩

/-- Object atom `o` exists and has kind `K`. -/
def kind (o : Nat) (K : Kind) : Fact a := kindP o (· = K)

/-- Object atom `o` exists and its prototype is `p`. -/
def proto (o : Nat) (p : Value) : Fact a :=
  ⟨.obj o, fun s => a.obj o < s.heap.size ∧ (s.objEntry (a.obj o)).proto = p,
    fun _ _ _ _ hF _ ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [(hF.obj_agree _ hl).2.1]; exact hk⟩⟩

/-- Object atom `o` exists and its own property `k` reads `r` (`none`: it has none). -/
def prop (o : Nat) (k : PropKey) (r : Option Property) : Fact a :=
  ⟨.prop o k, fun s => a.obj o < s.heap.size ∧ (s.objEntry (a.obj o)).props.get? k = r,
    fun _ _ _ hw hF hap ⟨hl, hk⟩ => ⟨heap_frame hF hl, by rw [props_frame hF hl (Loc.apart_prop hw hap)]; exact hk⟩⟩

/-- Record atom `e` is a declarative or function record (outer `oG`) whose binding `x` satisfies `P`. -/
def bind (e : Nat) (oG : Option EnvId) (x : JSStr) (P : Option Binding → Prop) : Fact a :=
  ⟨.bind e x, fun s => a.env e < s.envs.size ∧ ∃ bs, Scope.declLike? (s.envEntry (a.env e)) = some (bs, oG) ∧ P bs[x]?,
    fun _ _ _ hw hF hap ⟨hl, bs, hd, hp⟩ => by
      obtain ⟨bw, hdw, hag⟩ := declLike_frame hF hl hd
      exact ⟨envs_frame hF hl, bw, hdw, by rw [hag x (Loc.apart_bind hw hap)]; exact hp⟩⟩

/-- Record atom `e` is a declarative or function record with outer record `oG`. -/
def record (e : Nat) (oG : Option EnvId) : Fact a :=
  ⟨.record e, fun s => a.env e < s.envs.size ∧ ∃ bs, Scope.declLike? (s.envEntry (a.env e)) = some (bs, oG),
    fun _ _ _ _ hF _ ⟨hl, bs, hd⟩ => by
      obtain ⟨bw, hdw, -⟩ := declLike_frame hF hl hd
      exact ⟨envs_frame hF hl, bw, hdw⟩⟩

theorem Loc.apart_recordAll {f : SFoot} {e : Nat} (hw : a.Wf) (h : (Loc.recordAll e).apart a f = true) :
    (f.eval a).binds.all (fun p => p.1 != a.env e) = true := by
  simp only [Loc.apart, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hr, he⟩, hn⟩ := h
  simp only [SFoot.inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
  simp only [SFoot.eval, List.all_eq_true, List.mem_map, bne_iff_ne, ne_eq]
  rintro _ ⟨p, hp, rfl⟩ hq
  exact hn p hp (Atoms.env_inj hw (hr.1 p hp) he hq)

/-- Record atom `e` is a declarative or function record whose bindings are exactly `bs` (outer `oG`). -/
def recordIs (e : Nat) (bs : HashMap JSStr Binding) (oG : Option EnvId) : Fact a :=
  ⟨.recordAll e, fun s => a.env e < s.envs.size ∧ Scope.declLike? (s.envEntry (a.env e)) = some (bs, oG),
    fun _ _ _ hw hF hap ⟨hl, hd⟩ => ⟨envs_frame hF hl, by rw [envEntry_frame hF hl (Loc.apart_recordAll hw hap)]; exact hd⟩⟩

/-- `P` holds at every state a frame through `f` reaches from here (a read of the DOM, a string's method, …). -/
def closed (f : SFoot) (P : State → Prop) : Fact a :=
  ⟨.closed f, fun s => ∀ w, Frame (f.eval a) s w → P w,
    fun g _ _ _ hF hap h w hw => h w (SFoot.frame_sub (by
      have := frame_trans hF hw
      rw [← SFoot.eval_union] at this
      exact this) (by
        simp only [Loc.apart] at hap
        simp only [SFoot.sub, SFoot.union, Bool.and_eq_true, List.all_eq_true, List.mem_append, Bool.or_eq_true,
          Bool.not_eq_true', Bool.or_eq_false_iff] at hap ⊢
        obtain ⟨⟨hb, hp⟩, hj⟩ := hap
        refine ⟨⟨fun q hq => hq.elim (hb q) (fun h => List.contains_iff_mem.mpr h),
          fun q hq => hq.elim (hp q) (fun h => List.contains_iff_mem.mpr h)⟩, ?_⟩
        cases hj with
        | inl h => cases hf : f.jobs <;> simp_all
        | inr h => exact .inr h))⟩

/-- A closed fact through a wider footprint gives it through a narrower one. -/
theorem closed_mono {f g : SFoot} {P : State → Prop} {s : State} (h : (closed (a := a) g P).holds s)
    (hs : f.sub g = true) : (closed (a := a) f P).holds s := fun w hw => h w (SFoot.frame_sub hw hs)

/-- A binding fact read in the record's bindings `bs`. -/
theorem bind_get {e : Nat} {oG : Option EnvId} {x : JSStr} {P : Option Binding → Prop} {s : State}
    {bs : HashMap JSStr Binding} (hd : Scope.declLike? (s.envEntry (a.env e)) = some (bs, oG))
    (h : (bind (a := a) e oG x P).holds s) : P bs[x]? := by
  obtain ⟨-, bs', hd', hp⟩ := h
  rw [hd] at hd'
  cases hd'
  exact hp

end Fact

/-- Every fact of the list holds. -/
def Facts.holds {a : Atoms} (l : List (Fact a)) (s : State) : Prop := ∀ x ∈ l, x.holds s

/-- Every fact of the list lies outside the footprint (decided on atoms). -/
def Facts.apart {a : Atoms} (f : SFoot) (l : List (Fact a)) : Bool := l.all (fun x => x.loc.apart a f)

/-- The facts of the list outside the footprint. -/
def Facts.keep {a : Atoms} (f : SFoot) (l : List (Fact a)) : List (Fact a) := l.filter (fun x => x.loc.apart a f)

/-- **Facts through a frame**: those outside its footprint hold after it as before. -/
theorem Facts.frame {a : Atoms} {f : SFoot} {s w : State} (hw : a.Wf) (hF : Frame (f.eval a) s w)
    {l : List (Fact a)} (hap : Facts.apart f l = true) (h : Facts.holds l s) : Facts.holds l w :=
  fun x hx => x.stable f hw hF (List.all_eq_true.mp hap x hx) (h x hx)

/-- **What a frame leaves**: the facts outside its footprint. -/
theorem Facts.keep_frame {a : Atoms} {f : SFoot} {s w : State} (hw : a.Wf) (hF : Frame (f.eval a) s w)
    {l : List (Fact a)} (h : Facts.holds l s) : Facts.holds (Facts.keep f l) w := by
  intro x hx
  simp only [Facts.keep, List.mem_filter] at hx
  exact x.stable f hw hF hx.2 (h x hx.1)

theorem Facts.holds_append {a : Atoms} {l m : List (Fact a)} {s : State} :
    Facts.holds (l ++ m) s ↔ Facts.holds l s ∧ Facts.holds m s := by
  simp only [Facts.holds, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x)⟩

theorem Facts.holds_sub {a : Atoms} {l m : List (Fact a)} {s : State} (hs : ∀ x ∈ l, x ∈ m)
    (h : Facts.holds m s) : Facts.holds l s := fun x hx => h x (hs x hx)

/-- A member's statement, from the list's. -/
theorem Facts.get {a : Atoms} {l : List (Fact a)} {s : State} (h : Facts.holds l s) (i : Nat) (hi : i < l.length) :
    (l[i]).holds s := h _ (List.getElem_mem hi)

end Logic
