import JSProofs.Frame

/-!
# Rebasing a spec's premises along a frame (zippy docs/react-proofs.md)

A spec's premises describe its entry state `s`; a caller's contract asks for its conclusion at any state `u` with
`Frame fp s u`. `rebase_tac hw` proves one premise at `u` from the premises at `s` (in context): heap bounds and
records grow, objects outside `fp.props` and records outside `fp.binds` are as they were, premises quantified over
anything else is a premise as it stands. Premises quantified over framed states are passed by hand
(`frame_empty_trans`).
-/

open ES Logic

namespace Logic

theorem lt_heap_of_frame {fp : Footprint} {s u : State} (hw : Frame fp s u) {o : ObjId} (h : o < s.heap.size) :
    o < u.heap.size := Nat.lt_of_lt_of_le h hw.heap_le

theorem lt_envs_of_frame {fp : Footprint} {s u : State} (hw : Frame fp s u) {e : EnvId} (h : e < s.envs.size) :
    e < u.envs.size := Nat.lt_of_lt_of_le h hw.envs_le

/-- Through a footprint without objects every existing object is as it was. -/
theorem obj_eq_np {fp : Footprint} {s u : State} (hw : Frame fp s u) (hp : fp.props = []) {o : ObjId}
    (ho : o < s.heap.size) : u.objEntry o = s.objEntry o :=
  hw.obj_eq o ho (fun _ hh => by rw [hp] at hh; exact absurd hh (List.not_mem_nil))

theorem setEnv_envEntry_self (u : State) (e : EnvId) (a : Env) (h : e < u.envs.size) :
    (u.setEnv e a).envEntry e = a := by
  rw [setEnv_envEntry, if_pos ⟨rfl, h⟩]

theorem declLike_isSome_withBindings (ev : Env) (g : Std.HashMap JSStr Binding → Std.HashMap JSStr Binding) :
    (Scope.declLike? (ev.withBindings g)).isSome = (Scope.declLike? ev).isSome := by
  cases ev <;> rfl

/-- A frame, then nothing changed. -/
theorem frame_then_empty {fp : Footprint} {s u w : State} (h1 : Frame fp s u) (h2 : Frame {} u w) : Frame fp s w :=
  frame_mono (frame_trans h1 h2) (fun p hp => by simpa [Footprint.union] using hp)
    (fun p hp => by simpa [Footprint.union] using hp) (fun hj => by simpa [Footprint.union] using hj)

/-- A frame, then one within its bindings and touching no object. -/
theorem frame_then_sub {fp fq : Footprint} {s u w : State} (h1 : Frame fp s u) (h2 : Frame fq u w)
    (hb : ∀ p, p ∈ fq.binds → p ∈ fp.binds) (hp : fq.props = []) (hj : fq.jobs = false) : Frame fp s w :=
  frame_mono (frame_trans h1 h2)
    (fun p hp' => by
      simp only [Footprint.union, List.mem_append] at hp'
      rcases hp' with h | h
      · exact h
      · exact hb p h)
    (fun p hp' => by simp [Footprint.union, hp] at hp'; exact hp')
    (fun hj' => by simp [Footprint.union, hj, hj'])

end Logic

/-- One premise at the framed state `u` from the entry state's (see the module doc): the cheap cases. -/
macro "rebase_quick" hw:term : tactic => `(tactic| first
  | with_reducible assumption
  | exact lt_heap_of_frame $hw (by with_reducible assumption)
  | exact lt_envs_of_frame $hw (by with_reducible assumption)
  | (rw [objEntry_frame0 $hw (by with_reducible assumption)] <;> with_reducible assumption)
  | (rw [envEntry_frame0 $hw (by with_reducible assumption)] <;> with_reducible assumption)
  | (rw [obj_eq_np $hw rfl (by with_reducible assumption)] <;> with_reducible assumption))

/-- An object outside a footprint that mentions other objects (`simp_all` with the premises that they differ). -/
macro "rebase_objs" hw:term : tactic => `(tactic|
  (rw [($hw).obj_eq _ (by with_reducible assumption) (fun _ hh => by
    simp [Footprint.union] at hh
    first | exact absurd hh.1.symm (by assumption) | exact absurd hh.1 (by assumption) | simp_all)] <;>
      with_reducible assumption))

/-- One premise at the framed state `u` from the entry state's. -/
macro "rebase_tac" hw:term : tactic => `(tactic| first | rebase_quick $hw | rebase_objs $hw)

/-- As `rebase_tac`, and module bindings through `hbw` (`declLike_frame`'s: the bindings outside the footprint). -/
macro "rebase_tac'" hw:term "," hbw:term : tactic => `(tactic| first
  | rebase_quick $hw
  | (rw [$hbw _ (by simp [Footprint.union])] <;> with_reducible assumption)
  | rebase_objs $hw)
