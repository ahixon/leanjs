import JSProofs.Setter

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

end Logic

/-- One premise at the framed state `u` from the entry state's (see the module doc). -/
macro "rebase_tac" hw:term : tactic => `(tactic| first
  | with_reducible assumption
  | exact lt_heap_of_frame $hw (by with_reducible assumption)
  | exact lt_envs_of_frame $hw (by with_reducible assumption)
  | (rw [objEntry_frame0 $hw (by with_reducible assumption)]; with_reducible assumption)
  | (rw [envEntry_frame0 $hw (by with_reducible assumption)]; with_reducible assumption)
  | (rw [($hw).obj_eq _ (by with_reducible assumption) (fun _ hh => by simp at hh)]; with_reducible assumption)
  | (rw [($hw).obj_eq _ (by with_reducible assumption) (fun _ hh => by simp [Footprint.union] at hh; simp_all)];
      with_reducible assumption))

/-- As `rebase_tac`, and module bindings through `hbw` (`declLike_frame`'s: the bindings outside the footprint). -/
macro "rebase_tac'" hw:term "," hbw:term : tactic => `(tactic| first
  | rebase_tac $hw
  | (rw [$hbw _ (by simp)]; with_reducible assumption))
