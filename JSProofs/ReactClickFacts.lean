import JSProofs.ReactScheduleClick
import JSProofs.ReactEntangle

/-!
# What a click's `setN(v)` leaves, carried through frames (zippy docs/react-proofs.md)

The facts `setN(v)` ends with (the schedule, React's callback, the job queue) stay true through frames that write no
binding or property (calls that only read, a host call that only queues a job) and through restoring the caller's
realm.
-/

open ES HostRuns Logic

namespace ReactClickFacts

/-- A frame from `s` to `w` that writes nothing (it may queue jobs, if its footprint says so). -/
theorem frame_trans_bare {fp fq : Footprint} {s u w : State} (h1 : Frame fp s u) (h2 : Frame fq u w)
    (hb : fq.binds = []) (hp : fq.props = []) : Frame { fp with jobs := fp.jobs || fq.jobs } s w :=
  frame_mono (frame_trans h1 h2) (fun q hq => by simpa [Footprint.union, hb] using hq)
    (fun q hq => by simpa [Footprint.union, hp] using hq) (fun h => by simpa [Footprint.union] using h)

theorem envEntry_bare {fp : Footprint} {s w : State} (hF : Frame fp s w) (hb : fp.binds = []) {e : EnvId}
    (he : e < s.envs.size) : w.envEntry e = s.envEntry e :=
  envEntry_frame hF he (by simp [hb])

theorem objEntry_bare {fp : Footprint} {s w : State} (hF : Frame fp s w) (hp : fp.props = []) {o : ObjId}
    (ho : o < s.heap.size) : w.objEntry o = s.objEntry o :=
  objEntry_frame hF ho (by simp [hp])

theorem callback_bare {fp : Footprint} {s w : State} (hF : Frame fp s w) (hb : fp.binds = []) (hp : fp.props = [])
    {c : ObjId} {e g : EnvId} (h : ReactSchedTask.Callback s c e g) : ReactSchedTask.Callback w c e g := by
  obtain ⟨hc, dc, hk, h1, h2, h3, h4, he, hd⟩ := h
  exact ⟨heap_frame hF hc, dc, by rw [objEntry_bare hF hp hc]; exact hk, h1, h2, h3, h4, envs_frame hF he,
    by rw [envEntry_bare hF hb he]; exact hd⟩

theorem scheduled_bare {fp : Footprint} {s w : State} (hF : Frame fp s w) (hb : fp.binds = []) {e : EnvId}
    (he : e < s.envs.size) {oG : Option EnvId} {R : ObjId} (h : ReactEnsureRoot.Scheduled s e oG R) :
    ReactEnsureRoot.Scheduled w e oG R := by
  obtain ⟨bW, h1, h2⟩ := h
  exact ⟨bW, by rw [envEntry_bare hF hb he]; exact h1, h2⟩

@[simp] theorem restore_jobs (w s : State) : (w.restore s).jobs = w.jobs := rfl

end ReactClickFacts
