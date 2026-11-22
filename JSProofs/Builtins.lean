import JSProofs.Frame

/-!
# Built-in functions' specs (zippy docs/react-proofs.md)

A call of a built-in function object runs its behaviour from the engine's table (`callImpl_builtin`); a spec here
is that behaviour's, in the program logic's shape (value, frame, fuel). The table entry (`eng.builtins[id]? = some
fn`) is a hypothesis: it is a fact about the realm's setup, like the module's records.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- A state with the same records and objects (fuel, current realm, script aside) is framed by any footprint. -/
theorem frame_same {fp : Footprint} {s w : State} (he : w.envs = s.envs) (hh : w.heap = s.heap)
    (hr : w.realms = s.realms) (hj : w.jobs = s.jobs) : Frame fp s w where
  envs_le := by rw [he]; exact Nat.le_refl _
  heap_le := by rw [hh]; exact Nat.le_refl _
  env_agree e _ := by simp only [State.envEntry, he]; exact envAgree_refl _ _
  obj_agree o _ := by simp only [State.objEntry, hh]; exact objAgree_refl _ _
  env_eq e _ _ := by simp only [State.envEntry, he]
  obj_eq o _ _ := by simp only [State.objEntry, hh]
  realms_eq := hr
  jobs_prefix := ⟨#[], by simp [hj]⟩
  jobs_eq _ := hj

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`Object.is(x, y)`**: `SameValue(x, y)`, nothing changed, one step of fuel. -/
theorem objectIs_spec {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {t x y : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some objectIs) (hf : s.fuel ≠ 0) :
    WP eng answer n h (callImpl eng (.obj fo) t #[x, y]) s fun v w _ =>
      v = .bool (sameValue x y) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd objectIs t _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  exact wp_of_eq rfl ⟨rfl, frame_same rfl rfl rfl rfl, by simp; omega⟩

end

end Logic
