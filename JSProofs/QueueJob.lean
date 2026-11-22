import JSProofs.ReactClickFacts

/-!
# A host function that queues a job (zippy docs/react-proofs.md)

`queueMicrotask(c)` as a built-in: if its function, given a callable `c`, returns `undefined` having appended the job
`c()` and changed nothing else (`QueuesJob`), its call satisfies `ReactClick.click`'s hypothesis about the host. Zippy
proves its binding (`LeanBindings.opFn` with `queueMicrotask`'s slots) is such a function.
-/

open ES HostRuns Logic

namespace QueueJob

/-- A built-in function (its object `fo` of kind `.builtin bd`) that, called with a callable `c`, queues the job `c()`
and does nothing else. Stated with the interpreter's own reads, so a host can prove it without this library. -/
def QueuesJob (fn : BuiltinFn) (fo : ObjId) (bd : BuiltinData) : Prop :=
  ∀ (u : State) (c : ObjId), objKind fo u = .ok (.builtin bd) u → isCallable (.obj c) u = .ok true u →
    fn fo .undefined #[.obj c] .undefined u = .ok .undefined { u with jobs := u.jobs.push (.obj c, #[]) }

theorem objKind_of {u : State} {fo : ObjId} {bd : BuiltinData} (hlt : fo < u.heap.size)
    (hk : (u.objEntry fo).kind = .builtin bd) : objKind fo u = .ok (.builtin bd) u := by
  simp only [objKind]; rw [readObj_entry' _ _ _ hlt, hk]

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **The call**: the job queued, nothing written, one step of fuel. -/
theorem call_spec {n : Nat} {h : σ} {fo c : ObjId} {bd : BuiltinData} {fn : BuiltinFn} {w : State}
    (hlt : fo < w.heap.size) (hk : (w.objEntry fo).kind = .builtin bd) (hfn : eng.builtins[bd.id]? = some fn)
    (hq : QueuesJob fn fo bd) (hf : w.fuel ≠ 0) (hc : CallableC w (.obj c)) :
    WP eng answer n h (callImpl eng (.obj fo) .undefined #[.obj c]) w fun _ w' _ =>
      Frame ⟨[], [], true⟩ w w' ∧ w.fuel ≤ w'.fuel + 6 ∧ w'.jobs = w.jobs.push (.obj c, #[]) := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd fn .undefined _ w hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  have hok := objKind_of (u := { { w with fuel := w.fuel - 1 } with realm := bd.realm, script := w.script }) hlt hk
  refine wp_of_eq (hq _ c hok (isCallable_of hc)) ⟨?_, by simp; omega, rfl⟩
  exact {
    envs_le := Nat.le_refl _
    heap_le := Nat.le_refl _
    env_agree := fun _ _ => envAgree_refl _ _
    obj_agree := fun _ _ => objAgree_refl _ _
    env_eq := fun _ _ _ => rfl
    obj_eq := fun _ _ _ => rfl
    realms_eq := rfl
    jobs_prefix := ⟨#[(.obj c, #[])], rfl⟩
    jobs_eq := fun h => absurd h (by simp) }

end

end QueueJob
