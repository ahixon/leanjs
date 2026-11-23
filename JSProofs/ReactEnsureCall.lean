import JSProofs.ReactEnsureRoot
import JSProofs.ReactSchedTask
import JSProofs.QueueJob

/-!
# `ensureRootIsScheduled` inside the commit (zippy docs/react-proofs.md)

The commit's `flushSpawnedWork` calls `ensureRootIsScheduled(root)` with the root already scheduled and
`didScheduleMicrotask` false (`processRootScheduleInMicrotask` reset it): `ReactEnsureRoot.call_scheduled`, then
`scheduleImmediateRootScheduleTask` (`ReactSchedTask.call_spec_h`), then the host's `queueMicrotask`, a built-in that
appends the job (`QueueJob.QueuesJob`, which Zippy proves of its binding). What it writes: the two flags and the job
queue (`fpEn`); after it the schedule is as `ReactEnsureRoot.Scheduled` says, and the host is untouched.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEnsureCall

/-- What the call writes: the two flags, and a job queued. -/
def fpEn (e : EnvId) : Footprint :=
  ⟨[(e, "mightHavePendingSyncWork"), (e, "didScheduleMicrotask")], [], true⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem en_call {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdF bdL bdM bdD bdS bdQ : Binding} {R fS fQ : ObjId}
    {dS : FuncData} {bQ : BuiltinData} {fn : BuiltinFn}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = ERSGen.ensureRootIsScheduled_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGL : bG[JSStr.ofString "lastScheduledRoot"]? = some bdL) (hGLv : bdL.value = some (.obj R))
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM) (hGMm : bdM.mutable = true)
    (hGMv : bdM.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD) (hGDm : bdD.mutable = true)
    (hGDv : bdD.value = some (.bool false))
    (hGS : bG[JSStr.ofString "scheduleImmediateRootScheduleTask"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    (hScode : dS.code = SIRGen.scheduleImmediateRootScheduleTask_func) (hScls : dS.isClassCtor = false)
    (hSmode : dS.thisMode = .strict) (hSenv : dS.env = d.env)
    (hGQ : bG[JSStr.ofString "scheduleMicrotask"]? = some bdQ) (hGQv : bdQ.value = some (.obj fQ))
    (hQo : fQ < s.heap.size) (hQk : (s.objEntry fQ).kind = .builtin bQ)
    (hfn : eng.builtins[bQ.id]? = some fn) (hq : QueueJob.QueuesJob fn fQ bQ)
    (hP : ((s.realms[dS.realm]!).intrinsics["%Function.prototype%"]?).isSome = true)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) :
    WP eng answer (n + 3) h (callImpl eng (.obj fo) t #[.obj R]) s fun v w h' =>
      v = .undefined ∧ Frame (fpEn d.env) s w ∧ s.fuel ≤ w.fuel + 60 ∧ h' = h ∧
        ReactEnsureRoot.Scheduled w d.env oG R := by
  refine ReactEnsureRoot.call_scheduled (n := n + 2) (Q := fun w h' => Frame (fpEn d.env) s w ∧
    s.fuel ≤ w.fuel + 60 ∧ h' = h ∧ ReactEnsureRoot.Scheduled w d.env oG R) hlt hk (by omega) hcode hcls hmode hG hGe
    hGF hGFv hGL hGLv hGM hGMm hGMv hGD hGDm hGDv hGS hGSv hSo hSk hR hRk ?sir
  case sir =>
  intro w hF1 hSch1 hfu1
  have hGw : d.env < w.envs.size := envs_frame hF1 hG
  obtain ⟨bW, hW, hWx⟩ := declLike_frame hF1 hG hGe
  have hWQ : bW[JSStr.ofString "scheduleMicrotask"]? = some bdQ := by
    rw [hWx _ (by simp [ReactEnsureRoot.fpS])]; exact hGQ
  have hobj : ∀ o, o < s.heap.size → w.objEntry o = s.objEntry o := fun o ho =>
    objEntry_frame hF1 ho (by simp [ReactEnsureRoot.fpS])
  refine wp_mono (ReactSchedTask.call_spec_h (n := n + 1) (h := h) (fo := fS) (d := dS) (t := .undefined) (s := w)
    (bG := bW) (oG := oG) (fM := fQ) (bM := bQ) (Q := fun x h' => Frame (fpEn d.env) s (x.restore s) ∧
      s.fuel ≤ (x.restore s).fuel + 60 ∧ h' = h ∧ ReactEnsureRoot.Scheduled (x.restore s) d.env oG R)
    (heap_frame hF1 hSo) (by rw [hobj _ hSo]; exact hSk) (by omega) hScode hScls hSmode (by rw [hSenv]; exact hGw)
    (by rw [hSenv]; exact hW) hWQ hGQv (heap_frame hF1 hQo) (by rw [hobj _ hQo]; exact hQk)
    (by rw [hF1.realms_eq]; exact hP) ?qm) fun _ w' h' ⟨_, q⟩ => q
  case qm =>
  intro w2 hF2 hCb hfu2
  rw [hSenv] at hCb
  obtain ⟨hclt, dc, hck, -⟩ := hCb
  have hQ1 : fQ < w.heap.size := heap_frame hF1 hQo
  refine wp_mono (QueueJob.call_spec_h (n := n + 1) (h := h) (fo := fQ) (c := w.heap.size) (bd := bQ) (fn := fn) (w := w2)
    (heap_frame hF2 hQ1) (by rw [objEntry_frame0 hF2 hQ1, hobj _ hQo]; exact hQk) hfn hq (by omega)
    ⟨hclt, by rw [hck]; trivial⟩) ?post
  case post =>
  rintro _ w3 h3 ⟨hF3, hfu3, -, rfl⟩
  have hG2 : d.env < w2.envs.size := envs_frame hF2 hGw
  refine ⟨frame_restore ?fr s, by simp only [restore_restore, restore_fuel]; omega, rfl, ?sch⟩
  case fr =>
    have := frame_trans (frame_trans hF1 hF2) hF3
    refine frame_restore ?_ _
    simpa [Footprint.union, ReactEnsureRoot.fpS, fpEn] using this
  case sch =>
    obtain ⟨bS, hS1, hS2⟩ := hSch1
    refine ⟨bS, ?_, hS2⟩
    simp only [restore_restore, restore_envEntry]
    rw [envEntry_frame hF3 hG2 (by simp), envEntry_frame0 hF2 hGw]
    exact hS1

end

end ReactEnsureCall
