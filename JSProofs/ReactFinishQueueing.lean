import JSProofs.JsTactic
import JSProofs.FQCGen
import JSProofs.ReactRenderSync

/-!
# React's `finishQueueingConcurrentUpdates` with nothing queued (zippy docs/react-proofs.md)

After a render's work loop (`renderRootSync`'s last call) the concurrent queues are empty
(`concurrentQueuesIndex` is 0): the lanes and the index are reset and the loop runs no iteration.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactFinishQueueing

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = FQCGen.finishQueueingConcurrentUpdates_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FQCGen.finishQueueingConcurrentUpdates_func, Func.params, Func.info]

/-- What it writes: the two module bindings. -/
def fp (g : EnvId) : Footprint :=
  ⟨[(g, "concurrentlyUpdatedLanes"), (g, "concurrentQueuesIndex")], [], false⟩

set_option maxRecDepth 10000 in
/-- **`finishQueueingConcurrentUpdates()`, queues empty**: writes 0 to both bindings, returns. -/
theorem empty_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdL : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = FQCGen.finishQueueingConcurrentUpdates_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "concurrentQueuesIndex"]? = some bdI) (hGIm : bdI.mutable = true)
    (hGIv : bdI.value = some (.num (F64.fin false 0 (-1074))))
    (hGL : bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bdL) (hGLm : bdL.mutable = true)
    (hGLv : bdL.value.isSome = true) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame (fp d.env) s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h := by
  apply wp_callGen FQCGen.finishQueueingConcurrentUpdates_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "endIndex", JSStr.ofString "i", JSStr.ofString "fiber",
    JSStr.ofString "queue", JSStr.ofString "update", JSStr.ofString "lane", JSStr.ofString "pending"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FQCGen.finishQueueingConcurrentUpdates_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FQCGen.finishQueueingConcurrentUpdates]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGL, hGLm, hGLv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | (simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1])

/-- Ready to finish with nothing queued: the function object, and the module record's two bindings. -/
structure Ready (w : State) (g : EnvId) (f : ObjId) (df : FuncData) : Prop where
  g_lt : g < w.envs.size
  f_lt : f < w.heap.size
  f_kind : (w.objEntry f).kind = .func df
  record : ∃ bG oG bdI bdL, Scope.declLike? (w.envEntry g) = some (bG, oG) ∧
    bG[JSStr.ofString "concurrentQueuesIndex"]? = some bdI ∧ bdI.mutable = true ∧
    bdI.value = some (.num (F64.fin false 0 (-1074))) ∧
    bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bdL ∧ bdL.mutable = true ∧ bdL.value.isSome = true

/-- **`renderRootSync`'s last call, from `Ready` at the work loop's end**: the shape of its hypothesis (`hFinish`)
with this function's footprint. -/
theorem finish_of_ready {n : Nat} {Post : State → σ → Prop} {g e : EnvId} {I f : ObjId} {df : FuncData}
    {w2 w : State} {h1 : σ} {c : State}
    (hcode : df.code = FQCGen.finishQueueingConcurrentUpdates_func) (hcls : df.isClassCtor = false)
    (hmode : df.thisMode = .strict) (hdenv : df.env = g)
    (hR : Ready w2 g f df)
    (hP : ∀ e w w', Frame (ReactRenderSync.fpEnd e g I) w2 w → Frame (fp g) w w' → ∀ c, Post (w'.restore c) h1)
    (hFe : Frame (ReactRenderSync.fpEnd e g I) w2 w) (hfu : 20 ≤ w.fuel) :
    WP eng answer n h1 (callImpl eng (.obj f) .undefined #[]) w fun _ w' h' =>
      Frame (fp g) w w' ∧ w.fuel ≤ w'.fuel + 20 ∧ Post (w'.restore c) h' := by
  obtain ⟨hg, hf, hk, bG, oG, bdI, bdL, hd, hI, hIm, hIv, hL, hLm, hLv⟩ := hR
  obtain ⟨bW, hdW, hx⟩ := declLike_frame hFe hg hd
  have hnI : (g, JSStr.ofString "concurrentQueuesIndex") ∉ (ReactRenderSync.fpEnd e g I).binds := by
    simp [ReactRenderSync.fpEnd, ReactRenderSync.fpOwn]
  have hnL : (g, JSStr.ofString "concurrentlyUpdatedLanes") ∉ (ReactRenderSync.fpEnd e g I).binds := by
    simp [ReactRenderSync.fpEnd, ReactRenderSync.fpOwn]
  refine wp_mono (empty_spec (d := df) (bG := bW) (oG := oG) (bdI := bdI) (bdL := bdL) (heap_frame hFe hf)
    (by rw [kind_frame hFe hf]; exact hk) hfu hcode hcls hmode (by rw [hdenv]; exact envs_frame hFe hg)
    (by rw [hdenv]; exact hdW) (by rw [hx _ hnI]; exact hI) hIm hIv (by rw [hx _ hnL]; exact hL) hLm hLv) ?_
  intro v w' h' ⟨_, hFr, hfu', hh⟩
  subst hh
  exact ⟨by rw [hdenv] at hFr; exact hFr, hfu', hP e w w' hFe (by rw [hdenv] at hFr; exact hFr) c⟩

end

end ReactFinishQueueing
