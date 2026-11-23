import JSProofs.JsTactic
import JSProofs.FQCGen
import JSProofs.ReactRenderSync
import JSProofs.ReactMarkLane

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

/-- After it: no lanes updated concurrently. -/
def QueuesDone (w : State) (g : EnvId) : Prop :=
  ∃ bm oG, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧
    ∃ bd, bm[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bd ∧ bd.value = some (.num (F64.fin false 0 (-1074)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
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
      v = .undefined ∧ Frame (fp d.env) s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h ∧ QueuesDone w d.env := by
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
  all_goals first | rfl | omega | (unfold QueuesDone; exact ⟨_, _, by js_norm [hG, hG1, hne, Ne.symm hne, hGe]; rfl, _,
      by simp [Std.HashMap.getElem?_modify, hGL]; rfl, rfl⟩) |
    (simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1])

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
theorem finish_of_ready {n : Nat} {Post : State → σ → Prop} {EP : State → Prop} {g e : EnvId} {I f : ObjId} {df : FuncData}
    {w2 w : State} {h1 : σ} {c : State}
    (hcode : df.code = FQCGen.finishQueueingConcurrentUpdates_func) (hcls : df.isClassCtor = false)
    (hmode : df.thisMode = .strict) (hdenv : df.env = g)
    (hR : Ready w2 g f df)
    (hP : ∀ e w w', Frame (ReactRenderSync.fpEnd e g I) w2 w → EP w → Frame (fp g) w w' → QueuesDone w' g → ∀ c,
      Post (w'.restore c) h1)
    (hFe : Frame (ReactRenderSync.fpEnd e g I) w2 w) (hEP : EP w) (hfu : 20 ≤ w.fuel) :
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
  intro v w' h' ⟨_, hFr, hfu', hh, hQD⟩
  subst hh
  exact ⟨by rw [hdenv] at hFr; exact hFr, hfu', hP e w w' hFe hEP (by rw [hdenv] at hFr; exact hFr)
    (by rw [hdenv] at hQD; exact hQD) c⟩

/-- What it writes with one update queued: the bindings, the array's four elements, the queue's `pending`, the
update's `next`, and the lanes `markUpdateLaneFromFiberToRoot` marks. -/
def fpOne (g : EnvId) (A Qo U F Fa P Pa : ObjId) : Footprint :=
  ⟨[(g, "concurrentlyUpdatedLanes"), (g, "concurrentQueuesIndex")],
    [(A, .str "0"), (A, .str "1"), (A, .str "2"), (A, .str "3"), (Qo, .str "pending"), (U, .str "next")] ++
      (ReactMarkLane.fp F Fa P Pa).props, false⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **`finishQueueingConcurrentUpdates()`, one update queued** (a click's `setN` before its render): the update
`U` becomes the hook queue `Qo`'s only pending update (`U.next = U`), and its lane is marked from the counter's fiber
`F` up to the host root. -/
theorem one_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdL bdA bdM : Binding}
    {A Qo U F Fa P Pa Rt fM : ObjId} {dM : FuncData} {lane fl al pc ac L : F64} {v4 v5 : Value} {lw le lc : Bool}
    {e0 c0 e1 c1 e2 c2 e3 c3 qe qc ue uc fe fc ae ac' pe pc' xe xc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = FQCGen.finishQueueingConcurrentUpdates_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "concurrentQueuesIndex"]? = some bdI) (hGIm : bdI.mutable = true)
    (hGIv : bdI.value = some (.num (F64.fin false 4503599627370496 (-50))))
    (hGL : bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bdL) (hGLm : bdL.mutable = true)
    (hGLv : bdL.value.isSome = true)
    (hGA : bG[JSStr.ofString "concurrentQueues"]? = some bdA) (hGAv : bdA.value = some (.obj A))
    (hGM : bG[JSStr.ofString "markUpdateLaneFromFiberToRoot"]? = some bdM) (hGMv : bdM.value = some (.obj fM))
    (hMo : fM < s.heap.size) (hMk : (s.objEntry fM).kind = .func dM)
    (hMcode : dM.code = MULGen.markUpdateLaneFromFiberToRoot_func) (hMcls : dM.isClassCtor = false)
    (hMmode : dM.thisMode = .strict) (dMA : fM ≠ A) (dMQ : fM ≠ Qo) (dMU : fM ≠ U)
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hA0 : (s.objEntry A).props.get? (.str "0") = some (.data (.obj F) true e0 c0))
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data (.obj Qo) true e1 c1))
    (hA2 : (s.objEntry A).props.get? (.str "2") = some (.data (.obj U) true e2 c2))
    (hA3 : (s.objEntry A).props.get? (.str "3") = some (.data (.num lane) true e3 c3))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hL4 : 4 ≤ (Conv.toNat? L).getD 0)
    (hlane : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num lane) = false)
    (hQ : Qo < s.heap.size) (hQk : (s.objEntry Qo).kind.isPlain = true)
    (hQp : (s.objEntry Qo).props.get? (.str "pending") = some (.data .null true qe qc))
    (hU : U < s.heap.size) (hUk : (s.objEntry U).kind.isPlain = true)
    (hUn : (s.objEntry U).props.get? (.str "next") = some (.data v4 true ue uc))
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFa : Fa < s.heap.size) (hFak : (s.objEntry Fa).kind.isPlain = true)
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPa : Pa < s.heap.size) (hPak : (s.objEntry Pa).kind.isPlain = true)
    (dAQ : A ≠ Qo) (dAU : A ≠ U) (dAF : A ≠ F) (dAFa : A ≠ Fa) (dAP : A ≠ P) (dAPa : A ≠ Pa)
    (dQU : Qo ≠ U) (dQF : Qo ≠ F) (dQFa : Qo ≠ Fa) (dQP : Qo ≠ P) (dQPa : Qo ≠ Pa)
    (dUF : U ≠ F) (dUFa : U ≠ Fa) (dUP : U ≠ P) (dUPa : U ≠ Pa)
    (d1 : F ≠ Fa) (d2 : F ≠ P) (d3 : F ≠ Pa) (d4 : Fa ≠ P) (d5 : Fa ≠ Pa) (d6 : P ≠ Pa)
    (hFl : (s.objEntry F).props.get? (.str "lanes") = some (.data (.num fl) true fe fc))
    (hFal : (s.objEntry F).props.get? (.str "alternate") = some (.data (.obj Fa) r1 r2 r3))
    (hFr : (s.objEntry F).props.get? (.str "return") = some (.data (.obj P) r4 r5 r6))
    (hFal' : (s.objEntry Fa).props.get? (.str "lanes") = some (.data (.num al) true ae ac'))
    (hPc : (s.objEntry P).props.get? (.str "childLanes") = some (.data (.num pc) true pe pc'))
    (hPal : (s.objEntry P).props.get? (.str "alternate") = some (.data (.obj Pa) r7 r8 r9))
    (hPt : (s.objEntry P).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) r10 r11 r12))
    (hPr : (s.objEntry P).props.get? (.str "return") = some (.data .null r13 r14 r15))
    (hPs : (s.objEntry P).props.get? (.str "stateNode") = some (.data (.obj Rt) r16 r17 r18))
    (hPac : (s.objEntry Pa).props.get? (.str "childLanes") = some (.data (.num ac) true xe xc)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame (fpOne d.env A Qo U F Fa P Pa) s w ∧ s.fuel ≤ w.fuel + 100 ∧ h' = h ∧
      (w.objEntry Qo).props.get? (.str "pending") = some (.data (.obj U) true qe qc) ∧
      (w.objEntry U).props.get? (.str "next") = some (.data (.obj U) true ue uc) ∧
      (w.objEntry F).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr fl lane)) true fe fc) ∧
      (w.objEntry Fa).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr al lane)) true ae ac') ∧
      (w.objEntry P).props.get? (.str "childLanes") = some (.data (.num (numberBinOp .bitOr pc lane)) true pe pc') ∧
      (w.objEntry Pa).props.get? (.str "childLanes") = some (.data (.num (numberBinOp .bitOr ac lane)) true xe xc) ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "concurrentQueuesIndex"]? = some bd ∧ bd.mutable = true ∧ bd.value = some (.num (F64.fin false 0 (-1074)))) ∧
        (∃ bd, bm[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) := by
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
  have hL0 : 0 < (Conv.toNat? L).getD 0 := by omega
  have hL1 : 1 < (Conv.toNat? L).getD 0 := by omega
  have hL2 : 2 < (Conv.toNat? L).getD 0 := by omega
  have hL3 : 3 < (Conv.toNat? L).getD 0 := by omega
  clear hcode
  simp only [FQCGen.finishQueueingConcurrentUpdates]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGL, hGLm, hGLv, hGA, hL0, hL1, hL2, hL3, hGAv, hGM, hGMv, hMo, hMk, hA, hAk, hA0, hA1, hA2, hA3, hAL, hL4, hlane, hQ, hQk, hQp, hU, hUk, hUn, dAQ, dAU, dQU, Ne.symm dAQ, Ne.symm dAU, Ne.symm dQU, FDI.fdiCtx, Sem.inner]
  focus
    js_norm [CallableC, *, Ne.symm dMA, Ne.symm dMQ, Ne.symm dMU]
    refine wp_mono (ReactMarkLane.root_spec (d := dM) (Rt := Rt) (fl := fl) (al := al) (pc := pc) (ac := ac) (F := F) (Fa := Fa) (P := P) (Pa := Pa) (fe := fe) (fc := fc) (ae := ae) (ac' := ac') (pe := pe) (pc' := pc') (qe := xe) (qc := xc) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) (r11 := r11) (r12 := r12) (r13 := r13) (r14 := r14) (r15 := r15) (r16 := r16) (r17 := r17) (r18 := r18)
      ?_ ?_ ?_ hMcode hMcls hMmode ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d1 d2 d3 d4 d5 d6 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?post
    case post =>
      intro v w' h' ⟨hv, hFr, hfu', hh, hF', hFa', hP', hPa'⟩
      subst hh
      simp only [js_simp] at hfu'
      have hEw := envEntry_frame hFr (e := s.envs.size) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega)) (by simp [ReactMarkLane.fp])
      have hGw := envEntry_frame hFr (e := d.env) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega)) (by simp [ReactMarkLane.fp])
      have hEs : s.envs.size < w'.envs.size := envs_frame hFr (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
      js [hEw, hGw, hEs, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGL, hGLm, hGLv, hGA, hGAv, hF', hFa', hP', hPa', envEntry_frame hFr, props_frame hFr, kind_frame hFr, heap_frame hFr, envs_frame hFr, ReactMarkLane.fp, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, Ne.symm dAQ, Ne.symm dAU, Ne.symm dAF, Ne.symm dAFa, Ne.symm dAP, Ne.symm dAPa, Ne.symm dQU, Ne.symm dQF, Ne.symm dQFa, Ne.symm dQP, Ne.symm dQPa, Ne.symm dUF, Ne.symm dUFa, Ne.symm dUP, Ne.symm dUPa, Ne.symm dMA, Ne.symm dMQ, Ne.symm dMU, FDI.fdiCtx, Sem.inner]
      all_goals (repeat' apply And.intro)
      all_goals first | (refine ⟨_, rfl, ⟨_, by simp [Std.HashMap.getElem?_modify, hGI]; rfl, by simpa using hGIm, rfl⟩,
          ⟨_, by simp [Std.HashMap.getElem?_modify, hGL]; rfl, by simpa using hGLm, rfl⟩⟩) | omega | (simp only [js_simp] at *; omega) | exact hF' | exact hFa' | exact hP' | exact hPa' | (rw [props_frame hFr (by simp only [js_simp]; first | exact hQ | exact hU) (by simp [ReactMarkLane.fp, dQF, dQFa, dQP, dQPa, dUF, dUFa, dUP, dUPa])]; js_norm [*, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, Ne.symm dAQ, Ne.symm dAU, Ne.symm dAF, Ne.symm dAFa, Ne.symm dAP, Ne.symm dAPa, Ne.symm dQU, Ne.symm dQF, Ne.symm dQFa, Ne.symm dQP, Ne.symm dQPa, Ne.symm dUF, Ne.symm dUFa, Ne.symm dUP, Ne.symm dUPa, Ne.symm dMA, Ne.symm dMQ, Ne.symm dMU]; done) | skip
      all_goals (refine frame_restore ?_ s; refine frame_withFuel ?_ _; simp only [ReactMarkLane.fp] at hFr; simp only [fpOne, ReactMarkLane.fp, List.cons_append, List.nil_append]; frame_go' [*, ReactMarkLane.fp, hne, Ne.symm hne, hG1, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, Ne.symm dAQ, Ne.symm dAU, Ne.symm dAF, Ne.symm dAFa, Ne.symm dAP, Ne.symm dAPa, Ne.symm dQU, Ne.symm dQF, Ne.symm dQFa, Ne.symm dQP, Ne.symm dQPa, Ne.symm dUF, Ne.symm dUFa, Ne.symm dUP, Ne.symm dUPa, Ne.symm dMA, Ne.symm dMQ, Ne.symm dMU])
    all_goals first | omega | (simp only [js_simp]; omega) | (js_norm [*, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, Ne.symm dAQ, Ne.symm dAU, Ne.symm dAF, Ne.symm dAFa, Ne.symm dAP, Ne.symm dAPa, Ne.symm dQU, Ne.symm dQF, Ne.symm dQFa, Ne.symm dQP, Ne.symm dQPa, Ne.symm dUF, Ne.symm dUFa, Ne.symm dUP, Ne.symm dUPa, Ne.symm dMA, Ne.symm dMQ, Ne.symm dMU]; done) | skip

end

end ReactFinishQueueing
