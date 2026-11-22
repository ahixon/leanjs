import JSProofs.ReactDSSI
import JSProofs.PRSGen

/-!
# React's `processRootScheduleInMicrotask` for a click's root (zippy docs/react-proofs.md)

```js
function processRootScheduleInMicrotask() {
  mightHavePendingSyncWork = didScheduleMicrotask = !1;
  var syncTransitionLanes = 0;
  0 !== currentEventTransitionLane && shouldAttemptEagerTransition() && (…);
  for (var currentTime = now(), prev = null, root = firstScheduledRoot; null !== root; ) {
    var next = root.next, nextLanes = scheduleTaskForRootDuringMicrotask(root, currentTime);
    if (0 === nextLanes) (…remove the root…);
    else if (((prev = root), 0 !== syncTransitionLanes || 0 !== (nextLanes & 3)))
      mightHavePendingSyncWork = !0;
    root = next;
  }
  (0 !== pendingEffectsStatus && 5 !== pendingEffectsStatus) || flushSyncWorkAcrossRoots_impl(syncTransitionLanes, !1);
  0 !== currentEventTransitionLane && (currentEventTransitionLane = 0);
}
```
After a click (no transition, one root scheduled, no effects pending): the time is read (`now`, the scheduler's), the
root's task is scheduled (`scheduleTaskForRootDuringMicrotask`, returning sync lanes), the root stays scheduled, sync
work is pending again, and `flushSyncWorkAcrossRoots_impl(0, false)` runs it. The three callees are hypotheses here.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactProcessRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = PRSGen.processRootScheduleInMicrotask_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PRSGen.processRootScheduleInMicrotask_func, Func.params, Func.info]

/-- What this function itself writes: the two flags. -/
def fpA (g : EnvId) : Footprint := ⟨[(g, "mightHavePendingSyncWork"), (g, "didScheduleMicrotask")], [], false⟩

set_option maxHeartbeats 2000000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdM bdD bdC bdF bdN bdT bdP bdL : Binding} {R fN fT fL : ObjId} {dN dT dL : FuncData} {L : F64}
    {rw re rc : Bool} {fpT fpF : Footprint} {kF : Nat} {P : State → σ → Prop} {Q : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : kF + 200 ≤ s.fuel)
    (hcode : d.code = PRSGen.processRootScheduleInMicrotask_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM) (hGMm : bdM.mutable = true)
    (hGMv : bdM.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD) (hGDm : bdD.mutable = true)
    (hGDv : bdD.value.isSome = true)
    (hGC : bG[JSStr.ofString "currentEventTransitionLane"]? = some bdC)
    (hGCv : bdC.value = some (.num (F64.fin false 0 (-1074))))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGN : bG[JSStr.ofString "now"]? = some bdN) (hGNv : bdN.value = some (.obj fN))
    (hGT : bG[JSStr.ofString "scheduleTaskForRootDuringMicrotask"]? = some bdT) (hGTv : bdT.value = some (.obj fT))
    (hGP : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdP)
    (hGPv : bdP.value = some (.num (F64.fin false 0 (-1074))))
    (hGL : bG[JSStr.ofString "flushSyncWorkAcrossRoots_impl"]? = some bdL) (hGLv : bdL.value = some (.obj fL))
    (hNo : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .func dN)
    (hTo : fT < s.heap.size) (hTk : (s.objEntry fT).kind = .func dT)
    (hLo : fL < s.heap.size) (hLk : (s.objEntry fL).kind = .func dL)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null rw re rc))
    (hL0 : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num L) = false)
    (hL3 : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd L (F64.fin false 6755399441055744 (-51)))) = false)
    -- (`now()`: reads the time, writes nothing)
    (hNow : ∀ w h1, Frame (fpA d.env) s w → s.fuel ≤ w.fuel + 10 →
      WP eng answer n h1 (callImpl eng (.obj fN) .undefined #[]) w fun _ w' _ =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 10)
    -- (`scheduleTaskForRootDuringMicrotask(root, currentTime)`: the root's lanes `L`, sync)
    (hTask : ∀ w h1 tm, Frame (fpA d.env) s w → s.fuel ≤ w.fuel + 30 →
      WP eng answer n h1 (callImpl eng (.obj fT) .undefined #[.obj R, tm]) w fun v w' h' =>
        v = .num L ∧ Frame fpT w w' ∧ w.fuel ≤ w'.fuel + 30 ∧ P w' h')
    (hfpE : fpT.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpM : (d.env, JSStr.ofString "mightHavePendingSyncWork") ∉ fpT.binds)
    (hfpP : (d.env, JSStr.ofString "pendingEffectsStatus") ∉ fpT.binds)
    (hfpL : (d.env, JSStr.ofString "flushSyncWorkAcrossRoots_impl") ∉ fpT.binds)
    (hfpC : (d.env, JSStr.ofString "currentEventTransitionLane") ∉ fpT.binds)
    (hfpO : fpT.props.all (fun q => q.1 != fL) = true)
    -- (`flushSyncWorkAcrossRoots_impl(0, false)`)
    (hFlush : ∀ w2 w h1, P w2 h1 →
      Frame ⟨[(d.env, "mightHavePendingSyncWork"), (s.envs.size, "nextLanes"), (s.envs.size, "prev"),
        (s.envs.size, "root")], [], false⟩ w2 w →
      (∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (bm[JSStr.ofString "mightHavePendingSyncWork"]?.bind (·.value)) = some (.bool true)) →
      s.fuel ≤ w.fuel + 80 →
      WP eng answer n h1 (callImpl eng (.obj fL) .undefined #[.num (F64.fin false 0 (-1074)), .bool false]) w
        fun _ w' h' => Frame fpF w w' ∧ w.fuel ≤ w'.fuel + kF ∧ Q (w'.restore s) h')
    (hfpFE : fpF.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpFC : (d.env, JSStr.ofString "currentEventTransitionLane") ∉ fpF.binds) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' => v = .undefined ∧ Q w h' := by
  replace hNow := ReactDSSI.Hold.mk hNow
  replace hTask := ReactDSSI.Hold.mk hTask
  replace hFlush := ReactDSSI.Hold.mk hFlush
  apply wp_callGen PRSGen.processRootScheduleInMicrotask_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "syncTransitionLanes", JSStr.ofString "currentTime",
      JSStr.ofString "prev", JSStr.ofString "root", JSStr.ofString "next", JSStr.ofString "nextLanes"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, PRSGen.processRootScheduleInMicrotask_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PRSGen.processRootScheduleInMicrotask]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGM, hGMm, hGMv, hGD, hGDm, hGDv, hGC, hGCv, hGF, hGFv, hGN,
    hGNv, hNo, hNk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hNow) _ h ?fr ?fu) ?post1
  case fr => simp only [fpA]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu => js_side
  case post1 =>
  intro tm w1 h1 ⟨hF1, hfu1⟩
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by simp)
  have hG1e := envEntry_frame0 hF1 (e := d.env) (by simp; omega)
  have hE1s : s.envs.size < w1.envs.size := envs_frame hF1 (by simp)
  have hG1s : d.env < w1.envs.size := envs_frame hF1 (by simp; omega)
  have hR1 := objEntry_frame0 hF1 (o := R) (by simpa using hR)
  have hT1 := objEntry_frame0 hF1 (o := fT) (by simpa using hTo)
  have hR1s : R < w1.heap.size := heap_frame hF1 (by simpa using hR)
  have hT1s : fT < w1.heap.size := heap_frame hF1 (by simpa using hTo)
  try simp only [js_simp] at hfu1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGM, hGMm, hGMv, hGD, hGDm, hGDv, hGC, hGCv, hGF, hGFv,
    hGT, hGTv, hE1, hG1e, hE1s, hG1s, hR1, hT1, hR1s, hT1s, hR, hRk, hRn, hTo, hTk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hTask) _ h1 tm ?fr2 ?fu2) ?post2
  case fr2 => simp only [fpA]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu2 => js_side
  case post2 =>
  intro v w2 h2 ⟨hv2, hF2, hfu2, hP2⟩
  subst hv2
  have hE1s' : s.envs.size < (bodyState s fo d t #[]).envs.size := by simp
  have hE2 := envEntry_frame hF2 (e := s.envs.size) (by simp only [js_simp]; first | exact hE1s | omega) hfpE
  have hE2s : s.envs.size < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; first | exact hE1s | omega)
  have hG2s : d.env < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; first | exact hG1s | omega)
  obtain ⟨bW, hW, hWx⟩ := declLike_frame hF2 (e := d.env) (o := oG)
    (by simp only [js_simp]; first | exact hG1s | omega) (by js_norm [*]; rfl)
  have hWM := hWx _ hfpM
  have hWP := hWx _ hfpP
  have hWL := hWx _ hfpL
  have hWC := hWx _ hfpC
  have hL1 : fL < w1.heap.size := heap_frame hF1 (by simpa using hLo)
  have hL2 : fL < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact hL1)
  have hLk2 : (w2.objEntry fL).kind = .func dL := by
    rw [objEntry_frame hF2 (by simp only [js_simp]; exact hL1) hfpO]
    simp only [js_simp]
    rw [objEntry_frame0 hF1 (by simpa using hLo)]
    simpa using hLk
  try simp only [js_simp] at hfu2
  js [hE2, hE2s, hG2s, hW, hWM, hWP, hWL, hWC, hGM, hGP, hGL, hGC, hGMm, hGMv, hGPv, hGLv, hGCv, hL2, hLk2, hL0, hL3, hne, Ne.symm hne,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hFlush) w2 _ h2 hP2 ?frF ?mF ?fuF) ?post3
  case frF => frame_go' [*, hne, Ne.symm hne]
  case mF =>
    refine ⟨_, by js_norm [*]; rfl, ?_⟩
    simp only [Std.HashMap.getElem?_modify, js_simp, hWM, hGM, Option.map_some]
    rfl
  case fuF => js_side
  case post3 =>
  intro b w3 h3 ⟨hF3, hfu3, hQ⟩
  try simp only [js_simp] at hfu3
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp only [js_simp]; first | exact hE2s | omega) hfpFE
  have hE3s : s.envs.size < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; first | exact hE2s | omega)
  obtain ⟨bW3, hW3, hW3x⟩ := declLike_frame hF3 (e := d.env) (o := oG)
    (by simp only [js_simp]; first | exact hG2s | omega) (by js_norm [*]; rfl)
  have hW3C := hW3x _ hfpFC
  have hG3s : d.env < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; first | exact hG2s | omega)
  have hd3 : depth ≤ w3.fuel := by simp only [depth]; omega
  js [hE3, hE3s, hW3, hW3C, hWC, hGC, hGCv, hE2, hW, hd3, hG3s, FDI.fdiCtx, Sem.inner, hQ]


end

end ReactProcessRoot
