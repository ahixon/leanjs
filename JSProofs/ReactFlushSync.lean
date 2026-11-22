import JSProofs.ReactSchedTaskRoot
import JSProofs.FSWGen

/-!
# React's `flushSyncWorkAcrossRoots_impl` after a click (zippy docs/react-proofs.md)

```js
function flushSyncWorkAcrossRoots_impl(syncTransitionLanes, onlyLegacy) {
  if (!isFlushingWork && mightHavePendingSyncWork) {
    isFlushingWork = !0;
    do {
      var didPerformSomeWork = !1;
      for (var root$190 = firstScheduledRoot; null !== root$190; ) {
        if (!onlyLegacy) if (0 !== syncTransitionLanes) { … } else
          (JSCompiler_inline_result = getNextLanes(root$190, root$190 === workInProgressRoot ? … : 0, …)),
          0 === (JSCompiler_inline_result & 3) || checkIfRootIsPrerendering(root$190, JSCompiler_inline_result) ||
            ((didPerformSomeWork = !0), performSyncWorkOnRoot(root$190, JSCompiler_inline_result));
        root$190 = root$190.next;
      }
    } while (didPerformSomeWork);
    isFlushingWork = !1;
  }
}
```
`flushSyncWorkAcrossRoots_impl(0, false)` with one root scheduled for the sync lane: the first pass finds the lane
(`getNextLanes` 2, not prerendering) and runs `performSyncWorkOnRoot(root, 2)` (the render and commit: a hypothesis
here, with what the loop reads afterwards in its post); the second pass finds nothing (`getNextLanes` 0) and the loop
ends.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactFlushSync

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = FSWGen.flushSyncWorkAcrossRoots_impl_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FSWGen.flushSyncWorkAcrossRoots_impl_func, Func.params, Func.info]

def fpA (g : EnvId) : Footprint := ⟨[(g, "isFlushingWork")], [], false⟩

/-- What the function writes after the work: its own locals (record `e`) and the flag. -/
def fpW (e g : EnvId) : Footprint :=
  ⟨[(e, "didPerformSomeWork"), (e, "root$190"), (e, "JSCompiler_inline_result"), (g, "isFlushingWork")], [], false⟩

/-- After the work: the root's fields the loop reads again, no root in progress. -/
structure After (w : State) (g : EnvId) (oG : Option EnvId) (R : ObjId) (bdF : Binding) : Prop where
  record : ∃ bW bdW bdL lv, Scope.declLike? (w.envEntry g) = some (bW, oG) ∧
    bW[JSStr.ofString "workInProgressRoot"]? = some bdW ∧ bdW.value = some .null ∧
    bW[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL ∧ bdL.value = some lv ∧
    bW[JSStr.ofString "firstScheduledRoot"]? = some bdF
  next : ∃ a b c, (w.objEntry R).props.get? (.str "next") = some (.data .null a b c)
  cancel : ∃ a b c, (w.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null a b c)
  timeout : ∃ a b c, (w.objEntry R).props.get? (.str "timeoutHandle") =
    some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) a b c)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdI bdM bdF bdW bdL bdG bdP bdS : Binding} {lv0 : Value} {R fG fP fS : ObjId} {dG dP dS : FuncData}
    {nw ne nc cw ce cc tw te tc : Bool} {fpP : Footprint} {kP : Nat} {P : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : kP + 300 ≤ s.fuel)
    (hcode : d.code = FSWGen.flushSyncWorkAcrossRoots_impl_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "isFlushingWork"]? = some bdI) (hGIv : bdI.value = some (.bool false))
    (hGIm : bdI.mutable = true)
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM) (hGMv : bdM.value = some (.bool true))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL) (hGLv : bdL.value = some lv0)
    (hGG : bG[JSStr.ofString "getNextLanes"]? = some bdG) (hGGv : bdG.value = some (.obj fG))
    (hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hGS : bG[JSStr.ofString "performSyncWorkOnRoot"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hGo : fG < s.heap.size) (hGk : (s.objEntry fG).kind = .func dG)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null nw ne nc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    -- (the first pass)
    (hNext1 : ReactSchedTaskRoot.Reads eng answer n fG #[.obj R, .num (F64.fin false 0 (-1074)), .bool false]
      (.num (F64.fin false 4503599627370496 (-51))) s (fpA d.env) 20)
    (hPre : ReactSchedTaskRoot.Reads eng answer n fP #[.obj R, .num (F64.fin false 4503599627370496 (-51))]
      (.bool false) s (fpA d.env) 10)
    (hPerf : ∀ w h1, Frame (fpA d.env) s w → s.fuel ≤ w.fuel + 60 →
      WP eng answer n h1 (callImpl eng (.obj fS) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w
        fun _ w' h' => Frame fpP w w' ∧ w.fuel ≤ w'.fuel + kP ∧ After w' d.env oG R bdF ∧ P w' h')
    (hfpE : fpP.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpG : (d.env, JSStr.ofString "getNextLanes") ∉ fpP.binds)
    (hfpI : (d.env, JSStr.ofString "isFlushingWork") ∉ fpP.binds)
    (hfpO : fpP.props.all (fun q => q.1 != fG) = true)
    -- (the second pass: nothing left)
    (hNext2 : ∀ w2 w h1, P w2 h1 → Frame (fpW s.envs.size d.env) w2 w → 30 ≤ w.fuel →
      WP eng answer n h1 (callImpl eng (.obj fG) .undefined #[.obj R, .num (F64.fin false 0 (-1074)), .bool false]) w
        fun r w' _ => r = .num (F64.fin false 0 (-1074)) ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 20) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t
        #[.num (F64.fin false 0 (-1074)), .bool false]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨(d.env, JSStr.ofString "isFlushingWork") :: fpP.binds, fpP.props, fpP.jobs⟩ s w ∧
      s.fuel ≤ w.fuel + kP + 200 ∧ ∃ w2 h2, P w2 h2 ∧ Frame (fpW s.envs.size d.env) w2 w := by
  replace hNext1 := ReactDSSI.Hold.mk hNext1
  replace hPre := ReactDSSI.Hold.mk hPre
  replace hPerf := ReactDSSI.Hold.mk hPerf
  replace hNext2 := ReactDSSI.Hold.mk hNext2
  apply wp_callGen FSWGen.flushSyncWorkAcrossRoots_impl_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "syncTransitionLanes", JSStr.ofString "onlyLegacy"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "didPerformSomeWork", JSStr.ofString "root$190",
      JSStr.ofString "pendingLanes", JSStr.ofString "JSCompiler_inline_result", JSStr.ofString "suspendedLanes",
      JSStr.ofString "pingedLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, FSWGen.flushSyncWorkAcrossRoots_impl_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FSWGen.flushSyncWorkAcrossRoots_impl]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGIm, hGM, hGMv, hGF, hGFv, hGW, hGWv, hGL, hGLv, hGG, hGGv,
    hGo, hGk, hR, hRk, hRn, hRc, hRt, FDI.fdiCtx, Sem.inner]
  -- (`getNextLanes(root, 0, false)`: 2)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hNext1) _ h ?fr1 ?fu1) ?post1
  case fr1 => simp only [fpA]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu1 => js_side
  case post1 =>
  intro r w1 h1 ⟨hr, hF1, hfu1⟩
  subst hr
  try simp only [js_simp] at hfu1
  have hE1s : s.envs.size < w1.envs.size := envs_frame hF1 (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega) | (simp only [js_simp]; simp))
  have hG1s : d.env < w1.envs.size := envs_frame hF1 (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega) | (simp only [js_simp]; simp; omega))
  have hR1 : R < w1.heap.size := heap_frame hF1 (by simp only [js_simp]; simpa using hR)
  have hG1o : fG < w1.heap.size := heap_frame hF1 (by simp only [js_simp]; simpa using hGo)
  have hRk1 : (w1.objEntry R).kind.isPlain = true := by
    rw [objEntry_frame0 hF1 (by simp only [js_simp]; simpa using hR)]; simp only [js_simp]; simpa using hRk
  have hGk1 : (w1.objEntry fG).kind = .func dG := by
    rw [objEntry_frame0 hF1 (by simp only [js_simp]; simpa using hGo)]; simp only [js_simp]; simpa using hGk
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGIm, hGM, hGMv, hGF, hGFv, hGW, hGWv, hGL, hGLv, hGG,
    hGGv, hGP, hGPv, hGS, hGSv, hGo, hGk, hPo, hPk, hSo, hSk, hR, hRk, hRn, hRc, hRt, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, FDI.fdiCtx, Sem.inner]
  -- (`checkIfRootIsPrerendering(root, 2)`: no)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hPre) _ h1 ?fr2 ?fu2) ?post2
  case fr2 => simp only [fpA]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu2 => js_side
  case post2 =>
  intro r w2 h2 ⟨hr, hF2, hfu2⟩
  subst hr
  try simp only [js_simp] at hfu2
  have hE2s : s.envs.size < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hE1s)
  have hG2s : d.env < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hG1s)
  have hR2 : R < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact hR1)
  have hG2o : fG < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact hG1o)
  have hRk2 : (w2.objEntry R).kind.isPlain = true := by
    rw [objEntry_frame0 hF2 (by simp only [js_simp]; exact hR1)]; simp only [js_simp]; exact hRk1
  have hGk2 : (w2.objEntry fG).kind = .func dG := by
    rw [objEntry_frame0 hF2 (by simp only [js_simp]; exact hG1o)]; simp only [js_simp]; exact hGk1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGIm, hGM, hGMv, hGF, hGFv, hGW, hGWv, hGL, hGLv, hGG,
    hGGv, hGP, hGPv, hGS, hGSv, hGo, hGk, hPo, hPk, hSo, hSk, hR, hRk, hRn, hRc, hRt, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1,
    envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, FDI.fdiCtx, Sem.inner]
  -- (`performSyncWorkOnRoot(root, 2)`: the render and commit)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1, objEntry_frame0 hF2, heap_frame hF2], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hPerf) _ h2 ?fr3 ?fu3) ?post3
  case fr3 => simp only [fpA]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu3 => js_side
  case post3 =>
  intro r w3 h3 ⟨hF3, hfu3, hAft, hP3⟩
  obtain ⟨bW, bdW', bdL', lv, hW, hWW, hWWv, hWL, hWLv, hWF⟩ := hAft.record
  obtain ⟨n1, n2, n3, hRn3⟩ := hAft.next
  obtain ⟨c1, c2, c3, hRc3⟩ := hAft.cancel
  obtain ⟨t1, t2, t3, hRt3⟩ := hAft.timeout
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp only [js_simp]; exact hE2s) hfpE
  have hE3s : s.envs.size < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; exact hE2s)
  have hG3s : d.env < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; exact hG2s)
  obtain ⟨bW2, hW2, hW2x⟩ := declLike_frame hF3 (e := d.env) (o := oG)
    (by simp only [js_simp]; exact hG2s) (by js_norm [*, envEntry_frame0 hF1, envEntry_frame0 hF2]; rfl)
  have hbW : bW2 = bW := by rw [hW] at hW2; simp only [Option.some.injEq, Prod.mk.injEq] at hW2; exact hW2.1.symm
  subst hbW
  have hWG := hW2x _ hfpG
  have hWI := hW2x _ hfpI
  have hR3 : R < w3.heap.size := heap_frame hF3 (by simp only [js_simp]; exact hR2)
  have hRk3 : (w3.objEntry R).kind.isPlain = true := by
    rw [kind_frame hF3 (by simp only [js_simp]; exact hR2)]; simp only [js_simp]; exact hRk2
  have hG3 : fG < w3.heap.size := heap_frame hF3 (by simp only [js_simp]; exact hG2o)
  have hGk3 : (w3.objEntry fG).kind = .func dG := by
    rw [objEntry_frame hF3 (by simp only [js_simp]; exact hG2o) hfpO]; simp only [js_simp]; exact hGk2
  try simp only [js_simp] at hfu3
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE3, hE3s, hG3s, hW, hWW, hWWv, hWL, hWLv, hWF, hGFv, hWG, hWI, hGG, hGGv,
    hGI, hGIm, hR3, hRk3, hRn3, hRc3, hRt3, hG3, hGk3, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, FDI.fdiCtx, Sem.inner]
  -- (the second pass: `getNextLanes(root, 0, false)` finds nothing)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hNext2) w3 _ h3 hP3 ?fr4 ?fu4) ?post4
  case fr4 => simp only [fpW]; frame_go' [*, hne, Ne.symm hne]
  case fu4 => js_side
  case post4 =>
  intro r w4 h4 ⟨hr, hF4, hfu4⟩
  subst hr
  try simp only [js_simp] at hfu4
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE3, hE3s, hG3s, hW, hWW, hWWv, hWL, hWLv, hWF, hGFv, hWG, hWI, hGG, hGGv,
    hGI, hGIm, hR3, hRk3, hRn3, hRc3, hRt3, hG3, hGk3, envEntry_frame0 hF4, objEntry_frame0 hF4, heap_frame hF4,
    envs_frame hF4, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | (refine ⟨w3, h3, hP3, ?_⟩; simp only [fpW]; frame_go' [*, hne, Ne.symm hne, envEntry_frame0 hF4, objEntry_frame0 hF4, heap_frame hF4, envs_frame hF4]) | frame_go' [*, hne, Ne.symm hne, hG1, fpA, envEntry_frame0 hF4, objEntry_frame0 hF4, heap_frame hF4, envs_frame hF4]

end

end ReactFlushSync
