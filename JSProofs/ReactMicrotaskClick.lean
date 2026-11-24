import JSProofs.ReactSchedTaskRoot
import JSProofs.ReactExpiration
import JSProofs.ReactLanesPick
import JSProofs.ReactPrerender
import JSProofs.MathRules
import JSProofs.ReactFlushSync
import JSProofs.ReactProcessRoot
import JSProofs.SchedulerNow
import JSProofs.ReactMicrotask

/-!
# A click's microtask, composed (zippy docs/react-proofs.md)

Step 1: `scheduleTaskForRootDuringMicrotask` with its four reads-only callees discharged by their theorems
(`Math.clz32`, `computeExpirationTime`, `getNextLanes` with `getHighestPriorityLanes`, `checkIfRootIsPrerendering`),
each at the state of its call, its premises the start's read through the frame (only `expirationTimes[1]` and the
root's callback fields are written).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactMicrotaskClick

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

/-- 250 (ms), the sync lane's expiry. -/
abbrev ms250 : F64 := F64.fin false 8796093022208000 (-45)

theorem schedTask_click {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {tv : F64} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdC bdE bdW bdL bdG bdP bdH : Binding} {R A fC fE fG fP fH : ObjId} {dE dG dP dH : FuncData}
    {bC : BuiltinData} {wl : F64} {cp wv : Value}
    {sw se sc pw pe pc xw xe xc lw le lc cw ce cc tw te tc nw ne nc qe qc ae ac ww we wc : Bool} {L : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = STRGen.scheduleTaskForRootDuringMicrotask_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "clz32"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hGE : bG[JSStr.ofString "computeExpirationTime"]? = some bdE) (hGEv : bdE.value = some (.obj fE))
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL) (hGLv : bdL.value = some (.num wl))
    (hGG : bG[JSStr.ofString "getNextLanes"]? = some bdG) (hGGv : bdG.value = some (.obj fG))
    (hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hGH : bG[JSStr.ofString "getHighestPriorityLanes"]? = some bdH) (hGHv : bdH.value = some (.obj fH))
    (hCo : fC < s.heap.size) (hCk : (s.objEntry fC).kind = .builtin bC)
    (hCfn : eng.builtins[bC.id]? = some (ES.Builtins.Text.mathFn1 (fun x => Num.ofNat (Num.clz32 x))))
    (hEo : fE < s.heap.size) (hEk : (s.objEntry fE).kind = .func dE)
    (hEcode : dE.code = CETGen.computeExpirationTime_func) (hEcls : dE.isClassCtor = false)
    (hEmode : dE.thisMode = .strict)
    (hGo : fG < s.heap.size) (hGk : (s.objEntry fG).kind = .func dG)
    (hGcode : dG.code = GNLGen.getNextLanes_func) (hGcls : dG.isClassCtor = false) (hGmode : dG.thisMode = .strict)
    (hGenv : dG.env = d.env)
    (hHo : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = GHPGen.getHighestPriorityLanes_func) (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func) (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) (hRA : R ≠ A)
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRx : (s.objEntry R).props.get? (.str "expirationTimes") = some (.data (.obj A) xw xe xc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv ww we wc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    (hRn : (s.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc))
    (hRq : (s.objEntry R).props.get? (.str "callbackPriority") = some (.data cp true qe qc))
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array) (hAE : A ≠ fE) (hAG : A ≠ fG) (hAP : A ≠ fP)
    (hRG : R ≠ fG) (hRP : R ≠ fP) (hRE : R ≠ fE) (hAC : A ≠ fC) (hRC : R ≠ fC) (hAH : A ≠ fH) (hRH : R ≠ fH)
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) true ae ac))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) true false false))
    (hL : 1 < (Conv.toNat? L).getD 0) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj R, .num tv]) s fun v w h' =>
      v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame (ReactSchedTaskRoot.fp R A) s w ∧
      s.fuel ≤ w.fuel + 60 ∧ h' = h ∧
      (w.objEntry A).props.get? (.str "1") = some (.data (.num (numberBinOp .add tv ms250)) true ae ac) ∧
      (w.objEntry R).props.get? (.str "callbackPriority") =
        some (.data (.num (F64.fin false 4503599627370496 (-51))) true qe qc) ∧
      (w.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc) := by
  -- (reads through the frame: objects other than the root and the array as they were; the root's lanes too)
  have obj : ∀ {w : State}, Frame (ReactSchedTaskRoot.fp R A) s w → ∀ {o : ObjId}, o < s.heap.size → A ≠ o → R ≠ o →
      w.objEntry o = s.objEntry o := fun hF _ ho hA' hR' =>
    objEntry_frame hF ho (by simp [ReactSchedTaskRoot.fp, hA', hR'])
  have rk : ∀ {w : State}, Frame (ReactSchedTaskRoot.fp R A) s w → (w.objEntry R).kind.isPlain = true :=
    fun hF => by rw [kind_frame hF hR]; exact hRk
  refine ReactSchedTaskRoot.call_spec (n := n + 1) (nw := false) (tm := .num tv) (et := numberBinOp .add tv ms250) hlt hk hf hcode
    hcls hmode hG hGe hGC hGCv hGE hGEv hGW hGWv hGL hGLv hGG hGGv hGP hGPv hCo hCk hEo hEk hGo hGk hPo hPk hR hRk hRA
    hRs hRi hRx hRp hRc hRt hRn hRq hA hAk hAE hAG hAP hRG hRP hA1 hAL hL ?clz ?exp ?next ?pre
  case clz =>
    intro w h1 hF hfu
    refine wp_mono (mathFn1_spec (heap_frame hF hCo) (by rw [obj hF hCo hAC hRC]; exact hCk) hCfn (by omega)) ?_
    rintro r w' h' ⟨hv, hF', hfu', hh'⟩
    exact ⟨by rw [hv, clz32_two], hF', by omega, hh'⟩
  case exp =>
    intro w h1 hF hfu
    exact ReactExpiration.call_spec (heap_frame hF hEo) (by rw [obj hF hEo hAE hRE]; exact hEk) (by omega) hEcode
      hEcls hEmode
  case next =>
    intro w h1 hF hfu
    have hGw : w.envEntry d.env = s.envEntry d.env := envEntry_frame hF hG (by simp [ReactSchedTaskRoot.fp])
    exact ReactLanesPick.next_click (heap_frame hF hGo) (by rw [obj hF hGo hAG hRG]; exact hGk) (by omega) hGcode
      hGcls hGmode (by rw [hGenv]; exact envs_frame hF hG) (by rw [hGenv, hGw]; exact hGe) hGH hGHv
      (heap_frame hF hHo) (by rw [obj hF hHo hAH hRH]; exact hHk) hHcode hHcls hHmode (heap_frame hF hR) (rk hF)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRp)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRs)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRi)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRw)
  case pre =>
    intro w h1 hF hfu
    exact ReactPrerender.call_spec (heap_frame hF hPo) (by rw [obj hF hPo hAP hRP]; exact hPk) (by omega) hPcode
      hPcls hPmode (heap_frame hF hR) (rk hF)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRp)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRs)
      (by rw [props_frame hF hR (by simp [ReactSchedTaskRoot.fp, hRA])]; exact hRi)

/-- After the work, what the second pass needs: `getNextLanes` still that function, the root with nothing pending. -/
def AfterWork (w : State) (R fG : ObjId) (dG : FuncData) : Prop :=
  fG < w.heap.size ∧ (w.objEntry fG).kind = .func dG ∧ R < w.heap.size ∧ (w.objEntry R).kind.isPlain = true ∧
    ∃ a b c, (w.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) a b c)

/-- **Step 2**: `flushSyncWorkAcrossRoots_impl(0, false)` after a click, its `getNextLanes` (both passes) and
`checkIfRootIsPrerendering` by their theorems; the work (`performSyncWorkOnRoot(root, 2)`) a hypothesis, which now also
leaves the root with no pending lanes. -/
theorem flush_click {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdI bdM bdF bdW bdL bdG bdP bdS bdH : Binding} {lv0 wv : Value} {R fG fP fS fH : ObjId} {dG dP dS dH : FuncData}
    {nw ne nc cw ce cc tw te tc lw le lc sw se sc pw pe pc ww we wc : Bool} {fpP : Footprint} {kP : Nat}
    {Pu : State → σ → Prop}
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
    (hGH : bG[JSStr.ofString "getHighestPriorityLanes"]? = some bdH) (hGHv : bdH.value = some (.obj fH))
    (hGo : fG < s.heap.size) (hGk : (s.objEntry fG).kind = .func dG)
    (hGcode : dG.code = GNLGen.getNextLanes_func) (hGcls : dG.isClassCtor = false) (hGmode : dG.thisMode = .strict)
    (hGenv : dG.env = d.env)
    (hHo : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = GHPGen.getHighestPriorityLanes_func) (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func) (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null nw ne nc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv ww we wc))
    (hPerf : ∀ w h1, Frame (ReactFlushSync.fpA d.env) s w → HI h1 → (∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧ ∃ bd, bm[JSStr.ofString "isFlushingWork"]? = some bd ∧ bd.value = some (.bool true)) → s.fuel ≤ w.fuel + 60 →
      WP eng answer (n + 1) h1
        (callImpl eng (.obj fS) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w
        fun _ w' h' => Frame fpP w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactFlushSync.After w' d.env oG R bdF ∧
          (∃ a b c, (w'.objEntry R).props.get? (.str "pendingLanes") =
            some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w' h' ∧ HI h')
    (hfpE : fpP.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpG : (d.env, JSStr.ofString "getNextLanes") ∉ fpP.binds)
    (hfpI : (d.env, JSStr.ofString "isFlushingWork") ∉ fpP.binds)
    (hfpO : fpP.props.all (fun q => q.1 != fG) = true) (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t
        #[.num (F64.fin false 0 (-1074)), .bool false]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨(d.env, JSStr.ofString "isFlushingWork") :: fpP.binds, fpP.props, fpP.jobs⟩ s w ∧
      s.fuel ≤ w.fuel + kP + 200 ∧ (∃ w2 h2, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW s.envs.size d.env) w2 w) ∧
      HI h' := by
  have hGw : ∀ {w : State}, Frame (ReactFlushSync.fpA d.env) s w → ∀ {o : ObjId}, o < s.heap.size →
      w.objEntry o = s.objEntry o := fun hF _ ho => objEntry_frame hF ho (by simp [ReactFlushSync.fpA])
  refine wp_mono (ReactFlushSync.call_spec (n := n + 1) (P := fun w h => AfterWork w R fG dG ∧ Pu w h)
    hlt hk hf hcode hcls hmode hG hGe hGI hGIv hGIm hGM hGMv hGF hGFv hGW hGWv hGL hGLv hGG hGGv hGP hGPv hGS hGSv
    hGo hGk hPo hPk hSo hSk hR hRk hRn hRc hRt ?n1 ?pre ?perf hfpE hfpG hfpI hfpO ?n2 hHI) ?post
  case n1 =>
    intro w h1 hF hfu
    obtain ⟨bW, hW, hWx⟩ := declLike_frame hF hG hGe
    exact ReactLanesPick.next_click (heap_frame hF hGo) (by rw [hGw hF hGo]; exact hGk) (by omega) hGcode hGcls
      hGmode (by rw [hGenv]; exact envs_frame hF hG) (by rw [hGenv]; exact hW)
      (by rw [hWx _ (by simp [ReactFlushSync.fpA])]; exact hGH) hGHv (heap_frame hF hHo)
      (by rw [hGw hF hHo]; exact hHk) hHcode hHcls hHmode (heap_frame hF hR) (by rw [hGw hF hR]; exact hRk)
      (by rw [hGw hF hR]; exact hRp) (by rw [hGw hF hR]; exact hRs) (by rw [hGw hF hR]; exact hRi)
      (by rw [hGw hF hR]; exact hRw)
  case pre =>
    intro w h1 hF hfu
    exact ReactPrerender.call_spec (heap_frame hF hPo) (by rw [hGw hF hPo]; exact hPk) (by omega) hPcode hPcls hPmode
      (heap_frame hF hR) (by rw [hGw hF hR]; exact hRk) (by rw [hGw hF hR]; exact hRp) (by rw [hGw hF hR]; exact hRs)
      (by rw [hGw hF hR]; exact hRi)
  case perf =>
    intro w h1 hF hHI1 hIF hfu
    refine wp_mono (hPerf w h1 hF hHI1 hIF hfu) fun _ w' h' ⟨hF', hfu', hA, ⟨a, b, c, hp0⟩, hPu, hHI'⟩ =>
      ⟨hF', hfu', hA, ⟨?_, hPu⟩, hHI'⟩
    have hGo' : fG < w.heap.size := heap_frame hF hGo
    have hRo' : R < w.heap.size := heap_frame hF hR
    refine ⟨heap_frame hF' hGo', ?_, heap_frame hF' hRo', ?_, a, b, c, hp0⟩
    · rw [objEntry_frame hF' hGo' hfpO, hGw hF hGo]; exact hGk
    · rw [kind_frame hF' hRo', hGw hF hR]; exact hRk
  case n2 =>
    intro w2 w h1 ⟨⟨hGo2, hGk2, hR2, hRk2, a, b, c, hp0⟩, _⟩ hF hfu
    have hW : ∀ {o : ObjId}, o < w2.heap.size → w.objEntry o = w2.objEntry o := fun ho =>
      objEntry_frame hF ho (by simp [ReactFlushSync.fpW])
    exact wp_mono (ReactLanesPick.next_none (heap_frame hF hGo2) (by rw [hW hGo2]; exact hGk2) (by omega) hGcode
      hGcls hGmode (heap_frame hF hR2) (by rw [hW hR2]; exact hRk2) (by rw [hW hR2]; exact hp0))
      fun r w' h' ⟨hv, hF', hfu', hh'⟩ => ⟨hv, hF', by omega, hh'⟩
  case post =>
    intro v w h' ⟨hv, hFr, hfu, ⟨w2, h2, ⟨_, hPu⟩, hF2⟩, hHI'⟩
    exact ⟨hv, hFr, hfu, ⟨w2, h2, hPu, hF2⟩, hHI'⟩

/-- What the microtask writes before the work: the two flags, the lane's expiration time, the root's callback. -/
def fpPre (g : EnvId) (R A : ObjId) : Footprint :=
  ⟨[(g, "mightHavePendingSyncWork"), (g, "didScheduleMicrotask")], (ReactSchedTaskRoot.fp R A).props, false⟩

/-- … and the flag the flush sets. -/
def fpPerf (g : EnvId) (R A : ObjId) : Footprint :=
  ⟨[(g, "mightHavePendingSyncWork"), (g, "didScheduleMicrotask"), (g, "isFlushingWork")],
    (ReactSchedTaskRoot.fp R A).props, false⟩

/-- What the task scheduling leaves on the root: its expiration time, callback priority and node, writable. -/
def SchedOut (w : State) (R A : ObjId) : Prop :=
  (∃ v e c, (w.objEntry A).props.get? (.str "1") = some (.data v true e c)) ∧
  (∃ v e c, (w.objEntry R).props.get? (.str "callbackPriority") = some (.data v true e c)) ∧
  (∃ v e c, (w.objEntry R).props.get? (.str "callbackNode") = some (.data v true e c))

/-- Where the microtask starts the work: the flag set, the task scheduling's fields. -/
def MicroFacts (w : State) (g : EnvId) (oG : Option EnvId) (R A : ObjId) : Prop :=
  (∃ bm, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧ ∃ bd, bm[JSStr.ofString "isFlushingWork"]? = some bd ∧
    bd.value = some (.bool true)) ∧ SchedOut w R A ∧
  (∃ bm, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧
    (∃ bd, bm[JSStr.ofString "mightHavePendingSyncWork"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
    (∃ bd, bm[JSStr.ofString "didScheduleMicrotask"]? = some bd ∧ bd.mutable = true ∧ bd.value = some (.bool false)))

/-- **Step 3**: `processRootScheduleInMicrotask` after a click, every callee by its theorem: `now` (the scheduler's
`unstable_now`; the host's `performance.now()` a hypothesis), `scheduleTaskForRootDuringMicrotask` (step 1),
`flushSyncWorkAcrossRoots_impl` (step 2). Left: the host's clock and the work (`performSyncWorkOnRoot(root, 2)`),
stated from the microtask's start. -/
theorem processRoot_click {m : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdM bdD bdC bdF bdN bdT bdP0 bdL bdI bdW bdRL bdCz bdE bdG bdPr bdH bdS : Binding}
    {R A fN fT fL fC fE fG fP fH fS : ObjId} {dN dT dL dE dG dP dH dS : FuncData} {bC : BuiltinData} {wl : F64}
    -- (the scheduler's module: `localPerformance`)
    {gS : EnvId} {bS : HashMap JSStr Binding} {oS : Option EnvId} {bdLP : Binding} {Pf PfP fPN : ObjId}
    {bPN : BuiltinData} {pfw pfe pfc : Bool} {tm : F64}
    {cp wv : Value} {rw re rc sw se sc pw pe pc xw xe xc lw le lc cw ce cc tw te tc ne nc qe qc ae ac ww we wc : Bool}
    {L : F64} {fpP : Footprint} {kP : Nat} {Pu : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : kP + 1000 ≤ s.fuel)
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
    (hGP0 : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdP0)
    (hGP0v : bdP0.value = some (.num (F64.fin false 0 (-1074))))
    (hGL : bG[JSStr.ofString "flushSyncWorkAcrossRoots_impl"]? = some bdL) (hGLv : bdL.value = some (.obj fL))
    (hGI : bG[JSStr.ofString "isFlushingWork"]? = some bdI) (hGIv : bdI.value = some (.bool false))
    (hGIm : bdI.mutable = true)
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGRL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdRL) (hGRLv : bdRL.value = some (.num wl))
    (hGCz : bG[JSStr.ofString "clz32"]? = some bdCz) (hGCzv : bdCz.value = some (.obj fC))
    (hGE : bG[JSStr.ofString "computeExpirationTime"]? = some bdE) (hGEv : bdE.value = some (.obj fE))
    (hGG : bG[JSStr.ofString "getNextLanes"]? = some bdG) (hGGv : bdG.value = some (.obj fG))
    (hGPr : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdPr) (hGPrv : bdPr.value = some (.obj fP))
    (hGH : bG[JSStr.ofString "getHighestPriorityLanes"]? = some bdH) (hGHv : bdH.value = some (.obj fH))
    (hGS : bG[JSStr.ofString "performSyncWorkOnRoot"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    -- (the functions)
    (hNo : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .func dN) (hNcode : dN.code = NOWGen.fn0_func)
    (hNcls : dN.isClassCtor = false) (hNmode : dN.thisMode = .strict) (hNenv : dN.env = gS)
    (hTo : fT < s.heap.size) (hTk : (s.objEntry fT).kind = .func dT)
    (hTcode : dT.code = STRGen.scheduleTaskForRootDuringMicrotask_func) (hTcls : dT.isClassCtor = false)
    (hTmode : dT.thisMode = .strict) (hTenv : dT.env = d.env)
    (hLo : fL < s.heap.size) (hLk : (s.objEntry fL).kind = .func dL)
    (hLcode : dL.code = FSWGen.flushSyncWorkAcrossRoots_impl_func) (hLcls : dL.isClassCtor = false)
    (hLmode : dL.thisMode = .strict) (hLenv : dL.env = d.env)
    (hCo : fC < s.heap.size) (hCk : (s.objEntry fC).kind = .builtin bC)
    (hCfn : eng.builtins[bC.id]? = some (ES.Builtins.Text.mathFn1 (fun x => Num.ofNat (Num.clz32 x))))
    (hEo : fE < s.heap.size) (hEk : (s.objEntry fE).kind = .func dE)
    (hEcode : dE.code = CETGen.computeExpirationTime_func) (hEcls : dE.isClassCtor = false)
    (hEmode : dE.thisMode = .strict)
    (hGo : fG < s.heap.size) (hGk : (s.objEntry fG).kind = .func dG)
    (hGcode : dG.code = GNLGen.getNextLanes_func) (hGcls : dG.isClassCtor = false) (hGmode : dG.thisMode = .strict)
    (hGenv : dG.env = d.env)
    (hHo : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = GHPGen.getHighestPriorityLanes_func) (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func) (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    -- (the scheduler's clock)
    (hgS : gS < s.envs.size) (hgSg : gS ≠ d.env) (hSe : Scope.declLike? (s.envEntry gS) = some (bS, oS))
    (hSLP : bS[JSStr.ofString "localPerformance"]? = some bdLP) (hSLPv : bdLP.value = some (.obj Pf))
    (hPf : Pf < s.heap.size) (hPfk : (s.objEntry Pf).kind.isPlain = true)
    (hPfn0 : (s.objEntry Pf).props.get? (.str "now") = none) (hPfp : (s.objEntry Pf).proto = .obj PfP)
    (hPfP : PfP < s.heap.size) (hPfPk : (s.objEntry PfP).kind.isPlain = true)
    (hPfn : (s.objEntry PfP).props.get? (.str "now") = some (.data (.obj fPN) pfw pfe pfc))
    (hPNo : fPN < s.heap.size) (hPNk : (s.objEntry fPN).kind = .builtin bPN)
    (hClock : ∀ w, Frame (ReactProcessRoot.fpA d.env) s w →
      SchedulerNow.HostReads eng answer HI (m + 1) fPN (.obj Pf) #[] (.num tm) w 5)
    -- (the root and its expiration times)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) (hRA : R ≠ A)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null rw re rc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRx : (s.objEntry R).props.get? (.str "expirationTimes") = some (.data (.obj A) xw xe xc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv ww we wc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    (hRnode : (s.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc))
    (hRq : (s.objEntry R).props.get? (.str "callbackPriority") = some (.data cp true qe qc))
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) true ae ac))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) true false false))
    (hL : 1 < (Conv.toNat? L).getD 0)
    (hAE : A ≠ fE) (hAG : A ≠ fG) (hAP : A ≠ fP) (hAC : A ≠ fC) (hAH : A ≠ fH) (hAS : A ≠ fS) (hAF : A ≠ fL)
    (hRG : R ≠ fG) (hRP : R ≠ fP) (hRE : R ≠ fE) (hRC : R ≠ fC) (hRH : R ≠ fH) (hRS : R ≠ fS) (hRF : R ≠ fL)
    -- (the work: `performSyncWorkOnRoot(root, 2)`, from any state framed from the start by what came before)
    (hPerf : ∀ w h1, Frame (fpPerf d.env R A) s w → HI h1 → MicroFacts w d.env oG R A → s.fuel ≤ w.fuel + 400 →
      WP eng answer (m + 1) h1
        (callImpl eng (.obj fS) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w
        fun _ w' h' => Frame fpP w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactFlushSync.After w' d.env oG R bdF ∧
          (∃ a b c, (w'.objEntry R).props.get? (.str "pendingLanes") =
            some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w' h' ∧ HI h')
    (hfpB : fpP.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hfpG : (d.env, JSStr.ofString "getNextLanes") ∉ fpP.binds)
    (hfpI : (d.env, JSStr.ofString "isFlushingWork") ∉ fpP.binds)
    (hfpC : (d.env, JSStr.ofString "currentEventTransitionLane") ∉ fpP.binds)
    (hfpO : fpP.props.all (fun q => q.1 != fG) = true) (hHI : HI h) :
    WP eng answer (m + 3) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ (∃ w2 h2 e, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW e d.env) w2 w) ∧ HI h' := by
  have hne : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  -- (before the work: objects as they were through `fpA`)
  have objA : ∀ {w : State}, Frame (ReactProcessRoot.fpA d.env) s w → ∀ {o : ObjId}, o < s.heap.size →
      w.objEntry o = s.objEntry o := fun hF _ ho => objEntry_frame hF ho (by simp [ReactProcessRoot.fpA])
  refine wp_mono (ReactProcessRoot.call_spec (n := m + 2) (L := F64.fin false 4503599627370496 (-51))
    (fpT := ReactSchedTaskRoot.fp R A) (fpF := ⟨(d.env, JSStr.ofString "isFlushingWork") :: fpP.binds, fpP.props, fpP.jobs⟩)
    (kF := kP + 200) (P := fun w _ => Frame (fpPre d.env R A) s w ∧ SchedOut w R A)
    (Q := fun x _ => ∃ w2 h2 e, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW e d.env) w2 x)
    hlt hk (by omega) hcode hcls hmode hG hGe hGM hGMm hGMv hGD hGDm hGDv hGC hGCv hGF hGFv hGN hGNv hGT hGTv hGP0
    hGP0v hGL hGLv hNo hNk hTo hTk hLo hLk hR hRk hRn (by decide) (by decide) ?now ?task
    (by simp [ReactSchedTaskRoot.fp]) (by simp [ReactSchedTaskRoot.fp]) (by simp [ReactSchedTaskRoot.fp])
    (by simp [ReactSchedTaskRoot.fp]) (by simp [ReactSchedTaskRoot.fp]) (by simp [ReactSchedTaskRoot.fp])
    (by simp [ReactSchedTaskRoot.fp, hAF, hRF]) ?flush
    (by simp only [List.all_cons, binds_avoid hfpB (Nat.le_refl _), Bool.and_true]; simp [hne])
    (by simp [hfpC]) hHI) fun v w h' ⟨hv, hq, hHI'⟩ => ⟨hv, hq, hHI'⟩
  case now =>
    intro w h1 hF hHI1 hfu
    have hgSw : w.envEntry gS = s.envEntry gS := envEntry_frame hF hgS (by simp [ReactProcessRoot.fpA, Ne.symm hgSg])
    exact wp_mono (SchedulerNow.call_spec (n := m + 1) (heap_frame hF hNo) (by rw [objA hF hNo]; exact hNk) (by omega)
      hNcode hNcls hNmode (by rw [hNenv]; exact envs_frame hF hgS) (by rw [hNenv, hgSw]; exact hSe) hSLP hSLPv
      (heap_frame hF hPf) (by rw [objA hF hPf]; exact hPfk) (by rw [objA hF hPf]; exact hPfn0) (by rw [objA hF hPf]; exact hPfp)
      (heap_frame hF hPfP) (by rw [objA hF hPfP]; exact hPfPk) (by rw [objA hF hPfP]; exact hPfn) (heap_frame hF hPNo)
      (by rw [objA hF hPNo]; exact hPNk) (hClock w hF) hHI1) fun r w' h' ⟨hv, hF', hfu', hHI'⟩ => ⟨⟨tm, hv⟩, hF', hfu', hHI'⟩
  case task =>
    intro w h1 tv hF hHI1 hfu
    obtain ⟨bW, hW, hWx⟩ := declLike_frame hF hG hGe
    have b : ∀ {x : JSStr}, (d.env, x) ∉ (ReactProcessRoot.fpA d.env).binds → bW[x]? = bG[x]? := fun hx => hWx _ hx
    have rp : ∀ {k : PropKey}, (w.objEntry R).props.get? k = (s.objEntry R).props.get? k := by
      intro k; rw [objA hF hR]
    exact wp_mono (schedTask_click (n := m) (tv := tv) (bG := bW) (oG := oG) (ae := ae) (ac := ac) (qe := qe)
      (qc := qc) (ne := ne) (nc := nc) (sw := sw) (se := se) (sc := sc) (pw := pw) (pe := pe) (pc := pc) (xw := xw)
      (xe := xe) (xc := xc) (lw := lw) (le := le) (lc := lc) (cw := cw) (ce := ce) (cc := cc) (tw := tw) (te := te)
      (tc := tc) (ww := ww) (we := we) (wc := wc) (wv := wv) (cp := cp) (L := L) (wl := wl) (nw := false)
      (hlt := heap_frame hF hTo) (hk := by rw [objA hF hTo]; exact hTk) (hf := by omega) (hcode := hTcode)
      (hcls := hTcls) (hmode := hTmode) (hG := by rw [hTenv]; exact envs_frame hF hG) (hGe := by rw [hTenv]; exact hW)
      (hGC := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGCz) (hGCv := hGCzv)
      (hGE := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGE) (hGEv := hGEv)
      (hGW := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGW) (hGWv := hGWv)
      (hGL := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGRL) (hGLv := hGRLv)
      (hGG := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGG) (hGGv := hGGv)
      (hGP := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGPr) (hGPv := hGPrv)
      (hGH := by rw [b (by simp [ReactProcessRoot.fpA, js_simp])]; exact hGH) (hGHv := hGHv)
      (hCo := heap_frame hF hCo) (hCk := by rw [objA hF hCo]; exact hCk) (hCfn := hCfn)
      (hEo := heap_frame hF hEo) (hEk := by rw [objA hF hEo]; exact hEk) (hEcode := hEcode) (hEcls := hEcls)
      (hEmode := hEmode) (hGo := heap_frame hF hGo) (hGk := by rw [objA hF hGo]; exact hGk) (hGcode := hGcode)
      (hGcls := hGcls) (hGmode := hGmode) (hGenv := by rw [hGenv, hTenv]) (hHo := heap_frame hF hHo)
      (hHk := by rw [objA hF hHo]; exact hHk) (hHcode := hHcode) (hHcls := hHcls) (hHmode := hHmode)
      (hPo := heap_frame hF hPo) (hPk := by rw [objA hF hPo]; exact hPk) (hPcode := hPcode) (hPcls := hPcls)
      (hPmode := hPmode) (hR := heap_frame hF hR) (hRk := by rw [objA hF hR]; exact hRk) (hRA := hRA)
      (hRs := by rw [rp]; exact hRs) (hRi := by rw [rp]; exact hRi) (hRx := by rw [rp]; exact hRx)
      (hRp := by rw [rp]; exact hRp) (hRw := by rw [rp]; exact hRw) (hRc := by rw [rp]; exact hRc)
      (hRt := by rw [rp]; exact hRt) (hRn := by rw [rp]; exact hRnode) (hRq := by rw [rp]; exact hRq)
      (hA := heap_frame hF hA) (hAk := by rw [objA hF hA]; exact hAk) (hAE := hAE) (hAG := hAG) (hAP := hAP)
      (hRG := hRG) (hRP := hRP) (hRE := hRE) (hAC := hAC) (hRC := hRC) (hAH := hAH) (hRH := hRH)
      (hA1 := by rw [objA hF hA]; exact hA1) (hAL := by rw [objA hF hA]; exact hAL) (hL := hL))
      fun v w' h' ⟨hv, hF', hfu', hh', hA1', hCP', hCN'⟩ => ⟨hv, hF', hfu', ⟨by
        have := frame_trans hF hF'
        simpa [Footprint.union, ReactProcessRoot.fpA, ReactSchedTaskRoot.fp, fpPre] using this,
        ⟨_, _, _, hA1'⟩, ⟨_, _, _, hCP'⟩, ⟨_, _, _, hCN'⟩⟩, by rw [hh']; exact hHI1⟩
  case flush =>
    intro w2 w h1 ⟨hP2, ⟨⟨av, ae', ac', hA1s⟩, ⟨pv, pe', pc', hCPs⟩, ⟨nv, ne', nc', hCNs⟩⟩⟩ hHI1 hF2 ⟨bm, hbm, hmt, ⟨bdM2, hbdM2, hbdM2m⟩, ⟨bdD2, hbdD2, hbdD2m, hbdD2v⟩⟩ hfu
    have hFs := frame_trans hP2 hF2
    have hA2 : A < w2.heap.size := heap_frame hP2 hA
    have hR2 : R < w2.heap.size := heap_frame hP2 hR
    obtain ⟨bW, hW, hWx⟩ := declLike_frame hFs hG hGe
    have hbmW : bm = bW := by rw [hW] at hbm; simp only [Option.some.injEq, Prod.mk.injEq] at hbm; exact hbm.1.symm
    subst hbmW
    obtain ⟨bdM', hGM', hGMv'⟩ : ∃ bd, bm[JSStr.ofString "mightHavePendingSyncWork"]? = some bd ∧
        bd.value = some (.bool true) := by
      cases hx : bm[JSStr.ofString "mightHavePendingSyncWork"]? with
      | none => rw [hx] at hmt; simp at hmt
      | some bd => rw [hx] at hmt; exact ⟨bd, rfl, by simpa using hmt⟩
    have b : ∀ {x : JSStr}, (d.env, x) ∉ ((fpPre d.env R A).union ⟨[(d.env, "mightHavePendingSyncWork"),
        (s.envs.size, "nextLanes"), (s.envs.size, "prev"), (s.envs.size, "root")], [], false⟩).binds →
        bm[x]? = bG[x]? := fun hx => hWx _ hx
    have obj : ∀ {o : ObjId}, o < s.heap.size → A ≠ o → R ≠ o → w.objEntry o = s.objEntry o := fun ho hA' hR' =>
      objEntry_frame hFs ho (by simp [Footprint.union, fpPre, ReactSchedTaskRoot.fp, hA', hR'])
    have rp : ∀ {k : JSStr}, k ≠ JSStr.ofString "callbackPriority" → k ≠ JSStr.ofString "callbackNode" →
        (w.objEntry R).props.get? (.str k) = (s.objEntry R).props.get? (.str k) := fun h1 h2 =>
      props_frame hFs hR (by simp [Footprint.union, fpPre, ReactSchedTaskRoot.fp, hRA, h1, h2])
    have hle : s.envs.size ≤ w.envs.size := hFs.envs_le
    refine wp_mono (flush_click (n := m) (d := dL) (bG := bm) (oG := oG) (Pu := Pu) (fpP := fpP) (kP := kP)
      (lv0 := .num wl) (nw := rw) (ne := re) (nc := rc) (cw := cw) (ce := ce) (cc := cc) (tw := tw) (te := te) (tc := tc)
      (lw := lw) (le := le) (lc := lc) (sw := sw) (se := se) (sc := sc) (pw := pw) (pe := pe) (pc := pc) (wv := wv)
      (ww := ww) (we := we) (wc := wc)
      (hlt := heap_frame hFs hLo) (hk := by rw [obj hLo hAF hRF]; exact hLk) (hf := by omega) (hcode := hLcode)
      (hcls := hLcls) (hmode := hLmode) (hG := by rw [hLenv]; exact envs_frame hFs hG) (hGe := by rw [hLenv]; exact hW)
      (hGI := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGI) (hGIv := hGIv)
      (hGIm := hGIm) (hGM := hGM') (hGMv := hGMv')
      (hGF := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGF) (hGFv := hGFv)
      (hGW := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGW) (hGWv := hGWv)
      (hGL := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGRL) (hGLv := hGRLv)
      (hGG := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGG) (hGGv := hGGv)
      (hGP := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGPr) (hGPv := hGPrv)
      (hGS := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGS) (hGSv := hGSv)
      (hGH := by rw [b (by simp [Footprint.union, fpPre, hne, js_simp])]; exact hGH) (hGHv := hGHv)
      (hGo := heap_frame hFs hGo) (hGk := by rw [obj hGo hAG hRG]; exact hGk) (hGcode := hGcode) (hGcls := hGcls)
      (hGmode := hGmode) (hGenv := by rw [hGenv, hLenv]) (hHo := heap_frame hFs hHo)
      (hHk := by rw [obj hHo hAH hRH]; exact hHk) (hHcode := hHcode) (hHcls := hHcls) (hHmode := hHmode)
      (hPo := heap_frame hFs hPo) (hPk := by rw [obj hPo hAP hRP]; exact hPk) (hPcode := hPcode) (hPcls := hPcls)
      (hPmode := hPmode) (hSo := heap_frame hFs hSo) (hSk := by rw [obj hSo hAS hRS]; exact hSk)
      (hR := heap_frame hFs hR) (hRk := by rw [kind_frame hFs hR]; exact hRk)
      (hRn := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRn)
      (hRc := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRc)
      (hRt := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRt)
      (hRp := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRp)
      (hRs := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRs)
      (hRi := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRi)
      (hRw := by rw [rp (by simp [js_simp]) (by simp [js_simp])]; exact hRw)
      (hPerf := ?perf) (hfpE := binds_avoid hfpB hle) (hfpG := by rw [hLenv]; exact hfpG)
      (hfpI := by rw [hLenv]; exact hfpI) (hfpO := hfpO) (hHI := hHI1)) ?post
    case perf =>
      intro w' h1' hF' hHI' hIF hfu'
      rw [hLenv] at hF' hIF ⊢
      have hAw : (w'.objEntry A) = w2.objEntry A := by
        rw [hF'.obj_eq _ (heap_frame hF2 hA2) (fun _ hk => by simp [ReactFlushSync.fpA] at hk), hF2.obj_eq _ hA2 (fun _ hk => by simp at hk)]
      have hRw : (w'.objEntry R) = w2.objEntry R := by
        rw [hF'.obj_eq _ (heap_frame hF2 hR2) (fun _ hk => by simp [ReactFlushSync.fpA] at hk), hF2.obj_eq _ hR2 (fun _ hk => by simp at hk)]
      refine hPerf w' h1' ?_ hHI' ⟨hIF, ⟨⟨_, _, _, by rw [hAw]; exact hA1s⟩, ⟨_, _, _, by rw [hRw]; exact hCPs⟩,
        ⟨_, _, _, by rw [hRw]; exact hCNs⟩⟩, ?flags⟩ (by omega)
      case flags =>
        obtain ⟨bF, hbF, hbFx⟩ := declLike_frame hF' (envs_frame hFs hG) (by first | exact hW | (rw [hLenv] at hW; exact hW) | (rw [← hLenv]; exact hW))
        have hmv : bdM2.value.isSome = true := by rw [hbdM2] at hmt; simp at hmt; simp [hmt]
        exact ⟨bF, hbF, ⟨bdM2, by rw [hbFx _ (by simp [ReactFlushSync.fpA])]; exact hbdM2, hbdM2m, hmv⟩,
          ⟨bdD2, by rw [hbFx _ (by simp [ReactFlushSync.fpA])]; exact hbdD2, hbdD2m, hbdD2v⟩⟩
      refine frame_drop (frame_trans hFs hF') (fun q hq hq' => ?_) (fun q hq _ => by
        simpa [Footprint.union, fpPre, fpPerf, ReactFlushSync.fpA] using hq) (fun _ => rfl)
      simp only [Footprint.union, fpPre, ReactFlushSync.fpA, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_nil_iff, or_false, fpPerf] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd hq' (Nat.lt_irrefl _) | simp | (simp only [] at hq'; omega)
    case post =>
      intro v w' h' ⟨_, hFr, hfu', ⟨w3, h3, hPu, hF3⟩, hHI'⟩
      refine ⟨by rw [hLenv] at hFr; exact hFr, by omega, ⟨w3, h3, w.envs.size, hPu, ?_⟩, hHI'⟩
      rw [hLenv] at hF3
      exact frame_restore hF3 s

/-- **Step 4: the microtask**, the job a click queued: React's callback, `processRootScheduleInMicrotask` and every
callee by its theorem. Left: the host's clock and the work (`performSyncWorkOnRoot(root, 2)`), stated from the
microtask's start. -/
theorem microtask_click {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop} {m : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdM bdD bdC bdF bdN bdT bdP0 bdL bdI bdW bdRL bdCz bdE bdG bdPr bdH bdS : Binding} {R A fN fT fL fC fE fG fP fH fS : ObjId} {dN dT dL dE dG dP dH dS : FuncData} {bC : BuiltinData} {wl : F64} {gS : EnvId} {bS : HashMap JSStr Binding} {oS : Option EnvId} {bdLP : Binding} {Pf PfP fPN : ObjId} {bPN : BuiltinData} {pfw pfe pfc : Bool} {tm : F64} {cp wv : Value} {rw re rc sw se sc pw pe pc xw xe xc lw le lc cw ce cc tw te tc ne nc qe qc ae ac ww we wc : Bool} {L : F64} {fpP : Footprint} {kP : Nat} {Pu : State → σ → Prop} {c : ObjId} {e : EnvId} {bdX bdPRS : Binding} {ec : F64}
    (hcb : ReactSchedTask.Callback s c e d.env)
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX) (hGXv : bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)))) = true)
    (hGPRS : bG[JSStr.ofString "processRootScheduleInMicrotask"]? = some bdPRS) (hGPRSv : bdPRS.value = some (.obj fo))
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hf : kP + 1010 ≤ s.fuel)
    (hcode : d.code = PRSGen.processRootScheduleInMicrotask_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM)
    (hGMm : bdM.mutable = true)
    (hGMv : bdM.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD)
    (hGDm : bdD.mutable = true)
    (hGDv : bdD.value.isSome = true)
    (hGC : bG[JSStr.ofString "currentEventTransitionLane"]? = some bdC)
    (hGCv : bdC.value = some (.num (F64.fin false 0 (-1074))))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF)
    (hGFv : bdF.value = some (.obj R))
    (hGN : bG[JSStr.ofString "now"]? = some bdN)
    (hGNv : bdN.value = some (.obj fN))
    (hGT : bG[JSStr.ofString "scheduleTaskForRootDuringMicrotask"]? = some bdT)
    (hGTv : bdT.value = some (.obj fT))
    (hGP0 : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdP0)
    (hGP0v : bdP0.value = some (.num (F64.fin false 0 (-1074))))
    (hGL : bG[JSStr.ofString "flushSyncWorkAcrossRoots_impl"]? = some bdL)
    (hGLv : bdL.value = some (.obj fL))
    (hGI : bG[JSStr.ofString "isFlushingWork"]? = some bdI)
    (hGIv : bdI.value = some (.bool false))
    (hGIm : bdI.mutable = true)
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW)
    (hGWv : bdW.value = some .null)
    (hGRL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdRL)
    (hGRLv : bdRL.value = some (.num wl))
    (hGCz : bG[JSStr.ofString "clz32"]? = some bdCz)
    (hGCzv : bdCz.value = some (.obj fC))
    (hGE : bG[JSStr.ofString "computeExpirationTime"]? = some bdE)
    (hGEv : bdE.value = some (.obj fE))
    (hGG : bG[JSStr.ofString "getNextLanes"]? = some bdG)
    (hGGv : bdG.value = some (.obj fG))
    (hGPr : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdPr)
    (hGPrv : bdPr.value = some (.obj fP))
    (hGH : bG[JSStr.ofString "getHighestPriorityLanes"]? = some bdH)
    (hGHv : bdH.value = some (.obj fH))
    (hGS : bG[JSStr.ofString "performSyncWorkOnRoot"]? = some bdS)
    (hGSv : bdS.value = some (.obj fS))
    (hNo : fN < s.heap.size)
    (hNk : (s.objEntry fN).kind = .func dN)
    (hNcode : dN.code = NOWGen.fn0_func)
    (hNcls : dN.isClassCtor = false)
    (hNmode : dN.thisMode = .strict)
    (hNenv : dN.env = gS)
    (hTo : fT < s.heap.size)
    (hTk : (s.objEntry fT).kind = .func dT)
    (hTcode : dT.code = STRGen.scheduleTaskForRootDuringMicrotask_func)
    (hTcls : dT.isClassCtor = false)
    (hTmode : dT.thisMode = .strict)
    (hTenv : dT.env = d.env)
    (hLo : fL < s.heap.size)
    (hLk : (s.objEntry fL).kind = .func dL)
    (hLcode : dL.code = FSWGen.flushSyncWorkAcrossRoots_impl_func)
    (hLcls : dL.isClassCtor = false)
    (hLmode : dL.thisMode = .strict)
    (hLenv : dL.env = d.env)
    (hCo : fC < s.heap.size)
    (hCk : (s.objEntry fC).kind = .builtin bC)
    (hCfn : eng.builtins[bC.id]? = some (ES.Builtins.Text.mathFn1 (fun x => Num.ofNat (Num.clz32 x))))
    (hEo : fE < s.heap.size)
    (hEk : (s.objEntry fE).kind = .func dE)
    (hEcode : dE.code = CETGen.computeExpirationTime_func)
    (hEcls : dE.isClassCtor = false)
    (hEmode : dE.thisMode = .strict)
    (hGo : fG < s.heap.size)
    (hGk : (s.objEntry fG).kind = .func dG)
    (hGcode : dG.code = GNLGen.getNextLanes_func)
    (hGcls : dG.isClassCtor = false)
    (hGmode : dG.thisMode = .strict)
    (hGenv : dG.env = d.env)
    (hHo : fH < s.heap.size)
    (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = GHPGen.getHighestPriorityLanes_func)
    (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict)
    (hPo : fP < s.heap.size)
    (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func)
    (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hSo : fS < s.heap.size)
    (hSk : (s.objEntry fS).kind = .func dS)
    (hgS : gS < s.envs.size)
    (hgSg : gS ≠ d.env)
    (hSe : Scope.declLike? (s.envEntry gS) = some (bS, oS))
    (hSLP : bS[JSStr.ofString "localPerformance"]? = some bdLP)
    (hSLPv : bdLP.value = some (.obj Pf))
    (hPf : Pf < s.heap.size)
    (hPfk : (s.objEntry Pf).kind.isPlain = true)
    (hPfn0 : (s.objEntry Pf).props.get? (.str "now") = none) (hPfp : (s.objEntry Pf).proto = .obj PfP)
    (hPfP : PfP < s.heap.size) (hPfPk : (s.objEntry PfP).kind.isPlain = true)
    (hPfn : (s.objEntry PfP).props.get? (.str "now") = some (.data (.obj fPN) pfw pfe pfc))
    (hPNo : fPN < s.heap.size)
    (hPNk : (s.objEntry fPN).kind = .builtin bPN)
    (hClock : ∀ w, Frame (ReactProcessRoot.fpA d.env) s w →
      SchedulerNow.HostReads eng answer HI (m + 1) fPN (.obj Pf) #[] (.num tm) w 5)
    (hR : R < s.heap.size)
    (hRk : (s.objEntry R).kind.isPlain = true)
    (hRA : R ≠ A)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null rw re rc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRx : (s.objEntry R).props.get? (.str "expirationTimes") = some (.data (.obj A) xw xe xc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv ww we wc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    (hRnode : (s.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc))
    (hRq : (s.objEntry R).props.get? (.str "callbackPriority") = some (.data cp true qe qc))
    (hA : A < s.heap.size)
    (hAk : (s.objEntry A).kind = .array)
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) true ae ac))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) true false false))
    (hL : 1 < (Conv.toNat? L).getD 0)
    (hAE : A ≠ fE)
    (hAG : A ≠ fG)
    (hAP : A ≠ fP)
    (hAC : A ≠ fC)
    (hAH : A ≠ fH)
    (hAS : A ≠ fS)
    (hAF : A ≠ fL)
    (hRG : R ≠ fG)
    (hRP : R ≠ fP)
    (hRE : R ≠ fE)
    (hRC : R ≠ fC)
    (hRH : R ≠ fH)
    (hRS : R ≠ fS)
    (hRF : R ≠ fL)
    (hPerf : ∀ w h1, Frame (fpPerf d.env R A) s w → HI h1 → MicroFacts w d.env oG R A → s.fuel ≤ w.fuel + 402 →
      WP eng answer (m + 1) h1
        (callImpl eng (.obj fS) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w
        fun _ w' h' => Frame fpP w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactFlushSync.After w' d.env oG R bdF ∧
          (∃ a b c, (w'.objEntry R).props.get? (.str "pendingLanes") =
            some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w' h' ∧ HI h')
    (hfpB : fpP.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hfpG : (d.env, JSStr.ofString "getNextLanes") ∉ fpP.binds)
    (hfpI : (d.env, JSStr.ofString "isFlushingWork") ∉ fpP.binds)
    (hfpC : (d.env, JSStr.ofString "currentEventTransitionLane") ∉ fpP.binds)
    (hfpO : fpP.props.all (fun q => q.1 != fG) = true) (hHI : HI h) :
    WP eng answer (m + 4) h (callImpl eng (.obj c) .undefined #[]) s fun v w _ =>
      v = .undefined ∧ ∃ w2 h2 e, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW e d.env) w2 w := by
  refine wp_mono (ReactMicrotask.call_spec (n := m + 3)
    (Q := fun x _ => ∃ w2 h2 e, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW e d.env) w2 x) hcb (by omega) hG hGe hGX hGXv hec
    hGPRS hGPRSv hlt hk ?spec hHI) fun v w h' ⟨hv, hq⟩ => ⟨hv, hq⟩
  case spec =>
  intro w h1 hF hHI1 hfu
  refine wp_mono (processRoot_click (m := m) (hlt := by transfer hF, hlt) (hk := by transfer hF, hk) (hf := by omega) (hcode := by transfer hF, hcode) (hcls := by transfer hF, hcls) (hmode := by transfer hF, hmode) (hG := by transfer hF, hG) (hGe := by transfer hF, hGe) (hGM := by transfer hF, hGM) (hGMm := by transfer hF, hGMm) (hGMv := by transfer hF, hGMv) (hGD := by transfer hF, hGD) (hGDm := by transfer hF, hGDm) (hGDv := by transfer hF, hGDv) (hGC := by transfer hF, hGC) (hGCv := by transfer hF, hGCv) (hGF := by transfer hF, hGF) (hGFv := by transfer hF, hGFv) (hGN := by transfer hF, hGN) (hGNv := by transfer hF, hGNv) (hGT := by transfer hF, hGT) (hGTv := by transfer hF, hGTv) (hGP0 := by transfer hF, hGP0) (hGP0v := by transfer hF, hGP0v) (hGL := by transfer hF, hGL) (hGLv := by transfer hF, hGLv) (hGI := by transfer hF, hGI) (hGIv := by transfer hF, hGIv) (hGIm := by transfer hF, hGIm) (hGW := by transfer hF, hGW) (hGWv := by transfer hF, hGWv) (hGRL := by transfer hF, hGRL) (hGRLv := by transfer hF, hGRLv) (hGCz := by transfer hF, hGCz) (hGCzv := by transfer hF, hGCzv) (hGE := by transfer hF, hGE) (hGEv := by transfer hF, hGEv) (hGG := by transfer hF, hGG) (hGGv := by transfer hF, hGGv) (hGPr := by transfer hF, hGPr) (hGPrv := by transfer hF, hGPrv) (hGH := by transfer hF, hGH) (hGHv := by transfer hF, hGHv) (hGS := by transfer hF, hGS) (hGSv := by transfer hF, hGSv) (hNo := by transfer hF, hNo) (hNk := by transfer hF, hNk) (hNcode := by transfer hF, hNcode) (hNcls := by transfer hF, hNcls) (hNmode := by transfer hF, hNmode) (hNenv := by transfer hF, hNenv) (hTo := by transfer hF, hTo) (hTk := by transfer hF, hTk) (hTcode := by transfer hF, hTcode) (hTcls := by transfer hF, hTcls) (hTmode := by transfer hF, hTmode) (hTenv := by transfer hF, hTenv) (hLo := by transfer hF, hLo) (hLk := by transfer hF, hLk) (hLcode := by transfer hF, hLcode) (hLcls := by transfer hF, hLcls) (hLmode := by transfer hF, hLmode) (hLenv := by transfer hF, hLenv) (hCo := by transfer hF, hCo) (hCk := by transfer hF, hCk) (hCfn := by transfer hF, hCfn) (hEo := by transfer hF, hEo) (hEk := by transfer hF, hEk) (hEcode := by transfer hF, hEcode) (hEcls := by transfer hF, hEcls) (hEmode := by transfer hF, hEmode) (hGo := by transfer hF, hGo) (hGk := by transfer hF, hGk) (hGcode := by transfer hF, hGcode) (hGcls := by transfer hF, hGcls) (hGmode := by transfer hF, hGmode) (hGenv := by transfer hF, hGenv) (hHo := by transfer hF, hHo) (hHk := by transfer hF, hHk) (hHcode := by transfer hF, hHcode) (hHcls := by transfer hF, hHcls) (hHmode := by transfer hF, hHmode) (hPo := by transfer hF, hPo) (hPk := by transfer hF, hPk) (hPcode := by transfer hF, hPcode) (hPcls := by transfer hF, hPcls) (hPmode := by transfer hF, hPmode) (hSo := by transfer hF, hSo) (hSk := by transfer hF, hSk) (hgS := by transfer hF, hgS) (hgSg := by transfer hF, hgSg) (hSe := by transfer hF, hSe) (hSLP := by transfer hF, hSLP) (hSLPv := by transfer hF, hSLPv) (hPf := by transfer hF, hPf) (hPfk := by transfer hF, hPfk) (hPfn0 := by transfer hF, hPfn0) (hPfp := by transfer hF, hPfp) (hPfP := by transfer hF, hPfP) (hPfPk := by transfer hF, hPfPk) (hPfn := by transfer hF, hPfn) (hPNo := by transfer hF, hPNo) (hPNk := by transfer hF, hPNk) (hR := by transfer hF, hR) (hRk := by transfer hF, hRk) (hRA := by transfer hF, hRA) (hRn := by transfer hF, hRn) (hRs := by transfer hF, hRs) (hRi := by transfer hF, hRi) (hRx := by transfer hF, hRx) (hRp := by transfer hF, hRp) (hRw := by transfer hF, hRw) (hRc := by transfer hF, hRc) (hRt := by transfer hF, hRt) (hRnode := by transfer hF, hRnode) (hRq := by transfer hF, hRq) (hA := by transfer hF, hA) (hAk := by transfer hF, hAk) (hA1 := by transfer hF, hA1) (hAL := by transfer hF, hAL) (hL := by transfer hF, hL) (hAE := by transfer hF, hAE) (hAG := by transfer hF, hAG) (hAP := by transfer hF, hAP) (hAC := by transfer hF, hAC) (hAH := by transfer hF, hAH) (hAS := by transfer hF, hAS) (hAF := by transfer hF, hAF) (hRG := by transfer hF, hRG) (hRP := by transfer hF, hRP) (hRE := by transfer hF, hRE) (hRC := by transfer hF, hRC) (hRH := by transfer hF, hRH) (hRS := by transfer hF, hRS) (hRF := by transfer hF, hRF) (hfpB := binds_lt_mono hfpB hF.envs_le) (hfpG := by transfer hF, hfpG) (hfpI := by transfer hF, hfpI) (hfpC := by transfer hF, hfpC) (hfpO := by transfer hF, hfpO)
    (hClock := fun w' hF' => hClock w' (by simpa [Footprint.union] using frame_trans hF hF'))
    (hPerf := fun w' h2 hF' hHI2 hMF hfu' => hPerf w' h2 (by simpa [Footprint.union] using frame_trans hF hF') hHI2 hMF (by omega))
    (hHI := hHI1))
    fun v w' h' ⟨_, ⟨w2, h2, e2, hPu, hF2⟩, _⟩ => ⟨w2, h2, e2, hPu, frame_restore hF2 s⟩

end

end ReactMicrotaskClick
