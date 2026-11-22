import JSProofs.ReactSchedTaskRoot
import JSProofs.ReactExpiration
import JSProofs.ReactLanesPick
import JSProofs.ReactPrerender
import JSProofs.MathRules
import JSProofs.ReactFlushSync

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
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

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
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj R, .num tv]) s fun v w _ =>
      v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame (ReactSchedTaskRoot.fp R A) s w ∧
      s.fuel ≤ w.fuel + 60 ∧
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
    intro r w' h' ⟨hv, hF', hfu'⟩
    exact ⟨by rw [hv, clz32_two], hF', by omega⟩
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
    (hPerf : ∀ w h1, Frame (ReactFlushSync.fpA d.env) s w → s.fuel ≤ w.fuel + 60 →
      WP eng answer (n + 1) h1
        (callImpl eng (.obj fS) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w
        fun _ w' h' => Frame fpP w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactFlushSync.After w' d.env oG R bdF ∧
          (∃ a b c, (w'.objEntry R).props.get? (.str "pendingLanes") =
            some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w' h')
    (hfpE : fpP.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpG : (d.env, JSStr.ofString "getNextLanes") ∉ fpP.binds)
    (hfpI : (d.env, JSStr.ofString "isFlushingWork") ∉ fpP.binds)
    (hfpO : fpP.props.all (fun q => q.1 != fG) = true) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t
        #[.num (F64.fin false 0 (-1074)), .bool false]) s fun v w _ =>
      v = .undefined ∧ Frame ⟨(d.env, JSStr.ofString "isFlushingWork") :: fpP.binds, fpP.props, fpP.jobs⟩ s w ∧
      s.fuel ≤ w.fuel + kP + 200 ∧ ∃ w2 h2, Pu w2 h2 ∧ Frame (ReactFlushSync.fpW s.envs.size d.env) w2 w := by
  have hGw : ∀ {w : State}, Frame (ReactFlushSync.fpA d.env) s w → ∀ {o : ObjId}, o < s.heap.size →
      w.objEntry o = s.objEntry o := fun hF _ ho => objEntry_frame hF ho (by simp [ReactFlushSync.fpA])
  refine wp_mono (ReactFlushSync.call_spec (n := n + 1) (P := fun w h => AfterWork w R fG dG ∧ Pu w h)
    hlt hk hf hcode hcls hmode hG hGe hGI hGIv hGIm hGM hGMv hGF hGFv hGW hGWv hGL hGLv hGG hGGv hGP hGPv hGS hGSv
    hGo hGk hPo hPk hSo hSk hR hRk hRn hRc hRt ?n1 ?pre ?perf hfpE hfpG hfpI hfpO ?n2) ?post
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
    intro w h1 hF hfu
    refine wp_mono (hPerf w h1 hF hfu) fun _ w' h' ⟨hF', hfu', hA, ⟨a, b, c, hp0⟩, hPu⟩ => ⟨hF', hfu', hA, ?_, hPu⟩
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
      fun r w' h' ⟨hv, hF', hfu'⟩ => ⟨hv, hF', by omega⟩
  case post =>
    intro v w h' ⟨hv, hFr, hfu, w2, h2, ⟨_, hPu⟩, hF2⟩
    exact ⟨hv, hFr, hfu, w2, h2, hPu, hF2⟩

end

end ReactMicrotaskClick
