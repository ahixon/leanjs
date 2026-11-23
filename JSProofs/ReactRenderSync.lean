import JSProofs.ReactDispatchers
import JSProofs.ReactDSSI
import JSProofs.RRSGen

/-!
# React's `renderRootSync` for a click's root (zippy docs/react-proofs.md)

A fresh sync render: executionContext gets `RenderContext`, the dispatchers are pushed (by their theorems), no render
is in progress so the stack is prepared (`prepareFreshStack`), nothing is suspended so the work loop runs
(`workLoopSync`), the render completes; the context and dispatchers are restored, and with no work in progress left
the concurrent updates are finished (`finishQueueingConcurrentUpdates`). The three callees are hypotheses here.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderSync

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- After `prepareFreshStack`: nothing exited, nothing suspended. -/
def AfterPrep (w : State) (g : EnvId) (oG : Option EnvId) : Prop :=
  ∃ bm bdE bdS, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧
    bm[JSStr.ofString "workInProgressRootExitStatus"]? = some bdE ∧ bdE.value = some (.num (F64.fin false 0 (-1074))) ∧
    bm[JSStr.ofString "workInProgressSuspendedReason"]? = some bdS ∧ bdS.value = some (.num (F64.fin false 0 (-1074)))

/-- A binding that exists and can be written. -/
def Writable (bm : HashMap JSStr Binding) (x : String) : Prop :=
  ∃ bd, bm[JSStr.ofString x]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true

/-- After the work loop: the render completed (5), no work in progress; the variables written afterwards writable. -/
def AfterLoop (w : State) (g : EnvId) (oG : Option EnvId) : Prop :=
  ∃ bm bdE bdW, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧
    bm[JSStr.ofString "workInProgressRootExitStatus"]? = some bdE ∧
    bdE.value = some (.num (F64.fin false 5629499534213120 (-50))) ∧
    bm[JSStr.ofString "workInProgress"]? = some bdW ∧ bdW.value = some .null ∧
    Writable bm "lastContextDependency" ∧ Writable bm "currentlyRenderingFiber$1" ∧ Writable bm "executionContext" ∧
    Writable bm "workInProgressRoot" ∧ Writable bm "workInProgressRootRenderLanes"

/-- After its last writes: the execution context restored (`ec`, writable), no root in progress. -/
def EndBinds (w : State) (g : EnvId) (oG : Option EnvId) (ec : F64) : Prop :=
  ∃ bm, Scope.declLike? (w.envEntry g) = some (bm, oG) ∧
    (∃ bd, bm[JSStr.ofString "executionContext"]? = some bd ∧ bd.value = some (.num ec) ∧ bd.mutable = true) ∧
    (∃ bd, bm[JSStr.ofString "workInProgressRoot"]? = some bd ∧ bd.value = some .null) ∧
    (∃ bd, bm[JSStr.ofString "workInProgressRootRenderLanes"]? = some bd ∧
      bd.value = some (.num (F64.fin false 0 (-1074))))

/-- The function's own locals (record `e`). -/
def fpOwn (e : EnvId) : Footprint :=
  ⟨[(e, "root"), (e, "lanes"), (e, "shouldYieldForPrerendering"), (e, "prevExecutionContext"), (e, "prevDispatcher"),
    (e, "prevAsyncDispatcher"), (e, "exitStatus"), (e, "unitOfWork"), (e, "thrownValue"), (e, "reason")], [], false⟩

/-- What the function writes itself, before the stack is prepared and after the loop. -/
def fpPre (g : EnvId) (I : ObjId) : Footprint :=
  ⟨[(g, "executionContext"), (g, "workInProgressTransitions")], [(I, .str "H"), (I, .str "A")], false⟩

def fpEnd (e g : EnvId) (I : ObjId) : Footprint :=
  ⟨(fpOwn e).binds ++ ([(g, "lastContextDependency"), (g, "currentlyRenderingFiber$1"), (g, "executionContext"),
    (g, "workInProgressRoot"), (g, "workInProgressRootRenderLanes")] : List (EnvId × JSStr)),
    [(I, .str "H"), (I, .str "A")], false⟩

/-- What a render writes: the function's own module writes, the dispatchers, and the callees' footprints. -/
def fpRS (g : EnvId) (I : ObjId) (fpPF fpWL fpFQ : Footprint) : Footprint :=
  ⟨([(g, "executionContext"), (g, "workInProgressTransitions"), (g, "lastContextDependency"),
    (g, "currentlyRenderingFiber$1"), (g, "workInProgressRoot"), (g, "workInProgressRootRenderLanes")] :
      List (EnvId × JSStr)) ++ fpPF.binds ++ fpWL.binds ++ fpFQ.binds,
    [(I, .str "H"), (I, .str "A")] ++ fpPF.props ++ fpWL.props ++ fpFQ.props, fpPF.jobs || fpWL.jobs || fpFQ.jobs⟩

theorem simple (d : FuncData) (hc : d.code = RRSGen.renderRootSync_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RRSGen.renderRootSync_func, Func.params, Func.info]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdX bdI bdPD bdPA bdC bdD bdW bdL bdT bdPF : Binding} {I C D P R fPD fPA fPF : ObjId} {dPD dPA : FuncData}
    {ec : F64} {a : Value} {he hc ae ac : Bool} {lanes : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 300 ≤ s.fuel)
    (hcode : d.code = RRSGen.renderRootSync_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX) (hGXv : bdX.value = some (.num ec))
    (hGXm : bdX.mutable = true)
    (hGI : bG[JSStr.ofString "ReactSharedInternals"]? = some bdI) (hGIv : bdI.value = some (.obj I))
    (hGPD : bG[JSStr.ofString "pushDispatcher"]? = some bdPD) (hGPDv : bdPD.value = some (.obj fPD))
    (hGPA : bG[JSStr.ofString "pushAsyncDispatcher"]? = some bdPA) (hGPAv : bdPA.value = some (.obj fPA))
    (hGC : bG[JSStr.ofString "ContextOnlyDispatcher"]? = some bdC) (hGCv : bdC.value = some (.obj C))
    (hGD : bG[JSStr.ofString "DefaultAsyncDispatcher"]? = some bdD) (hGDv : bdD.value = some (.obj D))
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL)
    (hGLv : bdL.value = some (.num (F64.fin false 0 (-1074))))
    (hGT : bG[JSStr.ofString "workInProgressTransitions"]? = some bdT) (hGTm : bdT.mutable = true)
    (hGTv : bdT.value.isSome = true)
    (hGPF : bG[JSStr.ofString "prepareFreshStack"]? = some bdPF) (hGPFv : bdPF.value = some (.obj fPF))
    (hPDo : fPD < s.heap.size) (hPDk : (s.objEntry fPD).kind = .func dPD)
    (hPDcode : dPD.code = PDGen.pushDispatcher_func) (hPDcls : dPD.isClassCtor = false)
    (hPDmode : dPD.thisMode = .strict) (hPDenv : dPD.env = d.env)
    (hPAo : fPA < s.heap.size) (hPAk : (s.objEntry fPA).kind = .func dPA)
    (hPAcode : dPA.code = PADGen.pushAsyncDispatcher_func) (hPAcls : dPA.isClassCtor = false)
    (hPAmode : dPA.thisMode = .strict) (hPAenv : dPA.env = d.env)
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIH : (s.objEntry I).props.get? (.str "H") = some (.data (.obj P) true he hc))
    (hIA : (s.objEntry I).props.get? (.str "A") = some (.data a true ae ac))
    (hPFo : fPF < s.heap.size) (hIPD : I ≠ fPD) (hIPA : I ≠ fPA) (hIPF : I ≠ fPF)
    {bdWL bdFQ : Binding} {fWL fFQ : ObjId} {dPF dWL dFQ : FuncData} {fpPF fpWL fpFQ : Footprint} {kP kW kF : Nat}
    {P1 P2 : State → σ → Prop} {Q : State → σ → Prop}
    (hPFk : (s.objEntry fPF).kind = .func dPF)
    (hGWL : bG[JSStr.ofString "workLoopSync"]? = some bdWL) (hGWLv : bdWL.value = some (.obj fWL))
    (hGFQ : bG[JSStr.ofString "finishQueueingConcurrentUpdates"]? = some bdFQ) (hGFQv : bdFQ.value = some (.obj fFQ))
    (hWLo : fWL < s.heap.size) (hWLk : (s.objEntry fWL).kind = .func dWL) (hIWL : I ≠ fWL)
    (hFQo : fFQ < s.heap.size) (hFQk : (s.objEntry fFQ).kind = .func dFQ) (hIFQ : I ≠ fFQ)
    -- (`prepareFreshStack(root, lanes)`)
    (hPrep : ∀ w h1, Frame (fpPre d.env I) s w → s.fuel ≤ w.fuel + 60 → (∃ v a b, (w.objEntry I).props.get? (.str "H") = some (.data v true a b)) → (∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧ (∃ bd, bm[JSStr.ofString "executionContext"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧ (∃ bd, bm[JSStr.ofString "workInProgressTransitions"]? = some bd ∧ bd.value = some .null)) →
      WP eng answer n h1 (callImpl eng (.obj fPF) .undefined #[.obj R, .num lanes]) w fun _ w' h' =>
        Frame fpPF w w' ∧ w.fuel ≤ w'.fuel + kP ∧ AfterPrep w' d.env oG ∧ P1 w' h')
    (hfpPB : fpPF.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hfpPW : (d.env, JSStr.ofString "workLoopSync") ∉ fpPF.binds)
    (hfpPF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpPF.binds)
    (hfpPI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpPF.binds)
    (hfpPO : fpPF.props.all (fun q => q.1 != I && q.1 != fWL && q.1 != fFQ) = true)
    -- (`workLoopSync()`: the render)
    (hLoop : ∀ w1 w h1, P1 w1 h1 → Frame (fpOwn s.envs.size) w1 w → s.fuel ≤ w.fuel + kP + 100 →
      WP eng answer n h1 (callImpl eng (.obj fWL) .undefined #[]) w fun _ w' h' =>
        Frame fpWL w w' ∧ w.fuel ≤ w'.fuel + kW ∧ AfterLoop w' d.env oG ∧ P2 w' h')
    (hfpWB : fpWL.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hfpWF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpWL.binds)
    (hfpWI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpWL.binds)
    (hfpWO : fpWL.props.all (fun q => q.1 != I && q.1 != fFQ) = true)
    -- (`finishQueueingConcurrentUpdates()`)
    (hFinish : ∀ w2 w h1, P2 w2 h1 → Frame (fpEnd s.envs.size d.env I) w2 w → EndBinds w d.env oG ec → s.fuel ≤ w.fuel + kP + kW + 200 →
      WP eng answer n h1 (callImpl eng (.obj fFQ) .undefined #[]) w fun _ w' h' =>
        Frame fpFQ w w' ∧ w.fuel ≤ w'.fuel + kF ∧ Q (w'.restore s) h')
    (hfpFB : fpFQ.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hf' : kP + kW + kF + 400 ≤ s.fuel) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R, .num lanes, .bool true]) s
      fun v w h' => v = .num (F64.fin false 5629499534213120 (-50)) ∧ Frame (fpRS d.env I fpPF fpWL fpFQ) s w ∧
        s.fuel ≤ w.fuel + kP + kW + kF + 300 ∧ Q w h' := by
  replace hPrep := ReactDSSI.Hold.mk hPrep
  replace hLoop := ReactDSSI.Hold.mk hLoop
  replace hFinish := ReactDSSI.Hold.mk hFinish
  apply wp_callGen RRSGen.renderRootSync_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "lanes",
      JSStr.ofString "shouldYieldForPrerendering"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "prevExecutionContext", JSStr.ofString "prevDispatcher",
      JSStr.ofString "prevAsyncDispatcher", JSStr.ofString "exitStatus", JSStr.ofString "unitOfWork",
      JSStr.ofString "thrownValue", JSStr.ofString "reason"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RRSGen.renderRootSync_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RRSGen.renderRootSync]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGX, hGXv, hGXm, hGPD, hGPDv, hPDo, hPDk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (ReactDispatchers.push_spec (by simpa using hPDo) (by simpa using hPDk) (by simp; omega) hPDcode hPDcls
    hPDmode (by rw [hPDenv]; simp; omega) (by rw [hPDenv]; js_norm [*, Ne.symm hne]; rfl) (by js_norm [*]) hGIv
    (by js_norm [*]) hGCv (by simpa using hI) (by simpa using hIk) (by simpa using hIH)) ?p1
  case p1 =>
  intro r w1 h1 ⟨hr, hF1, hfu1, hIH1⟩
  subst hr
  try simp only [js_simp] at hfu1
  have hE1s : s.envs.size < w1.envs.size := envs_frame hF1 (by simp)
  have hG1s : d.env < w1.envs.size := envs_frame hF1 (by simp; omega)
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by simp) (by simp)
  have hG1e := envEntry_frame hF1 (e := d.env) (by simp; omega) (by simp)
  have hobj1 : ∀ {o : ObjId}, o < s.heap.size → I ≠ o → w1.objEntry o = s.objEntry o := fun ho hIo => by
    rw [objEntry_frame hF1 (by simpa using ho) (by simp [hIo])]; simp
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGX, hGXv, hGXm, hGPA, hGPAv, hE1s, hG1s, hobj1 hPAo hIPA,
    hPAk, hPAo, heap_frame hF1, hE1, hG1e, FDI.fdiCtx, Sem.inner]
  have hI1 : I < w1.heap.size := heap_frame hF1 (by simpa using hI)
  have hIk1 : (w1.objEntry I).kind.isPlain = true := by rw [kind_frame hF1 (by simpa using hI)]; simpa using hIk
  have hIA1 : (w1.objEntry I).props.get? (.str "A") = some (.data a true ae ac) := by
    rw [props_frame hF1 (by simpa using hI) (by simp [js_simp])]; simpa using hIA
  have hPA1 : fPA < w1.heap.size := heap_frame hF1 (by simpa using hPAo)
  have hPAk1 : (w1.objEntry fPA).kind = .func dPA := by rw [hobj1 hPAo hIPA]; exact hPAk
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (ReactDispatchers.pushAsync_spec (by simp only [js_simp]; exact hPA1)
    (by simp only [js_simp]; exact hPAk1) (by simp only [js_simp]; simp at hfu1; omega) hPAcode hPAcls hPAmode
    (by rw [hPAenv]; simp only [js_simp]; exact hG1s) (by rw [hPAenv]; js_norm [*, Ne.symm hne]; rfl) (by js_norm [*])
    hGIv (by js_norm [*]) hGDv (by simp only [js_simp]; exact hI1) (by simp only [js_simp]; exact hIk1)
    (by simp only [js_simp]; exact hIA1)) ?p2
  case p2 =>
  intro r w2 h2 ⟨hr, hF2, hfu2, hIA2⟩
  subst hr
  try simp only [js_simp] at hfu2
  have hE2 := envEntry_frame hF2 (e := s.envs.size) (by simp only [js_simp]; exact hE1s) (by simp)
  have hG2e := envEntry_frame hF2 (e := d.env) (by simp only [js_simp]; exact hG1s) (by simp)
  have hE2s : s.envs.size < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hE1s)
  have hG2s : d.env < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hG1s)
  have hobj2 : ∀ {o : ObjId}, o < s.heap.size → I ≠ o → w2.objEntry o = s.objEntry o := fun ho hIo => by
    rw [objEntry_frame hF2 (by simp only [js_simp]; exact heap_frame hF1 (by simpa using ho)) (by simp [hIo])]
    simp only [js_simp]; exact hobj1 ho hIo
  have hPF2 : fPF < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact heap_frame hF1 (by simpa using hPFo))
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGX, hGXv, hGXm, hE2, hG2e, hE2s, hG2s, hE1, hG1e, hGW, hGWv,
    hGL, hGLv, hGT, hGTm, hGTv, hGPF, hGPFv, hPF2, hobj2 hPFo hIPF, hPFk, FDI.fdiCtx, Sem.inner]
  -- (`prepareFreshStack(root, lanes)`)
  refine ⟨by js_norm [CallableC, *, hobj2 hPFo hIPF], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hPrep) _ h2 ?fr3 ?fu3 ?ih3 ?ec3) ?post3
  case fr3 => simp only [fpPre]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu3 => simp only [js_simp]; simp at hfu1 hfu2; omega
  case ec3 =>
    refine ⟨?bm, ?d1, ⟨?b1, ?d2, ?d3, ?d4⟩, ⟨?b2, ?d5, ?d6⟩⟩
    case d1 => js_norm [*, hne, Ne.symm hne]; rfl
    case d2 => simp [Std.HashMap.getElem?_modify, hGX]; rfl
    case d5 => simp [Std.HashMap.getElem?_modify, hGT]; rfl
    all_goals first | rfl | simp [hGXm] | simp [hGTm] | skip
  case ih3 =>
    refine ⟨.obj C, he, hc, ?_⟩
    simp only [js_simp]
    rw [props_frame hF2 (by simp only [js_simp]; exact hI1) (by simp [js_simp])]; simpa using hIH1
  case post3 =>
  intro r w3 h3 ⟨hF3, hfu3, ⟨bm, bdE, bdS, hW3, hW3E, hW3Ev, hW3S, hW3Sv⟩, hP1⟩
  try simp only [js_simp] at hfu3
  have hle3 : s.envs.size ≤ w2.envs.size := Nat.le_of_lt hE2s
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp only [js_simp]; exact hE2s) (binds_avoid hfpPB (Nat.le_refl _))
  have hE3s : s.envs.size < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; exact hE2s)
  have hG3s : d.env < w3.envs.size := envs_frame hF3 (by simp only [js_simp]; exact hG2s)
  obtain ⟨bW3, hW3', hW3x⟩ := declLike_frame hF3 (e := d.env) (o := oG) (by simp only [js_simp]; exact hG2s)
    (by js_norm [*, Ne.symm hne]; rfl)
  have hbm : bm = bW3 := by rw [hW3] at hW3'; simp only [Option.some.injEq, Prod.mk.injEq] at hW3'; exact hW3'.1
  subst hbm
  have hWWL := hW3x _ hfpPW
  have hWFQ := hW3x _ hfpPF
  have hWRI := hW3x _ hfpPI
  have hsz2 : ∀ {o : ObjId}, o < s.heap.size → o < w2.heap.size := fun ho =>
    heap_frame hF2 (by simp only [js_simp]; exact heap_frame hF1 (by simpa using ho))
  have pobj : ∀ {o : ObjId}, (fpPF.props.all (fun q => q.1 != o) = true) → o < s.heap.size → I ≠ o →
      w3.objEntry o = s.objEntry o := fun hp ho hIo => by
    rw [objEntry_frame hF3 (by simp only [js_simp]; exact hsz2 ho) hp]
    simp only [js_simp]; exact hobj2 ho hIo
  have hpo : ∀ {o : ObjId}, (∀ q ∈ fpPF.props, q.1 ≠ o) → fpPF.props.all (fun q => q.1 != o) = true := fun h => by
    simp only [List.all_eq_true, bne_iff_ne, ne_eq]; exact h
  have hPOs : ∀ q ∈ fpPF.props, q.1 ≠ I ∧ q.1 ≠ fWL ∧ q.1 ≠ fFQ := fun q hq => by
    have := List.all_eq_true.mp hfpPO q hq; simp at this; exact ⟨this.1.1, this.1.2, this.2⟩
  have hWL3 : fWL < w3.heap.size := heap_frame hF3 (by simp only [js_simp]; exact hsz2 hWLo)
  have hWLk3 : (w3.objEntry fWL).kind = .func dWL := by
    rw [pobj (hpo fun q hq => (hPOs q hq).2.1) hWLo hIWL]; exact hWLk
  try simp only [js_simp] at hfu3
  have hE3a : s.envs.size < w3.envs.size + 1 := Nat.lt_succ_of_lt hE3s
  have hE3b : s.envs.size ≠ w3.envs.size := Nat.ne_of_lt hE3s
  have hG3a : d.env < w3.envs.size + 1 := Nat.lt_succ_of_lt hG3s
  have hG3b : d.env ≠ w3.envs.size := Nat.ne_of_lt hG3s
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE3, hE3s, hG3s, hE3a, hE3b, hG3a, hG3b, Ne.symm hE3b, Ne.symm hG3b,
    hW3, hW3E, hW3Ev, hW3S, hW3Sv, hWWL, hGWL, hGWLv, hWL3, hWLk3, FDI.fdiCtx, Sem.inner]
  -- (`workLoopSync()`: the render)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hLoop) w3 _ h3 hP1 ?fr4 ?fu4) ?post4
  case fr4 => simp only [fpOwn]; frame_go' [*, hne, Ne.symm hne]
  case fu4 => simp only [js_simp]; simp at hfu1 hfu2; omega
  case post4 =>
  intro r w4 h4 ⟨hF4, hfu4, ⟨bm4, bdE4, bdW4, hW4, hW4E, hW4Ev, hW4W, hW4Wv, ⟨b1, hb1, hm1, hs1⟩, ⟨b2, hb2, hm2, hs2⟩,
    ⟨b3, hb3, hm3, hs3⟩, ⟨b4, hb4, hm4, hs4⟩, ⟨b5, hb5, hm5, hs5⟩⟩, hP2⟩
  try simp only [js_simp] at hfu4
  have hE4 := envEntry_frame hF4 (e := s.envs.size) (by simp only [js_simp]; exact hE3s) (binds_avoid hfpWB (Nat.le_refl _))
  have hE4s : s.envs.size < w4.envs.size := envs_frame hF4 (by simp only [js_simp]; exact hE3s)
  have hG4s : d.env < w4.envs.size := envs_frame hF4 (by simp only [js_simp]; exact hG3s)
  obtain ⟨bW4, hW4', hW4x⟩ := declLike_frame hF4 (e := d.env) (o := oG) (by simp only [js_simp]; exact hG3s)
    (by js_norm [*, Ne.symm hne, Ne.symm hG3b]; rfl)
  have hbm4 : bm4 = bW4 := by rw [hW4] at hW4'; simp only [Option.some.injEq, Prod.mk.injEq] at hW4'; exact hW4'.1
  subst hbm4
  have hWFQ4 := hW4x _ hfpWF
  have hWRI4 := hW4x _ hfpWI
  have hWOs : ∀ q ∈ fpWL.props, q.1 ≠ I ∧ q.1 ≠ fFQ := fun q hq => by
    have := List.all_eq_true.mp hfpWO q hq; simp at this; exact this
  have hsz3 : ∀ {o : ObjId}, o < s.heap.size → o < w3.heap.size := fun ho =>
    heap_frame hF3 (by simp only [js_simp]; exact hsz2 ho)
  have w4obj : ∀ {o : ObjId}, o < s.heap.size → (∀ q ∈ fpWL.props, q.1 ≠ o) → (∀ q ∈ fpPF.props, q.1 ≠ o) → I ≠ o →
      w4.objEntry o = s.objEntry o := fun {o} ho h4 h3 hIo => by
    have h4' : fpWL.props.all (fun q => q.1 != o) = true := by simp only [List.all_eq_true, bne_iff_ne, ne_eq]; exact h4
    rw [objEntry_frame hF4 (by simp only [js_simp]; exact hsz3 ho) h4']
    simp only [js_simp]; exact pobj (hpo h3) ho hIo
  have hFQ4 : fFQ < w4.heap.size := heap_frame hF4 (by simp only [js_simp]; exact hsz3 hFQo)
  have hFQk4 : (w4.objEntry fFQ).kind = .func dFQ := by
    rw [w4obj hFQo (fun q hq => (hWOs q hq).2) (fun q hq => (hPOs q hq).2.2) hIFQ]; exact hFQk
  have hI4 : I < w4.heap.size := heap_frame hF4 (by simp only [js_simp]; exact hsz3 hI)
  have hI4p : ∀ k, (w4.objEntry I).props.get? k = (w2.objEntry I).props.get? k := fun k => by
    rw [props_frame hF4 (by simp only [js_simp]; exact hsz3 hI) (by simpa using fun hp => (hWOs (I, k) hp).1 rfl)]
    simp only [js_simp]
    rw [props_frame hF3 (by simp only [js_simp]; exact hsz2 hI) (by simpa using fun hp => (hPOs (I, k) hp).1 rfl)]
    simp only [js_simp]
  have hIk4 : (w4.objEntry I).kind.isPlain = true := by
    rw [kind_frame hF4 (by simp only [js_simp]; exact hsz3 hI)]; simp only [js_simp]
    rw [kind_frame hF3 (by simp only [js_simp]; exact hsz2 hI)]; simp only [js_simp]
    rw [kind_frame hF2 (by simp only [js_simp]; exact hI1)]; simp only [js_simp]; exact hIk1
  have hIH4 : (w4.objEntry I).props.get? (.str "H") = some (.data (.obj C) true he hc) := by
    rw [hI4p, props_frame hF2 (by simp only [js_simp]; exact hI1) (by simp [js_simp])]; simp only [js_simp]; exact hIH1
  have hIA4 : (w4.objEntry I).props.get? (.str "A") = some (.data (.obj D) true ae ac) := by
    rw [hI4p]; exact hIA2
  have hE4a : s.envs.size < w4.envs.size + 1 := Nat.lt_succ_of_lt hE4s
  have hE4b : s.envs.size ≠ w4.envs.size := Nat.ne_of_lt hE4s
  have hG4a : d.env < w4.envs.size + 1 := Nat.lt_succ_of_lt hG4s
  have hG4b : d.env ≠ w4.envs.size := Nat.ne_of_lt hG4s
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE4, hE4s, hG4s, hE4a, hE4b, hG4a, hG4b, Ne.symm hE4b, Ne.symm hG4b,
    hW4, hW4E, hW4Ev, hW4W, hW4Wv, hb1, hm1, hs1, hb2, hm2, hs2, hb3, hm3, hs3, hb4, hm4, hs4, hb5, hm5, hs5,
    hWFQ4, hWFQ, hGFQ, hGFQv, hWRI4, hWRI, hGI, hGIv, hFQ4, hFQk4, hI4, hIk4, hIH4, hIA4, FDI.fdiCtx, Sem.inner]
  -- (`finishQueueingConcurrentUpdates()`)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hFinish) w4 _ h4 hP2 ?fr5 ?eb5 ?fu5) ?post5
  case fr5 => simp only [fpEnd, fpOwn]; frame_go' [*, hne, Ne.symm hne]
  case fu5 => simp only [js_simp]; simp at hfu1 hfu2; omega
  case eb5 =>
    refine ⟨?ebm, ?e1, ⟨?eb1, ?e2, ?e3, ?e4⟩, ⟨?eb2, ?e5, ?e6⟩, ⟨?eb3, ?e7, ?e8⟩⟩
    case e1 => js_norm [*, hne, Ne.symm hne]; rfl
    case e2 => simp [Std.HashMap.getElem?_modify, hb3]; rfl
    case e5 => simp [Std.HashMap.getElem?_modify, hb4]; rfl
    case e7 => simp [Std.HashMap.getElem?_modify, hb5]; rfl
    all_goals first | rfl | simp [hm3] | skip
  case post5 =>
  intro r w5 h5 ⟨hF5, hfu5, hQ⟩
  try simp only [js_simp] at hfu5
  have hE5 := envEntry_frame hF5 (e := s.envs.size) (by simp only [js_simp]; exact hE4s) (binds_avoid hfpFB (Nat.le_refl _))
  have hE5s : s.envs.size < w5.envs.size := envs_frame hF5 (by simp only [js_simp]; exact hE4s)
  js [hpn, hv, hl, ha, hE5, hE5s, hne, Ne.symm hne, hG4b, Ne.symm hG4b, FDI.fdiCtx, Sem.inner, hQ]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | exact hQ | omega | (simp only [js_simp] at hfu1 hfu2 hfu3 hfu4 hfu5 ⊢; omega) |
    skip
  simp only [fpRS]
  frame_go' [*, hne, Ne.symm hne, hG1]

end

end ReactRenderSync
