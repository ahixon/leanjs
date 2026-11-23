import JSProofs.ReactPerformWork
import JSProofs.ReactRenderSync

/-!
# The render, composed (zippy docs/react-proofs.md)

L1: `performWorkOnRoot(root, 2, true)` with `renderRootSync` by its theorem. Left: `prepareFreshStack`, `workLoopSync`,
`finishQueueingConcurrentUpdates` (each from any render start reachable from here: `∀ sR, Frame {} s sR → …`),
`completeRootWhenReady` (the commit) and `ensureRootIsScheduled`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderClick

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem work_render {eng : Engine} {σ : Type} {answer : HostAnswer σ} {j : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdX bdP bdRS : Binding} {R fP fRS : ObjId} {dP dRS : FuncData} {ec : F64} {lw le lc sw se sc pw pe pc : Bool} {Q : State → σ → Prop} {bdCR bdE : Binding} {fCR fE : ObjId} {dCR dE : FuncData} {fpC fpE : Footprint} {kC kE : Nat} {PC : State → σ → Prop} {bdI bdPD bdPA bdC bdD bdW bdL bdT bdPF : Binding} {I C D P fPD fPA fPF : ObjId} {dPD dPA : FuncData} {a : Value} {he hc ae ac : Bool} {bdWL bdFQ : Binding} {fWL fFQ : ObjId} {dPF dWL dFQ : FuncData} {fpPF fpWL fpFQ : Footprint} {kP kW kF : Nat} {P1 P2 : State → σ → Prop} {PRu : State → σ → Prop}
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hf : kP + kW + kF + kC + kE + 800 ≤ s.fuel)
    (hcode : d.code = PWRGen.performWorkOnRoot_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX)
    (hGXv : bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)))) = true)
    (hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdP)
    (hGPv : bdP.value = some (.obj fP))
    (hGRS : bG[JSStr.ofString "renderRootSync"]? = some bdRS)
    (hGRSv : bdRS.value = some (.obj fRS))
    (hPo : fP < s.heap.size)
    (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func)
    (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hRSo : fRS < s.heap.size)
    (hRSk : (s.objEntry fRS).kind = .func dRS)
    (hR : R < s.heap.size)
    (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hGCR : bG[JSStr.ofString "completeRootWhenReady"]? = some bdCR)
    (hGCRv : bdCR.value = some (.obj fCR))
    (hGE : bG[JSStr.ofString "ensureRootIsScheduled"]? = some bdE)
    (hGEv : bdE.value = some (.obj fE))
    (hCRo : fCR < s.heap.size)
    (hCRk : (s.objEntry fCR).kind = .func dCR)
    (hEo : fE < s.heap.size)
    (hEk : (s.objEntry fE).kind = .func dE)
    (hComplete : ∀ w2 w h1 C alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone w2 d.env oG R C alt bm x1 x2 x3 x4 x5 x6 x7 →
      PRu w2 h1 → Frame (ReactPerformWork.fpOwn s.envs.size) w2 w → s.fuel ≤ w.fuel + (kP + kW + kF + 300) + 80 →
      WP eng answer (j + 1) h1 (callImpl eng (.obj fCR) .undefined #[.obj R, alt, x1, x2, x3,
          .num (F64.fin false 4503599627370496 (-51)), x4, x5, x6, x7, .num (F64.fin false 5629499534213120 (-50)),
          .null, .num (F64.fin false 0 (-1074)).neg, .num (F64.fin false 0 (-1074))]) w fun _ w' h' =>
        Frame fpC w w' ∧ w.fuel ≤ w'.fuel + kC ∧ PC w' h')
    (hfpCE : fpC.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpCS : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpC.binds)
    (hfpCO : fpC.props.all (fun q => q.1 != fE) = true)
    (hEnsure : ∀ w3 w h1, PC w3 h1 → Frame (ReactPerformWork.fpOwn s.envs.size) w3 w → 20 ≤ w.fuel →
      WP eng answer (j + 1) h1 (callImpl eng (.obj fE) .undefined #[.obj R]) w fun _ w' h' =>
        Frame fpE w w' ∧ w.fuel ≤ w'.fuel + kE ∧ Q (w'.restore s) h')
    (hfpEB : fpE.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hRSenv : dRS.env = d.env)
    (hRS_code : dRS.code = RRSGen.renderRootSync_func)
    (hRS_cls : dRS.isClassCtor = false)
    (hRS_mode : dRS.thisMode = .strict)
    (r_GXm : bdX.mutable = true)
    (r_GI : bG[JSStr.ofString "ReactSharedInternals"]? = some bdI)
    (r_GIv : bdI.value = some (.obj I))
    (r_GPD : bG[JSStr.ofString "pushDispatcher"]? = some bdPD)
    (r_GPDv : bdPD.value = some (.obj fPD))
    (r_GPA : bG[JSStr.ofString "pushAsyncDispatcher"]? = some bdPA)
    (r_GPAv : bdPA.value = some (.obj fPA))
    (r_GC : bG[JSStr.ofString "ContextOnlyDispatcher"]? = some bdC)
    (r_GCv : bdC.value = some (.obj C))
    (r_GD : bG[JSStr.ofString "DefaultAsyncDispatcher"]? = some bdD)
    (r_GDv : bdD.value = some (.obj D))
    (r_GW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW)
    (r_GWv : bdW.value = some .null)
    (r_GL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL)
    (r_GLv : bdL.value = some (.num (F64.fin false 0 (-1074))))
    (r_GT : bG[JSStr.ofString "workInProgressTransitions"]? = some bdT)
    (r_GTm : bdT.mutable = true)
    (r_GTv : bdT.value.isSome = true)
    (r_GPF : bG[JSStr.ofString "prepareFreshStack"]? = some bdPF)
    (r_GPFv : bdPF.value = some (.obj fPF))
    (r_PDo : fPD < s.heap.size)
    (r_PDk : (s.objEntry fPD).kind = .func dPD)
    (r_PDcode : dPD.code = PDGen.pushDispatcher_func)
    (r_PDcls : dPD.isClassCtor = false)
    (r_PDmode : dPD.thisMode = .strict)
    (r_PDenv : dPD.env = d.env)
    (r_PAo : fPA < s.heap.size)
    (r_PAk : (s.objEntry fPA).kind = .func dPA)
    (r_PAcode : dPA.code = PADGen.pushAsyncDispatcher_func)
    (r_PAcls : dPA.isClassCtor = false)
    (r_PAmode : dPA.thisMode = .strict)
    (r_PAenv : dPA.env = d.env)
    (r_I : I < s.heap.size)
    (r_Ik : (s.objEntry I).kind.isPlain = true)
    (r_IH : (s.objEntry I).props.get? (.str "H") = some (.data (.obj P) true he hc))
    (r_IA : (s.objEntry I).props.get? (.str "A") = some (.data a true ae ac))
    (r_PFo : fPF < s.heap.size)
    (r_IPD : I ≠ fPD)
    (r_IPA : I ≠ fPA)
    (r_IPF : I ≠ fPF)
    (r_PFk : (s.objEntry fPF).kind = .func dPF)
    (r_GWL : bG[JSStr.ofString "workLoopSync"]? = some bdWL)
    (r_GWLv : bdWL.value = some (.obj fWL))
    (r_GFQ : bG[JSStr.ofString "finishQueueingConcurrentUpdates"]? = some bdFQ)
    (r_GFQv : bdFQ.value = some (.obj fFQ))
    (r_WLo : fWL < s.heap.size)
    (r_WLk : (s.objEntry fWL).kind = .func dWL)
    (r_IWL : I ≠ fWL)
    (r_FQo : fFQ < s.heap.size)
    (r_FQk : (s.objEntry fFQ).kind = .func dFQ)
    (r_IFQ : I ≠ fFQ)
    (r_Prep : ∀ sR, Frame {} s sR → s.fuel ≤ sR.fuel + 40 →
      ∀ w h1, Frame (ReactRenderSync.fpPre d.env I) sR w → sR.fuel ≤ w.fuel + 60 → (∃ v a b, (w.objEntry I).props.get? (.str "H") = some (.data v true a b)) →
      WP eng answer j h1 (callImpl eng (.obj fPF) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w fun _ w' h' =>
        Frame fpPF w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactRenderSync.AfterPrep w' d.env oG ∧ P1 w' h')
    (r_fpPB : fpPF.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (r_fpPW : (d.env, JSStr.ofString "workLoopSync") ∉ fpPF.binds)
    (r_fpPF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpPF.binds)
    (r_fpPI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpPF.binds)
    (r_fpPO : fpPF.props.all (fun q => q.1 != I && q.1 != fWL && q.1 != fFQ) = true)
    (r_Loop : ∀ sR, Frame {} s sR → s.fuel ≤ sR.fuel + 40 →
      ∀ w1 w h1, P1 w1 h1 → Frame (ReactRenderSync.fpOwn sR.envs.size) w1 w → sR.fuel ≤ w.fuel + kP + 100 →
      WP eng answer j h1 (callImpl eng (.obj fWL) .undefined #[]) w fun _ w' h' =>
        Frame fpWL w w' ∧ w.fuel ≤ w'.fuel + kW ∧ ReactRenderSync.AfterLoop w' d.env oG ∧ P2 w' h')
    (r_fpWB : fpWL.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (r_fpWF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpWL.binds)
    (r_fpWI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpWL.binds)
    (r_fpWO : fpWL.props.all (fun q => q.1 != I && q.1 != fFQ) = true)
    (r_Finish : ∀ sR, Frame {} s sR → s.fuel ≤ sR.fuel + 40 →
      ∀ w2 w h1, P2 w2 h1 → Frame (ReactRenderSync.fpEnd sR.envs.size d.env I) w2 w → sR.fuel ≤ w.fuel + kP + kW + 200 →
      WP eng answer j h1 (callImpl eng (.obj fFQ) .undefined #[]) w fun _ w' h' =>
        Frame fpFQ w w' ∧ w.fuel ≤ w'.fuel + kF ∧ (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore sR) h')
    (r_fpFB : fpFQ.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (c_PC : (d.env, JSStr.ofString "completeRootWhenReady") ∉ fpPF.binds)
    (c_WC : (d.env, JSStr.ofString "completeRootWhenReady") ∉ fpWL.binds)
    (c_FC : (d.env, JSStr.ofString "completeRootWhenReady") ∉ fpFQ.binds)
    (c_PE : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpPF.binds)
    (c_WE : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpWL.binds)
    (c_FE : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpFQ.binds)
    (c_PO : fpPF.props.all (fun q => q.1 != fCR && q.1 != fE) = true)
    (c_WO : fpWL.props.all (fun q => q.1 != fCR && q.1 != fE) = true)
    (c_FO : fpFQ.props.all (fun q => q.1 != fCR && q.1 != fE) = true)
    (c_ICR : I ≠ fCR) (c_IE : I ≠ fE) :
    WP eng answer (j + 2) h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 4503599627370496 (-51)), .bool true]) s
      fun v w h' => v = .undefined ∧ Frame ⟨(ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).binds ++ fpC.binds ++ fpE.binds,
        (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).props ++ fpC.props ++ fpE.props,
        (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).jobs || fpC.jobs || fpE.jobs⟩ s w ∧
        s.fuel ≤ w.fuel + (kP + kW + kF + 300) + kC + kE + 300 ∧ Q w h' := by
  refine ReactPerformWork.call_spec (n := j + 1) (fpR := ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ)
    (kR := kP + kW + kF + 300) (kC := kC) (kE := kE) (fpC := fpC) (fpE := fpE) (PC := PC) (PR := PRu) (hlt := hlt) (hk := hk) (hf := by omega) (hcode := hcode) (hcls := hcls) (hmode := hmode) (hG := hG) (hGe := hGe) (hGX := hGX) (hGXv := hGXv) (hec := hec) (hGP := hGP) (hGPv := hGPv) (hGRS := hGRS) (hGRSv := hGRSv) (hPo := hPo) (hPk := hPk) (hPcode := hPcode) (hPcls := hPcls) (hPmode := hPmode) (hRSo := hRSo) (hRSk := hRSk) (hR := hR) (hRk := hRk) (hRp := hRp) (hRs := hRs) (hRi := hRi) (hGCR := hGCR) (hGCRv := hGCRv) (hGE := hGE) (hGEv := hGEv) (hCRo := hCRo) (hCRk := hCRk) (hEo := hEo) (hEk := hEk) (hComplete := hComplete) (hfpCE := hfpCE) (hfpCS := hfpCS) (hfpCO := hfpCO) (hEnsure := hEnsure) (hfpEB := hfpEB)
    (hRender := ?render) (hfpRE := ?fRE) (hfpRC := ?fRC) (hfpRS := ?fRS) (hfpRO := ?fRO)
  case fRE =>
    simp only [ReactRenderSync.fpRS, List.all_append, binds_avoid r_fpPB (Nat.le_refl _),
      binds_avoid r_fpWB (Nat.le_refl _), binds_avoid r_fpFB (Nat.le_refl _), Bool.and_true]
    simp [Nat.ne_of_lt hG]
  case fRC => simp [ReactRenderSync.fpRS, c_PC, c_WC, c_FC, js_simp]
  case fRS => simp [ReactRenderSync.fpRS, c_PE, c_WE, c_FE, js_simp]
  case fRO =>
    simp only [ReactRenderSync.fpRS, List.all_append, c_PO, c_WO, c_FO, Bool.and_true]
    simp [c_ICR, c_IE]
  case render =>
    intro w h1 hF hfu
    refine wp_mono (ReactRenderSync.call_spec (n := j) (s := w) (d := { dRS with env := d.env }) (I := I) (bG := bG) (oG := oG) (R := R)
      (lanes := (F64.fin false 4503599627370496 (-51))) (Q := (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h)) (hlt := heap_frame hF hRSo) (hk := by rw [objEntry_frame0 hF hRSo, hRSk]; cases dRS; simp_all) (hf := by omega) (hG := envs_frame hF hG) (hGe := by show Scope.declLike? (w.envEntry d.env) = _; rw [envEntry_frame0 hF hG]; exact hGe) (hGX := hGX) (hGXv := hGXv) (hf' := by omega) (hcode := hRS_code) (hcls := hRS_cls) (hmode := hRS_mode) (hGXm := by first | exact r_GXm | transfer hF, r_GXm) (hGI := by first | exact r_GI | transfer hF, r_GI) (hGIv := by first | exact r_GIv | transfer hF, r_GIv) (hGPD := by first | exact r_GPD | transfer hF, r_GPD) (hGPDv := by first | exact r_GPDv | transfer hF, r_GPDv) (hGPA := by first | exact r_GPA | transfer hF, r_GPA) (hGPAv := by first | exact r_GPAv | transfer hF, r_GPAv) (hGC := by first | exact r_GC | transfer hF, r_GC) (hGCv := by first | exact r_GCv | transfer hF, r_GCv) (hGD := by first | exact r_GD | transfer hF, r_GD) (hGDv := by first | exact r_GDv | transfer hF, r_GDv) (hGW := by first | exact r_GW | transfer hF, r_GW) (hGWv := by first | exact r_GWv | transfer hF, r_GWv) (hGL := by first | exact r_GL | transfer hF, r_GL) (hGLv := by first | exact r_GLv | transfer hF, r_GLv) (hGT := by first | exact r_GT | transfer hF, r_GT) (hGTm := by first | exact r_GTm | transfer hF, r_GTm) (hGTv := by first | exact r_GTv | transfer hF, r_GTv) (hGPF := by first | exact r_GPF | transfer hF, r_GPF) (hGPFv := by first | exact r_GPFv | transfer hF, r_GPFv) (hPDo := by first | exact r_PDo | transfer hF, r_PDo) (hPDk := by first | exact r_PDk | transfer hF, r_PDk) (hPDcode := by first | exact r_PDcode | transfer hF, r_PDcode) (hPDcls := by first | exact r_PDcls | transfer hF, r_PDcls) (hPDmode := by first | exact r_PDmode | transfer hF, r_PDmode) (hPDenv := by first | exact r_PDenv | transfer hF, r_PDenv) (hPAo := by first | exact r_PAo | transfer hF, r_PAo) (hPAk := by first | exact r_PAk | transfer hF, r_PAk) (hPAcode := by first | exact r_PAcode | transfer hF, r_PAcode) (hPAcls := by first | exact r_PAcls | transfer hF, r_PAcls) (hPAmode := by first | exact r_PAmode | transfer hF, r_PAmode) (hPAenv := by first | exact r_PAenv | transfer hF, r_PAenv) (hI := by first | exact r_I | transfer hF, r_I) (hIk := by first | exact r_Ik | transfer hF, r_Ik) (hIH := by first | exact r_IH | transfer hF, r_IH) (hIA := by first | exact r_IA | transfer hF, r_IA) (hPFo := by first | exact r_PFo | transfer hF, r_PFo) (hIPD := by first | exact r_IPD | transfer hF, r_IPD) (hIPA := by first | exact r_IPA | transfer hF, r_IPA) (hIPF := by first | exact r_IPF | transfer hF, r_IPF) (hPFk := by first | exact r_PFk | transfer hF, r_PFk) (hGWL := by first | exact r_GWL | transfer hF, r_GWL) (hGWLv := by first | exact r_GWLv | transfer hF, r_GWLv) (hGFQ := by first | exact r_GFQ | transfer hF, r_GFQ) (hGFQv := by first | exact r_GFQv | transfer hF, r_GFQv) (hWLo := by first | exact r_WLo | transfer hF, r_WLo) (hWLk := by first | exact r_WLk | transfer hF, r_WLk) (hIWL := by first | exact r_IWL | transfer hF, r_IWL) (hFQo := by first | exact r_FQo | transfer hF, r_FQo) (hFQk := by first | exact r_FQk | transfer hF, r_FQk) (hIFQ := by first | exact r_IFQ | transfer hF, r_IFQ) (hPrep := r_Prep w hF hfu) (hfpPB := binds_lt_mono r_fpPB hF.envs_le) (hfpPW := by first | exact r_fpPW | transfer hF, r_fpPW) (hfpPF := by first | exact r_fpPF | transfer hF, r_fpPF) (hfpPI := by first | exact r_fpPI | transfer hF, r_fpPI) (hfpPO := by first | exact r_fpPO | transfer hF, r_fpPO) (hLoop := r_Loop w hF hfu) (hfpWB := binds_lt_mono r_fpWB hF.envs_le) (hfpWF := by first | exact r_fpWF | transfer hF, r_fpWF) (hfpWI := by first | exact r_fpWI | transfer hF, r_fpWI) (hfpWO := by first | exact r_fpWO | transfer hF, r_fpWO) (hFinish := r_Finish w hF hfu) (hfpFB := binds_lt_mono r_fpFB hF.envs_le))
      fun v w' h' ⟨hv, hFr, hfu', hQ⟩ => ⟨hv, hFr, by omega, hQ.1, hQ.2⟩

end

end ReactRenderClick
