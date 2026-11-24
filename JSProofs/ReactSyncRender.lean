import JSProofs.ReactRenderClick
import JSProofs.ReactPerformSync

/-!
# The render from `performSyncWorkOnRoot` (zippy docs/react-proofs.md)

L2: `performSyncWorkOnRoot(root, 2)` over `work_render`. The callees' hypotheses hold from every state the work can
start in (`∀ sW, Frame {} s sW → …`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderClick

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem sync_render {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop} {j : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdF bdW bdS bdV bdM bdL bdP bdX : Binding} {fF fW fM fL fX fP : ObjId} {dF dW dM dL dX dP : FuncData} {Q : State → σ → Prop} {w_bdX w_bdP bdRS : Binding} {R w_fP fRS : ObjId} {w_dP dRS : FuncData} {ec : F64} {lw le lc sw se sc pw pe pc : Bool} {bdCR bdE : Binding} {fCR fE : ObjId} {dCR dE : FuncData} {fpC fpE : Footprint} {kC kE : Nat} {PC : State → σ → Prop} {bdI bdPD bdPA bdC bdD w_bdW w_bdL bdT bdPF : Binding} {I C D P fPD fPA fPF : ObjId} {dPD dPA : FuncData} {a : Value} {he hc ae ac : Bool} {bdWL bdFQ : Binding} {fWL fFQ : ObjId} {dPF dWL dFQ : FuncData} {fpPF fpWL fpFQ : Footprint} {kP kW kF : Nat} {P1 P2 : State → σ → Prop} {PRu : State → σ → Prop}
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hf : 100 ≤ s.fuel)
    (hcode : d.code = PSWGen.performSyncWorkOnRoot_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "flushPendingEffects"]? = some bdF)
    (hGFv : bdF.value = some (.obj fF))
    (hGW : bG[JSStr.ofString "performWorkOnRoot"]? = some bdW)
    (hGWv : bdW.value = some (.obj fW))
    (hFo : fF < s.heap.size)
    (hFk : (s.objEntry fF).kind = .func dF)
    (hFcode : dF.code = FPEGen.flushPendingEffects_func)
    (hFcls : dF.isClassCtor = false)
    (hFmode : dF.thisMode = .strict)
    (hFenv : dF.env = d.env)
    (hWo : fW < s.heap.size)
    (hWk : (s.objEntry fW).kind = .func dW)
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074))))
    (hGV : bG[JSStr.ofString "pendingViewTransition"]? = some bdV)
    (hGVv : bdV.value = some .null)
    (hGM : bG[JSStr.ofString "flushMutationEffects"]? = some bdM)
    (hGMv : bdM.value = some (.obj fM))
    (hGL : bG[JSStr.ofString "flushLayoutEffects"]? = some bdL)
    (hGLv : bdL.value = some (.obj fL))
    (hGX : bG[JSStr.ofString "flushSpawnedWork"]? = some bdX)
    (hGXv : bdX.value = some (.obj fX))
    (hGP : bG[JSStr.ofString "flushPassiveEffects"]? = some bdP)
    (hGPv : bdP.value = some (.obj fP))
    (hMo : fM < s.heap.size)
    (hMk : (s.objEntry fM).kind = .func dM)
    (hMcode : dM.code = FMEGen.flushMutationEffects_func)
    (hMcls : dM.isClassCtor = false)
    (hMmode : dM.thisMode = .strict)
    (hMenv : dM.env = d.env)
    (hLo : fL < s.heap.size)
    (hLk : (s.objEntry fL).kind = .func dL)
    (hLcode : dL.code = FLEGen.flushLayoutEffects_func)
    (hLcls : dL.isClassCtor = false)
    (hLmode : dL.thisMode = .strict)
    (hLenv : dL.env = d.env)
    (hXo : fX < s.heap.size)
    (hXk : (s.objEntry fX).kind = .func dX)
    (hXcode : dX.code = FSPGen.flushSpawnedWork_func)
    (hXcls : dX.isClassCtor = false)
    (hXmode : dX.thisMode = .strict)
    (hXenv : dX.env = d.env)
    (hPo : fP < s.heap.size)
    (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = FPAGen.flushPassiveEffects_func)
    (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hPenv : dP.env = d.env)
    (x_hcode : dW.code = PWRGen.performWorkOnRoot_func)
    (x_hcls : dW.isClassCtor = false)
    (x_hmode : dW.thisMode = .strict)
    (x_hGX : bG[JSStr.ofString "executionContext"]? = some w_bdX)
    (x_hGXv : w_bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)))) = true)
    (x_hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some w_bdP)
    (x_hGPv : w_bdP.value = some (.obj w_fP))
    (hGRS : bG[JSStr.ofString "renderRootSync"]? = some bdRS)
    (hGRSv : bdRS.value = some (.obj fRS))
    (x_hPo : w_fP < s.heap.size)
    (x_hPk : (s.objEntry w_fP).kind = .func w_dP)
    (x_hPcode : w_dP.code = CPRGen.checkIfRootIsPrerendering_func)
    (x_hPcls : w_dP.isClassCtor = false)
    (x_hPmode : w_dP.thisMode = .strict)
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
    (hComplete : ∀ sW, Frame {} s sW → s.fuel ≤ sW.fuel + 70 →
      ∀ w2 w h1 C alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone w2 d.env oG R C alt bm x1 x2 x3 x4 x5 x6 x7 →
      PRu w2 h1 → HI h1 → Frame (ReactPerformWork.fpOwn sW.envs.size) w2 w → sW.fuel ≤ w.fuel + (kP + kW + kF + 300) + 80 →
      WP eng answer (j + 1) h1 (callImpl eng (.obj fCR) .undefined #[.obj R, alt, x1, x2, x3,
          .num (F64.fin false 4503599627370496 (-51)), x4, x5, x6, x7, .num (F64.fin false 5629499534213120 (-50)),
          .null, .num (F64.fin false 0 (-1074)).neg, .num (F64.fin false 0 (-1074))]) w fun _ w' h' =>
        Frame fpC w w' ∧ w.fuel ≤ w'.fuel + kC ∧ PC w' h' ∧ HI h')
    (hfpCE : fpC.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hfpCS : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpC.binds)
    (hfpCO : fpC.props.all (fun q => q.1 != fE) = true)
    (hEnsure : ∀ sW, Frame {} s sW → s.fuel ≤ sW.fuel + 70 →
      ∀ w3 w h1, PC w3 h1 → HI h1 → Frame (ReactPerformWork.fpOwn sW.envs.size) w3 w → 20 ≤ w.fuel →
      WP eng answer (j + 1) h1 (callImpl eng (.obj fE) .undefined #[.obj R]) w fun _ w' h' =>
        Frame fpE w w' ∧ w.fuel ≤ w'.fuel + kE ∧ (fun w h => Q (w.restore s) h) (w'.restore sW) h' ∧ HI h')
    (hfpEB : fpE.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hRSenv : dRS.env = d.env)
    (hRS_code : dRS.code = RRSGen.renderRootSync_func)
    (hRS_cls : dRS.isClassCtor = false)
    (hRS_mode : dRS.thisMode = .strict)
    (r_GXm : w_bdX.mutable = true)
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
    (r_GW : bG[JSStr.ofString "workInProgressRoot"]? = some w_bdW)
    (r_GWv : w_bdW.value = some .null)
    (r_GL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some w_bdL)
    (r_GLv : w_bdL.value = some (.num (F64.fin false 0 (-1074))))
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
    (r_Prep : ∀ sW, Frame {} s sW → s.fuel ≤ sW.fuel + 70 →
      ∀ sR, Frame {} sW sR → sW.fuel ≤ sR.fuel + 40 →
      ∀ w h1, Frame (ReactRenderSync.fpPre d.env I) sR w → HI h1 → sR.fuel ≤ w.fuel + 60 → (∃ v a b, (w.objEntry I).props.get? (.str "H") = some (.data v true a b)) → (∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧ (∃ bd, bm[JSStr.ofString "executionContext"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧ (∃ bd, bm[JSStr.ofString "workInProgressTransitions"]? = some bd ∧ bd.value = some .null)) →
      WP eng answer j h1 (callImpl eng (.obj fPF) .undefined #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) w fun _ w' h' =>
        Frame fpPF w w' ∧ w.fuel ≤ w'.fuel + kP ∧ ReactRenderSync.AfterPrep w' d.env oG ∧ P1 w' h' ∧ HI h')
    (r_fpPB : fpPF.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (r_fpPW : (d.env, JSStr.ofString "workLoopSync") ∉ fpPF.binds)
    (r_fpPF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpPF.binds)
    (r_fpPI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpPF.binds)
    (r_fpPO : fpPF.props.all (fun q => q.1 != I && q.1 != fWL && q.1 != fFQ) = true)
    (r_Loop : ∀ sW, Frame {} s sW → s.fuel ≤ sW.fuel + 70 →
      ∀ sR, Frame {} sW sR → sW.fuel ≤ sR.fuel + 40 →
      ∀ w1 w h1, P1 w1 h1 → HI h1 → Frame (ReactRenderSync.fpOwn sR.envs.size) w1 w → sR.fuel ≤ w.fuel + kP + 100 →
      WP eng answer j h1 (callImpl eng (.obj fWL) .undefined #[]) w fun _ w' h' =>
        Frame fpWL w w' ∧ w.fuel ≤ w'.fuel + kW ∧ ReactRenderSync.AfterLoop w' d.env oG ∧ P2 w' h' ∧ HI h')
    (r_fpWB : fpWL.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (r_fpWF : (d.env, JSStr.ofString "finishQueueingConcurrentUpdates") ∉ fpWL.binds)
    (r_fpWI : (d.env, JSStr.ofString "ReactSharedInternals") ∉ fpWL.binds)
    (r_fpWO : fpWL.props.all (fun q => q.1 != I && q.1 != fFQ) = true)
    (r_Finish : ∀ sW, Frame {} s sW → s.fuel ≤ sW.fuel + 70 →
      ∀ sR, Frame {} sW sR → sW.fuel ≤ sR.fuel + 40 →
      ∀ w2 w h1, P2 w2 h1 → HI h1 → Frame (ReactRenderSync.fpEnd sR.envs.size d.env I) w2 w → ReactRenderSync.EndBinds w d.env oG ec → sR.fuel ≤ w.fuel + kP + kW + 200 →
      WP eng answer j h1 (callImpl eng (.obj fFQ) .undefined #[]) w fun _ w' h' =>
        Frame fpFQ w w' ∧ w.fuel ≤ w'.fuel + kF ∧ (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore sR) h' ∧ HI h')
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
    (c_ICR : I ≠ fCR)
    (c_IE : I ≠ fE)
    (hWenv : dW.env = d.env)
    (hf2 : kP + kW + kF + kC + kE + 900 ≤ s.fuel) (hHI : HI h) :
    WP eng answer (j + 3) h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) s fun v w h' =>
      v = .undefined ∧ Frame (⟨(ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).binds ++ fpC.binds ++ fpE.binds, (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).props ++ fpC.props ++ fpE.props, (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).jobs || fpC.jobs || fpE.jobs⟩) s w ∧ s.fuel ≤ w.fuel + ((kP + kW + kF + 300) + kC + kE + 300) + 100 ∧ Q w h' ∧ HI h' := by
  refine ReactPerformSync.call_spec (n := j + 1) (hHI := hHI) (root := .obj R) (lanes := .num (F64.fin false 4503599627370496 (-51))) (fpW := ⟨(ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).binds ++ fpC.binds ++ fpE.binds, (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).props ++ fpC.props ++ fpE.props, (ReactRenderSync.fpRS d.env I fpPF fpWL fpFQ).jobs || fpC.jobs || fpE.jobs⟩) (kW := (kP + kW + kF + 300) + kC + kE + 300) (h := h) (fo := fo) (d := d) (t := t) (s := s) (bG := bG) (oG := oG) (bdF := bdF) (bdW := bdW) (bdS := bdS) (bdV := bdV) (bdM := bdM) (bdL := bdL) (bdP := bdP) (bdX := bdX) (fF := fF) (fW := fW) (fM := fM) (fL := fL) (fX := fX) (fP := fP) (dF := dF) (dW := dW) (dM := dM) (dL := dL) (dX := dX) (dP := dP) (Q := Q)
    (hlt := hlt) (hk := hk) (hf := hf) (hcode := hcode) (hcls := hcls) (hmode := hmode) (hG := hG) (hGe := hGe) (hGF := hGF) (hGFv := hGFv) (hGW := hGW) (hGWv := hGWv) (hFo := hFo) (hFk := hFk) (hFcode := hFcode) (hFcls := hFcls) (hFmode := hFmode) (hFenv := hFenv) (hWo := hWo) (hWk := hWk) (hGS := hGS) (hGSv := hGSv) (hGV := hGV) (hGVv := hGVv) (hGM := hGM) (hGMv := hGMv) (hGL := hGL) (hGLv := hGLv) (hGX := hGX) (hGXv := hGXv) (hGP := hGP) (hGPv := hGPv) (hMo := hMo) (hMk := hMk) (hMcode := hMcode) (hMcls := hMcls) (hMmode := hMmode) (hMenv := hMenv) (hLo := hLo) (hLk := hLk) (hLcode := hLcode) (hLcls := hLcls) (hLmode := hLmode) (hLenv := hLenv) (hXo := hXo) (hXk := hXk) (hXcode := hXcode) (hXcls := hXcls) (hXmode := hXmode) (hXenv := hXenv) (hPo := hPo) (hPk := hPk) (hPcode := hPcode) (hPcls := hPcls) (hPmode := hPmode) (hPenv := hPenv)
    (hWork := ?hole) (hfpWB := ?hfpWB)
  case hfpWB =>
    simp [ReactRenderSync.fpRS, List.all_append, r_fpPB, r_fpWB, r_fpFB, hfpCE, hfpEB, hG]
  case hole =>
    intro w h1 hF hHI1 hfu

    refine wp_mono (ReactRenderClick.work_render (hHI := hHI1) (fo := fW) (d := { dW with env := d.env }) (t := .undefined) (s := w) (h := h1) (bG := bG) (oG := oG) (Q := (fun w h => Q (w.restore s) h))
      (eng := eng) (σ := σ) (answer := answer) (j := j) (bdX := w_bdX) (bdP := w_bdP) (bdRS := bdRS) (R := R) (fP := w_fP) (fRS := fRS) (dP := w_dP) (dRS := dRS) (ec := ec) (lw := lw) (le := le) (lc := lc) (sw := sw) (se := se) (sc := sc) (pw := pw) (pe := pe) (pc := pc) (bdCR := bdCR) (bdE := bdE) (fCR := fCR) (fE := fE) (dCR := dCR) (dE := dE) (fpC := fpC) (fpE := fpE) (kC := kC) (kE := kE) (PC := PC) (bdI := bdI) (bdPD := bdPD) (bdPA := bdPA) (bdC := bdC) (bdD := bdD) (bdW := w_bdW) (bdL := w_bdL) (bdT := bdT) (bdPF := bdPF) (I := I) (C := C) (D := D) (P := P) (fPD := fPD) (fPA := fPA) (fPF := fPF) (dPD := dPD) (dPA := dPA) (a := a) (he := he) (hc := hc) (ae := ae) (ac := ac) (bdWL := bdWL) (bdFQ := bdFQ) (fWL := fWL) (fFQ := fFQ) (dPF := dPF) (dWL := dWL) (dFQ := dFQ) (fpPF := fpPF) (fpWL := fpWL) (fpFQ := fpFQ) (kP := kP) (kW := kW) (kF := kF) (P1 := P1) (P2 := P2) (PRu := PRu)
      (hlt := heap_frame hF hWo) (hk := by rw [objEntry_frame0 hF hWo, hWk]; cases dW; simp_all) (hf := by omega) (hcode := x_hcode) (hcls := x_hcls) (hmode := x_hmode) (hG := envs_frame hF hG) (hGe := by show Scope.declLike? (w.envEntry d.env) = _; rw [envEntry_frame0 hF hG]; exact hGe) (hGX := x_hGX) (hGXv := x_hGXv) (hec := hec) (hGP := x_hGP) (hGPv := x_hGPv) (hGRS := hGRS) (hGRSv := hGRSv) (hPo := by first | exact x_hPo | transfer hF, x_hPo) (hPk := by first | exact x_hPk | transfer hF, x_hPk) (hPcode := x_hPcode) (hPcls := x_hPcls) (hPmode := x_hPmode) (hRSo := by first | exact hRSo | transfer hF, hRSo) (hRSk := by first | exact hRSk | transfer hF, hRSk) (hR := by first | exact hR | transfer hF, hR) (hRk := by first | exact hRk | transfer hF, hRk) (hRp := by first | exact hRp | transfer hF, hRp) (hRs := by first | exact hRs | transfer hF, hRs) (hRi := by first | exact hRi | transfer hF, hRi) (hGCR := hGCR) (hGCRv := hGCRv) (hGE := hGE) (hGEv := hGEv) (hCRo := by first | exact hCRo | transfer hF, hCRo) (hCRk := by first | exact hCRk | transfer hF, hCRk) (hEo := by first | exact hEo | transfer hF, hEo) (hEk := by first | exact hEk | transfer hF, hEk) (hComplete := hComplete w hF hfu) (hfpCE := binds_avoid hfpCE hF.envs_le) (hfpCS := hfpCS) (hfpCO := hfpCO) (hEnsure := hEnsure w hF hfu) (hfpEB := binds_lt_mono hfpEB hF.envs_le) (hRSenv := hRSenv) (hRS_code := hRS_code) (hRS_cls := hRS_cls) (hRS_mode := hRS_mode) (r_GXm := r_GXm) (r_GI := r_GI) (r_GIv := r_GIv) (r_GPD := r_GPD) (r_GPDv := r_GPDv) (r_GPA := r_GPA) (r_GPAv := r_GPAv) (r_GC := r_GC) (r_GCv := r_GCv) (r_GD := r_GD) (r_GDv := r_GDv) (r_GW := r_GW) (r_GWv := r_GWv) (r_GL := r_GL) (r_GLv := r_GLv) (r_GT := r_GT) (r_GTm := r_GTm) (r_GTv := r_GTv) (r_GPF := r_GPF) (r_GPFv := r_GPFv) (r_PDo := by first | exact r_PDo | transfer hF, r_PDo) (r_PDk := by first | exact r_PDk | transfer hF, r_PDk) (r_PDcode := r_PDcode) (r_PDcls := r_PDcls) (r_PDmode := r_PDmode) (r_PDenv := r_PDenv) (r_PAo := by first | exact r_PAo | transfer hF, r_PAo) (r_PAk := by first | exact r_PAk | transfer hF, r_PAk) (r_PAcode := r_PAcode) (r_PAcls := r_PAcls) (r_PAmode := r_PAmode) (r_PAenv := r_PAenv) (r_I := by first | exact r_I | transfer hF, r_I) (r_Ik := by first | exact r_Ik | transfer hF, r_Ik) (r_IH := by first | exact r_IH | transfer hF, r_IH) (r_IA := by first | exact r_IA | transfer hF, r_IA) (r_PFo := by first | exact r_PFo | transfer hF, r_PFo) (r_IPD := r_IPD) (r_IPA := r_IPA) (r_IPF := r_IPF) (r_PFk := by first | exact r_PFk | transfer hF, r_PFk) (r_GWL := r_GWL) (r_GWLv := r_GWLv) (r_GFQ := r_GFQ) (r_GFQv := r_GFQv) (r_WLo := by first | exact r_WLo | transfer hF, r_WLo) (r_WLk := by first | exact r_WLk | transfer hF, r_WLk) (r_IWL := r_IWL) (r_FQo := by first | exact r_FQo | transfer hF, r_FQo) (r_FQk := by first | exact r_FQk | transfer hF, r_FQk) (r_IFQ := r_IFQ) (r_Prep := r_Prep w hF hfu) (r_fpPB := binds_lt_mono r_fpPB hF.envs_le) (r_fpPW := r_fpPW) (r_fpPF := r_fpPF) (r_fpPI := r_fpPI) (r_fpPO := r_fpPO) (r_Loop := r_Loop w hF hfu) (r_fpWB := binds_lt_mono r_fpWB hF.envs_le) (r_fpWF := r_fpWF) (r_fpWI := r_fpWI) (r_fpWO := r_fpWO) (r_Finish := r_Finish w hF hfu) (r_fpFB := binds_lt_mono r_fpFB hF.envs_le) (c_PC := c_PC) (c_WC := c_WC) (c_FC := c_FC) (c_PE := c_PE) (c_WE := c_WE) (c_FE := c_FE) (c_PO := c_PO) (c_WO := c_WO) (c_FO := c_FO) (c_ICR := c_ICR) (c_IE := c_IE)) ?_
    intro v w' h' ⟨hv, hFr, hfu', hQ, hHI'⟩
    exact ⟨hFr, by omega, hQ, hHI'⟩

end ReactRenderClick
