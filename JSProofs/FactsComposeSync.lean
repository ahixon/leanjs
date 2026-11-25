import JSProofs.FactsCompose
import JSProofs.ReactRenderClick
import JSProofs.ReactPerformSync
import JSProofs.ReactMicrotaskClick
import JSProofs.ReactFinishQueueing
import JSProofs.ReactPrepareFresh
import JSProofs.FactsComposeRender
import JSProofs.FactsComposeCompleteRoot
import JSProofs.ReactEnsureAfter

/-!
# The render from `performSyncWorkOnRoot`, composed (zippy docs/react-proofs.md)

`performWorkOnRoot` (`ReactRenderClick.work_render`) with `prepareFreshStack` and `finishQueueingConcurrentUpdates`
proved (`work_render_fin`); `performSyncWorkOnRoot(root, 2)` (`ReactPerformSync.call_spec`, whose work is the contract
`hWork` over an abstract footprint and fuel) with it: the outer footprint and fuel are the
work's, its postcondition `Q` read after `restore`; the click's microtask (`ReactMicrotaskClick.microtask_click`) with that render as
its `performSyncWorkOnRoot`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

facts_form ReactPerformSync.call_spec
facts_form ReactRenderClick.work_render
facts_form ReactMicrotaskClick.microtask_click
facts_form ReactPrepareFresh.call_spec
facts_post ReactPrepareFresh.call_spec
facts_post ReactCommitEntry.crw_comp

namespace ReactRenderClick

/-- `After` reads the heap and records, which `restore` keeps. -/
theorem after_restore {w c : State} {g : EnvId} {oG : Option EnvId} {R : ObjId} {bdF : Binding}
    (h : ReactFlushSync.After w g oG R bdF) : ReactFlushSync.After (w.restore c) g oG R bdF := by
  cases h; constructor <;> assumption

-- `performWorkOnRoot` with `prepareFreshStack` (`ReactPrepareFresh.call_spec`; `P1`: its call state, framed from the
-- start, with its facts there, and its result's facts) and `finishQueueingConcurrentUpdates` proved: the work loop's post (`P2`) says the queues'
-- function is there (`ReactFinishQueueing.Ready`) and that the render's result holds after its writes.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose work_render_fin {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId}
    {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbFSR cbEn : Binding}
    {cD : FuncData} (hcD : cD.env = d.env) (f_code : dFQ.code = FQCGen.finishQueueingConcurrentUpdates_func)
    (f_cls : dFQ.isClassCtor = false) (f_mode : dFQ.thisMode = .strict) (f_env : dFQ.env = d.env) :=
    ReactRenderClick.work_render
    (P2 := fun w2 h => ReactFinishQueueing.Ready w2 d.env fFQ dFQ ∧ ∀ e w w', Frame (ReactRenderSync.fpEnd e d.env I) w2 w →
      ReactRenderSync.EndBinds w d.env oG ec → Frame (ReactFinishQueueing.fp d.env) w w' →
      ReactFinishQueueing.QueuesDone w' d.env → ∀ c, (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore c) h)
    (fpFQ := ReactFinishQueueing.fp d.env) (kF := 20) (j := j + 12)
    (PC := fun x h => ∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fE cD ws oG R v x h)
    (fpE := ReactEnsureRoot.fpS d.env) (kE := 20)
    (Q := fun x h => ReactFlushSync.After x d.env oG R cbFSR ∧
      (∃ a b c, (x.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧
      (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe cD ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x))
    (PRu := fun x (_ : σ) => ∃ wL e, ReactWorkLoop.work_loop_comp.PLex lD oG pX lC1 lOP lX wL ∧
      Frame ((ReactRenderSync.fpEnd e d.env I).union (ReactFinishQueueing.fp d.env)) wL x)
    (P1 := fun w' (_ : σ) => ∃ w0, Frame (({} : Footprint).union (ReactRenderSync.fpPre d.env I)) s w0 ∧
      Facts.holds [Fact.propP R (.str (JSStr.ofString "current")) (fun r => ∃ a b c, r = some (.data (.obj pH) a b c)),
        Fact.kindP R (fun K => K.isPlain = true),
        Fact.propP pH (.str (JSStr.ofString "alternate")) (fun r => ∃ a b c, r = some (.data (.obj pX) a b c)),
        Fact.kindP pH (fun K => K.isPlain = true)] w0 ∧
      (∃ bm, Scope.declLike? (w0.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "executionContext"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "workInProgressTransitions"]? = some bd ∧ bd.value = some .null)) ∧
      Frame (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) w0 w' ∧
      ReactPrepareFresh.call_spec.PLex { dPF with env := d.env } oG R pH pX pF pFa pQo pU w')
    (fpPF := (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)) (kP := 400)
  | r_Prep => ReactPrepareFresh.call_spec (d := { dPF with env := d.env }) (oG := oG) (X := pX) (A := pA) (Qo := pQo)
      (U := pU) (F := pF) (Fa := pFa) (H := pH)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hF, hfu, hh, hA, -⟩ := hq
         refine ⟨hF, hfu, hA, ⟨_, frame_trans ‹Frame {} s _› ‹Frame (ReactRenderSync.fpPre _ _) _ _›,
           ?_, ‹∃ bm, Scope.declLike? _ = _ ∧ _›, hF,
           ReactPrepareFresh.call_spec.post_ex hq0⟩, hh ▸ ‹HI _›⟩
         refine Facts.holds_cons ?_ (Facts.holds_cons ?_ (Facts.holds_cons ?_ (Facts.holds_cons ?_ Facts.holds_nil)))
         all_goals dsimp only [Fact.propP, Fact.kindP]
         all_goals first
           | exact ⟨by facts_get hpreU, _, _, _, by facts_get hpreU⟩
           | exact ⟨by facts_get hpreU, by facts_get hpreU⟩
  | r_Loop => ReactWorkLoop.work_loop_comp (dPU := lD) (oG := oG) (Rw := pX) (C1 := lC1) (OP := lOP) (X := lX)
      with (lD.env = d.env ∧ Footprint.Sub (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp lD.env u_VS u_RI u_CF u_CS u_Cu u_Cx pX lC1) ⟨[(lD.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB u_K_d.env lC1 u_H0 u_Q u_RSI lX) ⟨[(u_K_d.env, "workInProgress")], [(lC1, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB lD.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU lD.env u_VS u_Cu u_Cx u_CS u_CF u_RI pX lC1 lX))))) fpWL ∧ 2400 ≤ kW ∧
        R ≠ u_Cu ∧ R ≠ u_CS ∧ R ≠ u_CF ∧ R ≠ u_RI)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hF, hfu, hh, -⟩ := hq
         obtain ⟨hdenv, hsub, hkW, hn1, hn2, hn3, hn4⟩ := hob.get.2
         obtain ⟨w0, hF0, hPre0, hX0, hFP, hPL1⟩ := ‹∃ w0, Frame _ s w0 ∧ _›
         repeat (obtain ⟨_, hPL1⟩ := hPL1)
         obtain ⟨Cn, F, hPLL, -⟩ := ReactWorkLoop.work_loop_comp.post_facts hq0
         have hX0f : Facts.holds [Fact.bind d.env oG (JSStr.ofString "executionContext")
             (fun b => ∃ bd, b = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true),
           Fact.bind d.env oG (JSStr.ofString "workInProgressTransitions") (fun b => ∃ bd, b = some bd ∧ bd.value = some .null)] w0 := by
           obtain ⟨bm, hd, h1, h2⟩ := hX0
           exact Facts.holds_cons ⟨lt_of_bind_P (P := fun b => ∃ bd, b = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) hd h1 (by simp), bm, hd, h1⟩
             (Facts.holds_cons ⟨lt_of_bind_P (P := fun b => ∃ bd, b = some bd ∧ bd.value = some .null) hd h2 (by simp), bm, hd, h2⟩ Facts.holds_nil)
         have hown : Frame (ReactRenderSync.fpOwn _) w1 w := ‹_›
         have c1 := frame_trans hown hF
         have c0 := frame_trans hFP c1
         have cs := frame_trans hF0 c0
         facts_frame hPre0 c0 as hA0
         facts_frame hX0f c0 as hB0
         facts_frame hPL1 c1 as hA1
         facts_frame hpre cs as hAS
         obtain ⟨hltL, bm, hdL⟩ : (Fact.record lD.env oG).holds w' := by facts_get hPLL
         have hd : Scope.declLike? (w'.envEntry d.env) = some (bm, oG) := hdenv ▸ hdL
         have hlt : d.env < w'.envs.size := hdenv ▸ hltL
         refine ⟨frame_mono hF hsub.1 hsub.2.1 hsub.2.2, Nat.le_trans hfu (Nat.add_le_add_left hkW _), ?_, ⟨?_, ?_⟩,
           hh ▸ ‹HI _›⟩
         · obtain ⟨bdE, hE1, hE2, -⟩ : ∃ bd, bm[JSStr.ofString "workInProgressRootExitStatus"]? = some bd ∧
               bd.value = some (.num (F64.fin false 5629499534213120 (-50))) ∧ bd.mutable = true := by facts_get hPLL
           obtain ⟨bdW, hW1, hW2⟩ : ∃ bd, bm[JSStr.ofString "workInProgress"]? = some bd ∧ bd.value = some .null := by
             facts_get hPLL
           obtain ⟨bdR, hR1, hR2, hR3⟩ : ∃ bd, bm[JSStr.ofString "workInProgressRoot"]? = some bd ∧ bd.value = some (.obj R) ∧
               bd.mutable = true := by facts_get hA1
           obtain ⟨bdL, hL1, hL2, hL3⟩ : ∃ bd, bm[JSStr.ofString "workInProgressRootRenderLanes"]? = some bd ∧
               bd.value = some (.num (F64.fin false 4503599627370496 (-51))) ∧ bd.mutable = true := by facts_get hA1
           refine ⟨bm, bdE, bdW, hd, hE1, hE2, hW1, hW2, ?_, ?_, ?_, ⟨bdR, hR1, hR3, by simp [hR2]⟩, ⟨bdL, hL1, hL3, by simp [hL2]⟩⟩
           · facts_get hPLL
           · facts_get hPLL
           · facts_get hB0
         · obtain ⟨bdI, hI1, hI2, hI3⟩ : ∃ bd, bm[JSStr.ofString "concurrentQueuesIndex"]? = some bd ∧ bd.mutable = true ∧
               bd.value = some (.num (F64.fin false 0 (-1074))) := by facts_get hA1
           obtain ⟨bdU, hU1, hU2, hU3⟩ : ∃ bd, bm[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bd ∧ bd.mutable = true ∧
               bd.value.isSome = true := by facts_get hA1
           exact ⟨hlt, by facts_get hAS, by facts_get hAS, bm, oG, bdI, bdU, hd, hI1, hI2, hI3, hU1, hU2, hU3⟩
         · intro e w3 w4 hFe _ hFQ _ c
           have cE := frame_restore (frame_trans hFe hFQ) c
           refine ⟨?_, w', e, ReactWorkLoop.work_loop_comp.post_ex hq0, cE⟩
           facts_frame hA0 cE as hR0
           facts_frame hA1 cE as hR1
           facts_frame hB0 cE as hRB
           obtain ⟨-, bmR, hdR⟩ : (Fact.record d.env oG).holds (w4.restore c) := by facts_get hR1
           refine ⟨pH, .obj pX, bmR, .null, .null, .bool false, .num (F64.fin false 0 (-1074)),
             .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)), .bool false,
             ⟨hdR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩⟩
           all_goals first | facts_get hR1 | facts_get hRB | facts_get hR0 | exact ⟨_, _, _, by facts_get hR0⟩
  | hComplete => ReactCommitEntry.crw_comp (EA := cEA) (XA := cXA) (dom := cdom) (RSI := cRSI) (RDSI := cRDSI) (kP := ckP)
      (R1 := cR1) (R2 := cR2) (gP := cgP) (bFSR := cbFSR) (bEn := cbEn) (fEn := fE) (d := cD) (oG := oG)
      with (Footprint.Sub (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE cD.env R).union ((((((ReactCommitRootFn.FPC cD.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB cD.env)).union
          (((ReactFlushMutation.FPRE cD.env cRSI cRDSI).union ((ReactCommitRoot.F0 cD.env).union
            (Footprint.union ⟨[(cD.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(cD.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(cD.env, JSStr.ofString "selectionInformation"), (cD.env, JSStr.ofString "eventsEnabled"),
              (cD.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL cD.env cRSI cRDSI)).union
          ((ReactSpawned.FPA cD.env cgP R).union (ReactEnsureCall.fpEn cD.env)))).union {})) {}) fpC ∧ 59400 + 100 ≤ kC)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hfu, w0, hP, hF0⟩ := hq
         obtain ⟨hsub, hkC⟩ := hob.get.2
         have hHIw : HI h' := by
           obtain ⟨⟨_, _, _, ⟨⟨_, ⟨⟨_, _, _, hh⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hP
           exact hh
         exact ⟨frame_mono (frame_trans hP.2 hF0) hsub.1 hsub.2.1 hsub.2.2, Nat.le_trans hfu (Nat.add_le_add_left hkC _),
           ⟨w, v, hq0⟩, hHIw⟩
  | hEnsure := fun w3 w h1 hPC hHI1 hO hfw => by
      obtain ⟨ws, v, hpost⟩ := hPC
      have hpost0 := hpost
      obtain ⟨-, -, w0, ⟨⟨s1, w0', -, ⟨⟨w1, ⟨-, hD⟩, hF1⟩, -⟩, hF2⟩, -⟩, hF3⟩ := hpost
      rw [hcD] at hD
      refine wp_mono (ReactEnsureAfter.ensure_call (sW := s) (sP := s)
        (Pu := fun x h => (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe cD ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x)) hD
        (frame_trans (frame_trans (frame_trans hF1 hF2) hF3) hO)
        (ReactEnsureAfter.binds_ne_of (e := s.envs.size) (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn])
          (Nat.ne_of_gt (by facts_get hpre)))
        (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn]) hfw
        (fun w' hS => ⟨_, w3, _, ⟨ws, v, hpost0⟩, frame_restore (frame_restore (frame_trans hO hS) s) s⟩)) ?_
      rintro v' w' h' ⟨hS, hfu, hA, hPL, hPu', hh⟩
      exact ⟨hS, hfu, ⟨hA, hPL, hPu'⟩, by rw [hh]; exact hHI1⟩
  | r_Finish := fun sR _ fuR w2 w h1 hP2 hHI1 hFe hEB hfu =>
      wp_mono (ReactFinishQueueing.finish_of_ready (σ := σ) (EP := fun w => ReactRenderSync.EndBinds w d.env oG ec) (Post := (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ ∃ wL e, ReactWorkLoop.work_loop_comp.PLex lD oG pX lC1 lOP lX wL ∧ Frame ((ReactRenderSync.fpEnd e d.env I).union (ReactFinishQueueing.fp d.env)) wL x)) (c := sR) f_code f_cls f_mode f_env hP2.1 hP2.2 hFe hEB
        (by omega)) (fun _ _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, by rw [d]; exact hHI1⟩)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose sync_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId} {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbFSR cbEn : Binding} {cD : FuncData}
    {fpWL fpC : Footprint} {kWL kC j : Nat} {I R : ObjId} :=
    ReactPerformSync.call_spec (n := j + 13) (root := .obj R) (lanes := .num (F64.fin false 4503599627370496 (-51)))
    (fpW := ⟨(ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).binds ++ fpC.binds ++ (ReactEnsureRoot.fpS dW.env).binds,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).props ++ fpC.props ++ (ReactEnsureRoot.fpS dW.env).props,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).jobs || fpC.jobs || (ReactEnsureRoot.fpS dW.env).jobs⟩)
    (kW := (400 + kWL + 20 + 300) + kC + 20 + 300)
    (Q := fun x h => ReactFlushSync.After x dW.env oG R cbFSR ∧
      (∃ a b c, (x.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧
      (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe cD ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS dW.env)) y x))
  | hWork => ReactRenderClick.work_render_fin (fo := fW) (d := dW) (t := .undefined) (I := I) (j := j)
      (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lC1 := lC1) (lX := lX) (lOP := lOP) (cEA := cEA) (cXA := cXA) (cdom := cdom) (cRSI := cRSI) (cRDSI := cRDSI) (ckP := ckP) (cR1 := cR1) (cR2 := cR2)
      (cgP := cgP) (cbEn := cbEn) (cD := cD) (cbFSR := cbFSR)
      (fpWL := fpWL) (fpC := fpC) (kW := kWL) (kC := kC) same
      by intro v w' h' hq
         obtain ⟨-, hF, hfu, ⟨hA, hPL, e, y, fe, hPC, hFy⟩, hHI⟩ := hq
         exact ⟨hF, by omega, ⟨after_restore hA, hPL, e, y, fe, hPC, frame_restore hFy s⟩, hHI⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose microtask_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId} {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbEn : Binding} {cD : FuncData}
    {fpWL fpC : Footprint} {kWL kC j : Nat} {I : ObjId} {wD : FuncData} :=
    ReactMicrotaskClick.microtask_click (m := j + 14)
    (fpP := ⟨(ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp d.env)).binds ++ fpC.binds ++ (ReactEnsureRoot.fpS d.env).binds,
      (ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp d.env)).props ++ fpC.props ++ (ReactEnsureRoot.fpS d.env).props,
      (ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp d.env)).jobs || fpC.jobs || (ReactEnsureRoot.fpS d.env).jobs⟩)
    (kP := (400 + kWL + 20 + 300) + kC + 20 + 300 + 100)
    (Pu := fun x h => (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP bdF cbEn fe cD ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x))
  | hPerf => ReactRenderClick.sync_render_comp (fo := fS) (d := dS) (t := .undefined) (R := R) (oG := oG) (j := j)
      (dW := { wD with env := d.env }) (I := I) (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lC1 := lC1) (lX := lX) (lOP := lOP) (cEA := cEA) (cXA := cXA) (cdom := cdom) (cRSI := cRSI) (cRDSI := cRDSI) (ckP := ckP) (cR1 := cR1) (cR2 := cR2)
      (cgP := cgP) (cbEn := cbEn) (cD := cD) (cbFSR := bdF)
      (fpWL := fpWL) (fpC := fpC) (kWL := kWL) (kC := kC)
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1.1, hq.2.2.2.1.2.1, hq.2.2.2.1.2.2, hq.2.2.2.2⟩

end ReactRenderClick
