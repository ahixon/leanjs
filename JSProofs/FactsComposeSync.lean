import JSProofs.FactsCompose
import JSProofs.ReactRenderClick
import JSProofs.ReactPerformSync
import JSProofs.ReactMicrotaskClick
import JSProofs.ReactFinishQueueing
import JSProofs.ReactPrepareFresh
import JSProofs.FactsComposeRender

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

namespace ReactRenderClick

-- `performWorkOnRoot` with `prepareFreshStack` (`ReactPrepareFresh.call_spec`; `P1`: its call state, framed from the
-- start, with its facts there, and its result's facts) and `finishQueueingConcurrentUpdates` proved: the work loop's post (`P2`) says the queues'
-- function is there (`ReactFinishQueueing.Ready`) and that the render's result holds after its writes.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose work_render_fin {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId} (f_code : dFQ.code = FQCGen.finishQueueingConcurrentUpdates_func)
    (f_cls : dFQ.isClassCtor = false) (f_mode : dFQ.thisMode = .strict) (f_env : dFQ.env = d.env) :=
    ReactRenderClick.work_render
    (P2 := fun w2 h => ReactFinishQueueing.Ready w2 d.env fFQ dFQ ∧ ∀ e w w', Frame (ReactRenderSync.fpEnd e d.env I) w2 w →
      ReactRenderSync.EndBinds w d.env oG ec → Frame (ReactFinishQueueing.fp d.env) w w' →
      ReactFinishQueueing.QueuesDone w' d.env → ∀ c, (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore c) h)
    (fpFQ := ReactFinishQueueing.fp d.env) (kF := 20) (j := j + 10)
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
  | r_Finish := fun sR _ fuR w2 w h1 hP2 hHI1 hFe hEB hfu =>
      wp_mono (ReactFinishQueueing.finish_of_ready (σ := σ) (EP := fun w => ReactRenderSync.EndBinds w d.env oG ec) (Post := (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ ∃ wL e, ReactWorkLoop.work_loop_comp.PLex lD oG pX lC1 lOP lX wL ∧ Frame ((ReactRenderSync.fpEnd e d.env I).union (ReactFinishQueueing.fp d.env)) wL x)) (c := sR) f_code f_cls f_mode f_env hP2.1 hP2.2 hFe hEB
        (by omega)) (fun _ _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, by rw [d]; exact hHI1⟩)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose sync_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId} {fpWL fpC fpE : Footprint} {kWL kC kE j : Nat} {I R : ObjId} :=
    ReactPerformSync.call_spec (n := j + 11) (root := .obj R) (lanes := .num (F64.fin false 4503599627370496 (-51)))
    (fpW := ⟨(ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).binds ++ fpC.binds ++ fpE.binds,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).props ++ fpC.props ++ fpE.props,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).jobs || fpC.jobs || fpE.jobs⟩)
    (kW := (400 + kWL + 20 + 300) + kC + kE + 300)
  | hWork => ReactRenderClick.work_render_fin (fo := fW) (d := dW) (t := .undefined) (I := I) (j := j)
      (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lC1 := lC1) (lX := lX) (lOP := lOP)
      (fpWL := fpWL) (fpC := fpC) (fpE := fpE) (kW := kWL) (kC := kC) (kE := kE)
      (Q := fun w h => Q (w.restore s) h) same
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1, hq.2.2.2.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose microtask_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lC1 lX lOP : ObjId} {fpWL fpC fpE' : Footprint} {kWL kC kE j : Nat}
    {I : ObjId} {wD : FuncData} :=
    ReactMicrotaskClick.microtask_click (m := j + 12)
    (fpP := ⟨(ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).binds ++ fpC.binds ++ fpE'.binds,
      (ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).props ++ fpC.props ++ fpE'.props,
      (ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).jobs || fpC.jobs || fpE'.jobs⟩)
    (kP := (400 + kWL + 20 + 300) + kC + kE + 300 + 100)
  | hPerf => ReactRenderClick.sync_render_comp (fo := fS) (d := dS) (t := .undefined) (R := R) (oG := oG) (j := j)
      (dW := wD) (I := I) (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lC1 := lC1) (lX := lX) (lOP := lOP)
      (fpWL := fpWL) (fpC := fpC) (fpE := fpE') (kWL := kWL) (kC := kC) (kE := kE)
      (Q := (fun w h => ReactFlushSync.After w d.env oG R bdF ∧ (∃ a b c, (w.objEntry R).props.get? (.str "pendingLanes") =
        some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w h))
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1.1, hq.2.2.2.1.2.1, hq.2.2.2.1.2.2, hq.2.2.2.2⟩
end ReactRenderClick
