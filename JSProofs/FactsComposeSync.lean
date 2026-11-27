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
facts_compose work_render_fin {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lX lOP : ObjId}
    {lVS lRI lCF lCS lCu lCx lH0 : ObjId} {lKd : FuncData}
    {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbFSR cbEn : Binding}
    {cD : FuncData}
    {qfl qhc qfl' qal : F64} {qvT qvL qvC qvMP qvMS qvUQ qvS qvI qvR qvRC : Value} {qhcle qhclc qx0e qx0c qx1e qx1c qx2e qx2c qx3e qx3c qx4e qx4c qx5e qx5c qx6e qx6c qx7e qx7c qx8e qx8c qx9e qx9c qx10e qx10c qx11e qx11c qx12e qx12c qx13e qx13c qx14e qx14c qx15e qx15c qqpe qqpc qune qunc qfle qflc qfale qfalc : Bool}
    {wR_e_fl wxE wfl wB_e3 : F64} {wR_e_e3 wR_e_e5 wR_e_c3 wR_e_c5 wR_e_re wR_e_rc wr_e2 wr_c2 wr_e3 wr_c3 we5 wc5 we8 wc8 wrew wrec wB_se3 wB_sc3 wB_le3 wB_lc3 : Bool} (f_code : dFQ.code = FQCGen.finishQueueingConcurrentUpdates_func)
    (f_cls : dFQ.isClassCtor = false) (f_mode : dFQ.thisMode = .strict) (f_env : dFQ.env = d.env) :=
    ReactRenderClick.work_render
    (P2 := fun w2 h => ReactFinishQueueing.Ready w2 d.env fFQ dFQ ∧ ∀ e w w', Frame (ReactRenderSync.fpEnd e d.env I) w2 w →
      ReactRenderSync.EndBinds w d.env oG ec → Frame (ReactFinishQueueing.fp d.env) w w' →
      ReactFinishQueueing.QueuesDone w' d.env → ∀ c, (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore c) h)
    (fpFQ := ReactFinishQueueing.fp d.env) (kF := 20) (j := j + 12)
    (PC := fun x h => ∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fE { cD with env := d.env } ws oG R v x h)
    (fpE := ReactEnsureRoot.fpS d.env) (kE := 20)
    (fpWL := (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX))))))
    (fpC := (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE d.env R).union ((((((ReactCommitRootFn.FPC d.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env cRSI cRDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env cRSI cRDSI)).union
          ((ReactSpawned.FPA d.env cgP R).union (ReactEnsureCall.fpEn d.env)))).union {})) {}))
    (Q := fun x h => ReactFlushSync.After x d.env oG R cbFSR ∧
      (∃ a b c, (x.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧
      (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe { cD with env := d.env } ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x))
    (PRu := fun x (_ : σ) => (∃ bm, ReactPerformWork.RenderDone x d.env oG R pH (.obj pX) bm .null .null (.bool false) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.bool false)) ∧ (∃ w3 w4, ReactRenderSync.EndBinds w3 d.env oG ec ∧ Frame (ReactFinishQueueing.fp d.env) w3 w4 ∧ ReactFinishQueueing.QueuesDone w4 d.env ∧ Frame {} w4 x) ∧ Facts.holds [Fact.bind d.env oG (JSStr.ofString "pendingEffectsLanes") (fun b => ∃ bd, b = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true)] x ∧ ∃ wL e e' Cn F, Frame ((((({} : Footprint).union (ReactRenderSync.fpPre d.env I)).union (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)).union (ReactRenderSync.fpOwn e')).union (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX)))))) s wL ∧ Facts.holds (ReactWorkLoop.work_loop_comp.PL { lD with env := d.env } oG pX pFa wR_e_fl wR_e_e3 wR_e_e5 wR_e_c3 wR_e_c5 wR_e_re wR_e_rc lOP wxE lX wfl wr_e2 wr_c2 wr_e3 wr_c3 we5 wc5 we8 wc8 wrew wrec wB_e3 wB_se3 wB_sc3 wB_le3 wB_lc3 Cn F) wL ∧
      Frame ((ReactRenderSync.fpEnd e d.env I).union (ReactFinishQueueing.fp d.env)) wL x)
    (P1 := fun w' (_ : σ) => ∃ w0, Frame (({} : Footprint).union (ReactRenderSync.fpPre d.env I)) s w0 ∧
      Facts.holds [Fact.propP R (.str (JSStr.ofString "current")) (fun r => ∃ a b c, r = some (.data (.obj pH) a b c)),
        Fact.kindP R (fun K => K.isPlain = true),
        Fact.propP pH (.str (JSStr.ofString "alternate")) (fun r => ∃ a b c, r = some (.data (.obj pX) a b c)),
        Fact.kindP pH (fun K => K.isPlain = true),
        Fact.propP I (.str (JSStr.ofString "H")) (fun r => ∃ v, r = some (.data v true he hc))] w0 ∧
      (∃ bm, Scope.declLike? (w0.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "executionContext"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "workInProgressTransitions"]? = some bd ∧ bd.value = some .null)) ∧
      Frame (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) w0 w' ∧
      Facts.holds (ReactPrepareFresh.call_spec.PL { dPF with env := d.env } oG R pH pX pF pFa pQo pU qfl qhc qfl' qal qvT qvL qvC qvMP qvMS qvUQ qvS qvI qvR qvRC qhcle qhclc qx0e qx0c qx1e qx1c qx2e qx2c qx3e qx3c qx4e qx4c qx5e qx5c qx6e qx6c qx7e qx7c qx8e qx8c qx9e qx9c qx10e qx10c qx11e qx11c qx12e qx12c qx13e qx13c qx14e qx14c qx15e qx15c qqpe qqpc qune qunc qfle qflc qfale qfalc) w')
    (fpPF := (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)) (kP := 400)
  | r_Prep => ReactPrepareFresh.call_spec (d := { dPF with env := d.env }) (oG := oG) (X := pX) (A := pA) (Qo := pQo)
      (U := pU) (F := pF) (Fa := pFa) (H := pH)
      (fl := qfl) (hc := qhc) (fl' := qfl') (al := qal) (vT := qvT) (vL := qvL) (vC := qvC) (vMP := qvMP) (vMS := qvMS) (vUQ := qvUQ) (vS := qvS) (vI := qvI) (vR := qvR) (vRC := qvRC) (hcle := qhcle) (hclc := qhclc) (x0e := qx0e) (x0c := qx0c) (x1e := qx1e) (x1c := qx1c) (x2e := qx2e) (x2c := qx2c) (x3e := qx3e) (x3c := qx3c) (x4e := qx4e) (x4c := qx4c) (x5e := qx5e) (x5c := qx5c) (x6e := qx6e) (x6c := qx6c) (x7e := qx7e) (x7c := qx7c) (x8e := qx8e) (x8c := qx8c) (x9e := qx9e) (x9c := qx9c) (x10e := qx10e) (x10c := qx10c) (x11e := qx11e) (x11c := qx11c) (x12e := qx12e) (x12c := qx12c) (x13e := qx13e) (x13c := qx13c) (x14e := qx14e) (x14c := qx14c) (x15e := qx15e) (x15c := qx15c) (qpe := qqpe) (qpc := qqpc) (une := qune) (unc := qunc) (fle := qfle) (flc := qflc) (fale := qfale) (falc := qfalc)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hF, hfu, hh, hA, -⟩ := hq
         refine ⟨hF, hfu, hA, ⟨_, frame_trans ‹Frame {} s _› ‹Frame (ReactRenderSync.fpPre _ _) _ _›,
           ?_, ‹∃ bm, Scope.declLike? _ = _ ∧ _›, hF,
           (ReactPrepareFresh.call_spec.post_facts hq0).1⟩, hh ▸ ‹HI _›⟩
         refine Facts.holds_cons ?_ (Facts.holds_cons ?_ (Facts.holds_cons ?_ (Facts.holds_cons ?_
           (Facts.holds_cons ?_ Facts.holds_nil))))
         all_goals dsimp only [Fact.propP, Fact.kindP]
         all_goals first
           | exact ⟨by facts_get hpreU, _, _, _, by facts_get hpreU⟩
           | exact ⟨by facts_get hpreU, by facts_get hpreU⟩
           | (obtain ⟨v, hH⟩ := ‹∃ v, ((_ : State).objEntry I).props.get? (.str "H") = some (.data v true he hc)›
              exact ⟨lt_of_props_ne_none (by rw [hH]; simp), v, hH⟩)
  | r_Loop => ReactWorkLoop.work_loop_comp (dPU := { lD with env := d.env }) (oG := oG) (Rw := pX) (C1 := pFa) (OP := lOP) (X := lX)
      (VS := lVS) (RI := lRI) (CF := lCF) (CS := lCS) (Cu := lCu) (Cx := lCx) (K_d := { lKd with env := d.env }) (H0 := lH0) (Q := pQo) (RSI := I) (U := pU) (un := (true, qune, qunc))
      (R_e_fl := wR_e_fl) (R_e_e3 := wR_e_e3) (R_e_e5 := wR_e_e5) (R_e_c3 := wR_e_c3) (R_e_c5 := wR_e_c5) (R_e_re := wR_e_re) (R_e_rc := wR_e_rc) (xE := wxE) (fl := wfl) (r_e2 := wr_e2) (r_c2 := wr_c2) (r_e3 := wr_e3) (r_c3 := wr_c3) (e5 := we5) (c5 := wc5) (e8 := we8) (c8 := wc8) (rew := wrew) (rec := wrec) (B_e3 := wB_e3) (B_se3 := wB_se3) (B_sc3 := wB_sc3) (B_le3 := wB_le3) (B_lc3 := wB_lc3)
      with (2400 ≤ kW ∧ R ≠ lCu ∧ R ≠ lCS ∧ R ≠ lCF ∧ R ≠ lRI)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hF, hfu, hh, -⟩ := hq
         obtain ⟨hkW, hn1, hn2, hn3, hn4⟩ := hob.get.2
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
         obtain ⟨hlt, bm, hd⟩ : (Fact.record d.env oG).holds w' := by facts_get hPLL
         refine ⟨hF, Nat.le_trans hfu (Nat.add_le_add_left hkW _), ?_, ⟨?_, ?_⟩,
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
         · intro e w3 w4 hFe hEBw hFQ hQD c
           have cE := frame_restore (frame_trans hFe hFQ) c
           -- (the render's values, stated: the commit's obligation reads them, `RenderDone`'s own are any)
           facts_frame hA1 cE as hR1
           suffices hRD : ∃ bm, ReactPerformWork.RenderDone (w4.restore c) d.env oG R pH (.obj pX) bm .null .null
               (.bool false) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.bool false) by
             obtain ⟨bmR', hRD'⟩ := hRD
             exact ⟨⟨pH, .obj pX, bmR', .null, .null, .bool false, .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)), .bool false, hRD'⟩,
               ⟨bmR', hRD'⟩, ⟨w3, w4, hEBw, hFQ, hQD, frame_restore (frame_refl _ w4) c⟩,
               Facts.holds_cons (by facts_get hR1) Facts.holds_nil,
               w', e, _, Cn, F, frame_trans (frame_trans (frame_trans hF0 hFP) hown) hF, hPLL, cE⟩
           facts_frame hA0 cE as hR0
           facts_frame hB0 cE as hRB
           obtain ⟨-, bmR, hdR⟩ : (Fact.record d.env oG).holds (w4.restore c) := by facts_get hR1
           refine ⟨bmR, ⟨hdR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩⟩
           all_goals first | facts_get hR1 | facts_get hRB | facts_get hR0 | exact ⟨_, _, _, by facts_get hR0⟩
  | hComplete => ReactCommitEntry.crw_comp (EA := cEA) (XA := cXA) (dom := cdom) (RSI := cRSI) (RDSI := cRDSI) (kP := ckP)
      (R1 := cR1) (R2 := cR2) (gP := cgP) (bFSR := cbFSR) (bEn := cbEn) (fEn := fE) (d := { cD with env := d.env }) (oG := oG)
      with (59400 + 100 ≤ kC)
      by intro v w' h' hq
         have hq0 := hq
         obtain ⟨-, hfu, w0, hP, hF0⟩ := hq
         have hkC := hob.get.2
         have hHIw : HI h' := by
           obtain ⟨⟨_, _, _, ⟨⟨_, ⟨⟨_, _, _, hh⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hP
           exact hh
         exact ⟨frame_trans hP.2 hF0, Nat.le_trans hfu (Nat.add_le_add_left hkC _),
           ⟨w, v, hq0⟩, hHIw⟩
  | hEnsure := fun w3 w h1 hPC hHI1 hO hfw => by
      obtain ⟨ws, v, hpost⟩ := hPC
      have hpost0 := hpost
      obtain ⟨-, -, w0, ⟨⟨s1, w0', -, ⟨⟨w1, ⟨-, hD⟩, hF1⟩, -⟩, hF2⟩, -⟩, hF3⟩ := hpost
      refine wp_mono (ReactEnsureAfter.ensure_call (sW := s) (sP := s)
        (Pu := fun x h => (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe { cD with env := d.env } ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x)) hD
        (frame_trans (frame_trans (frame_trans hF1 hF2) hF3) hO)
        (ReactEnsureAfter.binds_ne_of (e := s.envs.size) (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn])
          (Nat.ne_of_gt (by facts_get hpre)))
        (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn]) hfw
        (fun w' hS => ⟨_, w3, _, ⟨ws, v, hpost0⟩, frame_restore (frame_restore (frame_trans hO hS) s) s⟩)) ?_
      rintro v' w' h' ⟨hS, hfu, hA, hPL, hPu', hh⟩
      exact ⟨hS, hfu, ⟨hA, hPL, hPu'⟩, by rw [hh]; exact hHI1⟩
  | r_Finish := fun sR _ fuR w2 w h1 hP2 hHI1 hFe hEB hfu =>
      wp_mono (ReactFinishQueueing.finish_of_ready (σ := σ) (EP := fun w => ReactRenderSync.EndBinds w d.env oG ec) (Post := (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ (∃ bm, ReactPerformWork.RenderDone x d.env oG R pH (.obj pX) bm .null .null (.bool false) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) (.bool false)) ∧ (∃ w3 w4, ReactRenderSync.EndBinds w3 d.env oG ec ∧ Frame (ReactFinishQueueing.fp d.env) w3 w4 ∧ ReactFinishQueueing.QueuesDone w4 d.env ∧ Frame {} w4 x) ∧ Facts.holds [Fact.bind d.env oG (JSStr.ofString "pendingEffectsLanes") (fun b => ∃ bd, b = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true)] x ∧ ∃ wL e e' Cn F, Frame ((((({} : Footprint).union (ReactRenderSync.fpPre d.env I)).union (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)).union (ReactRenderSync.fpOwn e')).union (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX)))))) s wL ∧ Facts.holds (ReactWorkLoop.work_loop_comp.PL { lD with env := d.env } oG pX pFa wR_e_fl wR_e_e3 wR_e_e5 wR_e_c3 wR_e_c5 wR_e_re wR_e_rc lOP wxE lX wfl wr_e2 wr_c2 wr_e3 wr_c3 we5 wc5 we8 wc8 wrew wrec wB_e3 wB_se3 wB_sc3 wB_le3 wB_lc3 Cn F) wL ∧ Frame ((ReactRenderSync.fpEnd e d.env I).union (ReactFinishQueueing.fp d.env)) wL x)) (c := sR) f_code f_cls f_mode f_env hP2.1 hP2.2 hFe hEB
        (by omega)) (fun _ _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, by rw [d]; exact hHI1⟩)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose sync_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lX lOP : ObjId} {lVS lRI lCF lCS lCu lCx lH0 : ObjId} {lKd : FuncData} {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbFSR cbEn : Binding} {cD : FuncData}
    {qfl qhc qfl' qal : F64} {qvT qvL qvC qvMP qvMS qvUQ qvS qvI qvR qvRC : Value} {qhcle qhclc qx0e qx0c qx1e qx1c qx2e qx2c qx3e qx3c qx4e qx4c qx5e qx5c qx6e qx6c qx7e qx7c qx8e qx8c qx9e qx9c qx10e qx10c qx11e qx11c qx12e qx12c qx13e qx13c qx14e qx14c qx15e qx15c qqpe qqpc qune qunc qfle qflc qfale qfalc : Bool} {wR_e_fl wxE wfl wB_e3 : F64} {wR_e_e3 wR_e_e5 wR_e_c3 wR_e_c5 wR_e_re wR_e_rc wr_e2 wr_c2 wr_e3 wr_c3 we5 wc5 we8 wc8 wrew wrec wB_se3 wB_sc3 wB_le3 wB_lc3 : Bool}
    {kWL kC j : Nat} {I R : ObjId} :=
    ReactPerformSync.call_spec (n := j + 13) (root := .obj R) (lanes := .num (F64.fin false 4503599627370496 (-51)))
    (fpW := ⟨(ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp dW.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(dW.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB dW.env pFa lH0 pQo I lX) ⟨[(dW.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB dW.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU dW.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp dW.env)).binds ++ (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE dW.env R).union ((((((ReactCommitRootFn.FPC dW.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB dW.env)).union
          (((ReactFlushMutation.FPRE dW.env cRSI cRDSI).union ((ReactCommitRoot.F0 dW.env).union
            (Footprint.union ⟨[(dW.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(dW.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(dW.env, JSStr.ofString "selectionInformation"), (dW.env, JSStr.ofString "eventsEnabled"),
              (dW.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL dW.env cRSI cRDSI)).union
          ((ReactSpawned.FPA dW.env cgP R).union (ReactEnsureCall.fpEn dW.env)))).union {})) {}).binds ++ (ReactEnsureRoot.fpS dW.env).binds,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp dW.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(dW.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB dW.env pFa lH0 pQo I lX) ⟨[(dW.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB dW.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU dW.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp dW.env)).props ++ (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE dW.env R).union ((((((ReactCommitRootFn.FPC dW.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB dW.env)).union
          (((ReactFlushMutation.FPRE dW.env cRSI cRDSI).union ((ReactCommitRoot.F0 dW.env).union
            (Footprint.union ⟨[(dW.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(dW.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(dW.env, JSStr.ofString "selectionInformation"), (dW.env, JSStr.ofString "eventsEnabled"),
              (dW.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL dW.env cRSI cRDSI)).union
          ((ReactSpawned.FPA dW.env cgP R).union (ReactEnsureCall.fpEn dW.env)))).union {})) {}).props ++ (ReactEnsureRoot.fpS dW.env).props,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp dW.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(dW.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB dW.env pFa lH0 pQo I lX) ⟨[(dW.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB dW.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU dW.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp dW.env)).jobs || (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE dW.env R).union ((((((ReactCommitRootFn.FPC dW.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB dW.env)).union
          (((ReactFlushMutation.FPRE dW.env cRSI cRDSI).union ((ReactCommitRoot.F0 dW.env).union
            (Footprint.union ⟨[(dW.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(dW.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(dW.env, JSStr.ofString "selectionInformation"), (dW.env, JSStr.ofString "eventsEnabled"),
              (dW.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL dW.env cRSI cRDSI)).union
          ((ReactSpawned.FPA dW.env cgP R).union (ReactEnsureCall.fpEn dW.env)))).union {})) {}).jobs || (ReactEnsureRoot.fpS dW.env).jobs⟩)
    (kW := (400 + kWL + 20 + 300) + kC + 20 + 300)
    (Q := fun x h => ReactFlushSync.After x dW.env oG R cbFSR ∧
      (∃ a b c, (x.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧
      (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP cbFSR cbEn fe { cD with env := dW.env } ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS dW.env)) y x))
  | hWork => ReactRenderClick.work_render_fin (fo := fW) (d := dW) (t := .undefined) (I := I) (j := j)
      (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lX := lX) (lOP := lOP)
      (lVS := lVS) (lRI := lRI) (lCF := lCF) (lCS := lCS) (lCu := lCu) (lCx := lCx) (lH0 := lH0) (lKd := lKd) (cEA := cEA) (cXA := cXA) (cdom := cdom) (cRSI := cRSI) (cRDSI := cRDSI) (ckP := ckP) (cR1 := cR1) (cR2 := cR2)
      (cgP := cgP) (cbEn := cbEn) (cD := cD)
      (qfl := qfl) (qhc := qhc) (qfl' := qfl') (qal := qal) (qvT := qvT) (qvL := qvL) (qvC := qvC) (qvMP := qvMP) (qvMS := qvMS) (qvUQ := qvUQ) (qvS := qvS) (qvI := qvI) (qvR := qvR) (qvRC := qvRC) (qhcle := qhcle) (qhclc := qhclc) (qx0e := qx0e) (qx0c := qx0c) (qx1e := qx1e) (qx1c := qx1c) (qx2e := qx2e) (qx2c := qx2c) (qx3e := qx3e) (qx3c := qx3c) (qx4e := qx4e) (qx4c := qx4c) (qx5e := qx5e) (qx5c := qx5c) (qx6e := qx6e) (qx6c := qx6c) (qx7e := qx7e) (qx7c := qx7c) (qx8e := qx8e) (qx8c := qx8c) (qx9e := qx9e) (qx9c := qx9c) (qx10e := qx10e) (qx10c := qx10c) (qx11e := qx11e) (qx11c := qx11c) (qx12e := qx12e) (qx12c := qx12c) (qx13e := qx13e) (qx13c := qx13c) (qx14e := qx14e) (qx14c := qx14c) (qx15e := qx15e) (qx15c := qx15c) (qqpe := qqpe) (qqpc := qqpc) (qune := qune) (qunc := qunc) (qfle := qfle) (qflc := qflc) (qfale := qfale) (qfalc := qfalc)
      (wR_e_fl := wR_e_fl) (wR_e_e3 := wR_e_e3) (wR_e_e5 := wR_e_e5) (wR_e_c3 := wR_e_c3) (wR_e_c5 := wR_e_c5) (wR_e_re := wR_e_re) (wR_e_rc := wR_e_rc) (wxE := wxE) (wfl := wfl) (wr_e2 := wr_e2) (wr_c2 := wr_c2) (wr_e3 := wr_e3) (wr_c3 := wr_c3) (we5 := we5) (wc5 := wc5) (we8 := we8) (wc8 := wc8) (wrew := wrew) (wrec := wrec) (wB_e3 := wB_e3) (wB_se3 := wB_se3) (wB_sc3 := wB_sc3) (wB_le3 := wB_le3) (wB_lc3 := wB_lc3) (cbFSR := cbFSR)
      (kW := kWL) (kC := kC) same
      by intro v w' h' hq
         obtain ⟨-, hF, hfu, ⟨hA, hPL, e, y, fe, hPC, hFy⟩, hHI⟩ := hq
         exact ⟨hF, by omega, ⟨after_restore hA, hPL, e, y, fe, hPC, frame_restore hFy s⟩, hHI⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose microtask_render_comp {pX pA pQo pU pF pFa pH : ObjId} {lD : FuncData} {lX lOP : ObjId} {lVS lRI lCF lCS lCu lCx lH0 : ObjId} {lKd : FuncData} {cEA cXA cdom cRSI cRDSI : ObjId} {ckP : JSStr} {cR1 cR2 : State → σ → Prop} {cgP : EnvId} {cbEn : Binding} {cD : FuncData}
    {qfl qhc qfl' qal : F64} {qvT qvL qvC qvMP qvMS qvUQ qvS qvI qvR qvRC : Value} {qhcle qhclc qx0e qx0c qx1e qx1c qx2e qx2c qx3e qx3c qx4e qx4c qx5e qx5c qx6e qx6c qx7e qx7c qx8e qx8c qx9e qx9c qx10e qx10c qx11e qx11c qx12e qx12c qx13e qx13c qx14e qx14c qx15e qx15c qqpe qqpc qune qunc qfle qflc qfale qfalc : Bool} {wR_e_fl wxE wfl wB_e3 : F64} {wR_e_e3 wR_e_e5 wR_e_c3 wR_e_c5 wR_e_re wR_e_rc wr_e2 wr_c2 wr_e3 wr_c3 we5 wc5 we8 wc8 wrew wrec wB_se3 wB_sc3 wB_le3 wB_lc3 : Bool}
    {kWL kC j : Nat} {I : ObjId} {wD : FuncData} :=
    ReactMicrotaskClick.microtask_click (m := j + 14)
    (fpP := ⟨(ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp d.env)).binds ++ (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE d.env R).union ((((((ReactCommitRootFn.FPC d.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env cRSI cRDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env cRSI cRDSI)).union
          ((ReactSpawned.FPA d.env cgP R).union (ReactEnsureCall.fpEn d.env)))).union {})) {}).binds ++ (ReactEnsureRoot.fpS d.env).binds,
      (ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp d.env)).props ++ (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE d.env R).union ((((((ReactCommitRootFn.FPC d.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env cRSI cRDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env cRSI cRDSI)).union
          ((ReactSpawned.FPA d.env cgP R).union (ReactEnsureCall.fpEn d.env)))).union {})) {}).props ++ (ReactEnsureRoot.fpS d.env).props,
      (ReactRenderSync.fpRS d.env I (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginRoot.fp d.env lVS lRI lCF lCS lCu lCx pX pFa) ⟨[(d.env, "workInProgress")], [(pX, .str "memoizedProps")], false⟩) (Logic.Footprint.union (Logic.Footprint.union (ReactBeginCounter.fpB d.env pFa lH0 pQo I lX) ⟨[(d.env, "workInProgress")], [(pFa, .str "memoizedProps")], false⟩) (Logic.Footprint.union (ReactBeginButton.fpBB d.env lX) (Logic.Footprint.union ⟨[], [(lX, .str "memoizedProps")], false⟩ (ReactCompleteUnit.fpU d.env lVS lCu lCx lCS lCF lRI pX pFa lX))))) (ReactFinishQueueing.fp d.env)).jobs || (Footprint.union (Footprint.union ⟨[], [(R, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((ReactCommitEntry.FPE d.env R).union ((((((ReactCommitRootFn.FPC d.env R cRSI cRDSI).union (ReactMarkFinished.FPM R cEA cXA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env cRSI cRDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(cdom, .str ckP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(R, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env cRSI cRDSI)).union
          ((ReactSpawned.FPA d.env cgP R).union (ReactEnsureCall.fpEn d.env)))).union {})) {}).jobs || (ReactEnsureRoot.fpS d.env).jobs⟩)
    (kP := (400 + kWL + 20 + 300) + kC + 20 + 300 + 100)
    (Pu := fun x h => (∃ e y fe, (∃ ws v, ReactCommitEntry.crw_comp.Post σ HI cEA cXA cdom cRSI cRDSI ckP cR1 cR2 cgP bdF cbEn fe { cD with env := d.env } ws oG R v y h) ∧ Frame ((ReactPerformWork.fpOwn e).union (ReactEnsureRoot.fpS d.env)) y x))
  | hPerf => ReactRenderClick.sync_render_comp (fo := fS) (d := { dS with env := d.env }) (t := .undefined) (R := R) (oG := oG) (j := j)
      (dW := { wD with env := d.env }) (I := I) (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (lD := lD) (lX := lX) (lOP := lOP)
      (lVS := lVS) (lRI := lRI) (lCF := lCF) (lCS := lCS) (lCu := lCu) (lCx := lCx) (lH0 := lH0) (lKd := lKd) (cEA := cEA) (cXA := cXA) (cdom := cdom) (cRSI := cRSI) (cRDSI := cRDSI) (ckP := ckP) (cR1 := cR1) (cR2 := cR2)
      (cgP := cgP) (cbEn := cbEn) (cD := cD)
      (qfl := qfl) (qhc := qhc) (qfl' := qfl') (qal := qal) (qvT := qvT) (qvL := qvL) (qvC := qvC) (qvMP := qvMP) (qvMS := qvMS) (qvUQ := qvUQ) (qvS := qvS) (qvI := qvI) (qvR := qvR) (qvRC := qvRC) (qhcle := qhcle) (qhclc := qhclc) (qx0e := qx0e) (qx0c := qx0c) (qx1e := qx1e) (qx1c := qx1c) (qx2e := qx2e) (qx2c := qx2c) (qx3e := qx3e) (qx3c := qx3c) (qx4e := qx4e) (qx4c := qx4c) (qx5e := qx5e) (qx5c := qx5c) (qx6e := qx6e) (qx6c := qx6c) (qx7e := qx7e) (qx7c := qx7c) (qx8e := qx8e) (qx8c := qx8c) (qx9e := qx9e) (qx9c := qx9c) (qx10e := qx10e) (qx10c := qx10c) (qx11e := qx11e) (qx11c := qx11c) (qx12e := qx12e) (qx12c := qx12c) (qx13e := qx13e) (qx13c := qx13c) (qx14e := qx14e) (qx14c := qx14c) (qx15e := qx15e) (qx15c := qx15c) (qqpe := qqpe) (qqpc := qqpc) (qune := qune) (qunc := qunc) (qfle := qfle) (qflc := qflc) (qfale := qfale) (qfalc := qfalc)
      (wR_e_fl := wR_e_fl) (wR_e_e3 := wR_e_e3) (wR_e_e5 := wR_e_e5) (wR_e_c3 := wR_e_c3) (wR_e_c5 := wR_e_c5) (wR_e_re := wR_e_re) (wR_e_rc := wR_e_rc) (wxE := wxE) (wfl := wfl) (wr_e2 := wr_e2) (wr_c2 := wr_c2) (wr_e3 := wr_e3) (wr_c3 := wr_c3) (we5 := we5) (wc5 := wc5) (we8 := we8) (wc8 := wc8) (wrew := wrew) (wrec := wrec) (wB_e3 := wB_e3) (wB_se3 := wB_se3) (wB_sc3 := wB_sc3) (wB_le3 := wB_le3) (wB_lc3 := wB_lc3) (cbFSR := bdF)
      (kWL := kWL) (kC := kC)
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1.1, hq.2.2.2.1.2.1, hq.2.2.2.1.2.2, hq.2.2.2.2⟩

end ReactRenderClick
