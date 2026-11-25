import JSProofs.FactsCompose
import JSProofs.ReactRenderClick
import JSProofs.ReactPerformSync
import JSProofs.ReactMicrotaskClick
import JSProofs.ReactFinishQueueing
import JSProofs.ReactPrepareFresh

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

namespace ReactRenderClick

-- `performWorkOnRoot` with `prepareFreshStack` (`ReactPrepareFresh.call_spec`; `P1`: its fields, framed from the
-- start) and `finishQueueingConcurrentUpdates` proved: the work loop's post (`P2`) says the queues'
-- function is there (`ReactFinishQueueing.Ready`) and that the render's result holds after its writes.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose work_render_fin {pX pA pQo pU pF pFa pH : ObjId} (f_code : dFQ.code = FQCGen.finishQueueingConcurrentUpdates_func)
    (f_cls : dFQ.isClassCtor = false) (f_mode : dFQ.thisMode = .strict) (f_env : dFQ.env = d.env) :=
    ReactRenderClick.work_render
    (P2 := fun w2 h => ReactFinishQueueing.Ready w2 d.env fFQ dFQ ∧ ∀ e w w', Frame (ReactRenderSync.fpEnd e d.env I) w2 w →
      ReactRenderSync.EndBinds w d.env oG ec → Frame (ReactFinishQueueing.fp d.env) w w' →
      ReactFinishQueueing.QueuesDone w' d.env → ∀ c, (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h) (w'.restore c) h)
    (fpFQ := ReactFinishQueueing.fp d.env) (kF := 20) (j := j + 10)
    (P1 := fun w' (_ : σ) => Frame ((({} : Footprint).union (ReactRenderSync.fpPre d.env I)).union (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)) s w' ∧
      ReactPrepareFresh.PrepBinds w' d.env oG R pX ∧ ∃ (vT vL vC vMP vMS vUQ vS vI vR vRC : Value) (fl hc fl' al : F64)
      (x0e x0c x1e x1c x2e x2c x3e x3c x4e x4c x5e x5c x6e x6c x7e x7c x8e x8c x9e x9c x10e x10c x11e x11c x12e x12c x13e x13c x14e x14c x15e x15c hcle hclc fle flc fale falc qpe qpc une unc : Bool),
      ReactPrepareFresh.PrepFields w' pX pH pF pFa pQo pU vT vL vC vMP vMS vUQ vS vI vR vRC fl hc fl' al x0e x0c x1e x1c x2e x2c x3e x3c x4e x4c x5e x5c x6e x6c x7e x7c x8e x8c x9e x9c x10e x10c x11e x11c x12e x12c x13e x13c x14e x14c x15e x15c hcle hclc fle flc fale falc qpe qpc une unc)
    (fpPF := (ReactPrepareFresh.fp d.env pX pA pQo pU pF pFa pH)) (kP := 400)
  | r_Prep => ReactPrepareFresh.call_spec (d := { dPF with env := d.env }) (oG := oG) (X := pX) (A := pA) (Qo := pQo)
      (U := pU) (F := pF) (Fa := pFa) (H := pH)
      by intro v w' h' hq
         obtain ⟨-, hF, hfu, hh, hA, hB, hP⟩ := hq
         subst hh
         exact ⟨hF, hfu, hA, ⟨frame_trans (frame_trans ‹Frame {} s _› ‹Frame (ReactRenderSync.fpPre _ _) _ _›) hF, hB,
           _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hP⟩, ‹HI _›⟩
  | r_Finish := fun sR _ fuR w2 w h1 hP2 hHI1 hFe hEB hfu =>
      wp_mono (ReactFinishQueueing.finish_of_ready (Post := (fun x h => (∃ C' alt bm x1 x2 x3 x4 x5 x6 x7, ReactPerformWork.RenderDone x d.env oG R C' alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PRu x h)) (c := sR) f_code f_cls f_mode f_env hP2.1 hP2.2 hFe hEB
        (by omega)) (fun _ _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, by rw [d]; exact hHI1⟩)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose sync_render_comp {pX pA pQo pU pF pFa pH : ObjId} {fpWL fpC fpE : Footprint} {kWL kC kE j : Nat} {I R : ObjId} :=
    ReactPerformSync.call_spec (n := j + 11) (root := .obj R) (lanes := .num (F64.fin false 4503599627370496 (-51)))
    (fpW := ⟨(ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).binds ++ fpC.binds ++ fpE.binds,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).props ++ fpC.props ++ fpE.props,
      (ReactRenderSync.fpRS dW.env I (ReactPrepareFresh.fp dW.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp dW.env)).jobs || fpC.jobs || fpE.jobs⟩)
    (kW := (400 + kWL + 20 + 300) + kC + kE + 300)
  | hWork => ReactRenderClick.work_render_fin (fo := fW) (d := dW) (t := .undefined) (I := I) (j := j)
      (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (fpWL := fpWL) (fpC := fpC) (fpE := fpE) (kW := kWL) (kC := kC) (kE := kE)
      (Q := fun w h => Q (w.restore s) h) same
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1, hq.2.2.2.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
facts_compose microtask_render_comp {pX pA pQo pU pF pFa pH : ObjId} {fpWL fpC fpE' : Footprint} {kWL kC kE j : Nat}
    {I : ObjId} {wD : FuncData} :=
    ReactMicrotaskClick.microtask_click (m := j + 12)
    (fpP := ⟨(ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).binds ++ fpC.binds ++ fpE'.binds,
      (ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).props ++ fpC.props ++ fpE'.props,
      (ReactRenderSync.fpRS wD.env I (ReactPrepareFresh.fp wD.env pX pA pQo pU pF pFa pH) fpWL (ReactFinishQueueing.fp wD.env)).jobs || fpC.jobs || fpE'.jobs⟩)
    (kP := (400 + kWL + 20 + 300) + kC + kE + 300 + 100)
  | hPerf => ReactRenderClick.sync_render_comp (fo := fS) (d := dS) (t := .undefined) (R := R) (oG := oG) (j := j)
      (dW := wD) (I := I) (pX := pX) (pA := pA) (pQo := pQo) (pU := pU) (pF := pF) (pFa := pFa) (pH := pH)
      (fpWL := fpWL) (fpC := fpC) (fpE := fpE') (kWL := kWL) (kC := kC) (kE := kE)
      (Q := (fun w h => ReactFlushSync.After w d.env oG R bdF ∧ (∃ a b c, (w.objEntry R).props.get? (.str "pendingLanes") =
        some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w h))
      by intro v w' h' hq; exact ⟨hq.2.1, by have := hq.2.2.1; omega, hq.2.2.2.1.1, hq.2.2.2.1.2.1, hq.2.2.2.1.2.2, hq.2.2.2.2⟩

end ReactRenderClick
