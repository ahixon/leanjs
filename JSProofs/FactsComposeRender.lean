import JSProofs.FactsCompose
import JSProofs.ReactUseFiber
import JSProofs.ReactReconcileImpl
import JSProofs.ReactReconcileFibers
import JSProofs.ReactReconcileChildren
import JSProofs.ReactCounter
import JSProofs.ReactRenderHooks
import JSProofs.ReactUpdateFunction
import JSProofs.ReactBeginCounter

/-! The render's callees composed in Lean (contract-style specs and `facts_compose`, replacing
`tools/gen_react_*.py`): `useFiber` with `createWorkInProgress`; `reconcileChildFibersImpl` with `useFiber`;
`reconcileChildFibers` with `reconcileChildFibersImpl`;
`reconcileChildren` with `reconcileChildFibers`;
the counter component with `useState`; `renderWithHooks` with the counter component;
`updateFunctionComponent` with `renderWithHooks` and `reconcileChildren`; the counter's `beginWork` with
`updateFunctionComponent`. -/

facts_form ReactCreateWIP.reuse_spec
facts_form ReactUseFiber.spec_c

namespace ReactUseFiber
open ES Logic

facts_compose useFiber_comp := spec_c
  | hCW => ReactCreateWIP.reuse_spec (X := X) same

end ReactUseFiber

facts_form ReactReconcileImpl.click_spec_c

namespace ReactReconcileImpl
open ES Logic

facts_compose click_comp := click_spec_c
  | hUF => ReactUseFiber.useFiber_comp (X := X) (vT := vHT) same

end ReactReconcileImpl

facts_form ReactReconcileFibers.click_spec_c

namespace ReactReconcileFibers
open ES Logic

facts_compose click_comp := click_spec_c
  | hRI => ReactReconcileImpl.click_comp same

end ReactReconcileFibers

facts_form ReactReconcileChildren.click_spec_c

namespace ReactReconcileChildren
open ES Logic

facts_compose click_comp := click_spec_c
  | hcRF => ReactReconcileFibers.click_comp same

end ReactReconcileChildren

facts_form ReactUseState.click_spec
facts_form ReactCounter.click_spec_c

namespace ReactCounter
open ES Logic

facts_compose click_comp := click_spec_c
  | hcUS => ReactUseState.click_spec (d := d) same

end ReactCounter

facts_form ReactRenderHooks.click_spec_c

namespace ReactRenderHooks
open ES Logic ReactReducer

set_option maxHeartbeats 2000000 in
facts_compose click_comp := click_spec_c
  | hcK => ReactCounter.click_comp (d := d)
      (bG := (((bG.modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify
        (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })))
      (bdF := { bdF with value := some (.obj C1) }) (bdRL := { bdRL with value := some two })
      (bdSD := { bdSD with value := some (.bool false) }) same

end ReactRenderHooks

facts_form ReactUpdateFunction.click_spec_c

namespace ReactUpdateFunction
open ES Logic ReactReducer

set_option maxHeartbeats 2000000 in
facts_compose click_comp := click_spec_c
  | hcRW => ReactRenderHooks.click_comp (d := d)
      (bG := ((bG.modify (JSStr.ofString "currentlyRenderingFiber$1") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "lastContextDependency") (fun bd => { bd with value := some .null })))
      (rw := false) (ue := false) (le := false) (uwS := uw) (ucS := uc) same
  | hcRC => ReactReconcileChildren.click_comp (g := d.env) (El := E) (C := C) (RF := C1) (ln := two) (vEl := vT) (bG := bGc)
      (e1 := r_e1) (c1 := r_c1) (e2 := r_e2) (c2 := r_c2) (e3 := r_e3) (c3 := r_c3) (e4 := r_e4) (c4 := r_c4) (oG := oG) same

end ReactUpdateFunction

facts_form ReactBeginCounter.click_spec_c

namespace ReactBeginCounter
open ES Logic ReactReducer

set_option maxHeartbeats 2000000 in
facts_compose click_comp := click_spec_c
  | hcUF => ReactUpdateFunction.click_comp (d := d)
      (oG := oG) (bdDR := ({ bdDR with value := some (.bool false) })) (ln := (.num (F64.fin false 0 (-1074)))) (tUF := .undefined) (ec := false) (ee := false) (ew := false) (fw := false) (kc := false) (ke := false) (kw := false) (le := false) (r_pc := false) (r_pe := false) (r_pw := false) (rw := false) (tRW := .undefined) (ue := false) (yc := false) (ye := false) (yw := false) (uw := uw) (uc := uc) same

end ReactBeginCounter
