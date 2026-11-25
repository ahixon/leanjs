import JSProofs.FactsCompose
import JSProofs.ReactUseFiber
import JSProofs.ReactReconcileImpl
import JSProofs.ReactReconcileFibers
import JSProofs.ReactReconcileChildren
import JSProofs.ReactCounter
import JSProofs.ReactRenderHooks

/-! The render's callees composed in Lean (contract-style specs and `facts_compose`, replacing
`tools/gen_react_*.py`): `useFiber` with `createWorkInProgress`; `reconcileChildFibersImpl` with `useFiber`;
`reconcileChildFibers` with `reconcileChildFibersImpl`;
`reconcileChildren` with `reconcileChildFibers`;
the counter component with `useState`; `renderWithHooks` with the counter component. -/

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
