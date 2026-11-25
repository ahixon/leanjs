import JSProofs.FactsCompose
import JSProofs.ReactUseFiber
import JSProofs.ReactReconcileImpl
import JSProofs.ReactReconcileFibers
import JSProofs.ReactReconcileChildren
import JSProofs.ReactCounter
import JSProofs.ReactRenderHooks
import JSProofs.ReactUpdateFunction
import JSProofs.ReactBeginCounter
import JSProofs.ReactUnitCounter
import JSProofs.ReactUnitButton
import JSProofs.ReactEarlyBailout

/-! The render's callees composed in Lean (contract-style specs and `facts_compose`, replacing
`tools/gen_react_*.py`): `useFiber` with `createWorkInProgress`; `reconcileChildFibersImpl` with `useFiber`;
`reconcileChildFibers` with `reconcileChildFibersImpl`;
`reconcileChildren` with `reconcileChildFibers`;
the counter component with `useState`; `renderWithHooks` with the counter component;
`updateFunctionComponent` with `renderWithHooks` and `reconcileChildren`; the counter's `beginWork` with
`updateFunctionComponent`; `performUnitOfWork` on the counter with its `beginWork`; on the button with its `beginWork` and
`completeUnitOfWork`; the root's early bailout with its four callees. -/

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

facts_form ReactUnitCounter.counter_unit_spec_c

namespace ReactUnitCounter
open ES Logic ReactReducer

set_option maxHeartbeats 2000000 in
facts_compose counter_unit_comp := counter_unit_spec_c
  | hcBW => ReactBeginCounter.click_comp (d := d) (r := (.obj fBS)) (tB := .undefined) same

end ReactUnitCounter

facts_form ReactBeginButton.button_spec
facts_form ReactCompleteUnit.unit_spec
facts_form ReactUnitButton.button_unit_spec_c

namespace ReactUnitButton
open ES Logic

set_option maxHeartbeats 2000000 in
facts_compose button_unit_comp := button_unit_spec_c
  | hcBB => ReactBeginButton.button_spec (fB := b_fB) (dB := b_dB) (tB := .undefined) (str := b_str) (bdDR := b_bdDR) (bdPH := b_bdPH) (bdSS := b_bdSS) (bdMR := b_bdMR) (bdRC := b_bdRC) (bdCSC := bdCS) (bdGC := b_bdGC) (bdRCF := b_bdRCF) (bdT := b_bdT) (bdTS := b_bdTS) (fPH := b_fPH) (fSS := b_fSS) (fMR := b_fMR) (fC := b_fC) (fGC := b_fGC) (fR := b_fR) (dPH := b_dPH) (dSS := b_dSS) (dMR := b_dMR) (dC := b_dC) (dGC := b_dGC) (dR := b_dR) (bdRI := b_bdRI) (bdDel := b_bdDel) (bdST := b_bdST) (fI := b_fI) (fDel := b_fDel) (dI := b_dI) (dDel := b_dDel) (mpw := b_mpw) (mpe := b_mpe) (mpc := b_mpc) (hcw := b_hcw) (hce := b_hce) (hcc := b_hcc) (hrw := b_hrw) (hre := b_hre) (hrc := b_hrc) (ppw := b_ppw) (ppe := b_ppe) (ppc := b_ppc) (tgw := b_tgw) (tge := b_tge) (tgc := b_tgc) (tyw := b_tyw) (tye := b_tye) (tyc := b_tyc) (msw := b_msw) (mse := b_mse) (msc := b_msc) (xrw := b_xrw) (xre := b_xre) (xrc := b_xrc) (lw := b_lw) (lc := b_lc) (cw := b_cw) (cc := b_cc) (kw := b_kw) (ke := b_ke) (kc := b_kc) (csw := b_csw) (cse := b_cse) (csc := b_csc) (ch0 := b_ch0) (l0 := b_l0) same
  | hcCU => ReactCompleteUnit.unit_spec (fU := fCU) (dU := dCU) (tU := .undefined) (a := ((F64.fin false 0 (-1074)))) (cw := true) (ce := b_cw) (cc := b_cc) (xlw := true) (xle := b_lw) (xlc := b_lc) same

end ReactUnitButton

facts_form ReactHostContainer.call_spec
facts_form ReactRootBailout.provider_spec
facts_form ReactRootBailout.reset_spec
facts_form ReactBailout.root_spec
facts_form ReactEarlyBailout.root_spec_c

namespace ReactEarlyBailout
open ES Logic

set_option maxHeartbeats 4000000 in
facts_compose root_comp := root_spec_c
  | hcPHC => ReactHostContainer.call_spec (fo := fPHC) (d := dPHC) (t := .undefined) (bdCS := a_bdCS) (bdCF := a_bdCF) (bdRI := a_bdRI) (bdO := a_bdO) (bdGO := a_bdGO) (bdGC := a_bdGC) (CS := a_CS) (CF := a_CF) (RI := a_RI) (fO := a_fO) (fGO := a_fGO) (fGC := a_fGC) (dO := a_dO) (dGO := a_dGO) (dGC := a_dGC) (o0 := a_o0) (o1 := a_o1) (o2 := a_o2) (vr := a_vr) (vf := a_vf) (vc := a_vc) (e0 := a_e0) (c0 := a_c0) (e1 := a_e1) (c1 := a_c1) (e2 := a_e2) (c2 := a_c2) (re := a_re) (rc := a_rc) (fe := a_fe) (fc := a_fc) (ce := a_ce) (cc := a_cc) same
  | hcPPR => ReactRootBailout.provider_spec (bG := bG) (bdI := bdI) (fo := fPPR) (d := dPPR) (t := .undefined) (fib := ((.obj X))) (value := cache) (bG := bG) (bdI := bdI) (bdC := b_bdC) (Cu := b_Cu) (iv := ((F64.fin false 4503599627370496 (-51)))) (nv := ((F64.fin false 6755399441055744 (-51)))) (cur := b_cur) (old := b_old) (cv := b_cv) (ce := b_ce) (cc := b_cc) (oe := b_oe) (oc := b_oc) (xe := b_xe) (xc := b_xc) (i := 3) same
  | hcRHS => ReactRootBailout.reset_spec (bG := bG) (n := (n + 1)) (fo := fRHS) (d := dRHS) (t := .undefined) (b1 := c_b1) (b2 := c_b2) (b3 := c_b3) same
  | hcBOF => ReactBailout.root_spec (fo := fBOF) (d := dBOF) (t := .undefined) (bdS := e_bdS) (bdC := e_bdC) (fC := e_fC) (C0 := e_C0) (C1 := e_C1) (dC := e_dC) (sk := e_sk) (xl := e_xl) (xcl := e_xcl) (fl := e_fl) (vT := e_vT) (vCL := e_vCL) (vL := e_vL) (vC := e_vC) (vMP := e_vMP) (vMS := e_vMS) (vUQ := e_vUQ) (vS := e_vS) (vI := e_vI) (vR := e_vR) (vRC := e_vRC) (pp := e_pp) (xd := e_xd) (or := e_or) (o0 := e_o0) (o1 := e_o1) (o2 := e_o2) (o3 := e_o3) (o4 := e_o4) (o5 := e_o5) (o6 := e_o6) (o7 := e_o7) (o8 := e_o8) (o9 := e_o9) (o10 := e_o10) (o11 := e_o11) (o12 := e_o12) (o13 := e_o13) (o14 := e_o14) (o15 := e_o15) (hdw := e_hdw) (hde := e_hde) (hdc := e_hdc) (hcw := e_hcw) (hce := e_hce) (hcc := e_hcc) (xlw := e_xlw) (xle := e_xle) (xlc := e_xlc) (xclw := e_xclw) (xcle := e_xcle) (xclc := e_xclc) (cpw := e_cpw) (cpe := e_cpe) (cpc := e_cpc) (caw := e_caw) (cae := e_cae) (cac := e_cac) (cfw := e_cfw) (cfe := e_cfe) (cfc := e_cfc) (cdw := e_cdw) (cde := e_cde) (cdc := e_cdc) (c_typew := e_c_typew) (c_typee := e_c_typee) (c_typec := e_c_typec) (c_childLanesw := e_c_childLanesw) (c_childLanese := e_c_childLanese) (c_childLanesc := e_c_childLanesc) (c_lanesw := e_c_lanesw) (c_lanese := e_c_lanese) (c_lanesc := e_c_lanesc) (c_childw := e_c_childw) (c_childe := e_c_childe) (c_childc := e_c_childc) (c_memoizedPropsw := e_c_memoizedPropsw) (c_memoizedPropse := e_c_memoizedPropse) (c_memoizedPropsc := e_c_memoizedPropsc) (c_memoizedStatew := e_c_memoizedStatew) (c_memoizedStatee := e_c_memoizedStatee) (c_memoizedStatec := e_c_memoizedStatec) (c_updateQueuew := e_c_updateQueuew) (c_updateQueuee := e_c_updateQueuee) (c_updateQueuec := e_c_updateQueuec) (c_siblingw := e_c_siblingw) (c_siblinge := e_c_siblinge) (c_siblingc := e_c_siblingc) (c_indexw := e_c_indexw) (c_indexe := e_c_indexe) (c_indexc := e_c_indexc) (c_refw := e_c_refw) (c_refe := e_c_refe) (c_refc := e_c_refc) (c_refCleanupw := e_c_refCleanupw) (c_refCleanupe := e_c_refCleanupe) (c_refCleanupc := e_c_refCleanupc) (e0 := e_e0) (e1 := e_e1) (e2 := e_e2) (e3 := e_e3) (e4 := e_e4) (e5 := e_e5) (e6 := e_e6) (e7 := e_e7) (e8 := e_e8) (e9 := e_e9) (e10 := e_e10) (e11 := e_e11) (e12 := e_e12) (e13 := e_e13) (e14 := e_e14) (e15 := e_e15) (c0 := e_c0) (c1 := e_c1) (c2 := e_c2) (c3 := e_c3) (c4 := e_c4) (c5 := e_c5) (c6 := e_c6) (c7 := e_c7) (c8 := e_c8) (c9 := e_c9) (c10 := e_c10) (c11 := e_c11) (c12 := e_c12) (c13 := e_c13) (c14 := e_c14) (c15 := e_c15) (xde := e_xde) (xdc := e_xdc) (xce := e_xce) (xcc := e_xcc) (re := e_re) (rc := e_rc) same

end ReactEarlyBailout
