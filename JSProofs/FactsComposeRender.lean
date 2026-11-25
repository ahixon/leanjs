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
import JSProofs.ReactBeginRoot
import JSProofs.ReactUnitRoot
import JSProofs.ReactWorkLoop

/-! The render's callees composed in Lean (contract-style specs and `facts_compose`, replacing
`tools/gen_react_*.py`): `useFiber` with `createWorkInProgress`; `reconcileChildFibersImpl` with `useFiber`;
`reconcileChildFibers` with `reconcileChildFibersImpl`;
`reconcileChildren` with `reconcileChildFibers`;
the counter component with `useState`; `renderWithHooks` with the counter component;
`updateFunctionComponent` with `renderWithHooks` and `reconcileChildren`; the counter's `beginWork` with
`updateFunctionComponent`; `performUnitOfWork` on the counter with its `beginWork`; on the button with its `beginWork` and
`completeUnitOfWork`; the root's early bailout with its four callees; the root's `beginWork` with
the early bailout; the root's `performUnitOfWork` with its `beginWork`; `workLoopSync` with the three
units of work. -/

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

facts_form ReactBeginRoot.root_spec_c

namespace ReactBeginRoot
open ES Logic

set_option maxHeartbeats 4000000 in
facts_compose root_comp := root_spec_c
  | hcAEB => ReactEarlyBailout.root_comp (fo := fAEB) (d := dAEB) (t := .undefined) same

end ReactBeginRoot

facts_form ReactUnitRoot.root_spec_c

namespace ReactUnitRoot
open ES Logic

set_option maxHeartbeats 4000000 in
facts_compose root_comp := root_spec_c
  | hcBW => ReactBeginRoot.root_comp (fo := fBW) (d := dBW) (t := .undefined) same

end ReactUnitRoot

facts_form ReactWorkLoop.work_loop_spec_c

namespace ReactWorkLoop
open ES Logic

set_option maxHeartbeats 4000000 in
facts_compose work_loop_comp := work_loop_spec_c
  | hcR => ReactUnitRoot.root_comp (fo := fPU) (d := dPU) (t := .undefined) (bdI := R_bdI) (bdV := R_bdV) (a_bdCS := R_a_bdCS) (a_bdCF := R_a_bdCF) (a_bdRI := R_a_bdRI) (bdP := R_bdP) (a_bdO := R_a_bdO) (a_bdGO := R_a_bdGO) (a_bdGC := R_a_bdGC) (a_CS := CS) (a_CF := CF) (a_RI := RI) (fP := R_fP) (a_fO := R_a_fO) (a_fGO := R_a_fGO) (a_fGC := R_a_fGC) (X := Rw) (C := R_C) (dP := R_dP) (a_dO := R_a_dO) (a_dGO := R_a_dGO) (a_dGC := R_a_dGC) (L := R_L) (a_o0 := R_a_o0) (a_o1 := R_a_o1) (a_o2 := R_a_o2) (a_vr := R_a_vr) (a_vf := R_a_vf) (a_vc := R_a_vc) (a_e0 := R_a_e0) (a_c0 := R_a_c0) (a_e1 := R_a_e1) (a_c1 := R_a_c1) (a_e2 := R_a_e2) (a_c2 := R_a_c2) (lw := R_lw) (le := R_le) (lc := R_lc) (a_re := R_a_re) (a_rc := R_a_rc) (a_fe := R_a_fe) (a_fc := R_a_fc) (a_ce := R_a_ce) (a_cc := R_a_cc) (b_bdC := R_b_bdC) (b_Cu := Cu) (b_cur := R_b_cur) (b_old := R_b_old) (b_cv := R_b_cv) (b_ce := R_b_ce) (b_cc := R_b_cc) (b_oe := R_b_oe) (b_oc := R_b_oc) (b_xe := R_b_xe) (b_xc := R_b_xc) (c_b1 := R_c_b1) (c_b2 := R_c_b2) (c_b3 := R_c_b3) (e_bdS := R_e_bdS) (e_bdC := R_e_bdC) (e_fC := R_e_fC) (H := Rc) (e_C0 := C0) (e_C1 := C1) (e_dC := R_e_dC) (e_sk := R_e_sk) (e_xl := R_e_xl) (e_xcl := R_e_xcl) (e_fl := R_e_fl) (e_vT := (((.obj fK)))) (e_vCL := R_e_vCL) (e_vL := ln) (e_vC := ch0) (e_vMP := mpv) (e_vMS := ms1) (e_vUQ := uq) (e_vS := R_e_vS) (e_vI := R_e_vI) (e_vR := R_e_vR) (e_vRC := R_e_vRC) (e_pp := (((.obj Pp)))) (e_xd := R_e_xd) (e_or := R_e_or) (e_o0 := R_e_o0) (e_o1 := R_e_o1) (e_o2 := R_e_o2) (e_o3 := R_e_o3) (e_o4 := R_e_o4) (e_o5 := R_e_o5) (e_o6 := R_e_o6) (e_o7 := R_e_o7) (e_o8 := R_e_o8) (e_o9 := R_e_o9) (e_o10 := R_e_o10) (e_o11 := R_e_o11) (e_o12 := R_e_o12) (e_o13 := R_e_o13) (e_o14 := R_e_o14) (e_o15 := R_e_o15) (e_hdw := R_e_hdw) (e_hde := R_e_hde) (e_hdc := R_e_hdc) (e_hcw := R_e_hcw) (e_hce := R_e_hce) (e_hcc := R_e_hcc) (e_xlw := R_e_xlw) (e_xle := R_e_xle) (e_xlc := R_e_xlc) (e_xclw := R_e_xclw) (e_xcle := R_e_xcle) (e_xclc := R_e_xclc) (e_cpw := R_e_cpw) (e_cpe := R_e_cpe) (e_cpc := R_e_cpc) (e_caw := R_e_caw) (e_cae := R_e_cae) (e_cac := R_e_cac) (e_cfw := R_e_cfw) (e_cfe := R_e_cfe) (e_cfc := R_e_cfc) (e_cdw := R_e_cdw) (e_cde := R_e_cde) (e_cdc := R_e_cdc) (e_c_typew := R_e_c_typew) (e_c_typee := R_e_c_typee) (e_c_typec := R_e_c_typec) (e_c_childLanesw := R_e_c_childLanesw) (e_c_childLanese := R_e_c_childLanese) (e_c_childLanesc := R_e_c_childLanesc) (e_c_lanesw := R_e_c_lanesw) (e_c_lanese := R_e_c_lanese) (e_c_lanesc := R_e_c_lanesc) (e_c_childw := R_e_c_childw) (e_c_childe := R_e_c_childe) (e_c_childc := R_e_c_childc) (e_c_memoizedPropsw := R_e_c_memoizedPropsw) (e_c_memoizedPropse := R_e_c_memoizedPropse) (e_c_memoizedPropsc := R_e_c_memoizedPropsc) (e_c_memoizedStatew := R_e_c_memoizedStatew) (e_c_memoizedStatee := R_e_c_memoizedStatee) (e_c_memoizedStatec := R_e_c_memoizedStatec) (e_c_updateQueuew := R_e_c_updateQueuew) (e_c_updateQueuee := R_e_c_updateQueuee) (e_c_updateQueuec := R_e_c_updateQueuec) (e_c_siblingw := R_e_c_siblingw) (e_c_siblinge := R_e_c_siblinge) (e_c_siblingc := R_e_c_siblingc) (e_c_indexw := R_e_c_indexw) (e_c_indexe := R_e_c_indexe) (e_c_indexc := R_e_c_indexc) (e_c_refw := R_e_c_refw) (e_c_refe := R_e_c_refe) (e_c_refc := R_e_c_refc) (e_c_refCleanupw := R_e_c_refCleanupw) (e_c_refCleanupe := R_e_c_refCleanupe) (e_c_refCleanupc := R_e_c_refCleanupc) (e_e0 := R_e_e0) (e_e1 := R_e_e1) (e_e2 := R_e_e2) (e_e3 := R_e_e3) (e_e4 := R_e_e4) (e_e5 := R_e_e5) (e_e6 := R_e_e6) (e_e7 := R_e_e7) (e_e8 := R_e_e8) (e_e9 := R_e_e9) (e_e10 := R_e_e10) (e_e11 := R_e_e11) (e_e12 := R_e_e12) (e_e13 := R_e_e13) (e_e14 := R_e_e14) (e_e15 := R_e_e15) (e_c0 := R_e_c0) (e_c1 := R_e_c1) (e_c2 := R_e_c2) (e_c3 := R_e_c3) (e_c4 := R_e_c4) (e_c5 := R_e_c5) (e_c6 := R_e_c6) (e_c7 := R_e_c7) (e_c8 := R_e_c8) (e_c9 := R_e_c9) (e_c10 := R_e_c10) (e_c11 := R_e_c11) (e_c12 := R_e_c12) (e_c13 := R_e_c13) (e_c14 := R_e_c14) (e_c15 := R_e_c15) (e_xde := R_e_xde) (e_xdc := R_e_xdc) (e_xce := R_e_xce) (e_xcc := R_e_xcc) (e_re := R_e_re) (e_rc := R_e_rc) (fPHC := R_fPHC) (fPPR := R_fPPR) (fRHS := R_fRHS) (fBOF := R_fBOF) (Rt := R_Rt) (MS := R_MS) (dPHC := R_dPHC) (dPPR := R_dPPR) (dRHS := R_dRHS) (dBOF := R_dBOF) (bdPHC := R_bdPHC) (bdPPR := R_bdPPR) (bdRHS := R_bdRHS) (bdBOF := R_bdBOF) (bdCC := R_bdCC) (cache := R_cache) (tw := R_tw) (te := R_te) (tc := R_tc) (sw := R_sw) (se := R_se) (sc := R_sc) (kw := R_kw) (ke := R_ke) (kc := R_kc) (mw := R_mw) (me := R_me) (mc := R_mc) (cw := R_cw) (ce2 := R_ce2) (cc2 := R_cc2) (fAEB := R_fAEB) (fCHK := R_fCHK) (dAEB := R_dAEB) (dCHK := R_dCHK) (bdAEB := R_bdAEB) (bdCHK := R_bdCHK) (bdDRU := R_bdDRU) (hl0v := R_hl0v) (xf := R_xf) (hlw := R_hlw) (hle := R_hle) (hlc := R_hlc) (hdw2 := R_hdw2) (hde2 := R_hde2) (hdc2 := R_hdc2) (mpw := R_mpw) (mpe := R_mpe) (mpc := R_mpc) (ppw := R_ppw) (ppe := R_ppe) (ppc := R_ppc) (xfw := R_xfw) (xfe := R_xfe) (xfc := R_xfc) (fBW := R_fBW) (dBW := R_dBW) (bdBW := R_bdBW) (bdERL := R_bdERL) (bdWIP := R_bdWIP) (mpv := R_mpv) (aw := R_aw) (ae := R_ae) (ac := R_ac)  same
  | hcK => ReactUnitCounter.counter_unit_comp (tPU := .undefined) (wv := (((.obj C1)))) (d := K_d) (lw := R_e_e6) (lc := R_e_c6) (uw_2 := R_e_e10) (uc_2 := R_e_c10) (r := ((.obj fBS))) (me := R_e_e9) (mc := R_e_c9) (vHT := (((.str (JSStr.ofString "button"))))) (vMS := .null) (cw := R_e_e7) (cc := R_e_c7) (dpw := true) (dpe := R_e_e11) (dpc := R_e_c11) (fe := R_e_e2) (fc := R_e_c2) (ppw := true) (ppe := R_e_e0) (ppc := R_e_c0) (tyw := true) (tye := R_e_e1) (tyc := R_e_c1) (bdWIP := bdWIP) (bdDR := bdDR) (bdHy := bdHy) (fl1 := fl1) (mpe' := mpe') (mpc' := mpc') same
  | hcB => ReactUnitButton.button_unit_comp (fo := fPU) (d := dPU) (t := .undefined) (fCU := B_fCU) (dCU := B_dCU) (bdBW := B_bdBW) (bdCU := B_bdCU) (g := dPU.env) (fW := B_fW) (dW := B_dW) (bdCW := B_bdCW) (bdEL := B_bdEL) (bdES := B_bdES) (ln := B_ln) (wv := (((.obj X)))) (P0 := B_P0) (D := B_D) (CFb := B_CFb) (HT := B_HT) (Rb := Rw) (bdPT := B_bdPT) (bdPH := B_bdPH) (bdMU := B_bdMU) (bdBP := B_bdBP) (bdPI := B_bdPI) (bdTF := B_bdTF) (bdTC := B_bdTC) (bdCFb := B_bdCFb) (bdHT := B_bdHT) (fPT := B_fPT) (fPH := B_fPH) (fMU := B_fMU) (fBP := B_fBP) (fPI := B_fPI) (dPT := B_dPT) (dPH := B_dPH) (dMU := B_dMU) (dBP := B_dBP) (dPI := B_dPI) (sf := (((F64.fin false 0 (-1074))))) (m := B_m) (cl := vCL) (mpw := B_mpw) (mpe := B_mpe) (mpc := B_mpc) (ppw := true) (ppe := e0) (ppc := c0) (tgw := B_tgw) (tge := B_tge) (tgc := B_tgc) (tyw := true) (tye := r_e1) (tyc := r_c1) (snw := B_snw) (sne := B_sne) (snc := B_snc) (aw := B_aw) (ae := B_ae) (ac := B_ac) (hcw := B_hcw) (hce := B_hce) (hcc := B_hcc) (fe := r_e2) (fc := r_c2) (se := r_e3) (sc := r_c3) (le := e5) (lc := c5) (me := B_me) (mc := B_mc) (cfw := B_cfw) (cfe := B_cfe) (cfc := B_cfc) (htw := B_htw) (hte := B_hte) (htc := B_htc) (rwe := rew) (rwc := rec) (sbw := true) (sbe := e12) (sbc := c12) (C := C1) (A := C0) (pp2 := Pp) (cl2 := R_e_vCL) (e2 := (((F64.fin false 0 (-1074))))) (a2 := (((F64.fin false 0 (-1074))))) (ppw2 := true) (ppe2 := R_e_e0) (ppc2 := R_e_c0) (tgw2 := B_tgw2) (tge2 := B_tge2) (tgc2 := B_tgc2) (aw2 := B_aw2) (ae2 := B_ae2) (ac2 := B_ac2) (cw2 := true) (ce2 := R_e_e7) (cc2 := R_e_c7) (yw2 := B_yw2) (ye2 := B_ye2) (yc2 := B_yc2) (se2 := R_e_e3) (sc2 := R_e_c3) (le2 := R_e_e5) (lc2 := R_e_c5) (xlw2 := true) (xle2 := R_e_e6) (xlc2 := R_e_c6) (xfw2 := true) (xfe2 := R_e_e2) (xfc2 := R_e_c2) (rwe2 := R_e_re) (rwc2 := R_e_rc) (sbw2 := true) (sbe2 := R_e_e12) (sbc2 := R_e_c12) (RH := Rc) (R := Rw) (FR := B_FR) (MS0 := B_MS0) (MS1 := B_MS1) (CA := B_CA) (pp3 := B_pp3) (cl3 := B_cl3) (e3 := B_e3) (fR := B_fR) (bdPP := B_bdPP) (bdPHC := B_bdPHC) (bdCC := B_bdCC) (bdV := B_bdV) (bdVC := B_bdVC) (bdCS := B_bdCS) (bdCF := B_bdCF) (bdRI := B_bdRI) (bdO := B_bdO) (fPP := B_fPP) (fPHC := B_fPHC) (fO := B_fO) (dPP := B_dPP) (dPHC := B_dPHC) (dO := B_dO) (L := B_L) (o0 := R_a_vr) (o1 := R_a_vf) (o2 := R_a_vc) (o3 := R_b_cur) (vu := R_b_cv) (cxv := R_cache) (vr := (((.obj R_C)))) (vf := B_vf) (vc := (((.num (F64.fin false 0 (-1074)))))) (ppw3 := B_ppw3) (ppe3 := B_ppe3) (ppc3 := B_ppc3) (tgw3 := B_tgw3) (tge3 := B_tge3) (tgc3 := B_tgc3) (snw3 := B_snw3) (sne3 := B_sne3) (snc3 := B_snc3) (m0w := B_m0w) (m0e := B_m0e) (m0c := B_m0c) (m1w := B_m1w) (m1e := B_m1e) (m1c := B_m1c) (caw := B_caw) (cae := B_cae) (cac := B_cac) (cbw := B_cbw) (cbe := B_cbe) (cbc := B_cbc) (pcw := B_pcw) (pce := B_pce) (pcc := B_pcc) (hcw3 := B_hcw3) (hce3 := B_hce3) (hcc3 := B_hcc3) (aw3 := B_aw3) (ae3 := B_ae3) (ac3 := B_ac3) (cw3 := true) (ce3 := R_e_xce) (cc3 := R_e_xcc) (se3 := B_se3) (sc3 := B_sc3) (le3 := B_le3) (lc3 := B_lc3) (fw3 := B_fw3) (fe3 := B_fe3) (fc3 := B_fc3) (rw3 := B_rw3) (re3 := B_re3) (rc3 := B_rc3) (sw3 := B_sw3) (e0 := R_a_e0) (c0 := R_a_c0) (e1 := R_a_e1) (c1 := R_a_c1) (c2 := R_a_c2) (c3 := R_b_oc) (lw := B_lw) (lle := B_lle) (llc := B_llc) (ue := R_b_ce) (uc := R_b_cc) (xe := R_b_xe) (xc := R_b_xc) (re := R_a_re) (rc := R_a_rc) (vce := R_a_ce) (vcc := R_a_cc) (b_fB := B_b_fB) (b_dB := B_b_dB) (b_tB := B_b_tB) (b_bdPH := B_b_bdPH) (b_bdSS := B_b_bdSS) (b_bdMR := B_b_bdMR) (b_bdRC := B_b_bdRC) (b_bdGC := B_b_bdGC) (b_bdRCF := B_b_bdRCF) (b_fPH := B_b_fPH) (b_fSS := B_b_fSS) (b_fMR := B_b_fMR) (b_fC := B_b_fC) (b_fGC := B_b_fGC) (b_fR := B_b_fR) (b_dPH := B_b_dPH) (b_dSS := B_b_dSS) (b_dMR := B_b_dMR) (b_dC := B_b_dC) (b_dGC := B_b_dGC) (b_dR := B_b_dR) (b_bR := B_b_bR) (b_bdRI := B_b_bdRI) (b_bdDel := B_b_bdDel) (b_bdST := B_b_bdST) (b_fI := B_b_fI) (b_fDel := B_b_fDel) (b_dI := B_b_dI) (b_dDel := B_b_dDel) (b_mpw := B_b_mpw) (b_mpe := B_b_mpe) (b_mpc := B_b_mpc) (b_hcw := B_b_hcw) (b_hce := B_b_hce) (b_hcc := B_b_hcc) (b_hrw := B_b_hrw) (b_hre := B_b_hre) (b_hrc := B_b_hrc) (b_ppw := true) (b_ppe := e0) (b_ppc := c0) (b_tgw := B_b_tgw) (b_tge := B_b_tge) (b_tgc := B_b_tgc) (b_tyw := true) (b_tye := r_e1) (b_tyc := r_c1) (b_msw := true) (b_mse := e9) (b_msc := c9) (b_xrw := true) (b_xre := e14) (b_xrc := c14) (b_lw := e6) (b_lc := c6) (b_cw := e7) (b_cc := c7) (b_kw := true) (b_ke := true) (b_kc := true) (b_csw := true) (b_cse := R_a_ce) (b_csc := R_a_cc) (b_ch0 := vC) (b_l0 := vL) (mpv := vMP) (oG := oG) (bdWIP := bdWIP) (bdI := bdI) (P1 := P1) (fl := fl) (f2 := f2) (b_bdDR := b_bdDR) (b_bdT := b_bdT) (b_bdTS := b_bdTS) (b_str := b_str) (mpe' := mpe') (mpc' := mpc') same

end ReactWorkLoop
