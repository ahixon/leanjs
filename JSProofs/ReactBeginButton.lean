import JSProofs.ReactBeginCounter
import JSProofs.ReactButtonHelpers
import JSProofs.ReactReconcileNull

/-!
# beginWork for the counter's button (zippy docs/react-proofs.md)

`beginWork(current, workInProgress, 2)` for the button's host-component fiber in the click's render. The counter
re-rendered, so the button's props are a new object: `didReceiveUpdate = true`; the work in progress's lanes are
cleared; tag 5: `pushHostContext` (nothing pushed, `phc_button`), the text child set as text content
(`shouldSetTextContent`, so no child is reconciled), `markRef` (no refs), `reconcileChildren(current, wip, null)`
(`children_null`); it returns `workInProgress.child`, `null`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactBeginButton

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: `didReceiveUpdate`, the thenable variables, the work in progress's lanes and child. -/
def fpBB (g : EnvId) (X : ObjId) : Footprint :=
  ⟨[(g, "didReceiveUpdate"), (g, "thenableIndexCounter$1"), (g, "thenableState$1")],
    [(X, .str "lanes"), (X, .str "child")], false⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **`beginWork(current, workInProgress, 2)`** for the button. -/
theorem button_spec {n : Nat} {h : σ} {fB : ObjId} {dB : FuncData} {tB : Value} {s : State}
    {bG : HashMap JSStr Binding} {g : EnvId} {H X P0 P1 : ObjId} {str : JSStr} {ln : Value}
    {bdDR bdPH bdSS bdMR bdRC bdCSC bdGC bdRCF bdT bdTS : Binding}
    {fPH fSS fMR fC fGC fR CS : ObjId} {dPH dSS dMR dC dGC dR : FuncData}
    {bR : HashMap JSStr Binding} {bdRI bdDel bdST : Binding} {fI fDel : ObjId} {dI dDel : FuncData}
    {mpw mpe mpc hcw hce hcc hrw hre hrc ppw ppe ppc tgw tge tgc tyw tye tyc msw mse msc xrw xre xrc lw lc cw cc
      kw ke kc csw cse csc : Bool} {ch0 l0 : Value}
    {oG : Option EnvId}
    (hBW : fB < s.heap.size) (hBWk : (s.objEntry fB).kind = .func dB) (hf : 200 ≤ s.fuel)
    (hBWcode : dB.code = BWGen.beginWork_func) (hBWcls : dB.isClassCtor = false) (hBWmode : dB.thisMode = .strict)
    (hBWenv : dB.env = g)
    -- (react-dom's module record)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    (hGPH : bG[JSStr.ofString "pushHostContext"]? = some bdPH) (hGPHv : bdPH.value = some (.obj fPH))
    (hGSS : bG[JSStr.ofString "shouldSetTextContent"]? = some bdSS) (hGSSv : bdSS.value = some (.obj fSS))
    (hGMR : bG[JSStr.ofString "markRef"]? = some bdMR) (hGMRv : bdMR.value = some (.obj fMR))
    (hGRC : bG[JSStr.ofString "reconcileChildren"]? = some bdRC) (hGRCv : bdRC.value = some (.obj fC))
    (hGCSC : bG[JSStr.ofString "contextStackCursor"]? = some bdCSC) (hGCSCv : bdCSC.value = some (.obj CS))
    (hGGC : bG[JSStr.ofString "getChildHostContextProd"]? = some bdGC) (hGGCv : bdGC.value = some (.obj fGC))
    (hGRCF : bG[JSStr.ofString "reconcileChildFibers"]? = some bdRCF) (hGRCFv : bdRCF.value = some (.obj fR))
    (hGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some bdT) (hGTm : bdT.mutable = true)
    (hGTi : bdT.value.isSome = true)
    (hGS : bG[JSStr.ofString "thenableState$1"]? = some bdTS) (hGSm : bdTS.mutable = true)
    (hGSi : bdTS.value.isSome = true)
    -- (the module's functions)
    (hPH : fPH < s.heap.size) (hPHk : (s.objEntry fPH).kind = .func dPH)
    (hPHcode : dPH.code = PHCtxGen.pushHostContext_func) (hPHcls : dPH.isClassCtor = false)
    (hPHmode : dPH.thisMode = .strict) (hPHenv : dPH.env = g)
    (hSS : fSS < s.heap.size) (hSSk : (s.objEntry fSS).kind = .func dSS)
    (hSScode : dSS.code = SSTCGen.shouldSetTextContent_func) (hSScls : dSS.isClassCtor = false)
    (hSSmode : dSS.thisMode = .strict)
    (hMR : fMR < s.heap.size) (hMRk : (s.objEntry fMR).kind = .func dMR)
    (hMRcode : dMR.code = MRGen.markRef_func) (hMRcls : dMR.isClassCtor = false) (hMRmode : dMR.thisMode = .strict)
    (hRC : fC < s.heap.size) (hRCk : (s.objEntry fC).kind = .func dC)
    (hRCcode : dC.code = RChGen.reconcileChildren_func) (hRCcls : dC.isClassCtor = false)
    (hRCmode : dC.thisMode = .strict) (hRCenv : dC.env = g)
    (hGCo : fGC < s.heap.size) (hGCk : (s.objEntry fGC).kind = .func dGC)
    (hGCcode : dGC.code = GCHCGen.getChildHostContextProd_func) (hGCcls : dGC.isClassCtor = false)
    (hGCmode : dGC.thisMode = .strict)
    (hCS : CS < s.heap.size) (hCSk : (s.objEntry CS).kind.isPlain = true)
    (hCSc : (s.objEntry CS).props.get? (.str "current") = some (.data (.num (F64.fin false 0 (-1074))) csw cse csc))
    -- (the child reconciler: its returned function, `reconcileChildFibersImpl` and its helpers, in its closure record)
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = CCRGen.fn34_func) (hRcls : dR.isClassCtor = false) (hRmode : dR.thisMode = .strict)
    (hE : dR.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dR.env) = some (bR, some g)) (hgU : g ≠ dR.env)
    (hRRI : bR[JSStr.ofString "reconcileChildFibersImpl"]? = some bdRI) (hRRIv : bdRI.value = some (.obj fI))
    (hRnT : bR[JSStr.ofString "thenableIndexCounter$1"]? = none) (hRnS : bR[JSStr.ofString "thenableState$1"]? = none)
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI)
    (hIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict) (hIenv : dI.env = dR.env)
    (hRDel : bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel) (hRDelv : bdDel.value = some (.obj fDel))
    (hDel : fDel < s.heap.size) (hDelk : (s.objEntry fDel).kind = .func dDel)
    (hDelcode : dDel.code = CCRGen.deleteRemainingChildren_func) (hDelcls : dDel.isClassCtor = false)
    (hDelmode : dDel.thisMode = .strict) (hDelenv : dDel.env = dR.env)
    (hRST : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (hRSTv : bdST.value = some (.bool true))
    (hRg : dR.env ≠ g)
    -- (the current button fiber: its props, no child fiber, no ref)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHmp : (s.objEntry H).props.get? (.str "memoizedProps") = some (.data (.obj P0) mpw mpe mpc))
    (hHc : (s.objEntry H).props.get? (.str "child") = some (.data .null hcw hce hcc))
    (hHr : (s.objEntry H).props.get? (.str "ref") = some (.data .null hrw hre hrc))
    -- (the work in progress: a host component (tag 5) `button`, its new props with a string child)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true) (hHX : H ≠ X)
    (hXpp : (s.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj P1) ppw ppe ppc))
    (hXtag : (s.objEntry X).props.get? (.str "tag") = some (.data (.num (F64.fin false 5629499534213120 (-50))) tgw tge tgc))
    (hXty : (s.objEntry X).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) tyw tye tyc))
    (hXms : (s.objEntry X).props.get? (.str "memoizedState") = some (.data .null msw mse msc))
    (hXr : (s.objEntry X).props.get? (.str "ref") = some (.data .null xrw xre xrc))
    (hXl : (s.objEntry X).props.get? (.str "lanes") = some (.data l0 true lw lc))
    (hXc : (s.objEntry X).props.get? (.str "child") = some (.data ch0 true cw cc))
    (hP01 : P0 ≠ P1)
    (hdX : ∀ Y ∈ [fPH, fSS, fMR, fC, fGC, CS, fR, fI, fDel, P1, fB], Y ≠ X)
    (hP1 : P1 < s.heap.size) (hP1k : (s.objEntry P1).kind.isPlain = true)
    (hP1c : (s.objEntry P1).props.get? (.str "children") = some (.data (.str str) kw ke kc)) :
    WP eng answer (n + 4) h (callImpl eng (.obj fB) tB #[.obj H, .obj X, ln]) s fun v w h' =>
      v = .null ∧ Frame (fpBB g X) s w ∧ s.fuel ≤ w.fuel + 200 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) ∧
      (w.objEntry X).props.get? (.str "child") = some (.data .null true cw cc) := by
  apply wp_callGen BWGen.beginWork_eq (by decide) hBW hBWk (by omega) hBWcls hBWmode
    (by rw [hBWcode]; rfl) (by rw [hBWcode]; rfl) (ReactBeginCounter.simpleB dB hBWcode) (by rw [hBWcode]; rfl)
    (by rw [hBWcode]; rfl)
  have hpn : dB.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "renderLanes"] := by rw [hBWcode]; rfl
  have hv : dB.code.info.fdi.varNames = #[JSStr.ofString "props", JSStr.ofString "$$typeof", JSStr.ofString "prevState",
    JSStr.ofString "nextState"] := by rw [hBWcode]; rfl
  have hl : FDI.lexDecls dB = #[] := by simp [FDI.lexDecls, hBWcode, BWGen.beginWork_func, Func.info]
  have ha : dB.code.isAsync = false := by rw [hBWcode]; rfl
  have hne : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hG2 : g < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt hG1
  have hne2 : g ≠ s.envs.size + 1 := Nat.ne_of_lt hG1
  have hK2 : s.envs.size < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hK2' : s.envs.size ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  have hPs : isStrictlyEqual (.obj P0) (.obj P1) = false := by
    simp [isStrictlyEqual, sameValue, hP01]
  have x1 := hdX fPH (by simp); have x2 := hdX fSS (by simp); have x3 := hdX fMR (by simp)
  have x4 := hdX fC (by simp); have x5 := hdX fGC (by simp); have x6 := hdX CS (by simp)
  have x7 := hdX fR (by simp); have x8 := hdX fI (by simp); have x9 := hdX fDel (by simp)
  have x10 := hdX P1 (by simp); have x11 := hdX fB (by simp)
  clear hBWcode
  simp only [BWGen.beginWork]
  iterate 34 (first | js_go | js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC BWSwitch.lex ?_
  js [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c]
  have hdDR : ∀ x, x ≠ JSStr.ofString "didReceiveUpdate" → (bG.modify (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool true) }))[x]? = bG[x]? := fun x hx => by
    simp [Std.HashMap.getElem?_modify, Ne.symm hx]
  refine ⟨by js_norm [CallableC, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv], ?_⟩
  refine wp_mono (ReactButtonHelpers.phc_button (bG := bG.modify (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool true) })) (oG := oG) (bdCS := bdCSC) (bdGC := bdGC) (CS := CS)
      (fGC := fGC) (dGC := dGC) (X := X) (mw := msw) (me := mse) (mc := msc) (yw := tyw) (ye := tye) (yc := tyc)
      (cw := csw) (ce := cse) (cc := csc)
      (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by simp only [js_simp]; omega) hPHcode hPHcls hPHmode
      (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by rw [hdDR _ (by decide)]; exact hGCSC) hGCSCv
      (by rw [hdDR _ (by decide)]; exact hGGC) hGGCv (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) hGCcode hGCcls hGCmode
      (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv])
      (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv]) (by js_norm [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm x7, Ne.symm x8, Ne.symm x9, Ne.symm x10, Ne.symm x11, hPs, hG2, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hH, hHk, hHmp, hX, hXk, hXpp, hXtag, hP01, Ne.symm hP01, hGDR, hGDRm, hGDRi, hHX, Ne.symm hHX, hXl, FDI.fdiCtx, Sem.inner, hXty, hXms, hXr, hXc, hGPH, hGPHv, hPH, hPHk, hGSS, hGSSv, hSS, hSSk, hGMR, hGMRv, hMR, hMRk, hGRC, hGRCv, hRC, hRCk, hP1, hP1k, hP1c, hGCSC, hGCSCv, hGGC, hGGCv, hGCo, hGCk, hCS, hCSk, hCSc, hPHenv])) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst hv1 hh1
  have hw1K := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm)
  have hw1B := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm)
  have hw1G := envEntry_frame0 hF1 (e := g) (by js_norm [hG2])
  simp only [js_simp, ↓reduceIte, hG1, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2', Ne.symm hK2'] at hw1K hw1G hw1B
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = _ := fun o ho => objEntry_frame0 hF1 (o := o) (by js_norm [ho])
  simp only [js_simp] at hw1o
  have hw1X : w1.objEntry X = (s.objEntry X).withProps fun x => x.insert (PropKey.str (JSStr.ofString "lanes"))
      (Property.data (Value.num (F64.fin false 0 (-1074))) true lw lc) := by rw [hw1o X hX]; simp [hX]
  have hw1o' : ∀ o, o < s.heap.size → o ≠ X → w1.objEntry o = s.objEntry o := fun o ho hoX => by
    rw [hw1o o ho]; simp [Ne.symm hoX]
  have hw1E : s.envs.size + 1 + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  simp only [js_simp] at hfu1
  have hw1f : 150 ≤ w1.fuel := by omega
  have hK1 : s.envs.size < w1.envs.size := by omega
  have hB1 : s.envs.size + 1 < w1.envs.size := by omega
  have hG1' : g < w1.envs.size := Nat.lt_of_lt_of_le hG2 hw1E
  have hxs : X < w1.heap.size := Nat.lt_of_lt_of_le hX hw1z
  have hw1Xp : ∀ k, k ≠ PropKey.str (JSStr.ofString "lanes") → (w1.objEntry X).props.get? k = (s.objEntry X).props.get? k := by
    intro k hk; rw [hw1X]; simp [PropMap.get?_insert_ne _ _ _ _ (Ne.symm hk)]
  have hw1Xk : (w1.objEntry X).kind = (s.objEntry X).kind := by rw [hw1X]; simp
  have hw1Xty := (hw1Xp _ (by decide)).trans hXty
  have hw1Xpp := (hw1Xp _ (by decide)).trans hXpp
  have hw1Xms := (hw1Xp _ (by decide)).trans hXms
  have hw1Xr := (hw1Xp _ (by decide)).trans hXr
  have hw1Xc := (hw1Xp _ (by decide)).trans hXc
  have hw1Xl : (w1.objEntry X).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hw1X]; simp
  have hw1H := hw1o' H hH hHX
  have hw1P1 := hw1o' P1 hP1 x10
  have hw1SS := hw1o' fSS hSS x2
  have hw1MR := hw1o' fMR hMR x3
  have hw1C := hw1o' fC hRC x4
  have hnK1 : w1.envs.size ≠ s.envs.size := Nat.ne_of_gt hK1
  have hnB1 : w1.envs.size ≠ s.envs.size + 1 := Nat.ne_of_gt hB1
  have hnG1 : w1.envs.size ≠ g := Nat.ne_of_gt hG1'
  js [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactButtonHelpers.sstc_string (C := P1) (str := str) (cw := kw) (ce := ke) (cc := kc)
    (by js_norm [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by simp only [js_simp]; omega) hSScode hSScls hSSmode
    (by js_norm [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw1K, hw1B, hw1G, hw1Xk, hw1Xty, hw1Xpp, hw1Xms, hw1Xr, hw1Xc, hw1Xl, hw1H, hw1P1, hw1SS, hw1MR, hw1C, hnK1, hnB1, hnG1, Ne.symm hnK1, Ne.symm hnB1, Ne.symm hnG1, hK1, hB1, hG1', hxs, hw1f, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hP1 hw1z, Nat.lt_of_lt_of_le hSS hw1z, Nat.lt_of_lt_of_le hMR hw1z, Nat.lt_of_lt_of_le hRC hw1z, hXk, hHk, hP1k, hHmp, hHc, hHr, hP1c, hSSk, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGSS, hGSSv, hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner])) ?_
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hr2⟩
  subst hv2 hh2
  have hw2K := envEntry_frame0 hF2 (e := s.envs.size) (by js_norm [hK1])
  have hw2B := envEntry_frame0 hF2 (e := s.envs.size + 1) (by js_norm [hB1])
  have hw2G := envEntry_frame0 hF2 (e := g) (by js_norm [hG1'])
  simp only [js_simp, ↓reduceIte, hK1, hB1, hG1', hw1B, hw1G, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2', Ne.symm hK2']
    at hw2K hw2G hw2B
  have hw2o : ∀ o, o < w1.heap.size → w2.objEntry o = w1.objEntry o := fun o ho =>
    (objEntry_frame0 hF2 (o := o) (by js_norm [ho])).trans (by js_norm)
  have hw2E : w1.envs.size ≤ w2.envs.size := by have := hF2.envs_le; simp only [js_simp] at this; exact this
  have hw2z : w1.heap.size ≤ w2.heap.size := by have := hF2.heap_le; simp only [js_simp] at this; exact this
  simp only [js_simp] at hfu2
  have hw2f : 130 ≤ w2.fuel := by omega
  have hK2'' : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le hK1 hw2E
  have hB2 : s.envs.size + 1 < w2.envs.size := Nat.lt_of_lt_of_le hB1 hw2E
  have hG2' : g < w2.envs.size := Nat.lt_of_lt_of_le hG1' hw2E
  have hnK2 : w2.envs.size ≠ s.envs.size := Nat.ne_of_gt hK2''
  have hnB2 : w2.envs.size ≠ s.envs.size + 1 := Nat.ne_of_gt hB2
  have hnG2 : w2.envs.size ≠ g := Nat.ne_of_gt hG2'
  have hw2X := (hw2o X hxs).trans hw1X
  have hw2H := (hw2o H (Nat.lt_of_lt_of_le hH hw1z)).trans hw1H
  have hw2MR := (hw2o fMR (Nat.lt_of_lt_of_le hMR hw1z)).trans hw1MR
  have hw2C := (hw2o fC (Nat.lt_of_lt_of_le hRC hw1z)).trans hw1C
  have hw2Xk : (w2.objEntry X).kind = (s.objEntry X).kind := by rw [hw2X]; simp
  have hw2Xp : ∀ k, k ≠ PropKey.str (JSStr.ofString "lanes") → (w2.objEntry X).props.get? k = (s.objEntry X).props.get? k := by
    intro k hk; rw [hw2X]; simp [PropMap.get?_insert_ne _ _ _ _ (Ne.symm hk)]
  have hw2Xms := (hw2Xp _ (by decide)).trans hXms
  have hw2Xr := (hw2Xp _ (by decide)).trans hXr
  have hw2Xc := (hw2Xp _ (by decide)).trans hXc
  have hw2Xl : (w2.objEntry X).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hw2X]; simp
  have hxs2 : X < w2.heap.size := Nat.lt_of_lt_of_le hxs hw2z
  js [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactButtonHelpers.markref_null (H := H) (X := X) (xw := xrw) (xe := xre) (xc := xrc) (hw := hrw)
    (he := hre) (hc := hrc)
    (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by simp only [js_simp]; omega) hMRcode hMRcls hMRmode
    (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner])
    (by js_norm [hw2K, hw2B, hw2G, hw2Xk, hw2Xms, hw2Xr, hw2Xc, hw2Xl, hw2H, hw2MR, hw2C, hnK2, hnB2, hnG2, Ne.symm hnK2, Ne.symm hnB2, Ne.symm hnG2, hK2'', hB2, hG2', hxs2, hw2f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hH hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hMR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z, hXk, hHk, hHmp, hHc, hHr, hMRk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGMR, hGMRv, hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner])) ?_
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3⟩
  subst hv3 hh3
  have hw3K := envEntry_frame0 hF3 (e := s.envs.size) (by js_norm [hK2''])
  have hw3B := envEntry_frame0 hF3 (e := s.envs.size + 1) (by js_norm [hB2])
  have hw3G := envEntry_frame0 hF3 (e := g) (by js_norm [hG2'])
  simp only [js_simp, ↓reduceIte, hK2'', hB2, hG2', hw2B, hw2G, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2', Ne.symm hK2']
    at hw3K hw3G hw3B
  have hw3o : ∀ o, o < w2.heap.size → w3.objEntry o = w2.objEntry o := fun o ho =>
    (objEntry_frame0 hF3 (o := o) (by js_norm [ho])).trans (by js_norm)
  have hw3E : w2.envs.size ≤ w3.envs.size := by have := hF3.envs_le; simp only [js_simp] at this; exact this
  have hw3z : w2.heap.size ≤ w3.heap.size := by have := hF3.heap_le; simp only [js_simp] at this; exact this
  simp only [js_simp] at hfu3
  have hw3f : 110 ≤ w3.fuel := by omega
  have hK3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le hK2'' hw3E
  have hB3 : s.envs.size + 1 < w3.envs.size := Nat.lt_of_lt_of_le hB2 hw3E
  have hG3 : g < w3.envs.size := Nat.lt_of_lt_of_le hG2' hw3E
  have hnK3 : w3.envs.size ≠ s.envs.size := Nat.ne_of_gt hK3
  have hnB3 : w3.envs.size ≠ s.envs.size + 1 := Nat.ne_of_gt hB3
  have hnG3 : w3.envs.size ≠ g := Nat.ne_of_gt hG3
  have hw3X := (hw3o X hxs2).trans hw2X
  have hw3C := (hw3o fC (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z)).trans hw2C
  have hw3Xk : (w3.objEntry X).kind = (s.objEntry X).kind := by rw [hw3X]; simp
  have hxs3 : X < w3.heap.size := Nat.lt_of_lt_of_le hxs2 hw3z
  js [hw3K, hw3B, hw3G, hw3Xk, hw3C, hnK3, hnB3, hnG3, Ne.symm hnK3, Ne.symm hnB3, Ne.symm hnG3, hK3, hB3, hG3, hxs3, hw3f, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hRC hw1z) hw2z) hw3z, hXk, hRCk, hGe, hG, hG1, hG2, hne, Ne.symm hne, hne2, Ne.symm hne2, hK2, hK2', Ne.symm hK2', hGRC, hGRCv, hpn, hv, hl, ha, hBWenv, FDI.fdiCtx, Sem.inner]
  have hO3 : ∀ o, o < s.heap.size → o ≠ X → w3.objEntry o = s.objEntry o := fun o ho hoX =>
    ((hw3o o (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ho hw1z) hw2z)).trans
      (hw2o o (Nat.lt_of_lt_of_le ho hw1z))).trans (hw1o' o ho hoX)
  have hz3 : s.heap.size ≤ w3.heap.size := Nat.le_trans (Nat.le_trans hw1z hw2z) hw3z
  have hRe3 : w3.envEntry dR.env = s.envEntry dR.env := by
    have e1 := envEntry_frame0 hF1 (e := dR.env) (by js_norm [Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hE)])
    have e2 := envEntry_frame0 hF2 (e := dR.env) (by js_norm [Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hE)) hw1E])
    have e3 := envEntry_frame0 hF3 (e := dR.env) (by js_norm [Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hE)) hw1E) hw2E])
    have r1 : dR.env ≠ s.envs.size := Nat.ne_of_lt hE
    have r2 : dR.env ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hE)
    simp only [js_simp, ↓reduceIte, hE, Nat.lt_succ_of_lt hE, r1, r2, Ne.symm r1, Ne.symm r2, hRg, Ne.symm hRg] at e1 e2 e3
    rw [e3, e2, e1]
  have hGe3 : Scope.declLike? (w3.envEntry g) = some (bG.modify (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool true) }), oG) := by
    rw [hw3G]; js_norm [hGe]
  have hE3 : dR.env < w3.envs.size := Nat.lt_of_lt_of_le hE (by omega)
  have hHX' := Ne.symm hHX
  have hw3Xc : (w3.objEntry X).props.get? (.str "child") = some (.data ch0 true cw cc) := by
    rw [hw3X]; simp only [js_simp, ite_false]; exact hXc
  refine ⟨by js_norm [CallableC, hO3 fC hRC x4, hRCk, Nat.lt_of_lt_of_le hRC hz3], ?_⟩
  refine wp_mono (ReactReconcileNull.children_null (tC := .undefined) (bR := bR) (g := g)
    (bG := bG.modify (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) }))
    (hRC := Nat.lt_of_lt_of_le hRC hz3) (hRCk := by rw [hO3 fC hRC x4]; exact hRCk) (hf := by omega)
    (hRCcode := hRCcode) (hRCcls := hRCcls) (hRCmode := hRCmode) (hRCenv := hRCenv)
    (hGRCF := by rw [hdDR _ (by decide)]; exact hGRCF) (hGRCFv := hGRCFv)
    (hH := Nat.lt_of_lt_of_le hH hz3) (hHk := by rw [hO3 H hH hHX]; exact hHk) (hHc := by rw [hO3 H hH hHX]; exact hHc)
    (hX := hxs3) (hXk := by rw [hw3Xk]; exact hXk) (hXc := hw3Xc)
    (hR := Nat.lt_of_lt_of_le hR hz3) (hRk := by rw [hO3 fR hR x7]; exact hRk) (hRcode := hRcode) (hRcls := hRcls)
    (hRmode := hRmode) (hE := hE3) (hEe := by rw [hRe3]; exact hEe) (hG := hG3) (hGe := hGe3) (hgU := hgU)
    (hRRI := hRRI) (hRRIv := hRRIv) (hRnT := hRnT) (hRnS := hRnS)
    (hGT := by rw [hdDR _ (by decide)]; exact hGT) (hGTm := hGTm) (hGTi := hGTi)
    (hGS := by rw [hdDR _ (by decide)]; exact hGS) (hGSm := hGSm) (hGSi := hGSi)
    (hI := Nat.lt_of_lt_of_le hI hz3) (hIk := by rw [hO3 fI hI x8]; exact hIk) (hIcode := hIcode) (hIcls := hIcls)
    (hImode := hImode) (hIenv := hIenv) (hRDel := hRDel) (hRDelv := hRDelv) (hDel := Nat.lt_of_lt_of_le hDel hz3)
    (hDelk := by rw [hO3 fDel hDel x9]; exact hDelk) (hDelcode := hDelcode) (hDelcls := hDelcls)
    (hDelmode := hDelmode) (hDelenv := hDelenv) (hRST := hRST) (hRSTv := hRSTv)) ?_
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, hr4, hg4, hXc4⟩
  subst hv4 hh4
  have hgK : s.envs.size ≠ g := hne
  have hgB : s.envs.size + 1 ≠ g := Ne.symm hne2
  have hw4K : w4.envEntry s.envs.size = w3.envEntry s.envs.size :=
    envEntry_frame hF4 hK3 (by simp [ReactReconcileNull.fpCN, ReactReconcileNull.fpN, hgK, Ne.symm hgK])
  have hw4B : w4.envEntry (s.envs.size + 1) = w3.envEntry (s.envs.size + 1) :=
    envEntry_frame hF4 hB3 (by simp [ReactReconcileNull.fpCN, ReactReconcileNull.fpN, hgB, Ne.symm hgB])
  rw [hw3K] at hw4K
  rw [hw3B] at hw4B
  have hw4Xk : (w4.objEntry X).kind = (s.objEntry X).kind := by rw [kind_frame hF4 hxs3, hw3Xk]
  have hw4E : w3.envs.size ≤ w4.envs.size := hF4.envs_le
  have hw4z : w3.heap.size ≤ w4.heap.size := hF4.heap_le
  have hK4 : s.envs.size < w4.envs.size := Nat.lt_of_lt_of_le hK3 hw4E
  have hB4 : s.envs.size + 1 < w4.envs.size := Nat.lt_of_lt_of_le hB3 hw4E
  have hxs4 : X < w4.heap.size := Nat.lt_of_lt_of_le hxs3 hw4z
  have hw4f : 40 ≤ w4.fuel := by omega
  js [hw4K, hw4B, hw4Xk, hXc4, hK4, hB4, hxs4, hw4f, hXk, Nat.ne_of_gt hK4, Nat.ne_of_gt hB4, Ne.symm (Nat.ne_of_gt hK4),
    Ne.symm (Nat.ne_of_gt hB4), hK2', Ne.symm hK2', hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hBg : (bodyState s fB dB tB #[.obj H, .obj X, ln]).envEntry g = s.envEntry g := by
    js_norm [hG, hne, Ne.symm hne]
  have gB : Frame (fpBB g X) s (bodyState s fB dB tB #[.obj H, .obj X, ln]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) fB dB tB _) (by simp) (by simp) (fun _ => rfl)
  have gS := frame_pushEnv (frame_mono (fp' := fpBB g X) (frame_setProp_prop (frame_mono (fp' := fpBB g X)
    (frame_setEnv_bind gB hG (by rw [hBg]; exact hGe) (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool true) })) ?_ ?_ ?_) hX (.str (JSStr.ofString "lanes"))
      (.data (.num (F64.fin false 0 (-1074))) true lw lc)) ?_ ?_ ?_) (Env.decl ∅ (some s.envs.size))
  rotate_left
  · intro p hp; simp only [List.mem_cons] at hp; rcases hp with rfl | hp
    · simp [fpBB]
    · exact hp
  · intro p hp; exact hp
  · intro h; exact h
  · intro p hp; exact hp
  · intro p hp; simp only [List.mem_cons] at hp; rcases hp with rfl | hp
    · simp [fpBB]
    · exact hp
  · intro h; exact h
  rw [hBg] at gS
  have FW1 := frame_extend' gS hF1 (fun q hq _ => by simp at hq) (fun q hq _ => by simp at hq) (fun _ => rfl)
  have FW2 := frame_extend' (frame_setEnv_new FW1 (Nat.le_refl _) _) hF2 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq) (fun _ => rfl)
  have FW3 := frame_extend' (frame_setEnv_new FW2 (Nat.le_refl _) _) hF3 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq) (fun _ => rfl)
  have FW4 := frame_extend' FW3 hF4 (fun q hq _ => by simp [ReactReconcileNull.fpCN, ReactReconcileNull.fpN] at hq; simp [fpBB, hq])
    (fun q hq _ => by simp [ReactReconcileNull.fpCN] at hq; simp [fpBB, hq]) (fun _ => rfl)
  have hl4 : (w4.objEntry X).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [props_frame hF4 hxs3 (by simp [ReactReconcileNull.fpCN]), hw3X]; simp
  exact ⟨frame_restore FW4 s, by omega, rfl, hl4⟩
