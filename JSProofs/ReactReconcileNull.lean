import JSProofs.ReactReconcileFibers
import JSProofs.ReactReconcileHelpers
import JSProofs.ReactReconcileChildren

/-!
# Reconciling no children (zippy docs/react-proofs.md)

The counter's button has a text child, which React sets as text content (`shouldSetTextContent`), so its
`beginWork` reconciles `null` against no current child: `reconcileChildFibersImpl(returnFiber, null, null, lanes)`
deletes nothing and returns `null`; the reconciler's returned function resets and clears the thenable variables
around it; `reconcileChildren` sets the work in progress's `child` to `null`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactReconcileNull

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`reconcileChildFibersImpl(returnFiber, null, null, lanes)`**: `deleteRemainingChildren(returnFiber, null)`,
which is `null`. -/
theorem impl_null {n : Nat} {h : σ} {fI : ObjId} {dI : FuncData} {tI rf ln : Value} {s : State}
    {bR : HashMap JSStr Binding} {oR : Option EnvId} {bdDel bdST : Binding} {fDel : ObjId} {dDel : FuncData}
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI) (hf : 30 ≤ s.fuel)
    (hIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict)
    (hE : dI.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dI.env) = some (bR, oR))
    (hRDel : bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel) (hRDelv : bdDel.value = some (.obj fDel))
    (hDel : fDel < s.heap.size) (hDelk : (s.objEntry fDel).kind = .func dDel)
    (hDelcode : dDel.code = CCRGen.deleteRemainingChildren_func) (hDelcls : dDel.isClassCtor = false)
    (hDelmode : dDel.thisMode = .strict) (hDelenv : dDel.env = dI.env)
    (hRST : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (hRSTv : bdST.value = some (.bool true)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fI) tI #[rf, .null, .null, ln]) s fun v w h' =>
      v = .null ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 30 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen CCRGen.reconcileChildFibersImpl_eq (by decide) hI hIk (by omega) hIcls hImode
    (by rw [hIcode]; rfl) (by rw [hIcode]; rfl) (ReactReconcileImpl.simpleI dI hIcode) (by rw [hIcode]; rfl)
    (by rw [hIcode]; rfl)
  have hpn : dI.code.info.fdi.paramNames = #[JSStr.ofString "returnFiber", JSStr.ofString "currentFirstChild",
      JSStr.ofString "newChild", JSStr.ofString "lanes"] := by rw [hIcode]; rfl
  have hv : dI.code.info.fdi.varNames = #[JSStr.ofString "key"] := by rw [hIcode]; rfl
  have hl : FDI.lexDecls dI = #[] := by simp [FDI.lexDecls, hIcode, CCRGen.reconcileChildFibersImpl_func, Func.info]
  have ha : dI.code.isAsync = false := by rw [hIcode]; rfl
  have hne : s.envs.size ≠ dI.env := Nat.ne_of_gt hE
  have hE1 : dI.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  clear hIcode
  simp only [CCRGen.reconcileChildFibersImpl]
  repeat (first | (refine wp_typeofIdentC (by simp only [js_simp, depth]; omega) ?_) | js_go | js_norm [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hRDel, hRDelv, hDel, hDelk, hRST, hRSTv, FDI.fdiCtx, Sem.inner, TypeofC] | js_split)
  refine ⟨by js_norm [CallableC, hDel, hDelk], ?_⟩
  refine wp_mono (ReactReconcileHelpers.delete_none (oR := oR) (by js_norm [hDel]) (by js_norm [hDelk]) (by simp only [js_simp]; omega)
    hDelcode hDelcls hDelmode (by rw [hDelenv]; js_norm [hE1]) (by rw [hDelenv]; js_norm [hE, hE1, hne, Ne.symm hne, hEe]; done)
    hRST hRSTv) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst hv1 hh1
  refine ⟨rfl, frame_restore (frame_trans (frame_bodyState (frame_refl ({} : Footprint) s) fI dI tI _) hF1) s, ?_, rfl,
    rfl⟩
  simp only [js_simp] at hfu1; omega

/-- What the reconciler's returned function writes here: the module's thenable variables. -/
def fpN (g : EnvId) : Footprint := ⟨[(g, "thenableIndexCounter$1"), (g, "thenableState$1")], [], false⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`reconcileChildFibers(returnFiber, null, null, lanes)`** (the reconciler's returned function): the thenable
counter reset, `reconcileChildFibersImpl` (`impl_null`), the thenable state cleared; `null`. -/
theorem fibers_null {n : Nat} {h : σ} {fR : ObjId} {dR : FuncData} {tR rf ln : Value} {s : State}
    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdRI bdT bdTS bdDel bdST : Binding} {fI fDel : ObjId}
    {dI dDel : FuncData}
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR) (hf : 50 ≤ s.fuel)
    (hRcode : dR.code = CCRGen.fn34_func) (hRcls : dR.isClassCtor = false) (hRmode : dR.thisMode = .strict)
    (hE : dR.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dR.env) = some (bR, some g))
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, none)) (hgU : g ≠ dR.env)
    (hRRI : bR[JSStr.ofString "reconcileChildFibersImpl"]? = some bdRI) (hRRIv : bdRI.value = some (.obj fI))
    (hRnT : bR[JSStr.ofString "thenableIndexCounter$1"]? = none) (hRnS : bR[JSStr.ofString "thenableState$1"]? = none)
    (hGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some bdT) (hGTm : bdT.mutable = true)
    (hGTi : bdT.value.isSome = true)
    (hGS : bG[JSStr.ofString "thenableState$1"]? = some bdTS) (hGSm : bdTS.mutable = true)
    (hGSi : bdTS.value.isSome = true)
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI)
    (hIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict) (hIenv : dI.env = dR.env)
    (hRDel : bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel) (hRDelv : bdDel.value = some (.obj fDel))
    (hDel : fDel < s.heap.size) (hDelk : (s.objEntry fDel).kind = .func dDel)
    (hDelcode : dDel.code = CCRGen.deleteRemainingChildren_func) (hDelcls : dDel.isClassCtor = false)
    (hDelmode : dDel.thisMode = .strict) (hDelenv : dDel.env = dR.env)
    (hRST : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (hRSTv : bdST.value = some (.bool true)) :
    WP eng answer (n + 2) h (callImpl eng (.obj fR) tR #[rf, .null, .null, ln]) s fun v w h' =>
      v = .null ∧ Frame (fpN g) s w ∧ s.fuel ≤ w.fuel + 50 ∧ h' = h ∧ w.realm = s.realm ∧
      Scope.declLike? (w.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
        (fun bd => { bd with value := some .null }), none) := by
  apply wp_callGen CCRGen.fn34_eq (by decide) hR hRk (by omega) hRcls hRmode
    (by rw [hRcode]; rfl) (by rw [hRcode]; rfl) (ReactReconcileFibers.simpleR dR hRcode) (by rw [hRcode]; rfl)
    (by rw [hRcode]; rfl)
  have hpn : dR.code.info.fdi.paramNames = #[JSStr.ofString "returnFiber", JSStr.ofString "currentFirstChild",
      JSStr.ofString "newChild", JSStr.ofString "lanes"] := by rw [hRcode]; rfl
  have hv : dR.code.info.fdi.varNames = #[JSStr.ofString "firstChildFiber", JSStr.ofString "fiber"] := by
    rw [hRcode]; rfl
  have hl : FDI.lexDecls dR = #[] := by simp [FDI.lexDecls, hRcode, CCRGen.fn34_func, Func.info]
  have ha : dR.code.isAsync = false := by rw [hRcode]; rfl
  have hne : s.envs.size ≠ dR.env := Nat.ne_of_gt hE
  have hE1 : dR.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hRcode
  simp only [CCRGen.fn34]
  js [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRRI, hRRIv, hRnT,
    hRnS, hGT, hGTm, hGTi, hGS, hGSm, hGSi, hI, hIk, hgU, Ne.symm hgU, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hI, hIk], ?_⟩
  refine ReactReconcileFibers.wp_gen_state fun St hSt => ?_
  have hStO : ∀ o, St.objEntry o = s.objEntry o := by intro o; rw [hSt]; rfl
  have hStz : St.heap.size = s.heap.size := by rw [hSt]; rfl
  have hStE : St.envs.size = s.envs.size + 1 := by rw [hSt]; js_norm
  have hStF : St.fuel = s.fuel - 1 := by rw [hSt]; js_norm
  have hStU : St.envEntry dR.env = s.envEntry dR.env := by
    rw [hSt]; js_norm [hE, hne, Ne.symm hne, hgU, Ne.symm hgU, hE1]
  have hStg : Scope.declLike? (St.envEntry g) = some (bG.modify (JSStr.ofString "thenableIndexCounter$1")
      (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) }), none) := by
    rw [hSt]; js_norm [hG, hG1, hGe, hneG, Ne.symm hneG]
  have hStK : St.envEntry s.envs.size = (bodyState s fR dR tR #[rf, .null, .null, ln]).envEntry s.envs.size := by
    rw [hSt]; js_norm [hneG, Ne.symm hneG]
  have hF0 : Frame (fpN g) s St := by
    rw [hSt]; simp only [fpN]; frame_go' [hG, hG1, hGe, hneG, Ne.symm hneG]
  clear hSt
  refine wp_mono (impl_null (tI := .undefined) (oR := some g) (hI := (by rw [hStz]; exact hI))
      (hIk := (by rw [hStO]; exact hIk)) (hf := (by rw [hStF]; omega)) (hIcode := hIcode) (hIcls := hIcls)
      (hImode := hImode) (hE := (by rw [hStE, hIenv]; exact Nat.lt_succ_of_lt hE))
      (hEe := (by rw [hIenv, hStU]; exact hEe)) (hRDel := hRDel) (hRDelv := hRDelv)
      (hDel := (by rw [hStz]; exact hDel)) (hDelk := (by rw [hStO]; exact hDelk)) (hDelcode := hDelcode)
      (hDelcls := hDelcls) (hDelmode := hDelmode) (hDelenv := (by rw [hDelenv, hIenv])) (hRST := hRST)
      (hRSTv := hRSTv)) ?postI
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst v1 h1
  have hw1K : w1.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF1 (by rw [hStE]; exact Nat.lt_succ_self _) (by simp)
  have hw1g : w1.envEntry g = St.envEntry g := envEntry_frame hF1 (by rw [hStE]; exact hG1) (by simp)
  have hw1E : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by rw [hStE]; exact Nat.lt_succ_self _) hF1.envs_le
  have hw1f : 10 ≤ w1.fuel := by rw [hStF] at hfu1; omega
  rw [hStK] at hw1K
  have hw1U : w1.envEntry dR.env = s.envEntry dR.env :=
    (envEntry_frame hF1 (by rw [hStE]; exact hE1) (by simp)).trans hStU
  have hUw1 : dR.env < w1.envs.size :=
    Nat.lt_of_lt_of_le (Nat.lt_trans hE (by rw [hStE]; exact Nat.lt_succ_self _)) hF1.envs_le
  have hStgS := hStg
  rw [← hw1g] at hStg
  js [hpn, hv, hl, ha, hw1K, hw1E, hw1f, hStg,
    Nat.lt_of_lt_of_le (Nat.lt_trans hG (by rw [hStE]; exact Nat.lt_succ_self _)) hF1.envs_le,
    hGS, hGSm, hneG, Ne.symm hneG, hw1U, hUw1, hEe, hRnS, hStgS, hw1g, hgU, Ne.symm hgU, hne, Ne.symm hne,
    FDI.fdiCtx, Sem.inner]
  have hFw1 : Frame (fpN g) s w1 := frame_extend hF0 hF1 (by simp [fpN]) (by simp [fpN]) (fun _ => rfl)
  have hGw1 : g < w1.envs.size :=
    Nat.lt_of_lt_of_le (Nat.lt_trans hG (by rw [hStE]; exact Nat.lt_succ_self _)) hF1.envs_le
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | (rw [hStF] at hfu1; omega) | skip
  clear hF0 hF1
  refine frame_restore ?_ s
  rw [← hw1g]
  simp only [fpN] at hFw1 ⊢
  frame_go' [hFw1, hG, hGw1, hw1E, hStg, hneG, Ne.symm hneG]

/-- What `reconcileChildren` writes here: the thenable variables and the work in progress's `child`. -/
def fpCN (g : EnvId) (X : ObjId) : Footprint := ⟨(fpN g).binds, [(X, .str "child")], false⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`reconcileChildren(current, workInProgress, null, lanes)`** for a current fiber without children:
`workInProgress.child = reconcileChildFibers(workInProgress, null, null, lanes)` (`fibers_null`), `null`. -/
theorem children_null {n : Nat} {h : σ} {fC : ObjId} {dC : FuncData} {tC ln : Value} {s : State}
    {fR : ObjId} {dR : FuncData}
    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdRI bdT bdTS bdDel bdST bdRCF : Binding} {fI fDel H X : ObjId}
    {dI dDel : FuncData} {hcw hce hcc cw cc : Bool} {ch0 : Value}
    (hRC : fC < s.heap.size) (hRCk : (s.objEntry fC).kind = .func dC) (hf : 60 ≤ s.fuel)
    (hRCcode : dC.code = RChGen.reconcileChildren_func) (hRCcls : dC.isClassCtor = false)
    (hRCmode : dC.thisMode = .strict) (hRCenv : dC.env = g)
    (hGRCF : bG[JSStr.ofString "reconcileChildFibers"]? = some bdRCF) (hGRCFv : bdRCF.value = some (.obj fR))
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHc : (s.objEntry H).props.get? (.str "child") = some (.data .null hcw hce hcc))
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXc : (s.objEntry X).props.get? (.str "child") = some (.data ch0 true cw cc))
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = CCRGen.fn34_func) (hRcls : dR.isClassCtor = false) (hRmode : dR.thisMode = .strict)
    (hE : dR.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dR.env) = some (bR, some g))
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, none)) (hgU : g ≠ dR.env)
    (hRRI : bR[JSStr.ofString "reconcileChildFibersImpl"]? = some bdRI) (hRRIv : bdRI.value = some (.obj fI))
    (hRnT : bR[JSStr.ofString "thenableIndexCounter$1"]? = none) (hRnS : bR[JSStr.ofString "thenableState$1"]? = none)
    (hGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some bdT) (hGTm : bdT.mutable = true)
    (hGTi : bdT.value.isSome = true)
    (hGS : bG[JSStr.ofString "thenableState$1"]? = some bdTS) (hGSm : bdTS.mutable = true)
    (hGSi : bdTS.value.isSome = true)
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI)
    (hIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict) (hIenv : dI.env = dR.env)
    (hRDel : bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel) (hRDelv : bdDel.value = some (.obj fDel))
    (hDel : fDel < s.heap.size) (hDelk : (s.objEntry fDel).kind = .func dDel)
    (hDelcode : dDel.code = CCRGen.deleteRemainingChildren_func) (hDelcls : dDel.isClassCtor = false)
    (hDelmode : dDel.thisMode = .strict) (hDelenv : dDel.env = dR.env)
    (hRST : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (hRSTv : bdST.value = some (.bool true)) :
    WP eng answer (n + 3) h (callImpl eng (.obj fC) tC #[.obj H, .obj X, .null, ln]) s fun v w h' =>
      v = .undefined ∧ Frame (fpCN g X) s w ∧ s.fuel ≤ w.fuel + 60 ∧ h' = h ∧ w.realm = s.realm ∧
      Scope.declLike? (w.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
        (fun bd => { bd with value := some .null }), none) ∧
      (w.objEntry X).props.get? (.str "child") = some (.data .null true cw cc) := by
  apply wp_callGen RChGen.reconcileChildren_eq (by decide) hRC hRCk (by omega) hRCcls hRCmode
    (by rw [hRCcode]; rfl) (by rw [hRCcode]; rfl) (ReactReconcileChildren.simpleC dC hRCcode) (by rw [hRCcode]; rfl)
    (by rw [hRCcode]; rfl)
  have hpn : dC.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "nextChildren", JSStr.ofString "renderLanes"] := by rw [hRCcode]; rfl
  have hv : dC.code.info.fdi.varNames = #[] := by rw [hRCcode]; rfl
  have hl : FDI.lexDecls dC = #[] := by simp [FDI.lexDecls, hRCcode, RChGen.reconcileChildren_func, Func.info]
  have ha : dC.code.isAsync = false := by rw [hRCcode]; rfl
  have hne : s.envs.size ≠ dR.env := Nat.ne_of_gt hE
  have hE1 : dR.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hRCcode
  simp only [RChGen.reconcileChildren]
  js [hpn, hv, hl, ha, hRCenv, hG, hG1, hneG, Ne.symm hneG, hGe, hGRCF, hGRCFv, hH, hHk, hHc, hX, hXk, hR, hRk,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hR, hRk], ?_⟩
  refine ReactReconcileFibers.wp_gen_state fun St hSt => ?_
  have hStO : ∀ o, St.objEntry o = s.objEntry o := by intro o; rw [hSt]; rfl
  have hStz : St.heap.size = s.heap.size := by rw [hSt]; rfl
  have hStE : St.envs.size = s.envs.size + 1 := by rw [hSt]; js_norm
  have hStF : St.fuel = s.fuel - 1 := by rw [hSt]; js_norm
  have hStU : St.envEntry dR.env = s.envEntry dR.env := by rw [hSt]; js_norm [hE, hne, Ne.symm hne]
  have hStg : St.envEntry g = s.envEntry g := by rw [hSt]; js_norm [hG, hneG, Ne.symm hneG]
  have hStK : St.envEntry s.envs.size = (bodyState s fC dC tC #[.obj H, .obj X, .null, ln]).envEntry s.envs.size := by
    rw [hSt]
  have hF0 : Frame {} s St := by rw [hSt]; exact frame_bodyState (frame_refl _ s) _ _ _ _
  clear hSt
  refine wp_mono (fibers_null (tR := .undefined) (bR := bR) (bG := bG) (g := g)
      (hR := (by rw [hStz]; exact hR)) (hRk := (by rw [hStO]; exact hRk)) (hf := (by rw [hStF]; omega))
      (hRcode := hRcode) (hRcls := hRcls) (hRmode := hRmode) (hE := (by rw [hStE]; exact Nat.lt_succ_of_lt hE))
      (hEe := (by rw [hStU]; exact hEe)) (hG := (by rw [hStE]; exact Nat.lt_succ_of_lt hG))
      (hGe := (by rw [hStg]; exact hGe)) (hgU := hgU) (hRRI := hRRI) (hRRIv := hRRIv) (hRnT := hRnT) (hRnS := hRnS)
      (hGT := hGT) (hGTm := hGTm) (hGTi := hGTi) (hGS := hGS) (hGSm := hGSm) (hGSi := hGSi)
      (hI := (by rw [hStz]; exact hI)) (hIk := (by rw [hStO]; exact hIk)) (hIcode := hIcode) (hIcls := hIcls)
      (hImode := hImode) (hIenv := hIenv) (hRDel := hRDel) (hRDelv := hRDelv) (hDel := (by rw [hStz]; exact hDel))
      (hDelk := (by rw [hStO]; exact hDelk)) (hDelcode := hDelcode) (hDelcls := hDelcls) (hDelmode := hDelmode)
      (hDelenv := hDelenv) (hRST := hRST) (hRSTv := hRSTv)) ?postR
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1, hg1⟩
  subst v1 h1
  have hXw : w1.objEntry X = s.objEntry X := by
    rw [objEntry_frame hF1 (by rw [hStz]; exact hX) (by simp [fpN]), hStO]
  have hXw1 : X < w1.heap.size := Nat.lt_of_lt_of_le (by rw [hStz]; exact hX) hF1.heap_le
  have hw1K : w1.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF1 (by rw [hStE]; exact Nat.lt_succ_self _) (by simp [fpN, hneG, Ne.symm hneG])
  rw [hStK] at hw1K
  have hw1E : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by rw [hStE]; exact Nat.lt_succ_self _) hF1.envs_le
  have hGw1 : g < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_trans hG (by rw [hStE]; exact Nat.lt_succ_self _)) hF1.envs_le
  js [hpn, hv, hl, ha, hXw, hXw1, hX, hXk, hXc, hw1K, hw1E, hGw1, hneG, Ne.symm hneG, FDI.fdiCtx, Sem.inner]
  have hFs : Frame (fpN g) s St := frame_mono hF0 (fun p hp => by simp at hp) (fun p hp => by simp at hp)
    (fun _ => rfl)
  refine ⟨frame_restore (frame_mono (frame_setProp_prop (frame_extend hFs hF1 (by simp [fpN]) (by simp [fpN])
    (fun _ => rfl)) hX _ _) ?_ ?_ ?_) s, by rw [hStF] at hfu1; omega, rfl⟩
  · intro p hp; simpa [fpCN, fpN] using hp
  · intro p hp; simpa [fpCN, fpN] using hp
  · intro _; rfl

end

end ReactReconcileNull
