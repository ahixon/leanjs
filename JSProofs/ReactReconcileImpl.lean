import JSProofs.ReactUseFiber
import JSProofs.ReactReconcileHelpers
import JSProofs.Rules6

/-!
# `reconcileChildFibersImpl` for the counter's button (zippy docs/react-proofs.md)

`reconcileChildFibersImpl(returnFiber, current, element, lanes)` where the element is a `button` with no key and
the current child is a `button` fiber with no key and no sibling: the current child reused (`useFiber`), its ref
coerced, its `return` the parent; no placement (it has its alternate).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactReconcileImpl

/-- A frame from `s` carried on to a state `W` that agrees with `w` on everything `s` had. -/
theorem frame_of_agree' {fp : Footprint} {s w W : State} (hF : Frame fp s w)
    (he : ∀ e, e < s.envs.size → W.envEntry e = w.envEntry e) (ho : ∀ o, o < s.heap.size → W.objEntry o = w.objEntry o)
    (hE : w.envs.size ≤ W.envs.size) (hH : w.heap.size ≤ W.heap.size) (hr : W.realms = w.realms) (hj : W.jobs = w.jobs) :
    Frame fp s W where
  envs_le := Nat.le_trans hF.envs_le hE
  heap_le := Nat.le_trans hF.heap_le hH
  env_agree e h := by rw [he e h]; exact hF.env_agree e h
  obj_agree o h := by rw [ho o h]; exact hF.obj_agree o h
  env_eq e h hn := by rw [he e h]; exact hF.env_eq e h hn
  obj_eq o h hn := by rw [ho o h]; exact hF.obj_eq o h hn
  realms_eq := by rw [hr]; exact hF.realms_eq
  jobs_prefix := by rw [hj]; exact hF.jobs_prefix
  jobs_eq h := by rw [hj]; exact hF.jobs_eq h

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: the reused fiber's fields (createWorkInProgress's, `index`, `sibling`, `ref`) and `return`. -/
def fpI (X : ObjId) : Footprint := ⟨(ReactCreateWIP.fp X).binds, (ReactCreateWIP.fp X).props ++ [(X, .str "return")], false⟩

theorem simpleI (d : FuncData) (hc : d.code = CCRGen.reconcileChildFibersImpl_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CCRGen.reconcileChildFibersImpl_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`reconcileChildFibersImpl(returnFiber, H, El, lanes)`** for the button. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData}  {s : State} {fU : ObjId} {dU : FuncData}
    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdCW : Binding}
    {H X : ObjId} {fl : F64} {vHT vCL vL vC vMP vMS vUQ vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value} {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    (hU : fU < s.heap.size) (hUk : (s.objEntry fU).kind = .func dU) (hUcode : dU.code = CCRGen.useFiber_func)
    (hUcls : dU.isClassCtor = false) (hUmode : dU.thisMode = .strict)
    -- (useFiber's record: the reconciler's closure, whose outer record is the module's)
    (hE : dU.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dU.env) = some (bR, some g))
    (hEn : bR[JSStr.ofString "createWorkInProgress"]? = none)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, none))
    (hGC : bG[JSStr.ofString "createWorkInProgress"]? = some bdCW) (hGCv : bdCW.value = some (.obj fo))
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 120 ≤ s.fuel)
    (hcode : d.code = CWIPGen.createWorkInProgress_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
        (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true) (hHX : H ≠ X)
    (hHa : (s.objEntry H).props.get? (.str "alternate") = some (.data (.obj X) r11w r11e r11c))
    (hHf : (s.objEntry H).props.get? (.str "flags") = some (.data (.num fl) r12w r12e r12c))
    (hHd : (s.objEntry H).props.get? (.str "dependencies") = some (.data .null r13w r13e r13c))
    (hH_type : (s.objEntry H).props.get? (.str "type") = some (.data vHT r0w r0e r0c))
    (hH_childLanes : (s.objEntry H).props.get? (.str "childLanes") = some (.data vCL r1w r1e r1c))
    (hH_lanes : (s.objEntry H).props.get? (.str "lanes") = some (.data vL r2w r2e r2c))
    (hH_child : (s.objEntry H).props.get? (.str "child") = some (.data vC r3w r3e r3c))
    (hH_memoizedProps : (s.objEntry H).props.get? (.str "memoizedProps") = some (.data vMP r4w r4e r4c))
    (hH_memoizedState : (s.objEntry H).props.get? (.str "memoizedState") = some (.data vMS r5w r5e r5c))
    (hH_updateQueue : (s.objEntry H).props.get? (.str "updateQueue") = some (.data vUQ r6w r6e r6c))
    (hH_sibling : (s.objEntry H).props.get? (.str "sibling") = some (.data .null r7w r7e r7c))
    (hH_index : (s.objEntry H).props.get? (.str "index") = some (.data vI r8w r8e r8c))
    (hH_ref : (s.objEntry H).props.get? (.str "ref") = some (.data vR r9w r9e r9c))
    (hH_refCleanup : (s.objEntry H).props.get? (.str "refCleanup") = some (.data vRC r10w r10e r10c))
    (hX_pendingProps : (s.objEntry X).props.get? (.str "pendingProps") = some (.data o0 true e0 c0))
    (hX_type : (s.objEntry X).props.get? (.str "type") = some (.data o1 true e1 c1))
    (hX_flags : (s.objEntry X).props.get? (.str "flags") = some (.data o2 true e2 c2))
    (hX_subtreeFlags : (s.objEntry X).props.get? (.str "subtreeFlags") = some (.data o3 true e3 c3))
    (hX_deletions : (s.objEntry X).props.get? (.str "deletions") = some (.data o4 true e4 c4))
    (hX_childLanes : (s.objEntry X).props.get? (.str "childLanes") = some (.data o5 true e5 c5))
    (hX_lanes : (s.objEntry X).props.get? (.str "lanes") = some (.data o6 true e6 c6))
    (hX_child : (s.objEntry X).props.get? (.str "child") = some (.data o7 true e7 c7))
    (hX_memoizedProps : (s.objEntry X).props.get? (.str "memoizedProps") = some (.data o8 true e8 c8))
    (hX_memoizedState : (s.objEntry X).props.get? (.str "memoizedState") = some (.data o9 true e9 c9))
    (hX_updateQueue : (s.objEntry X).props.get? (.str "updateQueue") = some (.data o10 true e10 c10))
    (hX_dependencies : (s.objEntry X).props.get? (.str "dependencies") = some (.data o11 true e11 c11))
    (hX_sibling : (s.objEntry X).props.get? (.str "sibling") = some (.data o12 true e12 c12))
    (hX_index : (s.objEntry X).props.get? (.str "index") = some (.data o13 true e13 c13))
    (hX_ref : (s.objEntry X).props.get? (.str "ref") = some (.data o14 true e14 c14))
    (hX_refCleanup : (s.objEntry X).props.get? (.str "refCleanup") = some (.data o15 true e15 c15))
    {fI fDel fPl fCR RF El C OP : ObjId} {dI dDel dPl dCR : FuncData} {tI ln vEl vFr : Value}
    {bdDel bdUF bdPl bdST bdFr bdEl bdCR : Binding} {ew ee ec kw ke kc yw ye yc pw pe pc bkw bke bkc bew bee bec aw ae ac rew rec : Bool} {rv0 : Value}
    -- (reconcileChildFibersImpl, in the reconciler's closure record, as are its helpers)
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI)
    (hIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict) (hIenv : dI.env = dU.env)
    (hRDel : bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel) (hRDelv : bdDel.value = some (.obj fDel))
    (hDel : fDel < s.heap.size) (hDelk : (s.objEntry fDel).kind = .func dDel)
    (hDelcode : dDel.code = CCRGen.deleteRemainingChildren_func) (hDelcls : dDel.isClassCtor = false)
    (hDelmode : dDel.thisMode = .strict) (hDelenv : dDel.env = dU.env)
    (hRUF : bR[JSStr.ofString "useFiber"]? = some bdUF) (hRUFv : bdUF.value = some (.obj fU))
    (hRPl : bR[JSStr.ofString "placeSingleChild"]? = some bdPl) (hRPlv : bdPl.value = some (.obj fPl))
    (hPl : fPl < s.heap.size) (hPlk : (s.objEntry fPl).kind = .func dPl)
    (hPlcode : dPl.code = CCRGen.placeSingleChild_func) (hPlcls : dPl.isClassCtor = false)
    (hPlmode : dPl.thisMode = .strict) (hPlenv : dPl.env = dU.env)
    (hRST : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (hRSTv : bdST.value = some (.bool true))
    (hRnF : bR[JSStr.ofString "REACT_FRAGMENT_TYPE"]? = none) (hRnE : bR[JSStr.ofString "REACT_ELEMENT_TYPE"]? = none)
    (hRnC : bR[JSStr.ofString "coerceRef"]? = none)
    -- (the module: the element and fragment symbols, coerceRef)
    (hGFr : bG[JSStr.ofString "REACT_FRAGMENT_TYPE"]? = some bdFr) (hGFrv : bdFr.value = some vFr)
    (hGEl : bG[JSStr.ofString "REACT_ELEMENT_TYPE"]? = some bdEl) (hGElv : bdEl.value = some vEl)
    (hFrs : ∃ i, vFr = .sym i) (hEls : ∃ i, vEl = .sym i) (hFrEl : vFr ≠ vEl)
    (hGCR : bG[JSStr.ofString "coerceRef"]? = some bdCR) (hGCRv : bdCR.value = some (.obj fCR))
    (hCR : fCR < s.heap.size) (hCRk : (s.objEntry fCR).kind = .func dCR)
    (hCRcode : dCR.code = CRGen.coerceRef_func) (hCRcls : dCR.isClassCtor = false) (hCRmode : dCR.thisMode = .strict)
    -- (the new child: the button element; its props have no ref)
    (hEl : El < s.heap.size) (hElk : (s.objEntry El).kind = .ordinary)
    (hEltyp : (s.objEntry El).props.get? (.str "$$typeof") = some (.data vEl ew ee ec))
    (hElkey : (s.objEntry El).props.get? (.str "key") = some (.data .null kw ke kc))
    (hElty : (s.objEntry El).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) yw ye yc))
    (hElp : (s.objEntry El).props.get? (.str "props") = some (.data (.obj C) pw pe pc))
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind.isPlain = true) (hCp : (s.objEntry C).proto = .obj OP)
    (hCr : (s.objEntry C).props.get? (.str "ref") = none)
    (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isPlain = true) (hOPp : (s.objEntry OP).proto = .null)
    (hOPr : (s.objEntry OP).props.get? (.str "ref") = none)
    -- (the current child: a button with no key and no sibling; its alternate, reused, points back to it)
    (hHkey : (s.objEntry H).props.get? (.str "key") = some (.data .null bkw bke bkc))
    (hHet : (s.objEntry H).props.get? (.str "elementType") = some (.data (.str (JSStr.ofString "button")) bew bee bec))
    (hXa : (s.objEntry X).props.get? (.str "alternate") = some (.data (.obj H) aw ae ac))
    (hXret : (s.objEntry X).props.get? (.str "return") = some (.data rv0 true rew rec))
    -- (the closures, the element, its props, Object.prototype are not the reused fiber)
    (hdX : ∀ Y ∈ [fCR, fPl, El, C, OP], Y ≠ X) :
    WP eng answer (n + 2) h (callImpl eng (.obj fI) tI #[.obj RF, .obj H, .obj El, ln]) s fun v w h' =>
      v = .obj X ∧ Logic.Frame (fpI X) s w ∧ s.fuel ≤ w.fuel + 120 ∧ h' = h ∧
      (w.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj C) true e0 c0) ∧
      (w.objEntry X).props.get? (.str "type") = some (.data (vHT) true e1 c1) ∧
      (w.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd fl (F64.fin false 5062151534280704 (-22)))) true e2 c2) ∧
      (w.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (F64.fin false 0 (-1074))) true e3 c3) ∧
      (w.objEntry X).props.get? (.str "deletions") = some (.data (.null) true e4 c4) ∧
      (w.objEntry X).props.get? (.str "childLanes") = some (.data (vCL) true e5 c5) ∧
      (w.objEntry X).props.get? (.str "lanes") = some (.data (vL) true e6 c6) ∧
      (w.objEntry X).props.get? (.str "child") = some (.data (vC) true e7 c7) ∧
      (w.objEntry X).props.get? (.str "memoizedProps") = some (.data (vMP) true e8 c8) ∧
      (w.objEntry X).props.get? (.str "memoizedState") = some (.data (vMS) true e9 c9) ∧
      (w.objEntry X).props.get? (.str "updateQueue") = some (.data (vUQ) true e10 c10) ∧
      (w.objEntry X).props.get? (.str "dependencies") = some (.data (.null) true e11 c11) ∧
      (w.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12) ∧
      (w.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13) ∧
      (w.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14) ∧
      (w.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) ∧
      w.realm = s.realm ∧ (w.objEntry X).props.get? (.str "return") = some (.data (.obj RF) true rew rec) := by
  apply wp_callGen CCRGen.reconcileChildFibersImpl_eq (by decide) hI hIk (by omega) hIcls hImode
    (by rw [hIcode]; rfl) (by rw [hIcode]; rfl) (simpleI dI hIcode) (by rw [hIcode]; rfl) (by rw [hIcode]; rfl)
  have hpn : dI.code.info.fdi.paramNames = #[JSStr.ofString "returnFiber", JSStr.ofString "currentFirstChild",
      JSStr.ofString "newChild", JSStr.ofString "lanes"] := by rw [hIcode]; rfl
  have hv : dI.code.info.fdi.varNames = #[JSStr.ofString "key"] := by rw [hIcode]; rfl
  have hl : FDI.lexDecls dI = #[] := by simp [FDI.lexDecls, hIcode, CCRGen.reconcileChildFibersImpl_func, Func.info]
  have ha : dI.code.isAsync = false := by rw [hIcode]; rfl
  have hne : s.envs.size ≠ dU.env := Nat.ne_of_gt hE
  have hE1 : dU.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hE2 : dU.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt hE1
  have hG2 : g < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt hG1
  have hnE2 : dU.env ≠ s.envs.size + 1 := Nat.ne_of_lt hE1
  have hnG2 : g ≠ s.envs.size + 1 := Nat.ne_of_lt hG1
  obtain ⟨iF, rfl⟩ := hFrs
  obtain ⟨iE, rfl⟩ := hEls
  have hFE1 : (iF == iE) = false := by simp only [beq_eq_false_iff_ne]; intro h; exact hFrEl (by rw [h])
  have hFE2 : (iE == iF) = false := by simp only [beq_eq_false_iff_ne]; intro h; exact hFrEl (by rw [h])
  clear hIcode
  simp only [CCRGen.reconcileChildFibersImpl]
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC,
    hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, FDI.fdiCtx,
    Sem.inner]
  refine wp_typeofIdentC ?s1 ?_
  case s1 => js_side
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner], ?_⟩
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner]
  refine wp_typeofIdentC ?s1 ?_
  case s1 => js_side
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner], ?_⟩
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner]
  -- (`deleteRemainingChildren(returnFiber, currentFirstChild.sibling)`: the sibling is null)
  refine ⟨by js_norm [CallableC, hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hDel, hDelk, hDelenv, hRDel, hRDelv, hRST, hRSTv], ?_⟩
  refine wp_mono (ReactReconcileHelpers.delete_none (bR := bR) (oR := some g) (bdT := bdST) ?_ ?_ ?_ hDelcode hDelcls
    hDelmode ?_ ?_ ?_ ?_) ?postD
  all_goals first
    | (js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hDel, hDelk, hDelenv, hRDel, hRDelv, hRST, hRSTv]; done)
    | (js_norm [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hDel, hDelk, hDelenv, hRDel, hRDelv, hRST, hRSTv]; omega)
    | skip
  case postD =>
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst v1 h1
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := by
    intro o ho; rw [objEntry_frame0 hF1 (by js_norm [ho])]; js_norm
  have hw1eA := envEntry_frame0 hF1 (e := s.envs.size) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
  have hw1eB := envEntry_frame0 hF1 (e := s.envs.size + 1) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
  have hw1eU := envEntry_frame0 hF1 (e := dU.env) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
  have hw1eG := envEntry_frame0 hF1 (e := g) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte, hne, Ne.symm hne, hnE2, hnG2, Ne.symm hnE2,
    Ne.symm hnG2, hneG, Ne.symm hneG, hE, hG, hE1, hG1, hE2, hG2] at hw1eA hw1eB hw1eU hw1eG
  have hw1E : s.envs.size + 1 < w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; omega
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; omega
  have hw1f : 100 ≤ w1.fuel := by simp only [js_simp] at hfu1; omega
  have hw1all : ∀ e, e < s.envs.size → w1.envEntry e = s.envEntry e := by
    intro e he
    rw [envEntry_frame0 hF1 (by simp only [js_simp]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt he))]
    simp only [js_simp, Nat.ne_of_lt he, Nat.ne_of_gt he, Nat.ne_of_lt (Nat.lt_succ_of_lt he),
      Nat.ne_of_gt (Nat.lt_succ_of_lt he), ↓reduceIte, he, Nat.lt_succ_of_lt he, Nat.lt_succ_of_lt (Nat.lt_succ_of_lt he)]
  have hw1j : w1.jobs = s.jobs := by rw [hF1.jobs_eq rfl]; rfl
  have hw1R : w1.realms = s.realms := by rw [hF1.realms_eq]; rfl
  have hFw1 : Frame {} s w1 := frame_of_agree' (frame_refl {} s) hw1all (fun o ho => hw1o o ho)
    (by have := hF1.envs_le; simp only [js_simp] at this; omega) hw1z hw1R hw1j
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hw1eA, hw1eB, hw1eU, hw1eG, hw1E, hw1o, hw1f, Nat.lt_of_succ_lt hw1E, Nat.lt_trans hE1 hw1E, Nat.lt_trans hG1 hw1E, hRUF, hRUFv, hU, hUk, hRDel, hRPl, hRPlv, hX, hXk, hC, hCk]
  -- (`useFiber(currentFirstChild, newChild.props)`: the alternate reused)
  refine ⟨Nat.lt_of_lt_of_le hEl hw1z, by js_norm [CallableC, hw1o, hU, hUk, Nat.lt_of_lt_of_le hU hw1z], ?_⟩
  refine wp_mono (ReactUseFiber.spec (bR := bR) (bG := bG) (g := g) (bdCW := bdCW) (tU := .undefined) (pp := .obj C)
      (hU := (Nat.lt_of_lt_of_le hU hw1z)) (hUk := (by rw [hw1o fU hU]; exact hUk)) (hUcode := hUcode)
      (hUcls := hUcls) (hUmode := hUmode) (hE := (Nat.lt_trans hE (Nat.lt_of_succ_lt hw1E)))
      (hEe := (by rw [hw1eU]; exact hEe)) (hEn := hEn) (hG := (Nat.lt_trans hG (Nat.lt_of_succ_lt hw1E)))
      (hGe := (by rw [hw1eG]; exact hGe)) (hGC := hGC) (hGCv := hGCv) (hlt := (Nat.lt_of_lt_of_le hlt hw1z))
      (hk := (by rw [hw1o fo hlt]; exact hk)) (hf := (by omega)) (hcode := hcode) (hcls := hcls) (hmode := hmode)
      (hH := (Nat.lt_of_lt_of_le hH hw1z)) (hHk := (by rw [hw1o H hH]; exact hHk))
      (hX := (Nat.lt_of_lt_of_le hX hw1z)) (hXk := (by rw [hw1o X hX]; exact hXk)) (hHX := hHX)
      (hHa := (by rw [hw1o H hH]; exact hHa)) (hHf := (by rw [hw1o H hH]; exact hHf))
      (hHd := (by rw [hw1o H hH]; exact hHd)) (hH_type := (by rw [hw1o H hH]; exact hH_type))
      (hH_childLanes := (by rw [hw1o H hH]; exact hH_childLanes)) (hH_lanes := (by rw [hw1o H hH]; exact hH_lanes))
      (hH_child := (by rw [hw1o H hH]; exact hH_child))
      (hH_memoizedProps := (by rw [hw1o H hH]; exact hH_memoizedProps))
      (hH_memoizedState := (by rw [hw1o H hH]; exact hH_memoizedState))
      (hH_updateQueue := (by rw [hw1o H hH]; exact hH_updateQueue))
      (hH_sibling := (by rw [hw1o H hH]; exact hH_sibling)) (hH_index := (by rw [hw1o H hH]; exact hH_index))
      (hH_ref := (by rw [hw1o H hH]; exact hH_ref)) (hH_refCleanup := (by rw [hw1o H hH]; exact hH_refCleanup))
      (hX_pendingProps := (by rw [hw1o X hX]; exact hX_pendingProps))
      (hX_type := (by rw [hw1o X hX]; exact hX_type)) (hX_flags := (by rw [hw1o X hX]; exact hX_flags))
      (hX_subtreeFlags := (by rw [hw1o X hX]; exact hX_subtreeFlags))
      (hX_deletions := (by rw [hw1o X hX]; exact hX_deletions))
      (hX_childLanes := (by rw [hw1o X hX]; exact hX_childLanes)) (hX_lanes := (by rw [hw1o X hX]; exact hX_lanes))
      (hX_child := (by rw [hw1o X hX]; exact hX_child))
      (hX_memoizedProps := (by rw [hw1o X hX]; exact hX_memoizedProps))
      (hX_memoizedState := (by rw [hw1o X hX]; exact hX_memoizedState))
      (hX_updateQueue := (by rw [hw1o X hX]; exact hX_updateQueue))
      (hX_dependencies := (by rw [hw1o X hX]; exact hX_dependencies))
      (hX_sibling := (by rw [hw1o X hX]; exact hX_sibling)) (hX_index := (by rw [hw1o X hX]; exact hX_index))
      (hX_ref := (by rw [hw1o X hX]; exact hX_ref)) (hX_refCleanup := (by rw [hw1o X hX]; exact hX_refCleanup))) ?postU
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hpp2, hty2, hfl2, hsf2, hdel2, hcl2, hln2, hch2, hmp2, hms2, huq2, hdep2, hsib2,
    hidx2, href2, hrc2⟩
  subst v2 h2
  have hXw1 : X < w1.heap.size := Nat.lt_of_lt_of_le hX hw1z
  have hw2o : ∀ o, o < s.heap.size → o ≠ X → w2.objEntry o = s.objEntry o := by
    intro o ho hoX
    rw [objEntry_frame hF2 (Nat.lt_of_lt_of_le ho hw1z) (by simp [ReactCreateWIP.fp, Ne.symm hoX]), hw1o o ho]
  have hw2p : ∀ k, (ReactCreateWIP.fp X).props.contains (X, k) = false →
      (w2.objEntry X).props.get? k = (s.objEntry X).props.get? k := by
    intro k hk; rw [props_frame hF2 hXw1 hk, hw1o X hX]
  have hw2k : (w2.objEntry X).kind.isPlain = true := by rw [kind_frame hF2 hXw1, hw1o X hX]; exact hXk
  have hXa2 := (hw2p (.str "alternate") (by simp [ReactCreateWIP.fp])).trans hXa
  have hXret2 := (hw2p (.str "return") (by simp [ReactCreateWIP.fp])).trans hXret
  have hw2e : ∀ e, e < w1.envs.size → w2.envEntry e = w1.envEntry e := fun e he =>
    envEntry_frame hF2 he (by simp [ReactCreateWIP.fp])
  have hw2E : w1.envs.size ≤ w2.envs.size := hF2.envs_le
  have hw2z : w1.heap.size ≤ w2.heap.size := hF2.heap_le
  have hXw2 : X < w2.heap.size := Nat.lt_of_lt_of_le hXw1 hw2z
  have hw2f : 50 ≤ w2.fuel := by omega
  have hw2eA := (hw2e _ (Nat.lt_of_succ_lt hw1E)).trans hw1eA
  have hw2eB := (hw2e _ hw1E).trans hw1eB
  have hw2eU := (hw2e _ (Nat.lt_trans hE1 hw1E)).trans hw1eU
  have hw2eG := (hw2e _ (Nat.lt_trans hG1 hw1E)).trans hw1eG
  have hw2E' : s.envs.size + 1 < w2.envs.size := Nat.lt_of_lt_of_le hw1E hw2E
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hw2eA, hw2eB, hw2eU, hw2eG, hw2E', Nat.lt_of_succ_lt hw2E', Nat.lt_trans hE1 hw2E', Nat.lt_trans hG1 hw2E',
    hw2f, hXw2, hw2k, hGCR, hGCRv]
  -- (`coerceRef(lanes, newChild)`: no ref)
  have hCRX := hdX fCR (by simp)
  have hPlX := hdX fPl (by simp)
  have hElX := hdX El (by simp)
  have hCX := hdX C (by simp)
  have hOPX := hdX OP (by simp)
  have cfacts := And.intro (hw2o fCR hCR hCRX) (And.intro (hw2o El hEl hElX) (And.intro (hw2o C hC hCX) (hw2o OP hOP hOPX)))
  obtain ⟨hw2CR, hw2El, hw2C, hw2OP⟩ := cfacts
  refine ⟨by js_norm [CallableC, hw2CR, hCRk, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCR hw1z) hw2z], ?_⟩
  refine wp_mono (ReactReconcileHelpers.coerce_none (rv := false) (X := X) (El := El) (C := C) (OP := OP) (r0 := vR) (re := e14) (rc := c14) (pw := pw) (pe := pe) (pc := pc)
      ?_ ?_ ?_ hCRcode hCRcls hCRmode ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?postC
  all_goals first
    | (js_norm [hw2CR, hCRk, hw2El, hElk, hElp, hw2C, hCk, hCp, hCr, hw2OP, hOPk, hOPp, hOPr, hXw2, hw2k, href2,
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCR hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hEl hw1z) hw2z,
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC hw1z) hw2z, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hOP hw1z) hw2z,
        hw2f]; done)
    | (simp only [js_simp]; omega)
    | (simp [hElk]; done)
    | skip
  case postC =>
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, href3⟩
  subst v3 h3
  have hw3eS := envEntry_frame hF3 (e := s.envs.size) (by simp only [js_simp]; exact Nat.lt_of_succ_lt hw2E')
    (by simp)
  have hw3e : ∀ e, e < w2.envs.size → e ≠ s.envs.size → w3.envEntry e = w2.envEntry e := by
    intro e he hne'; rw [envEntry_frame hF3 (by simp only [js_simp]; exact he) (by simp)]
    simp only [js_simp, Ne.symm hne', ↓reduceIte]
  have hw3E : w2.envs.size ≤ w3.envs.size := by have := hF3.envs_le; simp only [js_simp] at this; exact this
  have hw3z : w2.heap.size ≤ w3.heap.size := by have := hF3.heap_le; simp only [js_simp] at this; exact this
  have hw3o : ∀ o, o < w2.heap.size → o ≠ X → w3.objEntry o = w2.objEntry o := by
    intro o ho hoX; rw [objEntry_frame hF3 (by simp only [js_simp]; exact ho) (by simp [Ne.symm hoX])]
    simp only [js_simp]
  have hw3X : ∀ k, k ≠ .str (JSStr.ofString "ref") → (w3.objEntry X).props.get? k = (w2.objEntry X).props.get? k := by
    intro k hk; rw [props_frame hF3 (by simp only [js_simp]; exact hXw2) (by simp [hk])]; simp only [js_simp]
  have hw3k : (w3.objEntry X).kind.isPlain = true := by
    rw [kind_frame hF3 (by simp only [js_simp]; exact hXw2)]; simp only [js_simp]; exact hw2k
  have hXret3 := (hw3X (.str "return") (by decide)).trans hXret2
  have hXa3 := (hw3X (.str "alternate") (by decide)).trans hXa2
  have hXw3 : X < w3.heap.size := Nat.lt_of_lt_of_le hXw2 hw3z
  have hw3f : 40 ≤ w3.fuel := by simp only [js_simp] at hfu3; omega
  have hw3eB := (hw3e _ hw2E' (Nat.succ_ne_self _)).trans hw2eB
  have hw3eU := (hw3e _ (Nat.lt_trans hE1 hw2E') hne.symm).trans hw2eU
  have hw3eG := (hw3e _ (Nat.lt_trans hG1 hw2E') hneG.symm).trans hw2eG
  have hw3E' : s.envs.size + 1 < w3.envs.size := Nat.lt_of_lt_of_le hw2E' hw3E
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte, Nat.lt_of_succ_lt hw2E'] at hw3eS
  js [hpn, hv, hl, ha, hIenv, hE, hE1, hne, Ne.symm hne, hEe, hG, hG1, hneG, Ne.symm hneG, hGe, hRnF, hRnE, hRnC, hGFr, hGFrv, hGEl, hGElv, hEl, hElk, hEltyp, hElkey, hElty, hElp, hH, hHk, hHkey, hHet, hH_sibling, hFE1, hFE2, beq_self_eq_true, hE2, hG2, hnE2, hnG2, Ne.symm hnE2, Ne.symm hnG2, FDI.fdiCtx, Sem.inner, hw3eS, hw3eB, hw3eU, hw3eG, hw3E', Nat.lt_of_succ_lt hw3E', Nat.lt_trans hE1 hw3E', Nat.lt_trans hG1 hw3E',
    hw3f, hXw3, hw3k, hXret3, hRPl, hRPlv]
  -- (`placeSingleChild(returnFiber)`: the reused fiber, no placement)
  have hw3Pl : w3.objEntry fPl = s.objEntry fPl := by
    rw [hw3o fPl (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hPl hw1z) hw2z) hPlX, hw2o fPl hPl hPlX]
  have hPlw3 : fPl < w3.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hPl hw1z) hw2z) hw3z
  refine ⟨by js_norm [CallableC, hw3Pl, hPlk, hPlw3, hPlX, Ne.symm hPlX], ?_⟩
  refine wp_mono (ReactReconcileHelpers.place_reused (bR := bR) (oR := some g) (bdT := bdST) (X := X) (A := H)
      (aw := aw) (ae := ae) (ac := ac) ?_ ?_ ?_ hPlcode hPlcls hPlmode ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?postP
  all_goals first
    | (js_norm [hw3Pl, hPlk, hPlw3, hPlX, Ne.symm hPlX, hPlenv, hw3eU, hEe, hRST, hRSTv, hXw3, hw3k, hXa3,
        Nat.lt_trans hE1 hw3E', hne, Ne.symm hne, hw3f]; done)
    | (simp only [js_simp]; omega)
    | skip
  case postP =>
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, hr4⟩
  subst v4 h4
  have hX4 := objEntry_frame0 hF4 (o := X) (by simp only [js_simp]; exact hXw3)
  have hX4p : ∀ k, k ≠ PropKey.str (JSStr.ofString "return") →
      (w4.objEntry X).props.get? k = (w3.objEntry X).props.get? k := by
    intro k hk; rw [hX4]; simp only [js_simp, State.setProp_entry_self _ _ _ _ hXw3, Obj.withProps_props,
      PropMap.get?_insert_ne _ _ _ _ (Ne.symm hk)]
  have f_pendingProps := (hX4p (.str (JSStr.ofString "pendingProps")) (by decide)).trans ((hw3X _ (by decide)).trans hpp2)
  have f_type := (hX4p (.str (JSStr.ofString "type")) (by decide)).trans ((hw3X _ (by decide)).trans hty2)
  have f_flags := (hX4p (.str (JSStr.ofString "flags")) (by decide)).trans ((hw3X _ (by decide)).trans hfl2)
  have f_subtreeFlags := (hX4p (.str (JSStr.ofString "subtreeFlags")) (by decide)).trans ((hw3X _ (by decide)).trans hsf2)
  have f_deletions := (hX4p (.str (JSStr.ofString "deletions")) (by decide)).trans ((hw3X _ (by decide)).trans hdel2)
  have f_childLanes := (hX4p (.str (JSStr.ofString "childLanes")) (by decide)).trans ((hw3X _ (by decide)).trans hcl2)
  have f_lanes := (hX4p (.str (JSStr.ofString "lanes")) (by decide)).trans ((hw3X _ (by decide)).trans hln2)
  have f_child := (hX4p (.str (JSStr.ofString "child")) (by decide)).trans ((hw3X _ (by decide)).trans hch2)
  have f_memoizedProps := (hX4p (.str (JSStr.ofString "memoizedProps")) (by decide)).trans ((hw3X _ (by decide)).trans hmp2)
  have f_memoizedState := (hX4p (.str (JSStr.ofString "memoizedState")) (by decide)).trans ((hw3X _ (by decide)).trans hms2)
  have f_updateQueue := (hX4p (.str (JSStr.ofString "updateQueue")) (by decide)).trans ((hw3X _ (by decide)).trans huq2)
  have f_dependencies := (hX4p (.str (JSStr.ofString "dependencies")) (by decide)).trans ((hw3X _ (by decide)).trans hdep2)
  have f_sibling := (hX4p (.str (JSStr.ofString "sibling")) (by decide)).trans ((hw3X _ (by decide)).trans hsib2)
  have f_index := (hX4p (.str (JSStr.ofString "index")) (by decide)).trans ((hw3X _ (by decide)).trans hidx2)
  have f_refCleanup := (hX4p (.str (JSStr.ofString "refCleanup")) (by decide)).trans ((hw3X _ (by decide)).trans hrc2)
  have f_ref := (hX4p (.str (JSStr.ofString "ref")) (by decide)).trans href3
  have f_ret : (w4.objEntry X).props.get? (.str (JSStr.ofString "return")) = some (.data (.obj RF) true rew rec) := by
    rw [hX4]; simp only [js_simp, State.setProp_entry_self _ _ _ _ hXw3, Obj.withProps_props, PropMap.get?_insert,
      ite_true, ↓reduceIte]
  have hfr : Frame (fpI X) s (w4.restore s) := by
    refine frame_restore (frame_mono (frame_trans (frame_setEnv_new (frame_setProp_prop (frame_trans
      (frame_setEnv_new (frame_trans hFw1 hF2) (Nat.le_refl _) _) hF3) hX _ _) (Nat.le_refl _) _) hF4) ?_ ?_ ?_) s
    · intro p hp; revert p; simp [Footprint.union, fpI, ReactCreateWIP.fp]
    · intro p hp; revert p; simp [Footprint.union, fpI, ReactCreateWIP.fp]
    · intro _; rfl
  have hfuel : s.fuel ≤ w4.fuel + 120 := by simp only [js_simp] at hfu1 hfu2 hfu3 hfu4; omega
  exact ⟨rfl, hfr, hfuel, rfl, f_pendingProps, f_type, f_flags, f_subtreeFlags, f_deletions, f_childLanes, f_lanes,
    f_child, f_memoizedProps, f_memoizedState, f_updateQueue, f_dependencies, f_sibling, f_index, f_ref, f_refCleanup,
    rfl, f_ret⟩



end

end ReactReconcileImpl
