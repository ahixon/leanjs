import JSProofs.ReactReconcileFibers
import JSProofs.RChGen

/-!
# `reconcileChildren` for the counter's re-render (zippy docs/react-proofs.md)

`reconcileChildren(current, workInProgress, nextChildren, renderLanes)` with a current fiber: the work in
progress's child is `reconcileChildFibers(workInProgress, current.child, nextChildren, renderLanes)`
(`ReactReconcileFibers.click_spec`: the current button fiber's alternate reused).
-/

open ES ES.M HostRuns Logic ReactReconcileImpl ReactReconcileFibers
open Std (HashMap)

namespace ReactReconcileChildren

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem wp_gen_state {n : Nat} {h : σ} {α : Type} {x : M α} {s : State} {Q : α → State → σ → Prop}
    (hw : ∀ St, St = s → WP eng answer n h x St Q) : WP eng answer n h x s Q := hw s rfl

/-- What it writes: reconcileChildFibers' and the work in progress's child. -/
def fpC (g : EnvId) (X RF : ObjId) : Footprint := ⟨(fpR g X).binds, (fpR g X).props ++ [(RF, .str "child")], false⟩

theorem simpleC (d : FuncData) (hc : d.code = RChGen.reconcileChildren_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RChGen.reconcileChildren_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`reconcileChildren(current, workInProgress, element, lanes)`** for the button. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData}  {s : State} {fU : ObjId} {dU : FuncData}
    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdCW : Binding}
    {H X : ObjId} {fl : F64} {vHT vCL vL vC vMP vMS vUQ vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value} {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    {oG : Option EnvId}
    (hU : fU < s.heap.size) (hUk : (s.objEntry fU).kind = .func dU) (hUcode : dU.code = CCRGen.useFiber_func)
    (hUcls : dU.isClassCtor = false) (hUmode : dU.thisMode = .strict)
    -- (useFiber's record: the reconciler's closure, whose outer record is the module's)
    (hE : dU.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dU.env) = some (bR, some g))
    (hEn : bR[JSStr.ofString "createWorkInProgress"]? = none)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hGC : bG[JSStr.ofString "createWorkInProgress"]? = some bdCW) (hGCv : bdCW.value = some (.obj fo))
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 170 ≤ s.fuel)
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
    {fI fDel fPl fCR RF El C OP : ObjId} {dI dDel dPl dCR : FuncData} {ln vEl vFr : Value}
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
    (hdX : ∀ Y ∈ [fCR, fPl, El, C, OP], Y ≠ X)
    {fR : ObjId} {dR : FuncData}  {bdRI bdT bdTS : Binding}
    -- (the reconciler's returned function, in its closure record; the module's thenable variables)
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR) (hRcode : dR.code = CCRGen.fn34_func)
    (hRcls : dR.isClassCtor = false) (hRmode : dR.thisMode = .strict) (hRenv : dR.env = dU.env)
    (hRRI : bR[JSStr.ofString "reconcileChildFibersImpl"]? = some bdRI) (hRRIv : bdRI.value = some (.obj fI))
    (hRnT : bR[JSStr.ofString "thenableIndexCounter$1"]? = none) (hRnS : bR[JSStr.ofString "thenableState$1"]? = none)
    (hGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some bdT) (hGTm : bdT.mutable = true)
    (hGTi : bdT.value.isSome = true)
    (hGS : bG[JSStr.ofString "thenableState$1"]? = some bdTS) (hGSm : bdTS.mutable = true)
    (hGSi : bdTS.value.isSome = true)
    (hgU : g ≠ dU.env)
    {fC C0 : ObjId} {dC : FuncData} {tC : Value} {bdRCF : Binding} {c0w c0e c0c cw cc : Bool} {ch0 : Value}
    -- (reconcileChildren, a module function; `reconcileChildFibers` the reconciler's returned function)
    (hRC : fC < s.heap.size) (hRCk : (s.objEntry fC).kind = .func dC) (hRCcode : dC.code = RChGen.reconcileChildren_func)
    (hRCcls : dC.isClassCtor = false) (hRCmode : dC.thisMode = .strict) (hRCenv : dC.env = g)
    (hGRCF : bG[JSStr.ofString "reconcileChildFibers"]? = some bdRCF) (hGRCFv : bdRCF.value = some (.obj fR))
    -- (the current fiber, whose child is the current button fiber; the work in progress's child)
    (hC0 : C0 < s.heap.size) (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hC0c : (s.objEntry C0).props.get? (.str "child") = some (.data (.obj H) c0w c0e c0c))
    (hRF : RF < s.heap.size) (hRFk : (s.objEntry RF).kind.isPlain = true)
    (hRFc : (s.objEntry RF).props.get? (.str "child") = some (.data ch0 true cw cc))
    (hRFX : RF ≠ X) :
    WP eng answer (n + 4) h (callImpl eng (.obj fC) tC #[.obj C0, .obj RF, .obj El, ln]) s fun v w h' =>
      v = .undefined ∧ Logic.Frame (fpC g X RF) s w ∧ s.fuel ≤ w.fuel + 170 ∧ h' = h ∧
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
      w.realm = s.realm ∧ (w.objEntry X).props.get? (.str "return") = some (.data (.obj RF) true rew rec) ∧
      Scope.declLike? (w.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
        (fun bd => { bd with value := some .null }), oG) ∧
      (w.objEntry RF).props.get? (.str "child") = some (.data (.obj X) true cw cc) := by
  apply wp_callGen RChGen.reconcileChildren_eq (by decide) hRC hRCk (by omega) hRCcls hRCmode
    (by rw [hRCcode]; rfl) (by rw [hRCcode]; rfl) (simpleC dC hRCcode) (by rw [hRCcode]; rfl) (by rw [hRCcode]; rfl)
  have hpn : dC.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "nextChildren", JSStr.ofString "renderLanes"] := by rw [hRCcode]; rfl
  have hv : dC.code.info.fdi.varNames = #[] := by rw [hRCcode]; rfl
  have hl : FDI.lexDecls dC = #[] := by simp [FDI.lexDecls, hRCcode, RChGen.reconcileChildren_func, Func.info]
  have ha : dC.code.isAsync = false := by rw [hRCcode]; rfl
  have hne : s.envs.size ≠ dU.env := Nat.ne_of_gt hE
  have hE1 : dU.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hRCcode
  simp only [RChGen.reconcileChildren]
  js [hpn, hv, hl, ha, hRCenv, hG, hG1, hneG, Ne.symm hneG, hGe, hGRCF, hGRCFv, hC0, hC0k, hC0c, hRF, hRFk, hR, hRk,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hR, hRk], ?_⟩
  refine wp_gen_state fun St hSt => ?_
  have hStO : ∀ o, St.objEntry o = s.objEntry o := by intro o; rw [hSt]; rfl
  have hStz : St.heap.size = s.heap.size := by rw [hSt]; rfl
  have hStE : St.envs.size = s.envs.size + 1 := by rw [hSt]; js_norm
  have hStF : St.fuel = s.fuel - 1 := by rw [hSt]; js_norm
  have hStU : St.envEntry dU.env = s.envEntry dU.env := by rw [hSt]; js_norm [hE, hne, Ne.symm hne]
  have hStg : Scope.declLike? (St.envEntry g) = some (bG, oG) := by rw [hSt]; js_norm [hG, hGe, hneG, Ne.symm hneG]
  have hStK : St.envEntry s.envs.size = (bodyState s fC dC tC #[.obj C0, .obj RF, .obj El, ln]).envEntry s.envs.size := by
    rw [hSt]
  have hF0 : Frame {} s St := by rw [hSt]; exact frame_bodyState (frame_refl _ s) _ _ _ _
  clear hSt
  refine wp_mono (ReactReconcileFibers.click_spec (bR := bR) (bG := bG) (g := g) (tR := .undefined)
      (hU := (by rw [hStz]; exact hU)) (hUk := (by rw [hStO]; exact hUk)) (hUcode := hUcode) (hUcls := hUcls)
      (hUmode := hUmode) (hE := (by rw [hStE]; exact Nat.lt_succ_of_lt hE)) (hEe := (by rw [hStU]; exact hEe))
      (hEn := hEn) (hG := (by rw [hStE]; exact Nat.lt_succ_of_lt hG)) (hGe := hStg) (hGC := hGC) (hGCv := hGCv)
      (hlt := (by rw [hStz]; exact hlt)) (hk := (by rw [hStO]; exact hk)) (hf := (by rw [hStF]; omega))
      (hcode := hcode) (hcls := hcls) (hmode := hmode) (hH := (by rw [hStz]; exact hH))
      (hHk := (by rw [hStO]; exact hHk)) (hX := (by rw [hStz]; exact hX)) (hXk := (by rw [hStO]; exact hXk))
      (hHX := hHX) (hHa := (by rw [hStO]; exact hHa)) (hHf := (by rw [hStO]; exact hHf))
      (hHd := (by rw [hStO]; exact hHd)) (hH_type := (by rw [hStO]; exact hH_type))
      (hH_childLanes := (by rw [hStO]; exact hH_childLanes)) (hH_lanes := (by rw [hStO]; exact hH_lanes))
      (hH_child := (by rw [hStO]; exact hH_child)) (hH_memoizedProps := (by rw [hStO]; exact hH_memoizedProps))
      (hH_memoizedState := (by rw [hStO]; exact hH_memoizedState))
      (hH_updateQueue := (by rw [hStO]; exact hH_updateQueue)) (hH_sibling := (by rw [hStO]; exact hH_sibling))
      (hH_index := (by rw [hStO]; exact hH_index)) (hH_ref := (by rw [hStO]; exact hH_ref))
      (hH_refCleanup := (by rw [hStO]; exact hH_refCleanup))
      (hX_pendingProps := (by rw [hStO]; exact hX_pendingProps)) (hX_type := (by rw [hStO]; exact hX_type))
      (hX_flags := (by rw [hStO]; exact hX_flags)) (hX_subtreeFlags := (by rw [hStO]; exact hX_subtreeFlags))
      (hX_deletions := (by rw [hStO]; exact hX_deletions)) (hX_childLanes := (by rw [hStO]; exact hX_childLanes))
      (hX_lanes := (by rw [hStO]; exact hX_lanes)) (hX_child := (by rw [hStO]; exact hX_child))
      (hX_memoizedProps := (by rw [hStO]; exact hX_memoizedProps))
      (hX_memoizedState := (by rw [hStO]; exact hX_memoizedState))
      (hX_updateQueue := (by rw [hStO]; exact hX_updateQueue))
      (hX_dependencies := (by rw [hStO]; exact hX_dependencies)) (hX_sibling := (by rw [hStO]; exact hX_sibling))
      (hX_index := (by rw [hStO]; exact hX_index)) (hX_ref := (by rw [hStO]; exact hX_ref))
      (hX_refCleanup := (by rw [hStO]; exact hX_refCleanup)) (hI := (by rw [hStz]; exact hI))
      (hIk := (by rw [hStO]; exact hIk)) (hIcode := hIcode) (hIcls := hIcls) (hImode := hImode) (hIenv := hIenv)
      (hRDel := hRDel) (hRDelv := hRDelv) (hDel := (by rw [hStz]; exact hDel))
      (hDelk := (by rw [hStO]; exact hDelk)) (hDelcode := hDelcode) (hDelcls := hDelcls) (hDelmode := hDelmode)
      (hDelenv := hDelenv) (hRUF := hRUF) (hRUFv := hRUFv) (hRPl := hRPl) (hRPlv := hRPlv)
      (hPl := (by rw [hStz]; exact hPl)) (hPlk := (by rw [hStO]; exact hPlk)) (hPlcode := hPlcode)
      (hPlcls := hPlcls) (hPlmode := hPlmode) (hPlenv := hPlenv) (hRST := hRST) (hRSTv := hRSTv) (hRnF := hRnF)
      (hRnE := hRnE) (hRnC := hRnC) (hGFr := hGFr) (hGFrv := hGFrv) (hGEl := hGEl) (hGElv := hGElv) (hFrs := hFrs)
      (hEls := hEls) (hFrEl := hFrEl) (hGCR := hGCR) (hGCRv := hGCRv) (hCR := (by rw [hStz]; exact hCR))
      (hCRk := (by rw [hStO]; exact hCRk)) (hCRcode := hCRcode) (hCRcls := hCRcls) (hCRmode := hCRmode)
      (hEl := (by rw [hStz]; exact hEl)) (hElk := (by rw [hStO]; exact hElk))
      (hEltyp := (by rw [hStO]; exact hEltyp)) (hElkey := (by rw [hStO]; exact hElkey))
      (hElty := (by rw [hStO]; exact hElty)) (hElp := (by rw [hStO]; exact hElp)) (hC := (by rw [hStz]; exact hC))
      (hCk := (by rw [hStO]; exact hCk)) (hCp := (by rw [hStO]; exact hCp)) (hCr := (by rw [hStO]; exact hCr))
      (hOP := (by rw [hStz]; exact hOP)) (hOPk := (by rw [hStO]; exact hOPk)) (hOPp := (by rw [hStO]; exact hOPp))
      (hOPr := (by rw [hStO]; exact hOPr)) (hHkey := (by rw [hStO]; exact hHkey))
      (hHet := (by rw [hStO]; exact hHet)) (hXa := (by rw [hStO]; exact hXa)) (hXret := (by rw [hStO]; exact hXret))
      (hdX := hdX) (hR := (by rw [hStz]; exact hR)) (hRk := (by rw [hStO]; exact hRk)) (hRcode := hRcode)
      (hRcls := hRcls) (hRmode := hRmode) (hRenv := hRenv) (hRRI := hRRI) (hRRIv := hRRIv) (hRnT := hRnT)
      (hRnS := hRnS) (hGT := hGT) (hGTm := hGTm) (hGTi := hGTi) (hGS := hGS) (hGSm := hGSm) (hGSi := hGSi)
      (hgU := hgU)) ?postR
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, hr1, hret1,
    hg1⟩
  subst v1 h1
  have hRFw : w1.objEntry RF = s.objEntry RF := by
    rw [objEntry_frame hF1 (by rw [hStz]; exact hRF) (by simp [fpR, fpI, ReactCreateWIP.fp, Ne.symm hRFX]), hStO]
  have hRFw1 : RF < w1.heap.size := Nat.lt_of_lt_of_le (by rw [hStz]; exact hRF) hF1.heap_le
  have hXw1 : X < w1.heap.size := Nat.lt_of_lt_of_le (by rw [hStz]; exact hX) hF1.heap_le
  have hw1K : w1.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF1 (by rw [hStE]; exact Nat.lt_succ_self _) (by simp [fpR, hneG, Ne.symm hneG])
  rw [hStK] at hw1K
  have hw1E : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by rw [hStE]; exact Nat.lt_succ_self _) hF1.envs_le
  js [hpn, hv, hl, ha, hRFw, hRFw1, hRF, hRFk, hRFc, hw1K, hw1E, FDI.fdiCtx, Sem.inner]
  have hFs : Frame (fpR g X) s St := frame_mono hF0 (fun p hp => by simp at hp) (fun p hp => by simp at hp)
    (fun _ => rfl)
  refine ⟨frame_restore (frame_mono (frame_setProp_prop (frame_extend hFs hF1 (by simp [fpR]) (by simp [fpR])
    (fun _ => rfl)) hRF _ _) ?_ ?_ ?_) s, by rw [hStF] at hfu1; omega, rfl⟩
  · intro p hp; simpa [fpC, fpR] using hp
  · intro p hp; revert p; simp [fpC, fpR, fpI, ReactCreateWIP.fp]
  · intro _; rfl


set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- `click_spec` with its callee as a contract (`facts_compose` composes it). -/
theorem click_spec_c {n : Nat}
    {h : σ}
    {fo : ObjId}
    {d : FuncData}
    {s : State}
    {fU : ObjId}
    {dU : FuncData}
    {bR bG : HashMap JSStr Binding}
    {g : EnvId}
    {bdCW : Binding}
    {H X : ObjId}
    {fl : F64}
    {vHT vCL vL vC vMP vMS vUQ vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value}
    {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    {oG : Option EnvId}
    -- (useFiber's record: the reconciler's closure, whose outer record is the module's)
    (hE : dU.env < s.envs.size)
    (hG : g < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hf : 170 ≤ s.fuel)
    (hX : X < s.heap.size)
    {fI fDel fPl fCR RF El C OP : ObjId}
    {dI dDel dPl dCR : FuncData}
    {ln vEl vFr : Value}
    {bdDel bdUF bdPl bdST bdFr bdEl bdCR : Binding}
    {ew ee ec kw ke kc yw ye yc pw pe pc bkw bke bkc bew bee bec aw ae ac rew rec : Bool}
    {rv0 : Value}
    -- (reconcileChildFibersImpl, in the reconciler's closure record, as are its helpers)
    -- (the module: the element and fragment symbols, coerceRef)
    -- (the new child: the button element; its props have no ref)
    -- (the current child: a button with no key and no sibling; its alternate, reused, points back to it)
    -- (the closures, the element, its props, Object.prototype are not the reused fiber)
    {fR : ObjId}
    {dR : FuncData}
    {bdRI bdT bdTS : Binding}
    -- (the reconciler's returned function, in its closure record; the module's thenable variables)
    (hR : fR < s.heap.size)
    (hRk : (s.objEntry fR).kind = .func dR)
    {fC C0 : ObjId}
    {dC : FuncData}
    {tC : Value}
    {bdRCF : Binding}
    {c0w c0e c0c cw cc : Bool}
    {ch0 : Value}
    -- (reconcileChildren, a module function; `reconcileChildFibers` the reconciler's returned function)
    (hRC : fC < s.heap.size)
    (hRCk : (s.objEntry fC).kind = .func dC)
    (hRCcode : dC.code = RChGen.reconcileChildren_func)
    (hRCcls : dC.isClassCtor = false)
    (hRCmode : dC.thisMode = .strict)
    (hRCenv : dC.env = g)
    (hGRCF : bG[JSStr.ofString "reconcileChildFibers"]? = some bdRCF)
    (hGRCFv : bdRCF.value = some (.obj fR))
    -- (the current fiber, whose child is the current button fiber; the work in progress's child)
    (hC0 : C0 < s.heap.size)
    (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hC0c : (s.objEntry C0).props.get? (.str "child") = some (.data (.obj H) c0w c0e c0c))
    (hRF : RF < s.heap.size)
    (hRFk : (s.objEntry RF).kind.isPlain = true)
    (hRFc : (s.objEntry RF).props.get? (.str "child") = some (.data ch0 true cw cc))
    (hRFX : RF ≠ X)
    (hcRF : ∀ w h1, Frame {} s w → 150 ≤ w.fuel →
      WP eng answer (n + 3) h1 (callImpl eng (.obj fR) .undefined #[.obj RF, .obj H, .obj El, ln]) w fun v w' h' =>
        v = .obj X ∧ Logic.Frame (fpR g X) w w' ∧ w.fuel ≤ w'.fuel + 150 ∧ h' = h1 ∧
        (w'.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj C) true e0 c0) ∧
        (w'.objEntry X).props.get? (.str "type") = some (.data (vHT) true e1 c1) ∧
        (w'.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd fl (F64.fin false 5062151534280704 (-22)))) true e2 c2) ∧
        (w'.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (F64.fin false 0 (-1074))) true e3 c3) ∧
        (w'.objEntry X).props.get? (.str "deletions") = some (.data (.null) true e4 c4) ∧
        (w'.objEntry X).props.get? (.str "childLanes") = some (.data (vCL) true e5 c5) ∧
        (w'.objEntry X).props.get? (.str "lanes") = some (.data (vL) true e6 c6) ∧
        (w'.objEntry X).props.get? (.str "child") = some (.data (vC) true e7 c7) ∧
        (w'.objEntry X).props.get? (.str "memoizedProps") = some (.data (vMP) true e8 c8) ∧
        (w'.objEntry X).props.get? (.str "memoizedState") = some (.data (vMS) true e9 c9) ∧
        (w'.objEntry X).props.get? (.str "updateQueue") = some (.data (vUQ) true e10 c10) ∧
        (w'.objEntry X).props.get? (.str "dependencies") = some (.data (.null) true e11 c11) ∧
        (w'.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12) ∧
        (w'.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13) ∧
        (w'.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14) ∧
        (w'.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) ∧
        w'.realm = w.realm ∧ (w'.objEntry X).props.get? (.str "return") = some (.data (.obj RF) true rew rec) ∧
        Scope.declLike? (w'.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
          (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
          (fun bd => { bd with value := some .null }), oG)) :
    WP eng answer (n + 4) h (callImpl eng (.obj fC) tC #[.obj C0, .obj RF, .obj El, ln]) s fun v w h' =>
      v = .undefined ∧ Logic.Frame (fpC g X RF) s w ∧ s.fuel ≤ w.fuel + 170 ∧ h' = h ∧
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
      w.realm = s.realm ∧ (w.objEntry X).props.get? (.str "return") = some (.data (.obj RF) true rew rec) ∧
      Scope.declLike? (w.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
        (fun bd => { bd with value := some .null }), oG) ∧
      (w.objEntry RF).props.get? (.str "child") = some (.data (.obj X) true cw cc) := by
  apply wp_callGen RChGen.reconcileChildren_eq (by decide) hRC hRCk (by omega) hRCcls hRCmode
    (by rw [hRCcode]; rfl) (by rw [hRCcode]; rfl) (simpleC dC hRCcode) (by rw [hRCcode]; rfl) (by rw [hRCcode]; rfl)
  have hpn : dC.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "nextChildren", JSStr.ofString "renderLanes"] := by rw [hRCcode]; rfl
  have hv : dC.code.info.fdi.varNames = #[] := by rw [hRCcode]; rfl
  have hl : FDI.lexDecls dC = #[] := by simp [FDI.lexDecls, hRCcode, RChGen.reconcileChildren_func, Func.info]
  have ha : dC.code.isAsync = false := by rw [hRCcode]; rfl
  have hne : s.envs.size ≠ dU.env := Nat.ne_of_gt hE
  have hE1 : dU.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hRCcode
  simp only [RChGen.reconcileChildren]
  js [hpn, hv, hl, ha, hRCenv, hG, hG1, hneG, Ne.symm hneG, hGe, hGRCF, hGRCFv, hC0, hC0k, hC0c, hRF, hRFk, hR, hRk,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hR, hRk], ?_⟩
  refine wp_gen_state fun St hSt => ?_
  have hStO : ∀ o, St.objEntry o = s.objEntry o := by intro o; rw [hSt]; rfl
  have hStz : St.heap.size = s.heap.size := by rw [hSt]; rfl
  have hStE : St.envs.size = s.envs.size + 1 := by rw [hSt]; js_norm
  have hStF : St.fuel = s.fuel - 1 := by rw [hSt]; js_norm
  have hStU : St.envEntry dU.env = s.envEntry dU.env := by rw [hSt]; js_norm [hE, hne, Ne.symm hne]
  have hStg : Scope.declLike? (St.envEntry g) = some (bG, oG) := by rw [hSt]; js_norm [hG, hGe, hneG, Ne.symm hneG]
  have hStK : St.envEntry s.envs.size = (bodyState s fC dC tC #[.obj C0, .obj RF, .obj El, ln]).envEntry s.envs.size := by
    rw [hSt]
  have hF0 : Frame {} s St := by rw [hSt]; exact frame_bodyState (frame_refl _ s) _ _ _ _
  clear hSt
  refine wp_mono (hcRF _ _ hF0 (by rw [hStF]; omega)) ?postR
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, hr1, hret1,
    hg1⟩
  subst v1 h1
  have hRFw : w1.objEntry RF = s.objEntry RF := by
    rw [objEntry_frame hF1 (by rw [hStz]; exact hRF) (by simp [fpR, fpI, ReactCreateWIP.fp, Ne.symm hRFX]), hStO]
  have hRFw1 : RF < w1.heap.size := Nat.lt_of_lt_of_le (by rw [hStz]; exact hRF) hF1.heap_le
  have hXw1 : X < w1.heap.size := Nat.lt_of_lt_of_le (by rw [hStz]; exact hX) hF1.heap_le
  have hw1K : w1.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF1 (by rw [hStE]; exact Nat.lt_succ_self _) (by simp [fpR, hneG, Ne.symm hneG])
  rw [hStK] at hw1K
  have hw1E : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by rw [hStE]; exact Nat.lt_succ_self _) hF1.envs_le
  js [hpn, hv, hl, ha, hRFw, hRFw1, hRF, hRFk, hRFc, hw1K, hw1E, FDI.fdiCtx, Sem.inner]
  have hFs : Frame (fpR g X) s St := frame_mono hF0 (fun p hp => by simp at hp) (fun p hp => by simp at hp)
    (fun _ => rfl)
  refine ⟨frame_restore (frame_mono (frame_setProp_prop (frame_extend hFs hF1 (by simp [fpR]) (by simp [fpR])
    (fun _ => rfl)) hRF _ _) ?_ ?_ ?_) s, by rw [hStF] at hfu1; omega, rfl⟩
  · intro p hp; simpa [fpC, fpR] using hp
  · intro p hp; revert p; simp [fpC, fpR, fpI, ReactCreateWIP.fp]
  · intro _; rfl

end

end ReactReconcileChildren
