import JSProofs.ReactCreateWIP
import JSProofs.CCRGen

/-!
# The child reconciler's `useFiber` (zippy docs/react-proofs.md)

`useFiber(fiber, pendingProps)`: `createWorkInProgress` (`ReactCreateWIP.reuse_spec`: the alternate reused), then
its `index` 0 and `sibling` null.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactUseFiber

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleU (d : FuncData) (hc : d.code = CCRGen.useFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CCRGen.useFiber_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`useFiber(H, pp)`** when `H` has its alternate `X`: `X`, reset and copied from `H`, at index 0, no sibling. -/
theorem spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {pp : Value} {s : State} {fU : ObjId} {dU : FuncData} {tU : Value}
    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdCW : Binding}
    {H X : ObjId} {fl : F64} {vT vCL vL vC vMP vMS vUQ vS vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value} {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    (hU : fU < s.heap.size) (hUk : (s.objEntry fU).kind = .func dU) (hUcode : dU.code = CCRGen.useFiber_func)
    (hUcls : dU.isClassCtor = false) (hUmode : dU.thisMode = .strict)
    -- (useFiber's record: the reconciler's closure, whose outer record is the module's)
    (hE : dU.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dU.env) = some (bR, some g))
    (hEn : bR[JSStr.ofString "createWorkInProgress"]? = none)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, none))
    (hGC : bG[JSStr.ofString "createWorkInProgress"]? = some bdCW) (hGCv : bdCW.value = some (.obj fo))
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = CWIPGen.createWorkInProgress_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
        (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true) (hHX : H ≠ X)
    (hHa : (s.objEntry H).props.get? (.str "alternate") = some (.data (.obj X) r11w r11e r11c))
    (hHf : (s.objEntry H).props.get? (.str "flags") = some (.data (.num fl) r12w r12e r12c))
    (hHd : (s.objEntry H).props.get? (.str "dependencies") = some (.data .null r13w r13e r13c))
    (hH_type : (s.objEntry H).props.get? (.str "type") = some (.data vT r0w r0e r0c))
    (hH_childLanes : (s.objEntry H).props.get? (.str "childLanes") = some (.data vCL r1w r1e r1c))
    (hH_lanes : (s.objEntry H).props.get? (.str "lanes") = some (.data vL r2w r2e r2c))
    (hH_child : (s.objEntry H).props.get? (.str "child") = some (.data vC r3w r3e r3c))
    (hH_memoizedProps : (s.objEntry H).props.get? (.str "memoizedProps") = some (.data vMP r4w r4e r4c))
    (hH_memoizedState : (s.objEntry H).props.get? (.str "memoizedState") = some (.data vMS r5w r5e r5c))
    (hH_updateQueue : (s.objEntry H).props.get? (.str "updateQueue") = some (.data vUQ r6w r6e r6c))
    (hH_sibling : (s.objEntry H).props.get? (.str "sibling") = some (.data vS r7w r7e r7c))
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
    (hX_refCleanup : (s.objEntry X).props.get? (.str "refCleanup") = some (.data o15 true e15 c15)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fU) tU #[.obj H, pp]) s fun v w h' =>
      v = .obj X ∧ Logic.Frame (ReactCreateWIP.fp X) s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h ∧
      (w.objEntry X).props.get? (.str "pendingProps") = some (.data (pp) true e0 c0) ∧
      (w.objEntry X).props.get? (.str "type") = some (.data (vT) true e1 c1) ∧
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
      (w.objEntry X).props.get? (.str "ref") = some (.data (vR) true e14 c14) ∧
      (w.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) := by
  apply wp_callGen CCRGen.useFiber_eq (by decide) hU hUk (by omega) hUcls hUmode
    (by rw [hUcode]; rfl) (by rw [hUcode]; rfl) (simpleU dU hUcode) (by rw [hUcode]; rfl) (by rw [hUcode]; rfl)
  have hpn : dU.code.info.fdi.paramNames = #[JSStr.ofString "fiber", JSStr.ofString "pendingProps"] := by
    rw [hUcode]; rfl
  have hv : dU.code.info.fdi.varNames = #[] := by rw [hUcode]; rfl
  have hl : FDI.lexDecls dU = #[] := by simp [FDI.lexDecls, hUcode, CCRGen.useFiber_func, Func.info]
  have ha : dU.code.isAsync = false := by rw [hUcode]; rfl
  have hne : s.envs.size ≠ dU.env := Nat.ne_of_gt hE
  have hE1 : dU.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  have hneG : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hUcode
  simp only [CCRGen.useFiber]
  js [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hEn, hG, hG1, hneG, Ne.symm hneG, hGe, hGC, hGCv, hlt, hk,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hlt, hk], ?_⟩
  refine wp_mono (ReactCreateWIP.reuse_spec
      (hlt := hlt) (hk := hk) (hcode := hcode) (hcls := hcls) (hmode := hmode) (hH := hH) (hHk := hHk) (hX := hX)
      (hXk := hXk) (hHX := hHX) (hHa := hHa) (hHf := hHf) (hHd := hHd) (hH_type := hH_type)
      (hH_childLanes := hH_childLanes) (hH_lanes := hH_lanes) (hH_child := hH_child)
      (hH_memoizedProps := hH_memoizedProps) (hH_memoizedState := hH_memoizedState)
      (hH_updateQueue := hH_updateQueue) (hH_sibling := hH_sibling) (hH_index := hH_index) (hH_ref := hH_ref)
      (hH_refCleanup := hH_refCleanup) (hX_pendingProps := hX_pendingProps) (hX_type := hX_type)
      (hX_flags := hX_flags) (hX_subtreeFlags := hX_subtreeFlags) (hX_deletions := hX_deletions)
      (hX_childLanes := hX_childLanes) (hX_lanes := hX_lanes) (hX_child := hX_child)
      (hX_memoizedProps := hX_memoizedProps) (hX_memoizedState := hX_memoizedState)
      (hX_updateQueue := hX_updateQueue) (hX_dependencies := hX_dependencies) (hX_sibling := hX_sibling)
      (hX_index := hX_index) (hX_ref := hX_ref) (hX_refCleanup := hX_refCleanup) (hf := by js_norm; omega)) ?post
  intro v w h1 ⟨hv, hF, hfu, hh, hpp, hty, hfl, hsf, hdel, hcl, hln, hch, hmp, hms, huq, hdep, hsib, hidx, href, hrc⟩
  subst v h1
  have hX1 : X < w.heap.size := heap_frame hF (by js_norm [hX])
  have hXw : (w.objEntry X).kind.isPlain = true := by rw [kind_frame hF (by js_norm [hX])]; js_norm [hXk]
  have hEw : s.envs.size < w.envs.size := envs_frame hF (by js_norm)
  have hEwe : w.envEntry s.envs.size = (bodyState s fU dU tU #[.obj H, pp]).envEntry s.envs.size :=
    envEntry_frame hF (by js_norm) (by simp [ReactCreateWIP.fp])
  have hfw : 15 ≤ w.fuel := by simp only [js_simp] at hfu; omega
  js [hpn, hv, hl, ha, hEw, hEwe, hX1, hXw, hsib, hidx, hfw, FDI.fdiCtx, Sem.inner]
  refine ⟨?_, by simp only [js_simp] at hfu; omega⟩
  have hFs : Frame (ReactCreateWIP.fp X) s w := frame_mono (frame_trans (frame_bodyState (frame_refl ({} : Footprint) s)
    fU dU tU #[.obj H, pp]) hF) (fun p hp => by simpa [Footprint.union] using hp)
    (fun p hp => by simpa [Footprint.union] using hp) (fun _ => rfl)
  clear hF
  refine frame_restore ?_ s
  simp only [ReactCreateWIP.fp] at hFs ⊢
  frame_go' [hFs, hX, hX1]

end

end ReactUseFiber
