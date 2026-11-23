import JSProofs.RRPGen
import JSProofs.LTEPGen
import JSProofs.ReactFlushSync
import JSProofs.Rebase
import JSProofs.ReactHostContainer
import JSProofs.Setter

/-!
# flushSpawnedWork's small callees for the click (zippy docs/react-proofs.md)

`releaseRootPooledCache(root, 0)` with no pooled cache: the pooled cache lanes become 0, nothing released.
`lanesToEventPriority(SyncLane)`: 2 (DiscreteEventPriority), nothing written. `flushSyncWorkAcrossRoots_impl(0, false)`
while work is already being flushed (the commit runs inside the microtask's flush): nothing.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSpawnedCallees

theorem binaryOp_ne_null_null (s : State) (hf : s.fuel ≠ 0) :
    Sem.binaryOp .ne .null .null s = .ok (.bool false) s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [Sem.binaryOp, isLooselyEqual, M.bind_eq, M.bind_apply]; unfold repeatFrom; rw [hk]
  rfl

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple_rrp (d : FuncData) (hc : d.code = RRPGen.releaseRootPooledCache_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RRPGen.releaseRootPooledCache_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem rrp_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {FR : ObjId} {pl : F64}
    {lw le lc cw ce cc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = RRPGen.releaseRootPooledCache_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRl : (s.objEntry FR).props.get? (.str (JSStr.ofString "pooledCacheLanes")) = some (.data (.num pl) true le lc))
    (hFRc : (s.objEntry FR).props.get? (.str (JSStr.ofString "pooledCache")) = some (.data .null cw ce cc))
    (hpl : numberBinOp .bitAnd pl (F64.fin false 0 (-1074)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj FR, .num (F64.fin false 0 (-1074))]) s fun v w h' =>
      Frame ⟨[], [(FR, .str (JSStr.ofString "pooledCacheLanes"))], false⟩ s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h := by
  apply wp_callGen RRPGen.releaseRootPooledCache_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_rrp d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "remainingLanes"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RRPGen.releaseRootPooledCache_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [RRPGen.releaseRootPooledCache]
  js_until [] [hpl, hFR, hFRk, hFRl, hFRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_of_eq (binaryOp_ne_null_null _ (by simp; omega)) ?_
  js_until [] [hpl, hFR, hFRk, hFRl, hFRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨?pfr, ?pfu⟩
  case pfr => frame_go' [hFR]
  case pfu => first | omega | exact ⟨by omega, rfl⟩


theorem simple_ltep (d : FuncData) (hc : d.code = LTEPGen.lanesToEventPriority_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [LTEPGen.lanesToEventPriority_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- `lanesToEventPriority(SyncLane)` is `DiscreteEventPriority` (2). -/
theorem ltep_sync {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = LTEPGen.lanesToEventPriority_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.num (F64.fin false 4503599627370496 (-51))]) s fun v w h' =>
      v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h := by
  apply wp_callGen LTEPGen.lanesToEventPriority_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_ltep d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "lanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, LTEPGen.lanesToEventPriority_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have n2 : numberBinOp .bitAnd (F64.fin false 4503599627370496 (-51)) (F64.fin false 4503599627370496 (-51)).neg =
    F64.fin false 4503599627370496 (-51) := by decide +kernel
  clear hcode
  simp only [LTEPGen.lanesToEventPriority]
  js_until [] [n2, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨?pfr, ?pfu⟩
  case pfr => frame_go' []
  case pfu => first | omega | exact ⟨by omega, rfl⟩


set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- `flushSyncWorkAcrossRoots_impl(0, false)` while work is already being flushed: nothing. -/
theorem fsw_flushing {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bF : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = FSWGen.flushSyncWorkAcrossRoots_impl_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (gF : bG[JSStr.ofString "isFlushingWork"]? = some bF) (gFv : bF.value = some (.bool true)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.num (F64.fin false 0 (-1074)), .bool false]) s
      fun v w h' => Frame {} s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h := by
  apply wp_callGen FSWGen.flushSyncWorkAcrossRoots_impl_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (ReactFlushSync.simple d hcode) (by rw [hcode]; rfl)
    (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "syncTransitionLanes", JSStr.ofString "onlyLegacy"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "didPerformSomeWork", JSStr.ofString "root$190",
      JSStr.ofString "pendingLanes", JSStr.ofString "JSCompiler_inline_result", JSStr.ofString "suspendedLanes",
      JSStr.ofString "pingedLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, FSWGen.flushSyncWorkAcrossRoots_impl_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FSWGen.flushSyncWorkAcrossRoots_impl]
  js_until [] [e1, Ne.symm e1, e4, hG, hGe, gF, gFv, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨by frame_go' [], by omega⟩

end

end ReactSpawnedCallees
