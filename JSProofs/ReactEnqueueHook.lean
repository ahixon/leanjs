import JSProofs.ReactEnqueue
import JSProofs.ReactRoot
import JSProofs.ECHUGen

/-!
# React's `enqueueConcurrentHookUpdate` (zippy docs/react-proofs.md)

```js
function enqueueConcurrentHookUpdate(fiber, queue, update, lane) {
  enqueueUpdate$1(fiber, queue, update, lane);
  return getRootForUpdatedFiber(fiber);
}
```
The update is queued (`ReactEnqueue.call_spec`) and the root found (`ReactRoot.call_spec`): the second call's facts
(the module's `nestedUpdateCount`, `fiber.return`, the root fiber's properties) are read through the first call's
frame, since its footprint (two module variables, four queue elements, `fiber.lanes`) does not touch them.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEnqueueHook

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = ECHUGen.enqueueConcurrentHookUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [ECHUGen.enqueueConcurrentHookUpdate_func, Func.params, Func.info]

theorem call_spec {n : Nat} {h : σ} {fo fEU fGR : ObjId} {d dEU dGR : FuncData} {t queue update : Value}
    {s : State} {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdA bdI bdL bdN bdEU bdGR : Binding} {A F R Root : ObjId} {L c p fl : F64}
    {lw le lc fe fc aw ae ac sw se sc rw re rc tw te tc nw ne nc : Bool} {v0 v1 v2 v3 : Value}
    {e0 e1 e2 e3 c0 c1 c2 c3 xe xc : Bool} {Alt : ObjId} {al : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = ECHUGen.enqueueConcurrentHookUpdate_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGEU : bG[JSStr.ofString "enqueueUpdate$1"]? = some bdEU) (hGEUv : bdEU.value = some (.obj fEU))
    (hGGR : bG[JSStr.ofString "getRootForUpdatedFiber"]? = some bdGR) (hGGRv : bdGR.value = some (.obj fGR))
    -- (enqueueUpdate$1, its module facts)
    (hEU : fEU < s.heap.size) (hEUk : (s.objEntry fEU).kind = .func dEU)
    (hEUcode : dEU.code = EUGen.fn0_func) (hEUcls : dEU.isClassCtor = false) (hEUmode : dEU.thisMode = .strict)
    (hEUenv : dEU.env = d.env)
    (hGA : bG[JSStr.ofString "concurrentQueues"]? = some bdA) (hGAv : bdA.value = some (.obj A))
    (hGI : bG[JSStr.ofString "concurrentQueuesIndex"]? = some bdI)
    (hGIv : bdI.value = some (.num (F64.fin false 0 (-1074)))) (hGIm : bdI.mutable = true)
    (hGL : bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bdL) (hGLv : bdL.value = some (.num c))
    (hGLm : bdL.mutable = true)
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hA0 : (s.objEntry A).props.get? (.str "0") = some (.data v0 true e0 c0))
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data v1 true e1 c1))
    (hA2 : (s.objEntry A).props.get? (.str "2") = some (.data v2 true e2 c2))
    (hA3 : (s.objEntry A).props.get? (.str "3") = some (.data v3 true e3 c3))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hL4 : 4 ≤ (Conv.toNat? L).getD 0)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true) (hFA : F ≠ A)
    (hFl : (s.objEntry F).props.get? (.str "lanes") = some (.data (.num fl) true fe fc))
    (hFa : (s.objEntry F).props.get? (.str "alternate") = some (.data (.obj Alt) aw ae ac))
    (hX : Alt < s.heap.size) (hXk : (s.objEntry Alt).kind.isPlain = true) (hXA : Alt ≠ A) (hXF : Alt ≠ F)
    (hXl : (s.objEntry Alt).props.get? (.str "lanes") = some (.data (.num al) true xe xc))
    -- (getRootForUpdatedFiber, its module facts: F's parent R is the host root fiber)
    (hGRo : fGR < s.heap.size) (hGRk : (s.objEntry fGR).kind = .func dGR)
    (hGRcode : dGR.code = GRFGen.getRootForUpdatedFiber_func) (hGRcls : dGR.isClassCtor = false)
    (hGRmode : dGR.thisMode = .strict) (hGRenv : dGR.env = d.env) (hGRA : fGR ≠ A) (hGRF : fGR ≠ F) (hGRX : fGR ≠ Alt)
    (hGN : bG[JSStr.ofString "nestedUpdateCount"]? = some bdN)
    (hGNv : bdN.value = some (.num (F64.fin false 0 (-1074))))
    (hFr : (s.objEntry F).props.get? (.str "return") = some (.data (.obj R) sw se sc))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) (hRA : R ≠ A) (hRF : R ≠ F) (hRX : R ≠ Alt)
    (hRr : (s.objEntry R).props.get? (.str "return") = some (.data .null rw re rc))
    (hRt : (s.objEntry R).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (hRs : (s.objEntry R).props.get? (.str "stateNode") = some (.data (.obj Root) nw ne nc)) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj F, queue, update, .num p]) s fun v w _ =>
      v = .obj Root ∧
      Frame ⟨[(d.env, "concurrentQueuesIndex"), (d.env, "concurrentlyUpdatedLanes")],
        [(A, .str "0"), (A, .str "1"), (A, .str "2"), (A, .str "3"), (F, .str "lanes"), (Alt, .str "lanes")]⟩ s w ∧
      (w.objEntry F).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr fl p)) true fe fc) ∧
      s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen ECHUGen.enqueueConcurrentHookUpdate_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber", JSStr.ofString "queue",
      JSStr.ofString "update", JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, ECHUGen.enqueueConcurrentHookUpdate_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [ECHUGen.enqueueConcurrentHookUpdate]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGEU, hGEUv, hEU, hEUk, FDI.fdiCtx, Sem.inner]
  -- (`enqueueUpdate$1(fiber, queue, update, lane)`: its theorem)
  refine ⟨by simp [CallableC, hEU, hEUk], ?_⟩
  have hGe0 : Scope.declLike? ((bodyState s fo d t #[.obj F, queue, update, .num p]).envEntry dEU.env) =
      some (bG, oG) := by rw [hEUenv, bodyState_envEntry_lt _ _ _ _ _ _ hG, hGe]
  refine wp_mono (ReactEnqueue.call_spec (by simpa using hEU) (by simpa using hEUk) (by simp; omega) hEUcode
    hEUcls hEUmode (by simpa [hEUenv] using hG1) hGe0 hGA hGAv hGI hGIv hGIm hGL hGLv hGLm (by simpa using hA)
    (by simpa using hAk) (by simpa using hA0) (by simpa using hA1) (by simpa using hA2) (by simpa using hA3)
    (by simpa using hAL) hL4 (by simpa using hF) (by simpa using hFk) hFA (by simpa using hFl)
    (by simpa using hFa) (by simpa using hX) (by simpa using hXk) hXA hXF (by simpa using hXl)) ?_
  intro v w1 h1 ⟨hv, hF1, hfu, h0, h1', h2, h3, hlanes, hxlanes⟩
  subst hv
  rw [hEUenv] at hF1
  -- (what the call left: the caller's record exactly; the module's lookups outside its footprint; objects)
  have hE1 : w1.envEntry s.envs.size = (bodyState s fo d t #[.obj F, queue, update, .num p]).envEntry s.envs.size :=
    envEntry_frame hF1 (by simp) (by simp [hne, Ne.symm hne])
  have hagG := hF1.env_agree d.env (by simp; omega)
  unfold EnvAgree at hagG
  rw [bodyState_envEntry_lt _ _ _ _ _ _ hG, hGe] at hagG
  obtain ⟨bW, hW, hWx⟩ := hagG
  have hWGR : bW[JSStr.ofString "getRootForUpdatedFiber"]? = some bdGR := by rw [hWx _ (by simp)]; exact hGGR
  have hWN : bW[JSStr.ofString "nestedUpdateCount"]? = some bdN := by rw [hWx _ (by simp)]; exact hGN
  have hGw1 : d.env < w1.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF1.envs_le
  have hEw1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp) hF1.envs_le
  have hGR1 : w1.objEntry fGR = s.objEntry fGR := by
    rw [objEntry_frame hF1 (by simpa using hGRo) (by simp [hGRA, hGRF, hGRX, Ne.symm hGRA, Ne.symm hGRF, Ne.symm hGRX]), bodyState_objEntry]
  have hR1 : w1.objEntry R = s.objEntry R := by
    rw [objEntry_frame hF1 (by simpa using hR) (by simp [hRA, hRF, hRX, Ne.symm hRA, Ne.symm hRF, Ne.symm hRX]), bodyState_objEntry]
  have hFr1 : (w1.objEntry F).props.get? (.str "return") = some (.data (.obj R) sw se sc) := by
    rw [props_frame hF1 (by simpa using hF) (by simp [hFA, Ne.symm hFA, hXF, Ne.symm hXF]), bodyState_objEntry, hFr]
  have hFk1 : (w1.objEntry F).kind.isPlain = true := by
    rw [kind_frame hF1 (by simpa using hF), bodyState_objEntry]; exact hFk
  have hF1h : F < w1.heap.size := heap_frame hF1 (by simpa using hF)
  have hfu1 : 50 ≤ w1.fuel := by simp at hfu; omega
  js [hpn, hv, hl, ha, hne, Ne.symm hne, hE1, hW, hWGR, hGw1, hEw1, hGR1, hGRo, hGRk, FDI.fdiCtx, Sem.inner]
  -- (`getRootForUpdatedFiber(fiber)`: its theorem, in the state the first call left)
  have hGR1k : (w1.objEntry fGR).kind = .func dGR := by rw [hGR1]; exact hGRk
  refine ⟨by simp [CallableC, hGR1, hGRk, heap_frame hF1 (by simpa using hGRo)], ?_⟩
  refine wp_mono (ReactRoot.call_spec (heap_frame hF1 (by simpa using hGRo)) hGR1k (by omega) hGRcode hGRcls
    hGRmode (by rw [hGRenv]; exact hGw1) (by rw [hGRenv]; exact hW) hWN hGNv hF1h hFk1 hFr1
    (by rw [hR1] at *; exact heap_frame hF1 (by simpa using hR)) (by rw [hR1]; exact hRk) (by rw [hR1]; exact hRr)
    (by rw [hR1]; exact hRt) (by rw [hR1]; exact hRs)) ?_
  intro v w2 h2 ⟨hv, hF2, hfu2⟩
  subst hv
  -- (the result: the root; both frames composed; `fiber.lanes` as the first call left it)
  have hFr : Frame ⟨[(d.env, "concurrentQueuesIndex"), (d.env, "concurrentlyUpdatedLanes")],
      [(A, .str "0"), (A, .str "1"), (A, .str "2"), (A, .str "3"), (F, .str "lanes"), (Alt, .str "lanes")]⟩ s w2 := by
    simpa [Footprint.union] using
      frame_trans (frame_trans (frame_bodyState (frame_refl {} s) fo d t #[.obj F, queue, update, .num p]) hF1) hF2
  have hl2 : (w2.objEntry F).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr fl p)) true fe fc) := by
    rw [props_frame hF2 hF1h (by simp)]; exact hlanes
  simp only [StmtsWP_cons, StmtsWP_nil] at *
  refine ⟨trivial, frame_restore hFr s, hl2, ?_⟩
  show s.fuel ≤ w2.fuel + 10
  rw [bodyState_fuel] at hfu
  omega

end

end ReactEnqueueHook
