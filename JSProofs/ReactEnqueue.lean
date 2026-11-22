import JSProofs.JsTactic
import JSProofs.EUGen

/-!
# React's `enqueueUpdate$1` (zippy docs/react-proofs.md)

```js
function enqueueUpdate$1(fiber, queue, update, lane) {
  concurrentQueues[concurrentQueuesIndex++] = fiber;
  concurrentQueues[concurrentQueuesIndex++] = queue;
  concurrentQueues[concurrentQueuesIndex++] = update;
  concurrentQueues[concurrentQueuesIndex++] = lane;
  concurrentlyUpdatedLanes |= lane;
  fiber.lanes |= lane;
  fiber = fiber.alternate;
  null !== fiber && (fiber.lanes |= lane);
}
```
An update is queued: four elements of the module's array, the queue's index, the lanes (the fiber's and, after the
first re-render, its alternate's: the steady state of every later click). The first React function
whose frame has a footprint (module variables, array elements, the fiber's `lanes`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEnqueue

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = EUGen.fn0_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [EUGen.fn0_func, Func.params, Func.info]

/-- The array's element `i` (a writable data property). -/
def Elem (s : State) (A : ObjId) (i : Nat) : Prop :=
  ∃ v e c, (s.objEntry A).props.get? (.str (numberToJSStr (Conv.ofNat i))) = some (.data v true e c)


theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t queue update : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdA bdI bdL : Binding} {A F : ObjId} {L c p fl : F64}
    {lw le lc fe fc aw ae ac xe xc : Bool} {Alt : ObjId} {al : F64} {v0 v1 v2 v3 : Value}
    {e0 e1 e2 e3 c0 c1 c2 c3 : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = EUGen.fn0_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
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
    (hXl : (s.objEntry Alt).props.get? (.str "lanes") = some (.data (.num al) true xe xc)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj F, queue, update, .num p]) s fun v w _ =>
      v = .undefined ∧
      Frame ⟨[(d.env, "concurrentQueuesIndex"), (d.env, "concurrentlyUpdatedLanes")],
        [(A, .str "0"), (A, .str "1"), (A, .str "2"), (A, .str "3"), (F, .str "lanes"), (Alt, .str "lanes")]⟩ s w ∧
      s.fuel ≤ w.fuel + 1 ∧
      (w.objEntry A).props.get? (.str "0") = some (.data (.obj F) true e0 c0) ∧
      (w.objEntry A).props.get? (.str "1") = some (.data queue true e1 c1) ∧
      (w.objEntry A).props.get? (.str "2") = some (.data update true e2 c2) ∧
      (w.objEntry A).props.get? (.str "3") = some (.data (.num p) true e3 c3) ∧
      (w.objEntry F).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr fl p)) true fe fc) ∧
      (w.objEntry Alt).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr al p)) true xe xc) := by
  apply wp_callGen EUGen.fn0_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber", JSStr.ofString "queue",
      JSStr.ofString "update", JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, EUGen.fn0_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hl0 : 0 < (Conv.toNat? L).getD 0 := by omega
  have hl1 : 1 < (Conv.toNat? L).getD 0 := by omega
  have hl2 : 2 < (Conv.toNat? L).getD 0 := by omega
  have hl3 : 3 < (Conv.toNat? L).getD 0 := by omega
  clear hcode
  simp only [EUGen.fn0]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGA, hGAv, hGI, hGIv, hGIm, hGL, hGLv, hGLm, hA, hAk,
    hA0, hA1, hA2, hA3, hAL, hl0, hl1, hl2, hl3, hF, hFk, hFA, Ne.symm hFA, hFl, hFa, hX, hXk, hXA, hXF, Ne.symm hXA, Ne.symm hXF, hXl,
    FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | omega | frame_go' [*, hG, hG1, hne, Ne.symm hne, hGe, hA, hF, hFA, Ne.symm hFA, hX, hXA, hXF]

end

end ReactEnqueue
