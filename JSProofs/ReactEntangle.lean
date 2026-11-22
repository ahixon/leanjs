import JSProofs.JsTactic
import JSProofs.ETUGen

/-!
# React's `entangleTransitionUpdate` for a click's lane (zippy docs/react-proofs.md)

```js
function entangleTransitionUpdate(root, queue, lane) {
  if (0 !== (lane & 4194048)) { … }
}
```
Only transition lanes entangle; a click's lane (`SyncLane`, 2) has none of those bits, so the call does nothing: it
returns `undefined`, writes nothing outside its own record, one step of fuel.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEntangle

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = ETUGen.entangleTransitionUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [ETUGen.entangleTransitionUpdate_func, Func.params, Func.info]

theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t root queue : Value} {s : State} {p : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = ETUGen.entangleTransitionUpdate_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hp : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd p (F64.fin false 9006649498927104 (-31)))) = true) :
    WP eng answer n h (callImpl eng (.obj fo) t #[root, queue, .num p]) s fun v w _ =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 := by
  apply wp_callGen ETUGen.entangleTransitionUpdate_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "queue", JSStr.ofString "lane"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "queueLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, ETUGen.entangleTransitionUpdate_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [ETUGen.entangleTransitionUpdate]
  js [hpn, hv, hl, ha, hp, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]
end

set_option maxRecDepth 100000 in
/-- The premise holds for a click's lane: `SyncLane` = 2 (`DiscreteEventPriority`). -/
example : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
    (.num (numberBinOp .bitAnd (F64.fin false 4503599627370496 (-51)) (F64.fin false 9006649498927104 (-31)))) = true :=
  by rfl

end ReactEntangle
