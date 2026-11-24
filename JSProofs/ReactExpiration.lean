import JSProofs.JsTactic
import JSProofs.CETGen

/-!
# React's `computeExpirationTime` for the sync lane (zippy docs/react-proofs.md)

`switch (lane) { case 1: case 2: case 4: case 8: case 64: return currentTime + 250; … }`: for `SyncLane` (2), the
time plus 250 ms. Reads only. The first proof through a `switch` (`Logic.wp_switchC`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactExpiration

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CETGen.computeExpirationTime_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CETGen.computeExpirationTime_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {tm : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CETGen.computeExpirationTime_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num (F64.fin false 4503599627370496 (-51)), .num tm]) s
      fun v w h' => v = .num (numberBinOp .add tm (F64.fin false 8796093022208000 (-45))) ∧ Frame {} s w ∧
        s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen CETGen.computeExpirationTime_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "lane", JSStr.ofString "currentTime"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CETGen.computeExpirationTime_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CETGen.computeExpirationTime]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

end ReactExpiration
